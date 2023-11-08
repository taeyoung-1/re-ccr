Require Import Coqlib.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import Any.
Require Import ModSem.
Require Import ModSemE.
Require Import ClightDmMem1.
From compcertip Require Export Ctypes Values AST Memdata Integers.

Set Implicit Arguments.

Section PROP.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memphyRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.
  Context `{@GRA.inG memidRA Σ}.

  Definition vlist_add (x: val) (l : list val) (at_tail: val) : list val :=
    if Val.eq at_tail Vzero then x :: l else snoc l x.

  Definition vlist_delete (l: list val) (from_tail: val) (default: val) : val * list val :=
    if Val.eq from_tail Vzero then (hd default l, tl l)
    else (last l default, removelast l).

  Definition vnth (index: val) (l: list val) (from_tail: val) (default: val) : val :=
    match index with
    | Vint i => if Val.eq from_tail Vzero then nth (Z.to_nat (Int.unsigned i)) l default
                else nth (List.length l - Z.to_nat (Int.unsigned i) - 1) l default
    | Vlong i => if Val.eq from_tail Vzero then nth (Z.to_nat (Int64.unsigned i)) l default
                 else nth (List.length l - Z.to_nat (Int64.unsigned i) - 1) l default
    | _ => Vundef
    end.

     (* is_xorlist represents the figure below    *)
     (*    ll_h                              ll_t *)
     (*     |                                 |   *)
     (*     v                                 v   *)
     (* xs  - - - - - - - - - - - - - - - - - -   *)

  Fixpoint _is_xorlist (hd_prev : val) (hd : val) (tl : val) (xs : list val) {struct xs} : iProp :=
    match xs with
    | [] => ⌜hd_prev = Vnullptr /\ hd = Vnullptr /\ tl = Vnullptr⌝
    | h :: t => ∃ b_prev ofs_prev hd_next b_next ofs_next i_hd_prev i_hd_next item,
                hd_prev ⊸ (b_prev, ofs_prev)
                ** b_next ↱1# (8, Dynamic, Some i_hd_prev)
                ** hd_next ⊸ (b_next, ofs_next)
                ** b_next ↱1# (8, Dynamic, Some i_hd_next)
                ** hd ⊢1#> (encode_val Mint64 item
                            ++ encode_val Mptr (Vptrofs (Ptrofs.repr (Z.lxor i_hd_prev i_hd_next))))
                ** _is_xorlist hd hd_next tl t
    end%I.

  Definition is_xorlist := _is_xorlist Vnullptr. 

End PROP.


Section SPEC.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memphyRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.
  Context `{@GRA.inG memidRA Σ}.

  (* The function only requires resource needed by capture *)
  Definition encrypt_spec : fspec :=
    (mk_simple
      (fun '(left_ptr, right_ptr, b1, b2, sz1, sz2, tag1, tag2, q1, q2) => (
            (ord_pure 1%nat),
            (fun varg => ∃ ofs1 ofs2 opt1 opt2, ⌜varg = [left_ptr; right_ptr]↑⌝
                          ** left_ptr ⊸ (b1, ofs1)
                          ** b1 ↱q1# (sz1, tag1, opt1)
                          ** right_ptr ⊸ (b2, ofs2)
                          ** b2 ↱q2# (sz2, tag2, opt2)),
            (fun vret => ∃ i1 i2, ⌜vret = (Vptrofs (Ptrofs.repr (Z.lxor i1 i2)))↑⌝
                          ** b1 ↱q1# (sz1, tag1, Some i1)
                          ** b2 ↱q2# (sz2, tag2, Some i2))

    )))%I.

  (* The function requires resource needed by capture *)
  Definition decrypt_spec : fspec :=
    (mk_simple
      (fun '(i1, ptr, b, sz, tag, q) => (
        (ord_pure 1%nat),
        (fun varg => ∃ ofs opt key, ⌜varg = [key; ptr]↑ /\ key = Vptrofs i1⌝
                     ** ptr ⊸ (b, ofs)
                     ** b ↱q# (sz, tag, opt)),
        (fun vret => ∃ i2, ⌜vret = (Vptrofs (Ptrofs.xor i1 (Ptrofs.repr i2)))↑⌝
                     ** b ↱q# (sz, tag, Some i2))
                     
    )))%I.

  (* {hd_handler |-> hd  /\ tl_handler |-> tl /\ is_xorlist hd tl xs}
     void add(node** hd_handler, node** tl_handler, long item, bool at_tail)
     {r. if hd = null
         then exists new_node, hd_handler |-> new_node /\ tl_handler |-> new_node /\ is_xorlist new_node new_node [item]
         else if at_tail = false
              then exists new_hd, hd_handler |-> new_hd /\ tl_handler |-> tl /\ is_xorlist new_hd tl (item :: xs)
              else exists new_tl, hd_handler |-> hd /\ tl_handler |-> new_tl /\ is_xorlist hd new_tl (xs ++ [item])
     } *)

  Definition add_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, item, at_tail, xs) => (
        (ord_pure 2%nat),
        (fun varg => ∃ hd_old tl_old,
                     ⌜varg = [hd_handler; tl_handler; item; at_tail]↑⌝
                     (* item should be vlong *)
                     ** hd_handler ⊢1#> encode_val Mptr hd_old
                     ** tl_handler ⊢1#> encode_val Mptr tl_old
                     ** is_xorlist hd_old tl_old xs),
        (fun vret => ∃ hd_new tl_new,
                     ⌜vret = Vundef↑⌝
                     ** hd_handler ⊢1#> encode_val Mptr hd_new
                     ** tl_handler ⊢1#> encode_val Mptr tl_new
                     ** is_xorlist hd_new tl_new (vlist_add item xs at_tail))
    )))%I.

  (* {hd_handler |-> hd  /\ tl_handler |-> tl /\ is_xorlist hd tl xs}
     long delete(node** hd_handler, node** tl_handler, bool from_tail)
     {r. if hd = null
         then r = 0 /\ hd_handler |-> hd /\ tl_handler |-> tl /\ is_xorlist hd tl []
         else if from_tail = false
              then r = last xs /\ exists new_hd, hd_handler |-> new_hd /\ tl_handler |-> tl /\ is_xorlist new_hd tl (removelast xs)
              else r = hd xs /\ exists new_tl, hd_handler |-> hd /\ tl_handler |-> new_tl /\ is_xorlist hd new_tl (tl xs)
     } *)
  Definition delete_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, from_tail, xs) => (
        (ord_pure 2%nat),
        (fun varg => ∃ hd_old tl_old, ⌜varg = [hd_handler; tl_handler; from_tail]↑⌝
                     ** hd_handler ⊢1#> encode_val Mptr hd_old
                     ** tl_handler ⊢1#> encode_val Mptr tl_old
                     ** is_xorlist hd_old tl_old xs),
        (fun vret => let '(item, xs') := vlist_delete xs from_tail (Vlong Int64.zero) in
                     ∃ hd_new tl_new, ⌜vret = item↑⌝
                     ** hd_handler ⊢1#> encode_val Mptr hd_new
                     ** tl_handler ⊢1#> encode_val Mptr tl_new
                     ** is_xorlist hd_new tl_new xs')
    )))%I.

  (* {is_xorlist hd tl xs}
     node* search(node* hd, size_t index)
     {r. r = nth index xs 0 /\ is_xorlist hd tl xs} *)

  Definition search_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, from_tail, index, xs) => (
        (ord_pure 2%nat),
        (fun varg => ∃ hd tl,
                     ⌜varg = [hd_handler; tl_handler; from_tail; index]↑⌝
                     ** hd_handler ⊢1#> encode_val Mptr hd
                     ** tl_handler ⊢1#> encode_val Mptr tl
                     ** is_xorlist hd tl xs),
        (fun vret => let item := vnth index xs from_tail (Vlong Int64.zero) in
                     ∃ hd tl node link b ofs q opti, ⌜vret = node↑ /\ (q < 1)%Qp⌝
                     ** hd_handler ⊢1#> encode_val Mptr hd
                     ** tl_handler ⊢1#> encode_val Mptr tl
                     ** node ⊢q#> ((encode_val Mint64 item) ++ (encode_val Mptr link))
                     ** node ⊸ (b, ofs)
                     ** b ↱q# (8, Dynamic, opti)
                     ** is_xorlist hd tl xs)
    )))%I.

  (* sealed *)
  Definition xorStb : list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("encrypt", encrypt_spec);
           ("decrypt", decrypt_spec);
           ("add", add_spec);
           ("delete", delete_spec);
           ("search", search_spec)
           ].
  Defined.

End SPEC.

Require Import xorlist0.

Section SMOD.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memphyRA Σ}.
  Context `{@GRA.inG memidRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.

  Definition xorSbtb: list (gname * fspecbody) :=
    [("encrypt",  mk_pure encrypt_spec);
     ("decrypt",  mk_pure decrypt_spec);
     ("add",  mk_pure add_spec);
     ("delete",  mk_pure delete_spec);
     ("search",  mk_pure search_spec)
     ].
  
  Definition SxorSem : SModSem.t := {|
    SModSem.fnsems := xorSbtb;
    SModSem.mn := "xorlist";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}.
  
  Definition Sxor : SMod.t := {|
    SMod.get_modsem := fun _ => SxorSem;
    SMod.sk := xorlist0.xor.(Mod.sk);
  |}.
  
  Definition xor stb : Mod.t := (SMod.to_tgt stb) Sxor.
  
End SMOD.