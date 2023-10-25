Require Import Coqlib.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import Any.
Require Import ModSem.
Require Import ModSemE.
(* Require Import ClightDmMem0. *)
Require Import ClightDmMem1.
From compcertip Require Export Ctypes Values AST Memdata Integers.

Set Implicit Arguments.

Section PROP.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memphyRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.

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
    | h :: t => ∃ hd_next i_hd_prev i_hd_next item,
                cast_to_int hd_prev i_hd_prev
                ** cast_to_int hd_next i_hd_next
                ** hd |-1#> ((encode_val Mint64 item) ++ (encode_val Mptr (Vptrofs (Ptrofs.xor i_hd_prev i_hd_next))))
                ** _is_xorlist hd hd_next tl t
    end%I.
  
  Definition is_xorlist := _is_xorlist Vnullptr. 

End PROP.


Section XORLIST.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memphyRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.

  (* The function only requires resource needed by capture *)
  Definition encrypt_spec : fspec :=
    (mk_simple
      (fun '(left_ptr, right_ptr) => (
            (ord_pure 1%nat),
            (fun varg => ⌜varg = [left_ptr; right_ptr]↑⌝
                          ** is_valid left_ptr
                          ** is_valid right_ptr),
            (fun vret => ∃ (i1 i2 : ptrofs), ⌜vret = (Vptrofs (Ptrofs.xor i1 i2))↑⌝
                         ** left_ptr ~~ i1
                         ** right_ptr ~~ i2
                         ** is_valid left_ptr ** is_valid right_ptr)
    ))).

  (* The function requires resource needed by capture *)
  Definition decrypt_spec : fspec :=
    (mk_simple
      (fun '(i1, ptr) => (
        (ord_pure 1%nat),
        (fun varg => ⌜exists key, varg = [key; ptr]↑ /\ key = Vptrofs i1⌝
                     ** is_valid ptr),
        (fun vret => ∃ i2 : ptrofs, ⌜vret = (Vptrofs (Ptrofs.xor i1 i2))↑⌝
                     ** ptr ~~ i2
                     ** is_valid ptr)
                     
    ))).
  
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
                     ⌜varg = [hd_handler; tl_handler; item; at_tail]↑
                     /\ exists intb, Vint intb = at_tail
                     /\ exists i, Vlong i = item⌝
                     ** hd_handler |-1#> encode_val Mptr hd_old
                     ** tl_handler |-1#> encode_val Mptr tl_old
                     ** is_xorlist hd_old tl_old xs),
        (fun vret => ∃ hd_new tail_new,
                     ⌜vret = Vundef↑⌝
                     ** hd_handler |-1> encode_val Mptr hd_new
                     ** tl_handler |-1> encode_val Mptr tl_new
                     ** is_xorlist hd_new tl_new (vlist_add item xs at_tail))
    ))).

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
        (fun varg => ∃ hd_old tl_old, ⌜varg = [hd_handler; tl_handler; from_tail]↑
                     /\ exists intb, Vint intb = from_tail⌝
                     ** hd_handler |-1#> encode_val Mptr hd_old
                     ** tl_handler |-1#> encode_val Mptr tl_old
                     ** is_xorlist hd_old tl_old xs),
        (fun vret => let '(Vlong i, xs') := vlist_delete xs from_tail (Vlong Int64.zero) in
                     ∃ head_new tail_new, ⌜vret = (Vlong i)↑⌝
                     ** hd_handler |-> encode_val Mptr head_new
                     ** tl_handler |-> encode_val Mptr tail_new
                     ** is_xorlist head_new tail_new xs')
    ))).

  (* {is_xorlist hd tl xs}
     node* search(node* hd, size_t index)
     {r. r = nth index xs 0 /\ is_xorlist hd tl xs} *)
 
  Definition search_spec : fspec :=
    (mk_simple
      (fun '(v_head, v_tail, p_head, p_tail, item, from_tail, xs) => (
        (ord_pure 2%nat),
        (fun varg => ∃ hd tl q1 q2,
                     ⌜varg = [hd_handler; tl_handler; from_tail; index]↑
                     /\ exists intb, Vint intb = from_tail
                     /\ exists i, Vptrofs i = index⌝
                     ** hd_handler |-q1#> encode_val Mptr hd
                     ** tl_handler |-q2#> encode_val Mptr tl
                     ** is_xorlist hd tl xs),
        (fun vret => let item := vnth index xs from_tail (Vlong Int64.zero) in
                     ∃ hd tl, ⌜vret = item↑⌝
                     ** hd_handler |-> encode_val Mptr hd
                     ** tl_handler |-> encode_val Mptr tl
                     ** is_xorlist hd tl xs)
    ))).
  
  Definition xorSbtb: list (gname * fspecbody) :=
    [("encrypt",  mk_pure encrypt_spec);
     ("decrypt",  mk_pure decrypt_spec);
     ("add",  mk_pure add_spec);
     ("delete",  mk_pure delete_spec);
     ("search",  mk_pure search_spec)
     ].
  
  Definition xorStb : list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun fsb => fsb.(fsb_fspec) : fspec)) xorSbtb) in
    let y := eval cbn in x in
      eapply y.
  Defined.
  
  Definition SxorSem : SModSem.t :=
    {|
      SModSem.fnsems := xorSbtb;
      SModSem.mn := "xorlist";
      SModSem.initial_mr := ε;
      SModSem.initial_st := tt↑;
    |}.
  
  Definition Sxor : SMod.t :=
    {|
      SMod.get_modsem := fun _ => SxorSem;
      SMod.sk := get_sk global_definitions;
    |}.
  
  Definition xor stb : Mod.t := (SMod.to_tgt stb) Sxor.
  
End XORLIST.