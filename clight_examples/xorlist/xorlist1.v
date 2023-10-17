Require Import Coqlib.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import Any.
Require Import ModSem.
Require Import ModSemE.
Require Import Clight_Mem0.
Require Import Clight_Mem1.
From compcertip Require Export Ctypes Values AST Memdata Integers.

Set Implicit Arguments.

Section DEFINITION.

  Context `{Σ : GRA.t}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG memRACAP Σ}.

  Definition pure_insert A (x : A) (l : list A) (from_tail : int) : list A :=
    if Int.eq from_tail Int.zero then x :: l
    else l ++ [x].
  
  Definition pure_delete A (l : list A) (from_tail : int) (default : A) : A * list A :=
    if Int.eq from_tail Int.zero then (hd default l, tl l)
    else (last l default, removelast l).

  Definition nullptr_cond := ((xH, 0%Z) ~~ 0).

  Definition val2ptr (v : val) : option (block * Z) :=
    match v with
    | Vptr b ofs => Some (b, Ptrofs.signed ofs)
    | _ => None
    end.

  Definition is_valid_ptr (v : val) (mvl : list memval) : iProp :=
    match v with
    | Vlong _ | Vint _ => (⌜ v = Vnullptr ⌝)%I
    | Vptr _ _ => (∃ p, ⌜ val2ptr v = Some p ⌝ ** (p |-> mvl))%I
    | _ => False%I
  end.
  
  (* xor operation between pointers => casting two (Vptr _ _) to (Vlong _) and apply xor operation for long value (Val.xorl) *)
  (* takes any value and return (Vlong _) *)
  
  Definition cast_to_intptr (v1 v2 : val) : iProp :=
    match v1 with
    | Vint i => (⌜ if Archi.ptr64 then Val.longofint v1 = v2 else v1 = v2 ⌝)%I
    | Vlong l => (⌜ if Archi.ptr64 then v2 = Vptrofs (Ptrofs.of_int64 l) else False ⌝)%I
    | Vptr _ _ => (∃ p i, ⌜ val2ptr v1 = Some p /\ v2 = Vptrofs i ⌝ ** (p ~~ Ptrofs.signed i))%I
    | _ => False%I
    end.
  

  
     (* is_xorlist represents the figure below    *)
     (*    ll_h                              ll_t *)
     (*     |                                 |   *)
     (*     v                                 v   *)
     (* xs  - - - - - - - - - - - - - - - - - -   *)
    
  Fixpoint _is_xorlist (ll_h_prev : val) (ll_h : val) (ll_t : val) (xs : list val) {struct xs} : iProp :=
    match xs with
    | [] => (⌜ll_h_prev = Vnullptr /\ ll_h = Vnullptr /\ ll_h = Vnullptr ⌝)%I (* null head and tail represents nil list *)
    | h :: t => (∃ (ll_next : val) (ptr_h ptr_t : block * Z) (ip_h_prev ip_next ip_xor : ptrofs) (xitem : int64),
                  ⌜ val2ptr ll_h = Some ptr_h /\ val2ptr ll_t = Some ptr_t /\ h = Vlong xitem ⌝
                  ** cast_to_intptr ll_h_prev (Vptrofs ip_h_prev)
                  ** cast_to_intptr ll_next (Vptrofs ip_next)
                  ** ⌜ Ptrofs.xor ip_h_prev ip_next = ip_xor ⌝
                  ** (ptr_h |-> ((encode_val Mint64 h) ++ (encode_val Mptr (Vptrofs ip_xor))))
                  ** _is_xorlist ll_h ll_next ll_t t)%I
    end.
  
  Definition is_xorlist := _is_xorlist Vnullptr. 

End DEFINITION.

Section XORLIST.

  Context `{Σ : GRA.t}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG memRACAP Σ}.

  (* {p1 |-> _ /\ p2 |-> _} encrypt(p1, p2) {r. r = x ^ y /\ p1 ~~ x /\ p2 ~~ y} *)
  Definition encrypt_spec : fspec :=
    mk_simple (X := val * val * list memval * list memval)
      (fun '(v1, v2, mvl1, mvl2) =>
         (ord_pure 1%nat,
           fun varg =>
             (⌜ varg = ([v1 ; v2])↑⌝
              ** is_valid_ptr v1 mvl1 ** is_valid_ptr v2 mvl2)%I,
            
           fun vret =>
             (∃ (i1 i2 : ptrofs), ⌜vret = (Vptrofs (Ptrofs.xor i1 i2))↑⌝
              ** cast_to_intptr v1 (Vptrofs i1) ** cast_to_intptr v2 (Vptrofs i2)
              ** is_valid_ptr v1 mvl1 ** is_valid_ptr v2 mvl2
             )%I
         )
      ).

  (* {p1 |-> _} decrypt(a, p1) {r. r = a ^ x /\ p1 ~~ x } *)
  Definition decrypt_spec : fspec :=
    mk_simple (X := _ * val * list memval)
      (fun '(ip_xor, v, mvl) =>
         (ord_pure 1%nat,
           fun varg =>
             (⌜ varg = ([Vptrofs ip_xor ; v])↑ ⌝
              ** is_valid_ptr v mvl)%I,
               
           fun vret =>
             (∃ (i : ptrofs), ⌜vret = (Vptrofs (Ptrofs.xor ip_xor i))↑⌝
               ** cast_to_intptr v (Vptrofs i) ** is_valid_ptr v mvl)%I
             
         )
      ).
  
  (* {ph |-> ll_h  /\ pt |-> ll_t /\ is_xorlist ll_h ll_t xs}                                        *)
  (* void insert(node** ph, node** pt, long item, bool from_tail)                                    *)
  (* {r. if ll_h = Null                                                                              *)
  (*     then exists ll_new, ph |-> ll_new /\ pt |-> ll_new /\ xorlist ll_new ll_new [item]          *)
  (*     else if from_tail = false                                                                   *)
  (*          then exists ll_new, ph |-> ll_new /\ pt |-> ll_t /\ xorlist ll_new ll_t (item :: xs)   *)
  (*          else exists ll_new, ph |-> ll_h /\ pt |-> ll_new /\ xorlist ll_h ll_new (xs ++ [item]) *)
  (* }                                                                                               *)
  
  Definition insert_spec : fspec :=
    mk_simple (X := val * val * _ * _ * int64 * int * list val)
      (fun '(v_head, v_tail, p_head, p_tail, item, from_tail, xs) =>
         (ord_pure 1%nat,
           fun varg =>
             (∃ (ll_h ll_t :val), ⌜ varg = ([v_head ; v_tail ; Vlong item ; Vint from_tail])↑
              /\ val2ptr v_head = Some p_head /\ val2ptr v_tail = Some p_tail ⌝
              ** (p_head |-> encode_val Mptr ll_h)
              ** (p_tail |-> encode_val Mptr ll_t)
              ** is_xorlist ll_h ll_t xs
              ** nullptr_cond)%I,
             
           fun vret =>
             let xs' := pure_insert (Vlong item) xs from_tail in
             (∃ (head_new tail_new : val),⌜vret = (Vundef)↑⌝
                 ** (p_head |-> encode_val Mptr head_new)
                 ** (p_tail |-> encode_val Mptr tail_new)
                 ** is_xorlist head_new tail_new xs'
             )%I
         )
      ).

  (* {ph |-> ll_h  /\ pt |-> ll_t /\ is_xorlist ll_h ll_t xs}                         *)
  (* void delete(node** ph, node** pt, bool from_tail)                                *)
  (* {r. exists ll_newh ll_newt, ph |-> ll_newh /\ pt |-> ll_newt                     *)
  (*     /\                                                                           *)
  (*     if ll_h = Null                                                               *)
  (*     then r = 0 /\ is_xorlist ll_h ll_t []                                        *)
  (*     else if from_tail = false                                                    *)
  (*          then r = last xs /\ is_xorlist ll_newh ll_newt (removelast xs)          *)
  (*          else r = hd xs /\ is_xorlist ll_newh ll_newt (tl xs)                    *) 
  (* }                                                                                *)
 
  Definition delete_spec : fspec :=
    mk_simple (X := val * val * _ * _ * int64 * int * list val)
      (fun '(v_head, v_tail, p_head, p_tail, item, from_tail, xs) =>
         (ord_pure 1%nat,
           fun varg =>
             (∃ (ll_h ll_t :val), ⌜ varg = ([v_head ; v_tail ; Vlong item ; Vint from_tail])↑
              /\ val2ptr v_head = Some p_head /\ val2ptr v_tail = Some p_tail ⌝
              ** (p_head |-> encode_val Mptr ll_h)
              ** (p_tail |-> encode_val Mptr ll_t)
              ** is_xorlist ll_h ll_t xs
              ** nullptr_cond)%I,
             
           fun vret =>
             let '(x, xs') := pure_delete xs from_tail (Vlong Int64.zero) in
             (∃ (head_new tail_new : val),⌜vret = x↑⌝
                 ** (p_head |-> encode_val Mptr head_new)
                 ** (p_tail |-> encode_val Mptr tail_new)
                 ** is_xorlist head_new tail_new xs'
             )%I
         )
      ).
  
  Definition xorSbtb: list (gname * fspecbody) :=
    [("encrypt",  mk_specbody encrypt_spec (fun _ => triggerNB));
     ("decrypt",  mk_specbody decrypt_spec (fun _ => triggerNB));
     ("insert",  mk_specbody insert_spec (fun _ => triggerNB));
     ("delete",  mk_specbody delete_spec (fun _ => triggerNB)) ].
  
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
      SMod.sk := Sk.unit;
    |}.
  
  Definition xor stb : Mod.t := (SMod.to_tgt stb) Sxor.
  
End XORLIST.