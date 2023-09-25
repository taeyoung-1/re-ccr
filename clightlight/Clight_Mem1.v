Require Import Coqlib.
Require Import ITreelib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
Require Import ProofMode.
Require Import Any.
From compcert Require Import Ctypes Floats Integers Values Memory AST Clight Clightdefs.

Set Implicit Arguments.


Let _memcntRA: URA.t := (block ==> Z ==> (Consent.t memval))%ra.
Let _memszRA: URA.t := (block ==> (Excl.t Z))%ra.

Compute (URA.car (t:=_memcntRA)).
Compute (URA.car (t:=_memszRA)).
Instance memcntRA: URA.t := Auth.t _memcntRA.
Instance memszRA: URA.t := Auth.t _memszRA.

Section RA.

Section POINTSTO.

  Local Open Scope Z.

  Definition __points_to (b: block) (ofs: Z) (q: Qnn) (mvs: list memval): _memcntRA :=
    (fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length mvs))))
                    then 
                      match List.nth_error mvs (Z.to_nat (_ofs - ofs)) with
                      | Some mv => Consent.just q mv
                      | None => ε
                      end
                    else ε)
  .

  (* Opaque _points_to. *)
  (* Lemma unfold__points_to b ofs vs:
    __points_to b ofs vs =
    (fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length vs))))%Z
                    then (List.nth_error vs (Z.to_nat (_ofs - ofs))) else ε)
  .
  Proof. refl. Qed. *)

  Definition _points_to (b: block) (ofs: Z) (q: Qnn) (mvs: list memval): memcntRA := Auth.white (__points_to b ofs q mvs).

  Lemma _points_to_split_aux
        blk ofs hd tl q
    :
      (_points_to blk ofs q (hd :: tl)) = (_points_to blk ofs q [hd]) ⋅ (_points_to blk (ofs + 1)%Z q tl)
  .
  Proof.
    ss. unfold _points_to, Auth.white. repeat (rewrite URA.unfold_add; ss).
    f_equal. unfold __points_to. ss.
    repeat (apply func_ext; i).
    des_ifs; bsimpl; des; des_sumbool; subst; ss;
      try rewrite Z.leb_gt in *; try rewrite Z.leb_le in *; try rewrite Z.ltb_ge in *; try rewrite Z.ltb_lt in *; try lia; clarify.
    - clear_tac. subst. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss. clarify. 
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq4; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss. clarify.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq4; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss. clarify.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq4; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss. clarify.
  Qed.

  Lemma __points_to_nil : forall blk ofs q _b _ofs, __points_to blk ofs q [] _b _ofs = ε.
  Proof.
    intros. unfold __points_to. ss. destruct ((ofs <=? _ofs) && (_ofs <? ofs + 0)) eqn : E; try nia.
    bsimpl. auto.
  Qed.

  Lemma points_to_nil : forall blk ofs q, _points_to blk ofs q [] = ε.
  Proof.
    intros. ss. unfold _points_to, Auth.white.
    change (memcntRA.(URA.unit)) with (Auth.frag (_memcntRA.(URA.unit))). f_equal. ss.
    repeat (apply func_ext; i). apply __points_to_nil.
  Qed.

  Lemma _points_to_app l l' q blk ofs:
    (_points_to blk ofs q (l++l')) = (_points_to blk ofs q l) ⋅ (_points_to blk (ofs + length l) q l').
  Proof.
    revert l' blk ofs. induction l;i;ss.
    - rewrite points_to_nil. rewrite URA.unit_idl. rewrite Z.add_0_r. auto.
    - rewrite _points_to_split_aux. rewrite (_points_to_split_aux blk ofs a l).
      replace (ofs + Z.pos (Pos.of_succ_nat (strings.length l)))
        with ((ofs + 1) + length l) by nia.
      rewrite <- URA.add_assoc. rewrite <- IHl. auto.
  Qed.

  Lemma _points_to_split :
    forall (blk : Values.block) (ofs : Z) (q: Qnn) (n : nat) (l : list memval),
      _points_to blk ofs q l =
        _points_to blk ofs q (firstn n l) ⋅ _points_to blk (ofs + (length (firstn n l))) q (skipn n l).
  Proof.
    intros. set l as k at 2 3 4. rewrite <- (firstn_skipn n l). unfold k. clear k.
    rewrite _points_to_app. auto.
  Qed.

End POINTSTO.

Section SZOF.

  Definition __sz_of (b: block) (sz: Z) : _memszRA :=
    (fun _b => if dec _b b
               then Excl.just sz
               else ε)
  .

  Definition _sz_of (b: block) (sz: Z) : memszRA := Auth.white (__sz_of b sz).

End SZOF.

End RA.

Section PROP.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memszRA Σ}.

  Definition updblk [A: Type] (i f: nat) (l l': list A) : list A := firstn i l ++ l' ++ skipn f l.
  Definition getblk [A: Type] (i delta: nat) (l: list A) : list A := firstn delta (skipn i l).

  Lemma getblk_updblk A (i delta: nat) (l: list A) : updblk i (i + delta) l (getblk i delta l) = l.
  Proof.
    unfold updblk, getblk. rewrite <- drop_drop. do 2 rewrite firstn_skipn. refl.
  Qed.

  Definition size_rule (sz: nat) : Z :=
    if sz <? 2 then 1
    else if sz <? 4 then 2
    else if sz <? 8 then 4
    else 8
  .

  Definition points_to addr q mvs : iProp :=
    match addr with
    | Vptr b ofs =>
          let ofs' := Ptrofs.unsigned ofs in
          let align := size_rule (Z.to_nat (length mvs)) in
          OwnM (_points_to b ofs' q mvs)
          ** ⌜(align | ofs')⌝
    | _ => ⌜False⌝%I 
    end.

  Definition mpoints_to addr sz mvs : iProp :=
    match addr with
    | Vptr b ofs =>
          let ofs' := Ptrofs.unsigned ofs in
          let align := size_rule (Z.to_nat sz) in
          OwnM (_points_to b ofs' 1 mvs) ** OwnM (_sz_of b sz)
          ** ⌜(align | ofs')⌝
    | _ => ⌜False⌝%I 
    end.

  Definition has_addr v b ofs : iProp :=
    match v with
    | Vptr b' ofs' => ⌜b' = b /\ Ptrofs.unsigned ofs' = ofs⌝%I
    | _ => ⌜False⌝%I 
    end.

  Definition allocated b sz : iProp := OwnM (_sz_of b sz).

  (* Lemma detach_size addr vs sz : (addr #↦ vs ⋯ sz) -∗ (addr ↦ vs).
  Proof. 
    iIntros "A". unfold mpoints_to, points_to. des_ifs.
    iDestruct "A" as "[B C]". iApply "B".
  Qed.

  Lemma asdf b ofs b' ofs' vs vs': Vptr b ofs ↦ vs ** Vptr b' ofs' ↦ vs' -∗ (Vptr b ofs ↦ vs ∧ Vptr b' ofs' ↦ vs').
  Proof.
    iIntros "A". iDestruct "A" as "[B C]".
    iSplit.
    - iApply "B".
    - iApply "C".
  Qed.
  Lemma _points_to_split :
    forall (blk: block) (ofs delta: ptrofs) (n: nat) (l: list memval)
    (IN_RANGE: 0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned delta < Ptrofs.modulus),
    n = Z.to_nat (Ptrofs.unsigned delta) ->
      Vptr blk ofs ↦ l -∗
        Vptr blk ofs ↦ (firstn n l) ** Vptr blk (Ptrofs.add ofs delta) (skipn (Z.to_nat (Ptrofs.unsigned delta)) l).
  Proof.
    intros. set l as k at 2 3 4. rewrite <- (firstn_skipn n l). unfold k. clear k.
    rewrite _points_to_app. auto.
  Qed.

  Lemma points_to_load :
    forall addr addr' (i delta : nat) l,
      0 <= i <= length l ->
      addr ↦ l -∗
       (addr' ↦ getblk i delta l **
         ((addr' ↦ getblk i delta l) -* (addr ↦ l))).
  Proof.
    intros. iIntros "A". unfold getblk, points_to. destruct H0 as [S1 S2].
    assert (S3 : Z.to_nat m ≤ strings.length l) by nia.
    pose proof (_points_to_split' blk ofs (Z.to_nat m) l S3) as Hr. set l as k at 4.
    rewrite Hr. unfold k. clear k.
    pose proof (_points_to_split blk (ofs + m) n (drop (Z.to_nat m) l)) as Ht.
    replace (ofs + Z.to_nat m) with (ofs + m) by nia.
    rewrite Ht. iDestruct "A" as "[A [B C]]".
    iSplitL "B";auto. iIntros "B". iCombine "B C" as "B". rewrite <- _points_to_split.
    iCombine "A B" as "A". replace (ofs + m) with (ofs + Z.to_nat m) by nia.
    rewrite <- _points_to_split';auto.
  Qed. *)

End PROP.

Notation "addr ↦ ( q , mvs )" := (points_to addr q mvs) (at level 20).
Notation "addr #↦ vs ⋯ sz" := (mpoints_to addr sz vs) (at level 10).

Section AUX.

  Context `{@GRA.inG memRA Σ}.

  (* Lemma points_to_disj
        ptr x0 x1
    :
      (ptr |-> [x0] -∗ ptr |-> [x1] -* ⌜False⌝)
  .
  Proof.
    destruct ptr as [blk ofs].
    iIntros "A B". iCombine "A B" as "A". iOwnWf "A" as WF0.
    unfold _points_to in WF0. rewrite ! unfold__points_to in *. repeat (ur in WF0); ss.
    specialize (WF0 blk ofs). des_ifs; bsimpl; des; SimComp.Coqlib.des_sumbool; zsimpl; ss; try lia.
  Qed. *)

  (** TODO-is_list **)
  (* Fixpoint is_list (ll: val) (xs: list val): iProp := *)
  (*   match xs with *)
  (*   | [] => (⌜ll = Vnullptr⌝: iProp)%I *)
  (*   | xhd :: xtl => *)
  (*     (∃ lhd ltl, ⌜ll = Vptr lhd (Ptrofs.repr 0)⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                            ** is_list ltl xtl: iProp)%I *)
  (*   end *)
  (* . *)

  (* Lemma unfold_is_list: forall ll xs, *)
  (*     is_list ll xs = *)
  (*     match xs with *)
  (*     | [] => (⌜ll = Vnullptr⌝: iProp)%I *)
  (*     | xhd :: xtl => *)
  (*       (∃ lhd ltl, ⌜ll = Vptr lhd (Ptrofs.repr 0)⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                              ** is_list ltl xtl: iProp)%I *)
  (*     end *)
  (* . *)
  (* Proof. *)
  (*   i. destruct xs; auto. *)
  (* Qed. *)

  (* Lemma unfold_is_list_cons: forall ll xhd xtl, *)
  (*     is_list ll (xhd :: xtl) = *)
  (*     (∃ lhd ltl, ⌜ll = Vptr lhd (Ptrofs.repr 0)⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                            ** is_list ltl xtl: iProp)%I. *)
  (* Proof. *)
  (*   i. eapply unfold_is_list. *)
  (* Qed. *)

  (* Lemma is_list_wf *)
  (*       ll xs *)
  (*   : *)
  (*     (is_list ll xs) -∗ (⌜(ll = Vnullptr) \/ (match ll with | Vptr _ ofs => Ptrofs.eq ofs (Ptrofs.repr 0) | _ => False end)⌝) *)
  (* . *)
  (* Proof. *)
  (*   iIntros "H0". destruct xs; ss; et. *)
  (*   { iPure "H0" as H0. iPureIntro. left. et. } *)
  (*   iDestruct "H0" as (lhd ltl) "[[H0 H1] H2]". *)
  (*   iPure "H0" as H0. iPureIntro. right. subst. et. *)
  (* Qed. *)

  (* Global Opaque is_list. *)
  (* Definition encode_list chunk vlist : list memval := flat_map (encode_val chunk) vlist. 
  
  Definition is_arr (chunk : memory_chunk) (ll : val) (xs : list val) :=
    (∃ (b :block) (ofs : ptrofs),
        ⌜ll = Vptr b ofs⌝ ** (b, Ptrofs.intval ofs) |-> (encode_list chunk xs))%I. *)
End AUX.

Definition wordsize_64 := 64%nat.
Definition modulus_64 := two_power_nat wordsize_64.
Definition modulus_64_half := (modulus_64 / 2)%Z.
Definition max_64 := (modulus_64_half - 1)%Z.
Definition min_64 := (- modulus_64_half)%Z.

(* Definition intrange_64 : Z -> Prop := fun z => (min_64 <= z <= max_64)%Z. *)
(* Definition modrange_64 : Z -> Prop := fun z => (- 1 < z < modulus_64)%Z. *)
Definition intrange_64 : Z -> bool := fun z => (Z_le_gt_dec min_64 z) && (Z_le_gt_dec z max_64).
Definition modrange_64 : Z -> bool := fun z => (Z_le_gt_dec 0 z) && (Z_lt_ge_dec z modulus_64).


Ltac unfold_intrange_64 := unfold intrange_64, min_64, max_64 in *; unfold modulus_64_half, modulus_64, wordsize_64 in *.
Ltac unfold_modrange_64 := unfold modrange_64, modulus_64, wordsize_64 in *.

Section PROOF.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memszRA Σ}.
  
  Definition salloc_spec: fspec :=
    (mk_simple (fun sz => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = sz↑⌝),
                    (fun vret => ∃ b addr, ⌜vret = b↑⌝
                                 ** addr ↦ (1, List.repeat Undef (Z.to_nat sz))
                                 ** has_addr addr b 0)
    )))%I.

  Definition sfree_spec: fspec :=
    (mk_simple (fun '() => (
                   (ord_pure 0%nat),
                   (fun varg => ∃ mvl addr b sz, ⌜varg = (b, sz)↑ /\ Z.of_nat (List.length mvl) = sz⌝
                                ** addr ↦ (1, mvl)
                                ** has_addr addr b 0),
                   (fun vret => ⌜vret = tt↑⌝)
    )))%I.

  Definition load_spec: fspec :=
    (mk_simple (fun '(chunk, addr, q, l) => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (chunk, addr)↑ /\ (0 ≤ q)%Qnn ⌝ ** addr ↦ (q, l)),
                    (fun vret => ∃ v, ⌜vret = v↑ /\ decode_val chunk l = v⌝ ** addr ↦ (q, l))
    )))%I.

  Definition loadbytes_spec: fspec :=
    (mk_simple (fun '(addr, q, n, l) => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (addr, n)↑ /\ Z.of_nat (List.length l) = n /\ (0 ≤ q)%Qnn⌝ ** addr ↦ (q, l)),
                    (fun vret => ⌜vret = l↑⌝ ** addr ↦ (q, l))
    ))).

  Definition store_spec: fspec :=
    (mk_simple
       (fun '(chunk, addr, v_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ l_old, ⌜varg = (chunk, addr, v_new)↑ /\ List.length l_old = size_chunk_nat chunk⌝
                         ** addr ↦ (1, l_old)),
            (fun vret => ∃ l_new, ⌜vret = tt↑ /\ encode_val chunk v_new = l_new⌝
                         ** addr ↦ (1, l_new))
    )))%I.

  Definition storebytes_spec: fspec :=
    (mk_simple
       (fun '(addr, l_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ l_old, ⌜varg = (addr, l_new)↑ /\ List.length l_old = List.length l_new⌝
                         ** addr ↦ (1, l_old)),
            (fun vret => ⌜vret = tt↑⌝ ** addr ↦ (1, l_new))
    )))%I.

  Definition valid_pointer_spec: fspec :=
    (mk_simple
       (fun '(result, iprop) => (
            (ord_pure 0%nat),
            (fun varg =>
            ((∃ addr q mvl, ⌜varg = addr↑ /\ iprop = (addr ↦ (q, mvl)) /\ result = true⌝) ∨
                (∃ addr q mvl, ⌜varg = addr↑ /\ iprop <> (addr ↦ (q, mvl)) /\ result = false⌝))
                ** iprop),
            (fun vret => ⌜vret = result↑⌝ ** iprop)%I
    )))%I.

  (* heap malloc free *)
  Definition malloc_spec: fspec :=
    (mk_simple (fun sz => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (Vptrofs sz)↑⌝),
                    (fun vret => ∃ addr b, ⌜vret = addr↑⌝
                                 ** addr #↦ List.repeat Undef (Z.to_nat (Ptrofs.unsigned sz)) ⋯ (Ptrofs.unsigned sz)
                                 ** has_addr addr b 0) 
    )))%I.

  Definition mfree_spec: fspec :=
    (mk_simple (fun '() => (
                    (ord_pure 0%nat),
                    (fun varg => ∃ mvl addr b sz, ⌜varg = addr↑ /\ Z.of_nat (List.length mvl) = sz⌝
                                 ** addr #↦ mvl ⋯ sz
                                 ** has_addr addr b 0),
                    (fun vret => ⌜vret = tt↑⌝)
    )))%I.

  
  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("salloc", salloc_spec); ("sfree", sfree_spec); 
           ("load", load_spec); ("loadbytes", loadbytes_spec); 
           ("store", store_spec); ("storebytes", storebytes_spec);
           ("valid_pointer", valid_pointer_spec);
           ("malloc", malloc_spec); ("mfree", mfree_spec)
           ].
    Defined.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("salloc", mk_specbody salloc_spec (fun _ => trigger (Choose _)));
    ("sfree",   mk_specbody sfree_spec (fun _ => trigger (Choose _)));
    ("load",   mk_specbody load_spec (fun _ => trigger (Choose _)));
    ("loadbytes",   mk_specbody loadbytes_spec (fun _ => trigger (Choose _)));
    ("store",  mk_specbody store_spec (fun _ => trigger (Choose _)));
    ("storebytes",   mk_specbody storebytes_spec (fun _ => trigger (Choose _)));
    ("valid_pointer",   mk_specbody valid_pointer_spec (fun _ => trigger (Choose _)));
    ("malloc",   mk_specbody malloc_spec (fun _ => trigger (Choose _)));
    ("mfree",   mk_specbody mfree_spec (fun _ => trigger (Choose _)))
    ]
  .

  Variable sk: Sk.t.
  Let skenv: SkEnv.t := Sk.load_skenv sk.

  (* have to make predicate *)
  Definition store_init_data (res : Σ) (b : block) (p : Z) (q: Qnn) (id : init_data) :=
    match id with
    | Init_int8 n => Some (GRA.embed (Auth.black (__points_to b p q (encode_val Mint8unsigned (Vint n)))) ⋅ res )
    | Init_int16 n => Some (GRA.embed (Auth.black (__points_to b p q (encode_val Mint16unsigned (Vint n)))) ⋅ res )
    | Init_int32 n => Some (GRA.embed (Auth.black (__points_to b p q (encode_val Mint32 (Vint n)))) ⋅ res)
    | Init_int64 n => Some (GRA.embed (Auth.black (__points_to b p q (encode_val Mint32 (Vlong n)))) ⋅ res)
    | Init_float32 n => Some (GRA.embed (Auth.black (__points_to b p q (encode_val Mfloat32 (Vsingle n)))) ⋅ res)
    | Init_float64 n => Some (GRA.embed (Auth.black (__points_to b p q (encode_val Mfloat64 (Vfloat n)))) ⋅ res)
    | Init_space _ => Some res
    | Init_addrof symb ofs =>
        match SkEnv.id2blk skenv (string_of_ident symb) with
        | Some b' => Some (GRA.embed (Auth.black (__points_to b p q (encode_val Mptr (Vptr (Pos.of_succ_nat b') ofs)))) ⋅ res)
        | None => None
        end
    end.

  Fixpoint store_init_data_list (res : Σ) (b : block) (p : Z) (q: Qnn) (idl : list init_data) {struct idl} : Σ :=
    match idl with
    | [] => res
    | id :: idl' =>
        match store_init_data res b p q id with
        | Some res' => store_init_data_list res' b (p + init_data_size id)%Z q idl'
        | None => GRA.embed (Auth.black _memcntRA.(URA.unit))
        end
    end.
  

  Program Definition qread : Qp := 
    {| Qp_to_Qc := {|Qcanon.this := {| QArith_base.Qnum := 1; QArith_base.Qden := 10 |}|}|}.
  Next Obligation. ss. Qed.

  Theorem qread_less: (qread < 1)%Qp.
  Proof. ss. Qed.

  Global Opaque qread. 

  Definition alloc_global (res : Σ) (b: block) (entry : string * Any.t) :=
    let (_, agd) := entry in
    match Any.downcast agd : option (globdef Clight.fundef type) with
    | Some g => 
      match g with
      | Gfun _ => GRA.embed (Auth.black (__points_to b 0 0 [Undef])) ⋅ res
      | Gvar v =>
        let init := gvar_init v in
        let q : Qnn := match Globalenvs.Genv.perm_globvar v with
                      | Freeable | Writable => 1%Qnn
                      | Readable => QP qread
                      | Nonempty => 0%Qnn
                      end
        in
        store_init_data_list res b 0 q init
      end
    | None => GRA.embed (Auth.black _memcntRA.(URA.unit))
    end.

  Fixpoint alloc_globals (res: Σ) (b: block) (sk: list (string * Any.t)) : Σ :=
  match sk with
  | nil => res
  | g :: gl' => alloc_globals (alloc_global res b g) (Pos.succ b) gl'
  end.

  Definition load_mem := alloc_globals (GRA.embed (Auth.black _memcntRA.(URA.unit))) xH sk.

  Definition SMemSem (sk: Sk.t): SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.mn := "Mem";
    SModSem.initial_mr := load_mem ⋅ (GRA.embed (Auth.black _memszRA.(URA.unit)));
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SMem: SMod.t := {|
    SMod.get_modsem := SMemSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition Mem: Mod.t := (SMod.to_tgt (fun _ => to_stb [])) SMem.

End PROOF.
Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
Global Opaque _sz_of.