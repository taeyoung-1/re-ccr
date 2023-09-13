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
From compcert Require Import Ctypes Floats Integers Values Memory AST.

Set Implicit Arguments.


Let _memcntRA: URA.t := (block ==> Z ==> (Excl.t memval))%ra.
Let _memszRA: URA.t := (block ==> (Excl.t nat))%ra.

Compute (URA.car (t:=_memcntRA)).
Compute (URA.car (t:=_memszRA)).
Instance memcntRA: URA.t := Auth.t _memcntRA.
Instance memszRA: URA.t := Auth.t _memszRA.

Section RA.

Section POINTSTO.

  Local Open Scope Z.

  Definition __points_to (b: block) (ofs: Z) (vs: list memval): _memcntRA :=
    (fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length vs))))
                    then (List.nth_error vs (Z.to_nat (_ofs - ofs))) else ε)
  .

  (* Opaque _points_to. *)
  (* Lemma unfold__points_to b ofs vs:
    __points_to b ofs vs =
    (fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length vs))))%Z
                    then (List.nth_error vs (Z.to_nat (_ofs - ofs))) else ε)
  .
  Proof. refl. Qed. *)

  Definition _points_to (b: block) (ofs: Z) (vs: list memval): memcntRA := Auth.white (__points_to b ofs vs).

  Lemma _points_to_split_aux
        blk ofs hd tl
    :
      (_points_to blk ofs (hd :: tl)) = (_points_to blk ofs [hd]) ⋅ (_points_to blk (ofs + 1)%Z tl)
  .
  Proof.
    ss. unfold _points_to, Auth.white. repeat (rewrite URA.unfold_add; ss).
    f_equal. unfold __points_to. ss.
    repeat (apply func_ext; i).
    des_ifs; bsimpl; des; des_sumbool; subst; ss;
      try rewrite Z.leb_gt in *; try rewrite Z.leb_le in *; try rewrite Z.ltb_ge in *; try rewrite Z.ltb_lt in *; try lia; clarify.
    - clear_tac. subst. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq1; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq1; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq1; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss.
  Qed.

  Lemma __points_to_nil : forall blk ofs _b _ofs, __points_to blk ofs [] _b _ofs = ε.
  Proof.
    intros. unfold __points_to. ss. destruct ((ofs <=? _ofs) && (_ofs <? ofs + 0)) eqn : E; try nia.
    bsimpl. auto.
  Qed.

  Lemma points_to_nil : forall blk ofs, _points_to blk ofs [] = ε.
  Proof.
    intros. ss. unfold _points_to, Auth.white.
    change (memcntRA.(URA.unit)) with (Auth.frag (_memcntRA.(URA.unit))). f_equal. ss.
    repeat (apply func_ext; i). apply __points_to_nil.
  Qed.

  Lemma _points_to_app l l' blk ofs:
    (_points_to blk ofs (l++l')) = (_points_to blk ofs l) ⋅ (_points_to blk (ofs + length l) l').
  Proof.
    revert l' blk ofs. induction l;i;ss.
    - rewrite points_to_nil. rewrite URA.unit_idl. rewrite Z.add_0_r. auto.
    - rewrite _points_to_split_aux. rewrite (_points_to_split_aux blk ofs a l).
      replace (ofs + Z.pos (Pos.of_succ_nat (strings.length l)))
        with ((ofs + 1) + length l) by nia.
      rewrite <- URA.add_assoc. rewrite <- IHl. auto.
  Qed.

  Lemma _points_to_split :
    forall (blk : Values.block) (ofs : Z) (n : nat) (l : list memval),
      _points_to blk ofs l =
        _points_to blk ofs (firstn n l) ⋅ _points_to blk (ofs + (length (firstn n l))) (skipn n l).
  Proof.
    intros. set l as k at 2 3 4. rewrite <- (firstn_skipn n l). unfold k. clear k.
    rewrite _points_to_app. auto.
  Qed.

End POINTSTO.

Section SZOF.

  Definition __sz_of (b: block) (sz: nat) : _memszRA :=
    (fun _b => if dec _b b
               then Excl.just sz
               else ε)
  .

  Definition _sz_of (b: block) (sz: nat) : memszRA := Auth.white (__sz_of b sz).

End SZOF.
  
  (** TODO-var **)
  (* Definition initial_mem_mr (csl: gname -> bool) (sk: Sk.t): _memRA := *)
  (*   fun blk ofs => *)
  (*     match List.nth_error sk (Pos.to_nat blk) with *)
  (*     | Some (g, gd) => *)
  (*       match gd with *)
  (*       | Sk.Gfun => ε *)
  (*       | Sk.Gvar gv => if csl g then if (dec ofs 0%Z) then Some (Vint (Int.repr gv)) else ε else ε *)
  (*       end *)
  (*     | _ => ε *)
  (*     end. *)

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

  Definition points_to addr vs : iProp :=
    match addr with
    | Vptr b ofs => OwnM (_points_to b (Ptrofs.unsigned ofs) vs)
    | _ => ⌜False⌝
    end.

  Definition mpoints_to addr sz vs : iProp :=
    match addr with
    | Vptr b ofs =>
        OwnM (_points_to b (Ptrofs.unsigned ofs) vs)
        ** OwnM (_sz_of b sz)
    | _ => ⌜False⌝
    end.

  Notation "addr ↦ vs" := (points_to addr vs) (at level 20).
  Notation "addr #↦ vs ⋯ sz" := (mpoints_to addr sz vs) (at level 10).

  Lemma detach_size addr vs sz : (addr #↦ vs ⋯ sz) -∗ (addr ↦ vs).
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
  Qed.

End PROP.


Section AUX.

  Context `{@GRA.inG memRA Σ}.

  Lemma points_to_disj
        ptr x0 x1
    :
      (ptr |-> [x0] -∗ ptr |-> [x1] -* ⌜False⌝)
  .
  Proof.
    destruct ptr as [blk ofs].
    iIntros "A B". iCombine "A B" as "A". iOwnWf "A" as WF0.
    unfold _points_to in WF0. rewrite ! unfold__points_to in *. repeat (ur in WF0); ss.
    specialize (WF0 blk ofs). des_ifs; bsimpl; des; SimComp.Coqlib.des_sumbool; zsimpl; ss; try lia.
  Qed.

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
  Definition encode_list chunk vlist : list memval := flat_map (encode_val chunk) vlist. 
  
  Definition is_arr (chunk : memory_chunk) (ll : val) (xs : list val) :=
    (∃ (b :block) (ofs : ptrofs),
        ⌜ll = Vptr b ofs⌝ ** (b, Ptrofs.intval ofs) |-> (encode_list chunk xs))%I.
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
  Context `{@GRA.inG memRA Σ}.

 Definition alloc_spec: fspec :=
    (mk_simple (fun '(lo, hi) => (
                    (ord_pure 0%nat),
                    (fun varg => (⌜varg = (lo, hi)↑ /\ (lo <= hi)%Z⌝)%I),
                    (fun vret => (∃ b, (⌜vret = b↑⌝
                                      ** ((b, lo) |-> (List.repeat Undef (Z.to_nat (hi - lo))))))%I
    )))).

  Definition free_spec: fspec :=
    (mk_simple (fun '() => (
                   (ord_pure 0%nat),
                   (fun varg => (∃ l b lo hi, (⌜varg = (b, lo, hi)↑ /\ Z.of_nat (List.length l) = hi - lo⌝) ** ((b, lo) |-> l))%I),
                    fun vret => ⌜vret = tt↑⌝%I
    ))).

  Definition load_spec: fspec :=
    (mk_simple (fun '(chunk, b, ofs, l) => (
                    (ord_pure 0%nat),
                    (fun varg => (⌜varg = (chunk, b, Ptrofs.repr ofs)↑⌝) ** ((b, ofs) |-> l)),
                    (fun vret => (∃ v, (b, ofs) |-> l ** ⌜vret = v↑ /\ decode_val chunk l = v⌝)%I)
    ))).

  Definition loadbytes_spec: fspec :=
    (mk_simple (fun '(b, ofs, n, l) => (
                    (ord_pure 0%nat),
                    (fun varg => (⌜varg = (b, Ptrofs.repr ofs, n)↑ /\ (Z.of_nat (List.length l) = n)⌝) ** (((b, ofs) |-> l))),
                    (fun vret => ((b, ofs) |-> l) ** ⌜vret = l↑⌝)
    ))).

  Definition store_spec: fspec :=
    (mk_simple
       (fun '(chunk, b, ofs, v_new) => (
            (ord_pure 0%nat),
            (fun varg => (∃ l_old, (⌜varg = (chunk, b, Ptrofs.repr ofs, v_new)↑ /\ List.length l_old = size_chunk_nat chunk⌝) ** ((b, ofs) |-> l_old))%I),
            (fun vret => (∃ l_new, ((b, ofs) |-> l_new) ** ⌜vret = tt↑ /\ encode_val chunk v_new = l_new⌝)%I)
    ))).

  Definition storebytes_spec: fspec :=
    (mk_simple
       (fun '(b, ofs, l_new) => (
            (ord_pure 0%nat),
            (fun varg => (∃ l_old, (⌜varg = (b, ofs, l_new)↑ /\ List.length l_old = List.length l_new⌝) ** ((b, ofs) |-> l_old))%I),
            (fun vret => ((b, ofs) |-> l_new) ** ⌜vret = tt↑⌝)
    ))).

  Definition valid_pointer_spec: fspec :=
    (mk_simple
       (fun '(result, resource) => (
            (ord_pure 0%nat),
            (fun varg =>
               ((∃ b ofs v, ⌜varg = (b, ofs)↑⌝ ** ⌜resource = (_points_to (b, ofs) [v])⌝ ** ⌜result = true⌝) ∨
                (∃ b ofs v, ⌜varg = (b, ofs)↑⌝ ** ⌜resource <> (_points_to (b, ofs) [v])⌝ ** ⌜result = false⌝))
                 ** OwnM (resource)
            ),
            (fun vret => OwnM(resource) ** ⌜vret = result↑⌝)
    ))).

  (* about capture *)
  
  (* { True } capture(p) { exists v, v.p ~ v } *)
  (* { p ~ v } (int)(p) { v } -> all pointer to int casting in C became capture and assign. *)
  (* { (p |-> _) * p ~ i } (ptr)i { r. r = p } *)

  (* p ~ i0 /\ p ~ i1 -> i0 = i1 *)
  (* p ~ i  ->  p+j ~ i+j *)

  (* p ~ i -> p~i * p~i *)

  Context `{@GRA.inG memRACAP Σ}.

  Definition capture_spec: fspec :=
    (@mk_simple _ (block * ptrofs)
       (fun '(b, ofs) => (
            (ord_pure 0%nat),
            (fun varg:Any.t => @bi_pure iProp (varg = (b, ofs)↑)),
            (fun vret => (∃ addr, ((b, Ptrofs.signed ofs) ~~ Ptrofs.signed addr) ** ⌜vret = addr↑⌝)%I)
    ))).

  (* Set Printing All. *)
  Definition int2ptr_spec: fspec :=
    (mk_simple
       (fun '(b, ofs) => (
            (ord_pure 0%nat),
            (fun varg:Any.t =>
               (∃ addr l, (⌜varg = addr↑⌝) ** ((b, ofs) ~~ addr) ** ((b, ofs) |-> l))%I
            ),
            (fun vret => (⌜vret = (b, ofs)↑⌝)%I)
    ))).

  (* Set Printing All. *)
  Definition ptr2int_spec: fspec :=
    (mk_simple
       (fun '(addr) => (
            (ord_pure 0%nat),
            (fun varg:Any.t =>
               (∃ b ofs, (⌜varg = (b, ofs)↑⌝) ** ((b, ofs) ~~ addr))%I
            ),
            (fun vret => (⌜vret = addr↑⌝)%I)
    ))).

  Context `{@GRA.inG memRASZ Σ}.

  Definition malloc_spec: fspec :=
    (mk_simple (fun sz => (
                    (ord_pure 0%nat),
                    (fun varg => (⌜varg = (Vint (Int.repr (Z.of_nat sz)))↑ /\ (8 * (Z.of_nat sz) < modulus_64)%Z⌝: iProp)%I),
                    (fun vret => (∃ b, (⌜vret = (Vptr b (Ptrofs.repr 0))↑⌝)
                                      ** ((b, 0%Z) |-> (List.repeat Undef sz))
                                      ** ((b, 0%Z) :== sz)): iProp)%I
    ))).

  (* malloc free *)
  Definition mfree_spec: fspec :=
    (mk_simple (fun '(b, ofs) => (
                    (ord_pure 0%nat),
                    (fun varg => (∃ l sz, (⌜varg = (b, ofs)↑ /\ Z.of_nat (List.length l) = sz⌝)
                                         ** ((b, ofs) |-> l)
                                         ** ((b, ofs) :== sz)
                              )%I),
                    fun vret => ⌜vret = tt↑⌝%I
    ))).

  
  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("alloc", alloc_spec); ("free", free_spec); ("load", load_spec);
           ("loadbytes", loadbytes_spec); ("store", store_spec); ("storebytes", storebytes_spec);
           ("valid_pointer", valid_pointer_spec); ("capture", capture_spec); ("int2ptr", int2ptr_spec);
           ("ptr2int", ptr2int_spec); ("malloc", malloc_spec); ("mfree", mfree_spec)
      ].
  Defined.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("alloc", mk_specbody alloc_spec (fun _ => trigger (Choose _)));
    ("free",   mk_specbody free_spec (fun _ => trigger (Choose _)));
    ("load",   mk_specbody load_spec (fun _ => trigger (Choose _)));
    ("loadbytes",   mk_specbody loadbytes_spec (fun _ => trigger (Choose _)));
    ("store",  mk_specbody store_spec (fun _ => trigger (Choose _)));
    ("storebytes",   mk_specbody storebytes_spec (fun _ => trigger (Choose _)));
    ("valid_pointer",   mk_specbody valid_pointer_spec (fun _ => trigger (Choose _)));
    ("capture",   mk_specbody capture_spec (fun _ => trigger (Choose _)));
    ("int2ptr",   mk_specbody int2ptr_spec (fun _ => trigger (Choose _)));
    ("ptr2int",   mk_specbody ptr2int_spec (fun _ => trigger (Choose _)));
    ("malloc",   mk_specbody malloc_spec (fun _ => trigger (Choose _)));
    ("mfree",   mk_specbody mfree_spec (fun _ => trigger (Choose _)))
    ]
  .

  Variable csl: gname -> bool.

  Definition SMemSem (sk: Sk.t): SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.mn := "Mem";
    (* SModSem.initial_mr := (GRA.embed (Auth.black (initial_mem_mr csl sk))); *)
    SModSem.initial_mr := (GRA.embed (Auth.black ε));
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
Global Opaque _relates_to.