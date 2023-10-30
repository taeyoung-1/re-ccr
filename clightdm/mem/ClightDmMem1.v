Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM IPM.
Require Import HoareDef STB.
From compcertip Require Import Floats Integers Values Memory AST Ctypes Clight Clightdefs.

Set Implicit Arguments.

Inductive tag :=
| Dynamic
| Local
| Unfreeable.

Let _memcntRA: URA.t := (block ==> Z ==> (Consent.t memval))%ra.
Let _memhdRA: URA.t := (block ==> (Consent.t (Z * tag)))%ra.

Compute (URA.car (t:=_memcntRA)).
Compute (URA.car (t:=_memhdRA)).
Instance memcntRA: URA.t := Auth.t _memcntRA.
Instance memphyRA: URA.t := (Z ==> (OneShot.t block))%ra.
Instance memidRA: URA.t := (block ==> (OneShot.t Z))%ra.
Instance memhdRA: URA.t := Auth.t _memhdRA.

Section POINTSTO.

  Local Open Scope Z.

  Definition __points_to (b: block) (ofs: Z) (mvs: list memval) (q: Qp): _memcntRA :=
    (fun _b _ofs => if (dec _b b) && ((Coqlib.zle ofs _ofs) && (Coqlib.zlt _ofs (ofs + Z.of_nat (List.length mvs))))
                    then 
                      match List.nth_error mvs (Z.to_nat (_ofs - ofs)) with
                      | Some mv => Consent.just q mv
                      | None => ε
                      end
                    else ε)
  .

  Definition _points_to (b: block) (ofs: Z) (mvs: list memval) (q: Qp): memcntRA := Auth.white (__points_to b ofs mvs q).

  (* Lemma _points_to_split_aux
        blk ofs hd tl q
    :
      (_points_to blk ofs (hd :: tl) q) = (_points_to blk ofs [hd] q) ⋅ (_points_to blk (ofs + 1)%Z tl q)
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

  Lemma __points_to_nil : forall blk ofs q _b _ofs, __points_to blk ofs [] _b _ofs q = ε.
  Proof.
    intros. unfold __points_to. ss. des_ifs. destruct (Z.to_nat _) in Heq0; ss. 
  Qed.

  Lemma points_to_nil : forall blk ofs q, _points_to blk ofs [] q = ε.
  Proof.
    intros. ss. unfold _points_to, Auth.white.
    change (memcntRA.(URA.unit)) with (Auth.frag (_memcntRA.(URA.unit))). f_equal. ss.
    repeat (apply func_ext; i). apply __points_to_nil.
  Qed.

  Lemma _points_to_app l l' q blk ofs:
    (_points_to blk ofs (l++l') q) = (_points_to blk ofs l q) ⋅ (_points_to blk (ofs + length l) l' q).
  Proof.
    revert l' blk ofs. induction l;i;ss.
    - rewrite points_to_nil. rewrite URA.unit_idl. rewrite Z.add_0_r. auto.
    - rewrite _points_to_split_aux. rewrite (_points_to_split_aux blk ofs a l).
      replace (ofs + Z.pos (Pos.of_succ_nat (strings.length l)))
        with ((ofs + 1) + length l) by nia.
      rewrite <- URA.add_assoc. rewrite <- IHl. auto.
  Qed.

  Lemma _points_to_split :
    forall (blk : Values.block) (ofs : Z) (q: Qp) (n : nat) (l : list memval),
      _points_to blk ofs l q =
        _points_to blk ofs (firstn n l) q ⋅ _points_to blk (ofs + (length (firstn n l))) (skipn n l) q.
  Proof.
    intros. set l as k at 2 3 4. rewrite <- (firstn_skipn n l). unfold k. clear k.
    rewrite _points_to_app. auto.
  Qed. *)

End POINTSTO.

Section RELATESTO.

  Definition _relates_to (b: block) (bID: Z) : memidRA :=
    (fun _b => if dec _b b
                then OneShot.white bID
                else ε)
  .

End RELATESTO.

Section ALLOCATEDWITH.

  Definition __allocated_with (b: block) (sz: Z) (tg: tag) (q: Qp) : _memhdRA :=
    (fun _b => if dec _b b
              then Consent.just q (sz, tg)
              else ε)
  .

  Definition _allocated_with (b: block) (sz: Z) (tg: tag) (q: Qp) : memhdRA := Auth.white (__allocated_with b sz tg q).

End ALLOCATEDWITH.

Section BELONGSTO.

  Definition _belongs_to (bID: Z) (sz: Z) (b: block) : memphyRA :=
    (fun _ofs => if (Coqlib.zle bID _ofs) && (Coqlib.zlt _ofs (bID + sz))
                 then OneShot.white b
                 else ε)
  .

End BELONGSTO.

Section PROP.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memphyRA Σ}.
  Context `{@GRA.inG memidRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.

  (* Definition updblk [A: Type] (i f: nat) (l l': list A) : list A := firstn i l ++ l' ++ skipn f l.
  Definition getblk [A: Type] (i delta: nat) (l: list A) : list A := firstn delta (skipn i l).

  (* how to use getblk, updblk *)
  Lemma getblk_updblk A (i delta: nat) (l: list A) : updblk i (i + delta) l (getblk i delta l) = l.
  Proof.
    unfold updblk, getblk. rewrite <- drop_drop. do 2 rewrite firstn_skipn. refl.
  Qed. *)

  Definition size_rule (sz: nat) : Z :=
    if lt_dec sz 2 then 1
    else if le_dec sz 4 then 2
    else if lt_dec sz 8 then 4
    else 8
  .

  Definition points_to addr mvs q : iProp :=
    match addr with
    | Vptr b ofs =>
          let ofs' := Ptrofs.unsigned ofs in
          let align := size_rule (Z.to_nat (length mvs)) in
          OwnM (_points_to b ofs' mvs q)
          ** ⌜(align | ofs')⌝
    | Vint i =>
        if Archi.ptr64 then ⌜False⌝%I
        else 
          let i' := Int.unsigned i in
          let align := size_rule (Z.to_nat (length mvs)) in
          (∃ b ofs, OwnM (_points_to b ofs mvs q) ** OwnM (_relates_to b (i' - ofs))
                    ** ⌜(align | ofs)⌝ ** ⌜(align | (i' - ofs))⌝)%I
    | Vlong i =>
        if negb Archi.ptr64 then ⌜False⌝%I
        else 
          let i' := Int64.unsigned i in
          let align := size_rule (Z.to_nat (length mvs)) in
          (∃ b ofs, OwnM (_points_to b ofs mvs q) ** OwnM (_relates_to b (i' - ofs))
                    ** ⌜(align | ofs)⌝ ** ⌜(align | (i' - ofs))⌝)%I
    | _ => ⌜False⌝%I 
    end.

  Definition allocated_with b sz tg opti q : iProp :=
    OwnM (_allocated_with b sz tg q)
    ** match opti with
       | Some i => OwnM (_belongs_to i sz b) ** OwnM (_relates_to b i)
       | None => ⌜True⌝
       end.

  Definition repr_to v b ofs : iProp :=
    match v with
    | Vptr b' ofs' => ⌜b' = b /\ Ptrofs.unsigned ofs' = ofs⌝%I
    | Vint i =>
        if Archi.ptr64 then ⌜False⌝%I
        else OwnM (_relates_to b (ofs - Int.unsigned i))
    | Vlong i =>
        if negb Archi.ptr64 then ⌜False⌝%I
        else OwnM (_relates_to b (ofs - Int64.unsigned i))
    | _ => ⌜False⌝%I 
    end.

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
        Vptr blk ofs ↦ (firstn n l) ** Vptr blk (Ptrofs.add ofs delta) (skipn n l).
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

Notation "addr |- q #> mvs" := (points_to addr mvs q) (at level 20).
Notation "b ↱ q # ( sz , tag , opti )" := (allocated_with b sz tag opti q) (at level 10).
Notation "addr ⊸ ( b , ofs ) " := (repr_to addr b ofs) (at level 10).

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

Section SPEC.
  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memphyRA Σ}.
  Context `{@GRA.inG memidRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.

  Definition salloc_spec: fspec :=
    (mk_simple (fun sz => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = sz↑⌝),
                    (fun vret => ∃ b vaddr, ⌜vret = b↑⌝
                                ** vaddr |-1#> List.repeat Undef (Z.to_nat sz)
                                ** b ↱1# (sz, Local, None)
                                ** vaddr ⊸ (b, 0))
    )))%I.

  Definition sfree_spec: fspec :=
    (mk_simple (fun '() => (
                  (ord_pure 0%nat),
                  (fun varg => ∃ mvl vaddr b sz opti,
                                ⌜varg = (b, sz)↑ /\ Z.of_nat (List.length mvl) = sz⌝
                                ** vaddr |-1#> mvl
                                ** b ↱1# (sz, Local, opti)
                                ** vaddr ⊸ (b, 0)),
                  (fun vret => ⌜vret = tt↑⌝)
    )))%I.

  Definition load_spec: fspec :=
    (mk_simple (fun '(chunk, vaddr, q, mvs) => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (chunk, vaddr)↑⌝
                                ** vaddr |-q#> mvs),
                    (fun vret => ∃ v, ⌜vret = v↑ /\ decode_val chunk mvs = v⌝
                                ** vaddr |-q#> mvs)
    )))%I.

  Definition loadbytes_spec: fspec :=
    (mk_simple (fun '(vaddr, sz, q, mvs) => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (vaddr, sz)↑ /\ Z.of_nat (List.length mvs) = sz⌝ 
                                ** vaddr |-q#> mvs),
                    (fun vret => ⌜vret = mvs↑⌝ ** vaddr |-q#> mvs)
    ))).

  Definition store_spec: fspec :=
    (mk_simple
      (fun '(chunk, vaddr, v_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ mvs_old, ⌜varg = (chunk, vaddr, v_new)↑
                                    /\ List.length mvs_old = size_chunk_nat chunk⌝
                                    ** vaddr |-1#> mvs_old),
            (fun vret => ∃ mvs_new, ⌜vret = tt↑ /\ encode_val chunk v_new = mvs_new⌝
                                    ** vaddr |-1#> mvs_new)
    )))%I.

  Definition storebytes_spec: fspec :=
    (mk_simple
      (fun '(vaddr, mvs_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ mvs_old, ⌜varg = (vaddr, mvs_new)↑
                                    /\ List.length mvs_old = List.length mvs_new⌝
                                    ** vaddr |-1#> mvs_old),
            (fun vret => ⌜vret = tt↑⌝ ** vaddr |-1#> mvs_new)
    )))%I.
  
  Local Open Scope Z.
  
  Definition cmp_ofs (c: comparison) (ofs0 ofs1: Z) :=
    match c with
    | Ceq => ofs0 =? ofs1
    | Cne => negb (ofs0 =? ofs1)
    | Clt => ofs0 <? ofs1
    | Cle => ofs0 <=? ofs1
    | Cgt => ofs0 >? ofs1
    | Cge => ofs0 >=? ofs1
    end.
  
  Definition cmp_ptr_hoare0 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(c) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (c, Vnullptr, Vnullptr)↑⌝ ),
            (fun vret => ⌜vret = match c with
                                 | Ceq => true↑
                                 | _ => false↑
                                 end⌝)
          )%I.

  Definition cmp_ptr_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(b, q, sz, tg, opti) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr ofs, ⌜varg = (Ceq, Vnullptr, vaddr)↑ /\ 0 ≤ ofs ≤ sz⌝
                         ** vaddr ⊸ (b, ofs)
                         ** b ↱q# (sz, tg, opti)),
            (fun vret => ⌜vret = false↑⌝ ** b ↱q# (sz, tg, opti))
          )%I.

  Definition cmp_ptr_hoare2 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(b, q, sz, tg, opti) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr ofs, ⌜varg = (Cne, Vnullptr, vaddr)↑ /\ 0 ≤ ofs ≤ sz⌝
                         ** vaddr ⊸ (b, ofs)
                         ** b ↱q# (sz, tg, opti)),
            (fun vret => ⌜vret = true↑⌝ ** b ↱q# (sz, tg, opti))
          )%I.

  Definition cmp_ptr_hoare3 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(b, q, sz, tg, opti) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr ofs, ⌜varg = (Ceq, vaddr, Vnullptr)↑ /\ 0 ≤ ofs ≤ sz⌝
                         ** vaddr ⊸ (b, ofs)
                         ** b ↱q# (sz, tg, opti)),
            (fun vret => ⌜vret = false↑⌝ ** b ↱q# (sz, tg, opti))
          )%I.

  Definition cmp_ptr_hoare4 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(b, q, sz, tg, opti) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr ofs, ⌜varg = (Cne, vaddr, Vnullptr)↑ /\ 0 ≤ ofs ≤ sz⌝
                         ** vaddr ⊸ (b, ofs)
                         ** b ↱q# (sz, tg, opti)),
            (fun vret => ⌜vret = true↑⌝ ** b ↱q# (sz, tg, opti))
          )%I.

  Definition cmp_ptr_hoare5 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(c, ofs0, ofs1, b, q, sz, tg, opti) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr0 vaddr1, ⌜varg = (c, vaddr0, vaddr1)↑ /\ 0 ≤ ofs0 ≤ sz /\ 0 ≤ ofs1 ≤ sz⌝
                         ** vaddr0 ⊸ (b, ofs0)
                         ** vaddr1 ⊸ (b, ofs1)
                         ** b ↱q# (sz, tg, opti)),
            (fun vret => ⌜vret = (cmp_ofs c ofs0 ofs1)↑⌝ ** b ↱q# (sz, tg, opti))
          )%I.

  Definition cmp_ptr_hoare6 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(b0, ofs0, q0, sz0, tg0, opti0, b1, ofs1, q1, sz1, tg1, opti1) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr0 vaddr1, ⌜varg = (Ceq, vaddr0, vaddr1)↑ /\ 0 ≤ ofs0 < sz0 /\ 0 ≤ ofs1 < sz1⌝
                         ** vaddr0 ⊸ (b0, ofs0)
                         ** vaddr1 ⊸ (b1, ofs1)
                         ** b0 ↱q0# (sz0, tg0, opti0)
                         ** b1 ↱q1# (sz1, tg1, opti1)),
            (fun vret => ⌜vret = false↑⌝ 
                         ** b0 ↱q0# (sz0, tg0, opti0)
                         ** b1 ↱q1# (sz1, tg1, opti1))
          )%I.

  Definition cmp_ptr_hoare7 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(b0, ofs0, q0, sz0, tg0, opti0, b1, ofs1, q1, sz1, tg1, opti1) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr0 vaddr1, ⌜varg = (Cne, vaddr0, vaddr1)↑ /\ 0 ≤ ofs0 < sz0 /\ 0 ≤ ofs1 < sz1⌝
                         ** vaddr0 ⊸ (b0, ofs0)
                         ** vaddr1 ⊸ (b1, ofs1)
                         ** b0 ↱q0# (sz0, tg0, opti0)
                         ** b1 ↱q1# (sz1, tg1, opti1)),
            (fun vret => ⌜vret = true↑⌝ 
                         ** b0 ↱q0# (sz0, tg0, opti0)
                         ** b1 ↱q1# (sz1, tg1, opti1))
          )%I.

  Definition cmp_ptr_spec: fspec :=
    mk_simple (
      cmp_ptr_hoare0
      @ cmp_ptr_hoare1
      @ cmp_ptr_hoare2
      @ cmp_ptr_hoare3
      @ cmp_ptr_hoare4
      @ cmp_ptr_hoare5
      @ cmp_ptr_hoare6
      @ cmp_ptr_hoare7
    ).

  Definition sub_ptr_spec: fspec :=
    (mk_simple
      (fun '(ofs0, ofs1, sz) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr0 vaddr1 b,
                        ⌜varg = (sz, vaddr0, vaddr1)↑ /\ 0 < sz ≤ Ptrofs.max_signed⌝
                        ** vaddr0 ⊸ (b, ofs0)
                        ** vaddr1 ⊸ (b, ofs1)),
            (fun vret => ⌜vret = (Vptrofs (Ptrofs.repr (Z.div (ofs0 - ofs1) sz)))↑⌝)
    )))%I.

  Definition non_null_spec: fspec :=
    (mk_simple
      (fun '(b, q, sz, tg, opti) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr ofs, ⌜varg = vaddr↑ /\ 0 ≤ ofs ≤ sz⌝
                        ** vaddr ⊸ (b, ofs)
                        ** b ↱q# (sz, tg, opti)),
            (fun vret => ⌜vret = true↑⌝ 
                        ** b ↱q# (sz, tg, opti))
    )))%I.

  (* heap malloc free *)
  Definition malloc_spec: fspec :=
    (mk_simple (fun sz => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = [Vptrofs sz]↑⌝),
                    (fun vret => ∃ vaddr b, ⌜vret = vaddr↑⌝
                                ** vaddr |-1#> List.repeat Undef (Z.to_nat (Ptrofs.unsigned sz))
                                ** b ↱1# (Ptrofs.unsigned sz, Dynamic, None)
                                ** vaddr ⊸ (b, 0)) 
    )))%I.

  Definition mfree_spec: fspec :=
    (mk_simple (fun '() => (
                    (ord_pure 0%nat),
                    (fun varg => ∃ mvs vaddr b sz opti,
                                ⌜varg = [vaddr]↑ /\ Z.of_nat (List.length mvs) = sz⌝
                                ** vaddr |-1#> mvs
                                ** b ↱1# (sz, Dynamic, opti)
                                ** vaddr ⊸ (b, 0)),
                    (fun vret => ⌜vret = Vundef↑⌝)
    )))%I.

  Definition memcpy_resource (vaddr vaddr': val) (mvs_src mvs_dst: list memval) : iProp :=
    if Val.eq vaddr' vaddr then vaddr |-1#> mvs_dst
    else vaddr' |-1#> mvs_src ** vaddr |-1#> mvs_dst.

  Definition memcpy_spec: fspec :=
    (mk_simple
       (fun '(vaddr, vaddr', mvs_dst) => (
            (ord_pure 0%nat),
            (fun varg => ∃ al sz mvs_src,
                         ⌜varg = (al, sz, [vaddr; vaddr'])↑
                         /\ List.length mvs_src = List.length mvs_dst
                         /\ List.length mvs_dst = sz
                         /\ (al | sz)⌝
                         ** memcpy_resource vaddr vaddr' mvs_src mvs_dst),
            (fun vret => ⌜vret = Vundef↑⌝ ** memcpy_resource vaddr vaddr' mvs_dst mvs_dst)
    )))%I.
  
  (* Inductive is_pretty : iProp -> Prop :=
  | is_points_to vaddr q mv : is_pretty (vaddr |-q#> mv)
  | is_relates_to vaddr b ofs : is_pretty (vaddr ⊸ (b, ofs))
  | is_conj ip1 ip2 (I1: is_pretty ip1) (I2: is_pretty ip2) : is_pretty (ip1 ** ip2)
  | is_wand ip1 ip2 (IC: is_pretty ip2) : is_pretty (ip1 -* ip2)
  . *)

  Definition capture_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(i) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = [Vptrofs i]↑⌝),
            (fun vret => ⌜vret = (Vptrofs i)↑⌝ )
          )%I.

  Definition capture_hoare2 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(b, q, sz, tg) => (
            (ord_pure 0%nat),
            (fun varg => ∃ ofs opti, ⌜varg = [Vptr b ofs]↑⌝ ** b ↱q# (sz, tg, opti)),
            (fun vret => ∃ i, ⌜vret = (Vptrofs i)↑⌝ ** b ↱q# (sz, tg, Some (Ptrofs.unsigned i)) )
          )%I.

  Definition capture_spec: fspec :=
    mk_simple (capture_hoare1 @ capture_hoare2).

  (* sealed *)
  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("salloc", salloc_spec); ("sfree", sfree_spec); 
           ("load", load_spec); ("loadbytes", loadbytes_spec); 
           ("store", store_spec); ("storebytes", storebytes_spec);
           ("sub_ptr", sub_ptr_spec); ("cmp_ptr", cmp_ptr_spec);
           ("non_null?", non_null_spec);
           ("malloc", malloc_spec); ("mfree", mfree_spec);
           ("memcpy", memcpy_spec);
           ("capture", capture_spec)
           ].
    Defined.

End SPEC.

Section MRS.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.

  Variable sk: Sk.t.
  Let skenv: SkEnv.t := Sk.load_skenv sk.

  Definition store_init_data (res : _memcntRA) (b : block) (p : Z) (optq : option Qp) (id : init_data) : option _memcntRA :=
    match id with
    | Init_int8 n => 
      if Zdivide_dec (align_chunk Mint8unsigned) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint8unsigned (Vint n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_int16 n =>
      if Zdivide_dec (align_chunk Mint16unsigned) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint16unsigned (Vint n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_int32 n =>
      if Zdivide_dec (align_chunk Mint32) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint32 (Vint n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_int64 n =>
      if Zdivide_dec (align_chunk Mint64) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint64 (Vlong n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_float32 n =>
      if Zdivide_dec (align_chunk Mfloat32) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mfloat32 (Vsingle n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_float64 n =>
      if Zdivide_dec (align_chunk Mfloat64) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mfloat64 (Vfloat n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_space z => 
      match optq with
      | Some q => Some (__points_to b p (repeat (Byte Byte.zero) (Z.to_nat z)) q ⋅ res)
      | None => Some res
      end
    | Init_addrof symb ofs =>
      match SkEnv.id2blk skenv (string_of_ident symb) with
      | Some b' =>
        if Zdivide_dec (align_chunk Mptr) p
        then
          match optq with
          | Some q => Some (__points_to b p (encode_val Mptr (Vptr (Pos.of_succ_nat b') ofs)) q ⋅ res)
          | None => Some res
          end
        else None
      | None => None
      end
    end.

  Fixpoint store_init_data_list (res : _memcntRA) (b : block) (p : Z) (optq: option Qp) (idl : list init_data) {struct idl} : option _memcntRA :=
    match idl with
    | [] => Some res
    | id :: idl' =>
        match store_init_data res b p optq id with
        | Some res' => store_init_data_list res' b (p + init_data_size id)%Z optq idl'
        | None => None
        end
    end.

  Definition alloc_global (res : Σ) (b: block) (entry : string * Any.t) : option Σ :=
    let (_, agd) := entry in
    match Any.downcast agd : option (globdef Clight.fundef type) with
    | Some g => 
      match g with
      | Gfun _ => Some (GRA.embed (Auth.black (__allocated_with b 1 Unfreeable (1/2)%Qp)) ⋅ res)
      | Gvar v =>
        let optq := match Globalenvs.Genv.perm_globvar v with
                    | Freeable | Writable => Some 1%Qp
                    | Readable => Some (1/2)%Qp
                    | Nonempty => None
                    end
        in
        match store_init_data_list ε b 0 optq (gvar_init v) with
        | Some res' => Some (GRA.embed (Auth.black (__allocated_with b (init_data_list_size (gvar_init v)) Unfreeable (1/2)%Qp))
                             ⋅ GRA.embed (Auth.black res') ⋅ res)
        | None => None
        end
      end
    | None => None
    end.

  Fixpoint alloc_globals (res: Σ) (b: block) (sk: list (string * Any.t)) : Σ :=
    match sk with
    | nil => res
    | g :: gl' => 
      match alloc_global res b g with
      | Some res' => alloc_globals res' (Pos.succ b) gl'
      | None => ε
      end
    end.

  Definition res_init : Σ := alloc_globals ε xH sk.

  (* Context `{@GRA.inG memphyRA Σ}.
  Context `{@GRA.inG memtagRA Σ}.

  Definition tag_init : memtagRA :=
    fun b => if Coqlib.plt (Pos.of_nat (length sk)) b then OneShot.black
             else OneShot.white Unfreeable.

  Definition phy_init : memphyRA := fun _ => OneShot.black. *)

End MRS.

Section SMOD.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memphyRA Σ}.
  Context `{@GRA.inG memidRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("salloc", mk_pure salloc_spec);
    ("sfree",   mk_pure sfree_spec);
    ("load",   mk_pure load_spec);
    ("loadbytes",   mk_pure loadbytes_spec);
    ("store",  mk_pure store_spec);
    ("storebytes",   mk_pure storebytes_spec);
    ("sub_ptr", mk_pure sub_ptr_spec);
    ("cmp_ptr", mk_pure cmp_ptr_spec);
    ("non_null?",   mk_pure non_null_spec);
    ("malloc",   mk_pure malloc_spec);
    ("mfree",   mk_pure mfree_spec);
    ("memcpy", mk_pure memcpy_spec);
    ("capture", mk_pure capture_spec)
    ]
  .

  (* nextblock = Pos.of_nat (length sk + 1) *)
  Definition SMemSem sk : SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.mn := "Mem";
    SModSem.initial_mr := res_init sk ⋅ GRA.embed ((fun _ => OneShot.black) : memidRA) ⋅ GRA.embed ((fun _ => OneShot.black) : memphyRA);
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SMem: SMod.t := {|
    SMod.get_modsem := SMemSem;
    SMod.sk := [("malloc", (@Gfun Clight.fundef type (External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default))↑);
                ("free", (@Gfun Clight.fundef type (External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default))↑);
                ("memcpy", (@Gfun Clight.fundef type (External (EF_memcpy 1 1) (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) (tptr tvoid) cc_default))↑);
                ("capture", (@Gfun Clight.fundef type (External EF_capture (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) (tptr tvoid) cc_default))↑)]
  |}
  .

  Definition Mem: Mod.t := (SMod.to_tgt (fun _ => to_stb [])) SMem.

End SMOD.

Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
Global Opaque _relates_to.
Global Opaque _allocated_with.
Global Opaque _belongs_to.