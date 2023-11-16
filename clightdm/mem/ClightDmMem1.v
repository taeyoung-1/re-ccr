Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM IPM.
Require Import HoareDef STB.
Require Import ClightDmExprgen.
Require Import ClightDmgen.
From compcert Require Import Floats Integers Values Memory AST Ctypes Clight Clightdefs.

Set Implicit Arguments.

Inductive tag :=
| Dynamic
| Local
| Unfreeable.

Record metadata := { blk : block; sz : Z }.

Let _pointstoRA: URA.t := (block ==> Z ==> (Consent.t memval))%ra.
Let _allocatedRA: URA.t := (block ==> (Consent.t tag))%ra.

Compute (URA.car (t:=_pointstoRA)).
Compute (URA.car (t:=_allocatedRA)).
Instance pointstoRA: URA.t := Auth.t _pointstoRA.
Instance allocatedRA: URA.t := Auth.t _allocatedRA.
Instance blocksizeRA: URA.t := (block ==> (OneShot.t Z))%ra.
Instance blockaddressRA: URA.t := (block ==> (OneShot.t ptrofs))%ra.

Local Open Scope Z.
Local Open Scope bi_scope.

Section POINTSTO.

  Definition __points_to (b: block) (ofs: Z) (mvs: list memval) (q: Qp): _pointstoRA :=
    (fun _b _ofs => if (dec _b b) && (Coqlib.zle ofs _ofs) && (Coqlib.zlt _ofs (ofs + Z.of_nat (List.length mvs)))
                    then 
                      match List.nth_error mvs (Z.to_nat (_ofs - ofs)) with
                      | Some mv => Consent.just q mv
                      | None => ε
                      end
                    else ε)
  .

  Definition _points_to (b: block) (ofs: Z) (mvs: list memval) (q: Qp): pointstoRA := Auth.white (__points_to b ofs mvs q).

End POINTSTO.

Section ALLOCATEDWITH.

  Definition __allocated_with (b: block) (tg: tag) (q: Qp) : _allocatedRA :=
    (fun _b => if dec _b b
              then Consent.just q tg
              else ε)
  .

  Definition _allocated_with (b: block) (tg: tag) (q: Qp) : allocatedRA := Auth.white (__allocated_with b tg q).

End ALLOCATEDWITH.

Section BLOCKSIZE.

  Definition _has_size (b: block) (sz: Z) : blocksizeRA :=
    (fun _b => if dec _b b
              then OneShot.white sz
              else ε).

End BLOCKSIZE.

Section BLOCKADDR.

  Definition _has_base (b: block) (base: ptrofs) : blockaddressRA :=
    (fun _b => if dec _b b
              then OneShot.white base
              else ε).

End BLOCKADDR.

Section PROP.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition get_align (sz: nat) : Z :=
    if lt_dec sz 2 then 1
    else if le_dec sz 4 then 2
    else if lt_dec sz 8 then 4
    else 8
  .

  Definition captured_to vaddr m i : iProp :=
    match vaddr with
    | Vptr b ofs =>
      OwnM (_has_size m.(blk) m.(sz))
      ** ∃ a, OwnM (_has_base m.(blk) a)
      ** ⌜b = m.(blk) /\ ofs = Ptrofs.sub i a
         /\ Ptrofs.unsigned a + m.(sz) ≤ Ptrofs.max_unsigned⌝
    | Vint i' => if Archi.ptr64 then False
                 else ⌜i = Ptrofs.of_int i'⌝
    | Vlong i' => if Archi.ptr64 then ⌜i = Ptrofs.of_int64 i'⌝
                  else False
    | _ => ⌜False⌝
    end%I.

  Definition _has_offset vaddr m ofs : iProp :=
    OwnM (_has_size m.(blk) m.(sz))
    ** match vaddr with
       | Vptr b ofs' => ⌜b = m.(blk) /\ ofs = ofs'⌝
       | Vint i =>
          if Archi.ptr64 then ⌜False⌝
          else captured_to (Vptr m.(blk) ofs) m (Ptrofs.of_int i)
       | Vlong i =>
          if negb Archi.ptr64 then ⌜False⌝
          else captured_to (Vptr m.(blk) ofs) m (Ptrofs.of_int64 i)
       | _ => ⌜False⌝
       end.

  Definition metadata_alive m tg q : iProp :=
    OwnM (_allocated_with m.(blk) tg q)
    ** OwnM (_has_size m.(blk) m.(sz)).

  Definition points_to vaddr m mvs q : iProp :=
    OwnM (_has_size m.(blk) m.(sz))
    ** ∃ ofs, OwnM (_points_to m.(blk) (Ptrofs.unsigned ofs) mvs q)
    ** _has_offset vaddr m ofs
    ** ⌜Ptrofs.unsigned ofs + length mvs ≤ m.(sz)⌝
    ** match vaddr with
       | Vptr b ofs'  =>
          ⌜Ptrofs.unsigned ofs + length mvs ≤ Ptrofs.max_unsigned⌝
       | Vint i =>
          ⌜Ptrofs.unsigned ofs + length mvs ≤ Ptrofs.max_unsigned
          /\ Int.unsigned i + length mvs ≤ Ptrofs.max_unsigned⌝
       | Vlong i =>
          ⌜Ptrofs.unsigned ofs + length mvs ≤ Ptrofs.max_unsigned
          /\ Int64.unsigned i + length mvs ≤ Ptrofs.max_unsigned⌝
       | _ => ⌜False⌝
       end%I.

  Definition has_offset vaddr m ofs tg q : iProp :=
    metadata_alive m tg q ** _has_offset vaddr m ofs.

  Definition disjoint (m m0: metadata) : Prop :=
    m.(blk) <> m0.(blk).
  
  Definition valid (m: metadata) (ofs: ptrofs) : Prop :=
    Ptrofs.unsigned ofs < m.(sz).

  Definition weak_valid (m: metadata) (ofs: ptrofs) : Prop :=
    Ptrofs.unsigned ofs ≤ m.(sz).

End PROP.

Notation "vaddr '(≃_' m ) i " := (captured_to vaddr m i) (at level 10).
Notation "vaddr ⊨ m # ofs" := (_has_offset vaddr m ofs) (at level 10).
Notation "'live_' q # ( m , tg )" := (metadata_alive m tg q) (at level 10).
Notation "vaddr '(↦_' m , q ) mvs" := (points_to vaddr m mvs q) (at level 20).
Notation "vaddr '(⊨_' m , tg , q ) ofs" := (has_offset vaddr m ofs tg q) (at level 10).
Notation "m #^ m0" := (disjoint m m0) (at level 20).

Section AUX.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.


End AUX.

Section RULES.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Lemma capture_slide
      vaddr m i k
    :
      vaddr (≃_m) i ⊢ (Val.addl vaddr (Vptrofs k)) (≃_m) (Ptrofs.add i k).
  Proof.
    unfold captured_to; des_ifs.
    - unfold Val.addl in *. des_ifs. iIntros "%". iPureIntro. clarify.
      unfold Vptrofs in Heq1. des_ifs.
      unfold Ptrofs.add, Ptrofs.of_int64, Ptrofs.to_int64, Int64.add.
      rewrite (Ptrofs.unsigned_repr).
      2:{ change Ptrofs.max_unsigned with Int64.max_unsigned.
          apply Int64.unsigned_range_2. }
      rewrite (Int64.unsigned_repr (Ptrofs.unsigned k)).
      2:{ change Int64.max_unsigned with Ptrofs.max_unsigned.
          apply Ptrofs.unsigned_range_2. }
      apply Ptrofs.eqm_repr_eq.
      rewrite (Ptrofs.unsigned_repr).
      2:{ change Ptrofs.max_unsigned with Int64.max_unsigned.
          apply Int64.unsigned_range_2. }
      rewrite <- Ptrofs.eqm64; et.
      apply Int64.eqm_unsigned_repr.
    - unfold Val.addl in *. des_ifs. unfold Vptrofs in *. des_ifs.
      iIntros "[a b]". iDestruct "b" as (a) "[b %]".
      iFrame. iExists _. iFrame. iPureIntro. des. clarify. split; et.
      rewrite Ptrofs.of_int64_to_int64; et.
      do 2 rewrite Ptrofs.sub_add_opp. do 2 rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut k). split; et.
  Qed.

  Lemma capture_unique
      vaddr m i j
    :
      vaddr (≃_m) i ** vaddr (≃_m) j ⊢ ⌜i = j⌝.
  Proof.
    iIntros "[A B]". unfold captured_to. des_ifs. 
    - iDestruct "A" as "%".
      iDestruct "B" as "%".
      iPureIntro. clarify.
    - iDestruct "A" as "[A a]".
      iDestruct "B" as "[B b]".
      iDestruct "a" as (a) "[a %]".
      iDestruct "b" as (n) "[b %]".
      des. iCombine "a b" as "c". iOwnWf "c" as wfc.
      ur in wfc. ur in wfc.
      specialize (wfc (blk m)). unfold _has_base in wfc.
      des_ifs. iPureIntro.
      assert (Ptrofs.sub j x0 = Ptrofs.sub i x0).
      { rewrite Heq0. rewrite Heq. f_equal. apply proof_irr. }
      apply (f_equal (Ptrofs.add x0)) in H3.
      do 2 rewrite Ptrofs.sub_add_opp in H3.
      do 2 rewrite (Ptrofs.add_permut x0) in H3.
      rewrite Ptrofs.add_neg_zero in H3.
      do 2 rewrite Ptrofs.add_zero in H3. et.
  Qed.

  Lemma capture_dup
      vaddr m i
    :
      vaddr (≃_m) i ⊢ vaddr (≃_m) i ** vaddr (≃_m) i.
  Proof.
    iIntros "A". unfold captured_to. des_ifs; et.
    iDestruct "A" as "[A B]".
    iDestruct "B" as (a) "[B %]".
    des. clarify.
    set (_has_size (blk m) (sz m)) at 1.
    replace c with ((_has_size (blk m) (sz m)) ⋅ (_has_size (blk m) (sz m))).
    2:{ unfold c. ur. apply func_ext. i. ur. des_ifs. unfold _has_size in Heq. des_ifs. }
    clear c.
    iDestruct "A" as "[B1 B2]".
    iFrame.
    replace (_has_base (blk m) a) with ((_has_base (blk m) a) ⋅ (_has_base (blk m) a)).
    2:{ ur. apply func_ext. i. ur. des_ifs. unfold _has_base in Heq. des_ifs. }
    iDestruct "B" as "[B1 B2]".
    iSplitL "B1".
    { iExists _. iFrame. ss. }
    { iExists _. iFrame. ss. }
  Qed.

  Lemma capture_trans
      vaddr m i j
    :
      vaddr (≃_m) i ** Vptrofs i (≃_m) j
      ⊢ vaddr (≃_m) j.
  Proof.
    iIntros "[A B]". unfold captured_to.
    des_ifs.
    - iDestruct "A" as "%".
      iDestruct "B" as "%".
      clarify. unfold Vptrofs in Heq0. des_ifs.
      rewrite Ptrofs.of_int64_to_int64; et.
    - iDestruct "A" as "[A C]".
      iDestruct "B" as "%".
      iDestruct "C" as (a) "[C %]".
      des. clarify. iFrame. iExists _. iFrame.
      unfold Vptrofs in Heq. des_ifs.
      rewrite Ptrofs.of_int64_to_int64; et.
  Qed.

  Lemma capture_refl
      m i
    :
      (∃ vaddr, vaddr (≃_m) i)
      ⊢ (Vptrofs i) (≃_m) i.
  Proof.
    iIntros "A". iDestruct "A" as (vaddr) "A".
    unfold captured_to. des_ifs.
    - unfold Vptrofs in Heq0. des_ifs. iDestruct "A" as "%". clarify.
      rewrite Ptrofs.of_int64_to_int64; et.
    - unfold Vptrofs in Heq. des_ifs. iDestruct "A" as "[A B]".
      iDestruct "B" as (a) "[B %]". des. clarify.
      rewrite Ptrofs.of_int64_to_int64; et.
  Qed.

  Lemma _has_size_dup
      b s
    :
      OwnM (_has_size b s) ⊢ OwnM (_has_size b s) ** OwnM (_has_size b s).
  Proof.
    iIntros "A".
    set (_has_size _ _) at 1.
    replace c with ((_has_size b s) ⋅ (_has_size b s)).
    2:{ unfold c. ur. apply func_ext. i. ur. des_ifs. unfold _has_size in Heq. des_ifs. }
    iDestruct "A" as "[? ?]". iFrame.
  Qed.

  Lemma _has_offset_slide
      vaddr m ofs k
    :
      vaddr ⊨ m # ofs ⊢ Val.addl vaddr (Vptrofs k) ⊨ m # (Ptrofs.add ofs k).
  Proof.
    iIntros "A".
    unfold _has_offset.
    des_ifs; try solve [iDestruct "A" as "[A %]"; clarify]. 
    - iDestruct "A" as "[? A]".
      iFrame.
      replace (Vptr (blk m) (Ptrofs.add ofs k))
        with (Val.addl (Vptr (blk m) ofs) (Vptrofs k)).
      2:{ ss. des_ifs. unfold Vptrofs in *. des_ifs. rewrite Ptrofs.of_int64_to_int64; et. }
      unfold Val.addl in Heq0. des_ifs.
      unfold Vptrofs in Heq1. des_ifs.
      replace (Ptrofs.of_int64 (Int64.add i (Ptrofs.to_int64 k)))
        with (Ptrofs.add (Ptrofs.of_int64 i) k).
      2:{ unfold Ptrofs.add, Ptrofs.of_int64, Int64.add, Ptrofs.to_int64.
          rewrite (Int64.unsigned_repr (Ptrofs.unsigned _)).
          2:{ change Int64.max_unsigned with Ptrofs.max_unsigned.
              apply Ptrofs.unsigned_range_2. }
          rewrite Ptrofs.unsigned_repr.
          2:{ change Ptrofs.max_unsigned with Int64.max_unsigned.
              apply Int64.unsigned_range_2. }
          apply Ptrofs.eqm_samerepr.
          rewrite <- Ptrofs.eqm64; et.
          apply Int64.eqm_unsigned_repr_r.
          apply Int64.eqm_refl. }
      iApply capture_slide. et.
    - iDestruct "A" as "[A %]".
      iFrame. iPureIntro. des. clarify.
      ss. des_ifs. unfold Vptrofs in *. des_ifs.
      split; et. rewrite Ptrofs.of_int64_to_int64; et.
  Qed.

  Lemma _has_offset_unique
      vaddr m ofs0 ofs1
    :
      vaddr ⊨ m # ofs0 ** vaddr ⊨ m # ofs1 ⊢ ⌜ofs0 = ofs1⌝.
  Proof.
    iIntros "[A B]".
    unfold _has_offset.
    des_ifs; try solve [iDestruct "A" as "[A %]"; clarify]. 
    - iDestruct "A" as "[_ A]".
      iDestruct "B" as "[_ B]".
      unfold captured_to. 
      iDestruct "A" as "[A A1]".
      iDestruct "B" as "[B B1]".
      iDestruct "A1" as (a) "[A1 %]".
      iDestruct "B1" as (a0) "[B1 %]".
      des. clarify.
      iCombine "A1 B1" as "C".
      iOwnWf "C" as wfc. iPureIntro.
      ur in wfc. specialize (wfc (blk m)).
      ur in wfc. unfold _has_base in wfc. des_ifs.
    - iDestruct "A" as "[A %]".
      iDestruct "B" as "[B %]".
      des. clarify.
  Qed.

  Lemma offset_slide
      vaddr m tg q ofs k
    :
      vaddr (⊨_ m, tg, q) ofs ⊢ (Val.addl vaddr (Vptrofs k)) (⊨_ m,tg,q) (Ptrofs.add ofs k).
  Proof.
    iIntros "[? A]".
    unfold has_offset. iFrame. iApply _has_offset_slide. et.
  Qed.

  Lemma offset_unique
      vaddr m tg q0 q1 ofs0 ofs1
    :
      vaddr (⊨_ m, tg, q0) ofs0 ** vaddr (⊨_ m, tg, q1) ofs1 ⊢ ⌜ofs0 = ofs1⌝.
  Proof.
    iIntros "[A B]".
    iDestruct "A" as "[_ A]".
    iDestruct "B" as "[_ B]".
    iCombine "A B" as "C".
    iApply _has_offset_unique; et.
  Qed.

  Lemma _offset_dup
      vaddr m ofs
    :
      vaddr ⊨m# ofs ⊢ vaddr ⊨m# ofs ** vaddr ⊨m# ofs.
  Proof.
    iIntros "[A B]".
    unfold _has_offset.
    iPoseProof (_has_size_dup with "A") as "[? ?]".
    des_ifs.
    - iPoseProof (capture_dup with "B") as "[? ?]". iFrame.
    - iDestruct "B" as "%". iFrame. ss.
  Qed.

  Lemma points_to_ownership
      vaddr mvs m q0 q1
    : 
      ⊢ vaddr (↦_ m, q0 + q1) mvs ∗-∗ (vaddr (↦_ m, q0) mvs ** vaddr (↦_ m, q1) mvs).
  Proof.
    iIntros. iSplit.
    - iIntros "A". unfold points_to.
      iDestruct "A" as "[B A]".
      iPoseProof (_has_size_dup with "B") as "[Y T]".
      des_ifs; iDestruct "A" as (ofs) "[[[A B] %] %]"; des; clarify.
      + unfold _has_offset. des_ifs. iDestruct "B" as "[? %]".
        clarify.
      + iPoseProof (_offset_dup with "B") as "[C D]".
        replace (_points_to (blk m) (Ptrofs.unsigned ofs) mvs (q0+q1)%Qp)
          with ((_points_to (blk m) (Ptrofs.unsigned ofs) mvs q0)
                ⋅ (_points_to (blk m) (Ptrofs.unsigned ofs) mvs q1)).
        2:{ unfold _points_to. unfold Auth.white. ur. ur. ur.
            f_equal. apply func_ext. i. apply func_ext. i. ur.
            unfold __points_to. des_ifs. }
        iDestruct "A" as "[A B]".
        iSplitL "A Y D"; iFrame; iExists _; iFrame; et.
      + iPoseProof (_offset_dup with "B") as "[C D]".
        replace (_points_to (blk m) (Ptrofs.unsigned ofs) mvs (q0+q1)%Qp)
          with ((_points_to (blk m) (Ptrofs.unsigned ofs) mvs q0)
                ⋅ (_points_to (blk m) (Ptrofs.unsigned ofs) mvs q1)).
        2:{ unfold _points_to. unfold Auth.white. ur. ur. ur.
            f_equal. apply func_ext. i. apply func_ext. i. ur.
            unfold __points_to. des_ifs. }
        iDestruct "A" as "[A B]".
        iSplitL "A Y D"; iFrame; iExists _; iFrame; et.
    - iIntros "A". unfold points_to.
      iDestruct "A" as "[[A B] [C D]]".
      iDestruct "B" as (ofs0) "[[[E G] %] F]".
      iDestruct "D" as (ofs1) "[[[H I] %] J]".
      iCombine "I G" as "T".
      iPoseProof (_has_offset_unique with "T") as "%".
      clarify.
      des_ifs; try solve [iDestruct "F" as "%"; clarify].
      + unfold _has_offset. des_ifs. iDestruct "T" as "[[_ %] _]".
        clarify.
      + iSplitL "A"; ss. iDestruct "T" as "[T T']".
        iExists _. iFrame.
        replace (_points_to (blk m) (Ptrofs.unsigned ofs0) mvs (q0+q1)%Qp)
          with ((_points_to (blk m) (Ptrofs.unsigned ofs0) mvs q0)
                ⋅ (_points_to (blk m) (Ptrofs.unsigned ofs0) mvs q1)).
        2:{ unfold _points_to. unfold Auth.white. ur. ur. ur.
            f_equal. apply func_ext. i. apply func_ext. i. ur.
            unfold __points_to. des_ifs. }
        iCombine "E H" as "?". iFrame. ss.
      + iSplitL "A"; ss. iDestruct "T" as "[T T']".
        iExists _. iFrame.
        replace (_points_to (blk m) (Ptrofs.unsigned ofs0) mvs (q0+q1)%Qp)
          with ((_points_to (blk m) (Ptrofs.unsigned ofs0) mvs q0)
                ⋅ (_points_to (blk m) (Ptrofs.unsigned ofs0) mvs q1)).
        2:{ unfold _points_to. unfold Auth.white. ur. ur. ur.
            f_equal. apply func_ext. i. apply func_ext. i. ur.
            unfold __points_to. des_ifs. }
        iCombine "E H" as "?". iFrame. ss.
  Qed.

  Lemma _allocated_disjoint
      m0 m1 tg0 tg1 q
    : 
      live_ 1# (m0, tg0) ** live_ q# (m1, tg1)
      ⊢ ⌜m0 #^ m1⌝%I. 
  Proof.
    unfold metadata_alive.
    iIntros "[[A _][B _]]".
    iCombine "A B" as "C".
    iOwnWf "C" as wfc. iPureIntro.
    unfold _allocated_with, __allocated_with in wfc.
    ur in wfc. ur in wfc. specialize (wfc (blk m0)).
    ur in wfc. des_ifs.
    apply Qp_not_add_le_l in wfc. clarify.
  Qed.

  Lemma _allocated_ownership
      m tg q0 q1
    : 
      ⊢ live_ (q0 + q1)%Qp# (m, tg) ∗-∗ (live_ q0# (m, tg) ** live_ q1# (m, tg)).
  Proof.
    iIntros. iSplit.
    - iIntros "A".
      unfold metadata_alive.
      iDestruct "A" as "[A A']".
      iPoseProof (_has_size_dup with "A'") as "[? ?]".
      iFrame.
      replace (_allocated_with (blk m) tg (q0 + q1)%Qp)
        with ((_allocated_with (blk m) tg q0) ⋅ (_allocated_with (blk m) tg q1)). 
      2:{ unfold _allocated_with. unfold Auth.white. ur. ur.
          f_equal. apply func_ext. i. unfold __allocated_with.
          ur. des_ifs. }
      iDestruct "A" as "[? ?]".
      iFrame.
    - iIntros "A".
      unfold metadata_alive.
      iDestruct "A" as "[[A B] [A' B']]".
      iFrame.
      replace (_allocated_with (blk m) tg (q0 + q1)%Qp)
        with ((_allocated_with (blk m) tg q0) ⋅ (_allocated_with (blk m) tg q1)). 
      2:{ unfold _allocated_with. unfold Auth.white. ur. ur.
          f_equal. apply func_ext. i. unfold __allocated_with.
          ur. des_ifs. }
      iSplitL "A"; iFrame.
  Qed.

  Lemma offset_ownership
      vaddr m tg q0 q1 ofs
    :
      ⊢ vaddr (⊨_ m, tg, (q0 + q1)%Qp) ofs  ∗-∗ (vaddr (⊨_ m, tg, q0) ofs ** vaddr (⊨_ m, tg, q1) ofs).
  Proof.
    iIntros. iSplit.
    - iIntros "A". unfold has_offset.
      iDestruct "A" as "[A A']".
      iPoseProof (_allocated_ownership with "A") as "[? ?]".
      iPoseProof (_offset_dup with "A'") as "[? ?]".
      iFrame.
    - iIntros "A". unfold has_offset.
      iDestruct "A" as "[[A B] [A' B']]".
      iCombine "A A'" as "A".
      iPoseProof (_allocated_ownership with "A") as "?".
      iFrame.
  Qed.

  Lemma points_to_split
      vaddr mvs0 mvs1 m q
    : 
      vaddr (↦_ m , q) (mvs0 ++ mvs1)
      ⊢ vaddr (↦_ m , q) mvs0 ** (Val.addl vaddr (Vptrofs (Ptrofs.repr (length mvs0))) (↦_m,q) mvs1).
  Proof.
    iIntros "A". unfold points_to.
    iDestruct "A" as "[A B]".
    des_ifs; try solve [iDestruct "B" as (ofs) "[_ %]"; clarify].
    - iDestruct "B" as (ofs) "[B %]".
      unfold _has_offset. des_ifs. iDestruct "B" as "[[_ [_ %]] _]". clarify.
    - iDestruct "B" as (ofs) "[[[B C] %] %]".
      des. clarify.
      iPoseProof (_has_size_dup with "A") as "[A A']".
      iPoseProof (_offset_dup with "C") as "[C C']".
      replace (_points_to (blk m) (Ptrofs.unsigned ofs) (mvs0 ++ mvs1) q)
        with ((_points_to (blk m) (Ptrofs.unsigned ofs) mvs0 q)
              ⋅ (_points_to (blk m) (Ptrofs.unsigned ofs + length mvs0) mvs1 q)).
      2:{ unfold _points_to. unfold Auth.white. ur. ur.
          f_equal. apply func_ext. i. ur. apply func_ext. i. ur.
          unfold __points_to.
          destruct dec; ss;
          destruct Coqlib.zle; ss;
          destruct Coqlib.zlt; ss;
          try destruct Coqlib.zle; ss;
          try destruct Coqlib.zlt; ss;
          try destruct Coqlib.zlt; ss;
          des_ifs; rewrite app_length in *; try nia;
          try solve [rewrite nth_error_app1 in *; try nia; clarify
                    |rewrite nth_error_app2 in *; try nia;
                     replace (Z.to_nat _) with
                      ((Z.to_nat (x0 - Ptrofs.unsigned ofs)) - length mvs0)%nat in Heq3 by nia;
                        clarify]. }
      iDestruct "B" as "[B B']".
      iSplitL "A B C".
      { iSplitL "A"; ss. iExists _. iFrame. iPureIntro. rewrite app_length in *. nia. }
      iSplitL "A'"; ss. iExists (Ptrofs.repr (Ptrofs.unsigned ofs + length mvs0)).
      des_ifs.
      rewrite Ptrofs.unsigned_repr. 
      2:{ rewrite app_length in *. destruct ofs; ss. nia. }
      iFrame.
      iSplitL "C'".
      { unfold _has_offset. des_ifs. iDestruct "C'" as "[? C]". iFrame.
        iPoseProof ((capture_slide _ _ _ (Ptrofs.repr (length mvs0))) with "C") as "C".
        unfold Val.addl. des_ifs_safe. unfold Vptrofs in *.
        des_ifs. rewrite Ptrofs.of_int64_to_int64; et. 
        unfold Ptrofs.add, Int64.add, Ptrofs.to_int64, Ptrofs.of_int64.
        rewrite app_length in *.
        destruct ofs; ss.
        destruct i; ss.
        rewrite Ptrofs.unsigned_repr; try nia.
        rewrite (Int64.unsigned_repr (length _)).
        2:{ change Int64.max_unsigned with Ptrofs.max_unsigned. nia. }
        iDestruct "C" as "[? C]". iFrame.
        iDestruct "C" as (a) "[C %]". des.
        iSplit.
        2:{ iPureIntro. nia. }
        iExists _. iFrame. iPureIntro.
        split; et. rewrite Int64.unsigned_repr; try nia.
        rewrite Ptrofs.unsigned_repr in *; try nia.
        2:{ change Int64.max_unsigned with Ptrofs.max_unsigned. nia. }
        et. }
      iPureIntro. rewrite app_length in *.
      unfold Vptrofs in *. des_ifs. unfold Int64.add, Ptrofs.to_int64.
      destruct i; ss; destruct ofs; ss.      
      rewrite Ptrofs.unsigned_repr; try nia.
      rewrite (Int64.unsigned_repr (length _)).
      2:{ change Int64.max_unsigned with Ptrofs.max_unsigned. nia. }
      rewrite Int64.unsigned_repr; try nia.
      change Int64.max_unsigned with Ptrofs.max_unsigned. nia.
    - iDestruct "B" as (ofs) "[[[B C] %] %]".
      iPoseProof (_has_size_dup with "A") as "[A A']".
      iPoseProof (_offset_dup with "C") as "[C C']".
      replace (_points_to (blk m) (Ptrofs.unsigned ofs) (mvs0 ++ mvs1) q)
        with ((_points_to (blk m) (Ptrofs.unsigned ofs) mvs0 q)
              ⋅ (_points_to (blk m) (Ptrofs.unsigned ofs + length mvs0) mvs1 q)).
      2:{ unfold _points_to. unfold Auth.white. ur. ur.
          f_equal. apply func_ext. i. ur. apply func_ext. i. ur.
          unfold __points_to.
          destruct dec; ss;
          destruct Coqlib.zle; ss;
          destruct Coqlib.zlt; ss;
          try destruct Coqlib.zle; ss;
          try destruct Coqlib.zlt; ss;
          try destruct Coqlib.zlt; ss;
          des_ifs; rewrite app_length in *; try nia;
          try solve [rewrite nth_error_app1 in *; try nia; clarify
                    |rewrite nth_error_app2 in *; try nia;
                     replace (Z.to_nat _) with
                      ((Z.to_nat (x0 - Ptrofs.unsigned ofs)) - length mvs0)%nat in Heq3 by nia;
                        clarify]. }
      iDestruct "B" as "[B B']".
      iSplitL "A B C".
      { iSplitL "A"; ss. iExists _. iFrame. iPureIntro. rewrite app_length in *. nia. }
      iSplitL "A'"; ss. iExists (Ptrofs.repr (Ptrofs.unsigned ofs + length mvs0)).
      des_ifs.
      rewrite Ptrofs.unsigned_repr. 
      2:{ rewrite app_length in *. destruct ofs; ss. nia. }
      iFrame.
      iSplitL "C'".
      { unfold _has_offset. iDestruct "C'" as "[? %]". iFrame.
        iPureIntro. des. clarify. rewrite app_length in *.
        split; try nia.
        unfold Vptrofs in *.
        des_ifs. rewrite Ptrofs.of_int64_to_int64; et. 
        unfold Ptrofs.add.
        rewrite Ptrofs.unsigned_repr.
        2:{ destruct i; ss. nia. } et. }
      iPureIntro. rewrite app_length in *.
      unfold Vptrofs in *. des_ifs. nia.
  Qed.

  Lemma points_to_collect
      vaddr mvs0 mvs1 m q
    : 
      vaddr (↦_m,q) mvs0 ** (Val.addl vaddr (Vptrofs (Ptrofs.repr (Z.of_nat (List.length mvs0)))) (↦_m,q) mvs1)
      ⊢ vaddr (↦_m,q) (mvs0 ++ mvs1).
  Proof.
    iIntros "[A B]". unfold points_to.
    iDestruct "A" as "[A' A]".
    iDestruct "B" as "[B' B]".
    iDestruct "A" as (ofs0) "[[[A C] %] H]".
    iDestruct "B" as (ofs1) "[[[B D] %] J]".
    des_ifs.
    - iDestruct "H" as "%".
      iDestruct "J" as "%".
      rewrite <- Heq.
      iPoseProof (_offset_dup with "C") as "[C C']".
      iPoseProof ((_has_offset_slide _ _ _ (Ptrofs.repr (length mvs0))) with "C'") as "C'".
      iCombine "C' D" as "C'".
      iPoseProof (_has_offset_unique with "C'") as "%".
      clarify.
      iDestruct "C'" as "[C' _]".
      iCombine "A B" as "A".
      replace (Ptrofs.unsigned (Ptrofs.add ofs0 (Ptrofs.repr (length mvs0))))
        with (Ptrofs.unsigned ofs0 + length mvs0).
      2:{ des. unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr (length _)).
          2:{ destruct ofs0; ss. nia. }
          rewrite Ptrofs.unsigned_repr.
          2:{ destruct ofs0; ss. nia. } et. }
      replace ((_points_to (blk m) (Ptrofs.unsigned ofs0) mvs0 q)
                ⋅ (_points_to (blk m) (Ptrofs.unsigned ofs0 + (length mvs0))) mvs1 q)
          with (_points_to (blk m) (Ptrofs.unsigned ofs0) (mvs0 ++ mvs1) q).
      2:{ unfold _points_to. unfold Auth.white. ur. ur.
          f_equal. ss. apply func_ext. i. ur. apply func_ext. i. ur.
          unfold __points_to.
          destruct dec; ss;
          destruct Coqlib.zle; ss;
          destruct Coqlib.zlt; ss;
          try destruct Coqlib.zle; ss;
          try destruct Coqlib.zlt; ss;
          try destruct Coqlib.zlt; ss;
          des_ifs; try rewrite app_length in *; try nia;
          try solve [rewrite nth_error_app1 in *; try nia; clarify
                    |rewrite nth_error_app2 in *; try nia;
                     replace (Z.to_nat _) with
                      ((Z.to_nat (x0 - Ptrofs.unsigned ofs0)) - length mvs0)%nat in Heq3 by nia;
                        clarify]. }
      iSplitL "A'"; ss. iExists _. iFrame.
      iPureIntro. des.
      unfold Vptrofs in *. des_ifs.
      unfold Ptrofs.add, Ptrofs.to_int64, Int64.add in *. 
      rewrite (Ptrofs.unsigned_repr (length mvs0)) in *.
      2,3,4: destruct ofs0; ss; nia.
      rewrite (Int64.unsigned_repr (length mvs0)) in *.
      2: change Int64.max_unsigned with Ptrofs.max_unsigned;
           destruct i; ss; nia.
      rewrite Ptrofs.unsigned_repr in *.
      2,3: destruct ofs0; ss; nia.
      rewrite (Int64.unsigned_repr) in *.
      2: change Int64.max_unsigned with Ptrofs.max_unsigned;
           destruct i; ss; nia.
      rewrite app_length in *. nia.
    - iDestruct "H" as "%".
      iDestruct "J" as "%".
      rewrite <- Heq.
      iPoseProof (_offset_dup with "C") as "[C C']".
      iPoseProof ((_has_offset_slide _ _ _ (Ptrofs.repr (length mvs0))) with "C'") as "C'".
      iCombine "C' D" as "C'".
      iPoseProof (_has_offset_unique with "C'") as "%".
      clarify.
      iDestruct "C'" as "[C' _]".
      iCombine "A B" as "A".
      replace (Ptrofs.unsigned (Ptrofs.add ofs0 (Ptrofs.repr (length mvs0))))
        with (Ptrofs.unsigned ofs0 + length mvs0).
      2:{ des. unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr (length _)).
          2:{ destruct ofs0; ss. nia. }
          rewrite Ptrofs.unsigned_repr.
          2:{ destruct ofs0; ss. nia. } et. }
      replace ((_points_to (blk m) (Ptrofs.unsigned ofs0) mvs0 q)
                ⋅ (_points_to (blk m) (Ptrofs.unsigned ofs0 + (length mvs0))) mvs1 q)
          with (_points_to (blk m) (Ptrofs.unsigned ofs0) (mvs0 ++ mvs1) q).
      2:{ unfold _points_to. unfold Auth.white. ur. ur.
          f_equal. ss. apply func_ext. i. ur. apply func_ext. i. ur.
          unfold __points_to.
          destruct dec; ss;
          destruct Coqlib.zle; ss;
          destruct Coqlib.zlt; ss;
          try destruct Coqlib.zle; ss;
          try destruct Coqlib.zlt; ss;
          try destruct Coqlib.zlt; ss;
          des_ifs; try rewrite app_length in *; try nia;
          try solve [rewrite nth_error_app1 in *; try nia; clarify
                    |rewrite nth_error_app2 in *; try nia;
                     replace (Z.to_nat _) with
                      ((Z.to_nat (x0 - Ptrofs.unsigned ofs0)) - length mvs0)%nat in Heq3 by nia;
                        clarify]. }
      iSplitL "A'"; ss. iExists _. iFrame.
      iPureIntro. des.
      unfold Vptrofs in *. des_ifs.
      unfold Ptrofs.add, Ptrofs.to_int64, Int64.add in *. 
      rewrite (Ptrofs.unsigned_repr (length mvs0)) in *.
      2,3: destruct ofs0; ss; nia.
      rewrite Ptrofs.unsigned_repr in *.
      2,3: destruct ofs0; ss; nia.
      rewrite app_length in *. nia.
  Qed.

  Lemma _capture_offset_comm
      vaddr i m ofs
    : 
      vaddr (≃_m) i ⊢ vaddr ⊨m# ofs ∗-∗ Vptrofs i ⊨m# ofs.
  Proof.
    iIntros "A".
    iSplit; iIntros "B"; unfold _has_offset; des_ifs.
    - iDestruct "B" as "[B C]". iFrame.
      unfold captured_to. des_ifs.
      iDestruct "A" as "%". clarify.
      iDestruct "C" as "[A B]".
      iFrame. 
      iDestruct "B" as (a) "[A %]".
      iExists _. iFrame. iPureIntro. des. clarify. split; et.
      unfold Vptrofs in *. des_ifs. rewrite Ptrofs.of_int64_to_int64; et.
    - iDestruct "B" as "[B %]". iFrame.
      des. clarify.
      unfold Vptrofs in *. des_ifs. rewrite Ptrofs.of_int64_to_int64; et.
    - iDestruct "B" as "[B C]". iFrame.
      unfold captured_to. des_ifs.
      iDestruct "A" as "%". clarify.
      iDestruct "C" as "[A B]".
      iFrame. 
      iDestruct "B" as (a) "[A %]".
      iExists _. iFrame. iPureIntro. des. clarify. split; et.
      unfold Vptrofs in *. des_ifs. rewrite Ptrofs.of_int64_to_int64; et.
    - iDestruct "B" as "[B C]". iFrame.
      unfold captured_to.
      iDestruct "A" as "[A A']".
      iDestruct "C" as "[C B]".
      iDestruct "B" as (a) "[B %]".
      iDestruct "A'" as (a0) "[A' %]".
      des. clarify.
      iCombine "A' B" as "A'".
      iOwnWf "A'" as wfc.
      ur in wfc. specialize (wfc (blk m)). ur in wfc.
      unfold _has_base in *. des_ifs.
      iPureIntro. des. clarify. split; et.
      unfold Vptrofs in *. des_ifs. rewrite Ptrofs.of_int64_to_int64; et.
  Qed.

  Lemma capture_offset_comm
      vaddr i m tg q ofs
    : 
      vaddr (≃_m) i ⊢ vaddr (⊨_m,tg,q) ofs ∗-∗ Vptrofs i (⊨_m,tg,q) ofs.
  Proof.
    iIntros "A".
    iPoseProof (_capture_offset_comm with "A") as "A".
    iSplit.
    - iIntros "[B C]". iPoseProof ("A" with "C") as "?". iFrame.
    - iIntros "[B C]". iPoseProof ("A" with "C") as "?". iFrame.
  Qed.


  Lemma capture_pointto_comm
      vaddr i m q mvs
    : 
      vaddr (≃_m) i ⊢ vaddr (↦_m,q) mvs ∗-∗ Vptrofs i (↦_m,q) mvs.
  Proof.
    iIntros "A".
    iSplit; iIntros "B"; unfold points_to; des_ifs. 
    - iDestruct "B" as "[B C]". iFrame.
      iDestruct "C" as (ofs) "[[C D] %]".
      unfold Vptrofs in *. ss. des_ifs.
      iDestruct "A" as "%".
      des. clarify. iExists _. iSplitR "".
      { iSplitL "C"; ss.
        rewrite Ptrofs.to_int64_of_int64; et. }
      iPureIntro. rewrite Ptrofs.to_int64_of_int64; et.
    - iDestruct "B" as "[B C]". iFrame.
      iDestruct "C" as (ofs) "[[[C D] %] %]".
      unfold Vptrofs in *. des_ifs.
      iExists _. iSplit.
      { iPoseProof (_capture_offset_comm with "A") as "A".
        iPoseProof ("A" with "D") as "D". iFrame. ss. }
      unfold captured_to.
      iDestruct "A" as "[A B]".
      iDestruct "B" as (a) "[B %]".
      des. clarify.
      unfold _has_offset.
      iDestruct "D" as "[D %]".
      des. clarify.
      iPureIntro. split; et.
      replace (Int64.unsigned (Ptrofs.to_int64 i)) with (Ptrofs.unsigned i).
      2:{ unfold Ptrofs.to_int64. rewrite Int64.unsigned_repr; et.
          change Int64.max_unsigned with Ptrofs.max_unsigned.
          apply Ptrofs.unsigned_range_2. }
      assert (Ptrofs.unsigned (Ptrofs.sub i a) + Ptrofs.unsigned a + length mvs ≤ Ptrofs.max_unsigned) by nia.
      assert (Ptrofs.unsigned i ≤ Ptrofs.unsigned (Ptrofs.sub i a) + Ptrofs.unsigned a); try nia.
      unfold Ptrofs.sub.
      destruct (classic (0 ≤ Ptrofs.unsigned i - Ptrofs.unsigned a ≤ Ptrofs.max_unsigned)).
      { rewrite Ptrofs.unsigned_repr; nia. }
      pose proof (Ptrofs.unsigned_range_2 i).
      pose proof (Ptrofs.unsigned_range_2 a).
      assert (Ptrofs.unsigned i ≤ Ptrofs.unsigned a) by nia.
      pose proof (Ptrofs.unsigned_range_2 (Ptrofs.repr (Ptrofs.unsigned i - Ptrofs.unsigned a))).
      nia.
    - iDestruct "B" as "[B C]". iFrame.
      iDestruct "C" as (ofs) "[[C D] %]".
      unfold Vptrofs in *. ss. des_ifs.
      iDestruct "A" as "%".
      des. clarify. iExists _. iSplitR "".
      { iSplitL "C"; ss.
        rewrite Ptrofs.to_int64_of_int64; et. }
      iPureIntro. rewrite Ptrofs.to_int64_of_int64 in H5; et.
    - iDestruct "B" as "[B C]". iFrame.
      iDestruct "C" as (ofs) "[[[C D] %] %]".
      unfold Vptrofs in *. des_ifs.
      iExists _. iSplit.
      { iPoseProof (_capture_offset_comm with "A") as "A".
        iPoseProof ("A" with "D") as "D". iFrame. ss. }
      unfold captured_to.
      iDestruct "A" as "[A B]".
      iDestruct "B" as (a) "[B %]".
      des. clarify.
  Qed.

  Lemma replace_meta_to_alive
      vaddr m0 m1 q mvs i
    :
      vaddr (↦_m0,q) mvs ** vaddr (≃_m1) i ⊢ vaddr (↦_m0,q) mvs ** vaddr (≃_m0) i.
  Proof.
  Admitted.

  Definition cast_to_ptr (v: val) : itree Es val :=
    match v with
    | Vptr _ _ => Ret v
    | Vint _ => if Archi.ptr64 then triggerUB else Ret v
    | Vlong _ => if Archi.ptr64 then Ret v else triggerUB
    | _ => triggerUB
    end.

  Lemma _offset_ptr v m ofs
    : 
      v ⊨m# ofs ⊢ ⌜cast_to_ptr v = Ret v⌝.
  Proof.
    iIntros "A". unfold has_offset.
    destruct v; ss; des_ifs_safe;
    iDestruct "A" as "[A %]"; clarify.
  Qed.

  Lemma offset_cast_ptr v m tg q ofs
    : 
      v (⊨_m,tg,q) ofs ⊢ ⌜cast_to_ptr v = Ret v⌝.
  Proof.
    iIntros "[_ A]".
    iPoseProof (_offset_ptr with "A") as "%". ss.
  Qed.

  Lemma points_to_is_ptr v m q mvs
    : 
      v (↦_m,q) mvs ⊢ ⌜is_ptr_val v = true⌝.
  Proof.
    iIntros "A". unfold points_to, _has_offset.
    destruct v; ss; des_ifs_safe;
    iDestruct "A" as "[A B]"; clarify;
    iDestruct "B" as (ofs) "[[[B C] %] %]"; clarify.
    iDestruct "C" as "[_ %]". clarify.
  Qed.

  Lemma decode_encode_ptr v m tg q ofs 
    : 
      v (⊨_m,tg,q) ofs ⊢ ⌜decode_val Mptr (encode_val Mptr v) = v⌝.
  Proof.
    unfold Mptr. des_ifs.
    pose proof (decode_encode_val_general v Mint64 Mint64).
    unfold decode_encode_val in H3.
    iIntros "A". unfold has_offset, _has_offset.
    destruct v; try solve [iDestruct "A" as "[A [A' %]]"; clarify];
    des_ifs; rewrite H3; et.
  Qed.

  Lemma add_null_r v m tg q ofs: 
      v (⊨_m,tg,q) ofs ⊢ ⌜Val.addl v (Vptrofs Ptrofs.zero) = v⌝.
  Proof.
    iIntros "A". unfold has_offset, _has_offset.
    des_ifs; try solve [iDestruct "A" as "[A [A' %]]"; clarify].
    - iPureIntro. ss. unfold Vptrofs. des_ifs.
      change (Ptrofs.to_int64 _) with Int64.zero. 
      rewrite Int64.add_zero. et.
    - iPureIntro. ss. unfold Vptrofs. des_ifs.
      rewrite Ptrofs.of_int64_to_int64; et.
      rewrite Ptrofs.add_zero. et.
  Qed.

End RULES.

Section SPEC.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition salloc_spec: fspec :=
    (mk_simple (fun n => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = n↑ /\ Z.of_nat n ≤ Ptrofs.max_unsigned⌝),
                    (fun vret => ∃ m vaddr,
                                 ⌜vret = (m.(blk))↑ /\ m.(sz) = Z.of_nat n
                                 ⌝
                                 ** vaddr (↦_m,1) List.repeat Undef n
                                 ** vaddr (⊨_m,Local, 1) Ptrofs.zero)
    )))%I.

  Definition sfree_spec: fspec :=
    (mk_simple (fun '() => (
                  (ord_pure 0%nat),
                  (fun varg => ∃ m mvs vaddr,
                                ⌜varg = (m.(blk), m.(sz))↑
                                /\ Z.of_nat (List.length mvs) = m.(sz)⌝
                                ** vaddr (↦_m,1) mvs
                                ** vaddr (⊨_m,Local,1) Ptrofs.zero),
                  (fun vret => ⌜vret = tt↑⌝)
    )))%I.

  Definition load_spec: fspec :=
    (mk_simple (fun '(chunk, vaddr, m, tg, q0, ofs, q1, mvs) => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (chunk, vaddr)↑
                                 /\ List.length mvs = size_chunk_nat chunk
                                 /\ ((size_chunk chunk) | Ptrofs.unsigned ofs)⌝
                                 ** vaddr (⊨_m,tg,q0) ofs
                                 ** vaddr (↦_m,q1) mvs),
                    (fun vret => ∃ v, ⌜vret = v↑ /\ decode_val chunk mvs = v⌝
                                 ** vaddr (⊨_m,tg,q0) ofs
                                 ** vaddr (↦_m,q1) mvs)
    )))%I.

  (* Definition loadbytes_spec: fspec :=
    (mk_simple (fun '(vaddr, sz, q, mvs) => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (vaddr, sz)↑ /\ Z.of_nat (List.length mvs) = sz⌝ 
                                ** vaddr ⊢q#> mvs),
                    (fun vret => ⌜vret = mvs↑⌝ ** vaddr ⊢q#> mvs)
    ))). *)

  Definition store_spec: fspec :=
    (mk_simple
      (fun '(chunk, vaddr, m, ofs, tg, q, v_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ mvs_old, ⌜varg = (chunk, vaddr, v_new)↑
                         /\ List.length mvs_old = size_chunk_nat chunk
                         /\ ((size_chunk chunk) | Ptrofs.unsigned ofs)⌝
                         ** vaddr (⊨_m,tg,q) ofs
                         ** vaddr (↦_m,1) mvs_old),
            (fun vret => ∃ mvs_new, ⌜vret = tt↑
                         /\ encode_val chunk v_new = mvs_new⌝
                         ** vaddr (⊨_m,tg,q) ofs
                         ** vaddr (↦_m,1) mvs_new)
    )))%I.

  (* Definition storebytes_spec: fspec :=
    (mk_simple
      (fun '(vaddr, mvs_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ mvs_old, ⌜varg = (vaddr, mvs_new)↑
                                    /\ List.length mvs_old = List.length mvs_new⌝
                                    ** vaddr ⊢1#> mvs_old),
            (fun vret => ⌜vret = tt↑⌝ ** vaddr ⊢1#> mvs_new)
    )))%I. *)

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
            (fun varg => ⌜varg = (c, Vnullptr, Vnullptr)↑⌝),
            (fun vret => ⌜vret = match c with
                                 | Ceq | Cle | Cge => true↑
                                 | _ => false↑
                                 end⌝)
          )%I.

  Definition cmp_ptr_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, tg, q, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Ceq, Vnullptr, vaddr)↑ /\ weak_valid m ofs⌝
                         ** vaddr (⊨_m,tg,q) ofs),
            (fun vret => ⌜vret = false↑⌝ 
                         ** vaddr (⊨_m,tg,q) ofs)
          )%I.

  Definition cmp_ptr_hoare2 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, tg, q, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Cne, Vnullptr, vaddr)↑ /\ weak_valid m ofs⌝
                         ** vaddr (⊨_m,tg,q) ofs),
            (fun vret => ⌜vret = true↑⌝ 
                         ** vaddr (⊨_m,tg,q) ofs)
          )%I.

  Definition cmp_ptr_hoare3 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, tg, q, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Ceq, vaddr, Vnullptr)↑ /\ weak_valid m ofs⌝
                         ** vaddr (⊨_m,tg,q) ofs),
            (fun vret => ⌜vret = false↑⌝ 
                         ** vaddr (⊨_m,tg,q) ofs)
          )%I.

  Definition cmp_ptr_hoare4 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, tg, q, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Cne, vaddr, Vnullptr)↑ /\ weak_valid m ofs⌝
                         ** vaddr (⊨_m,tg,q) ofs),
            (fun vret => ⌜vret = true↑⌝ 
                         ** vaddr (⊨_m,tg,q) ofs)
          )%I.

  Definition cmp_ptr_hoare5 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(c, vaddr0, vaddr1, m, ofs0, ofs1, q0, q1, tg) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (c, vaddr0, vaddr1)↑ /\ weak_valid m ofs0 /\ weak_valid m ofs1⌝
                         ** vaddr0 (⊨_m,tg,q0) ofs0
                         ** vaddr1 (⊨_m,tg,q1) ofs1),
            (fun vret => ⌜vret = (cmp_ofs c (Ptrofs.unsigned ofs0) (Ptrofs.unsigned ofs1))↑⌝
                         ** vaddr0 (⊨_m,tg,q0) ofs0
                         ** vaddr1 (⊨_m,tg,q1) ofs1)
          )%I.

  Definition cmp_ptr_hoare6 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr0, vaddr1, m0, m1, ofs0, ofs1, q0, q1, tg0, tg1) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Ceq, vaddr0, vaddr1)↑ /\ m0 #^ m1
                         /\ valid m0 ofs0 /\ valid m1 ofs1⌝
                         ** vaddr0 (⊨_m0,tg0,q0) ofs0
                         ** vaddr1 (⊨_m1,tg1,q1) ofs1),
            (fun vret => ⌜vret = false↑⌝ 
                         ** vaddr0 (⊨_m0,tg0,q0) ofs0
                         ** vaddr1 (⊨_m1,tg1,q1) ofs1)
          )%I.

  Definition cmp_ptr_hoare7 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr0, vaddr1, m0, m1, ofs0, ofs1, q0, q1, tg0, tg1) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Cne, vaddr0, vaddr1)↑ /\ m0 #^ m1
                         /\ valid m0 ofs0 /\ valid m1 ofs1⌝
                         ** vaddr0 (⊨_m0,tg0,q0) ofs0
                         ** vaddr1 (⊨_m1,tg1,q1) ofs1),
            (fun vret => ⌜vret = true↑⌝ 
                         ** vaddr0 (⊨_m0,tg0,q0) ofs0
                         ** vaddr1 (⊨_m1,tg1,q1) ofs1)
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

  Definition sub_ptr_spec : fspec :=
    (mk_simple
      (fun '(size, vaddr0, vaddr1, m, ofs0, ofs1, q0, q1, tg) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (size, vaddr0, vaddr1)↑ /\ 0 < size ≤ Ptrofs.max_signed
                         /\ weak_valid m ofs0 /\ weak_valid m ofs1⌝
                         ** vaddr0 (⊨_m,tg,q0) ofs0
                         ** vaddr1 (⊨_m,tg,q1) ofs1),
            (fun vret => ⌜vret = (Vptrofs (Ptrofs.repr (Z.div (Ptrofs.unsigned ofs0 - Ptrofs.unsigned ofs1) size)))↑⌝
                         ** vaddr0 (⊨_m,tg,q0) ofs0
                         ** vaddr1 (⊨_m,tg,q1) ofs1)
    )))%I.

  Definition non_null_spec: fspec :=
    (mk_simple
      (fun '(vaddr, m, q, tg, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = vaddr↑ /\ weak_valid m ofs⌝
                         ** vaddr (⊨_m,tg,q) ofs),
            (fun vret => ⌜vret = true↑⌝ 
                         ** vaddr (⊨_m,tg,q) ofs)
    )))%I.

  (* heap malloc free *)
  Definition malloc_spec: fspec :=
    (mk_simple (fun n => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = [Vptrofs n]↑ /\ Ptrofs.unsigned n > 0⌝),
                    (fun vret => ∃ m vaddr, ⌜vret = vaddr↑ /\ m.(sz) = Ptrofs.unsigned n⌝
                                 ** vaddr (↦_m,1) List.repeat Undef (Z.to_nat (Ptrofs.unsigned n))
                                 ** vaddr (⊨_m,Dynamic,1) Ptrofs.zero)
    )))%I.

  Definition mfree_spec: fspec :=
    (mk_simple (fun '() => (
                    (ord_pure 0%nat),
                    (fun varg => ∃ m mvs vaddr,
                                 ⌜varg = [vaddr]↑ /\ Z.of_nat (List.length mvs) = m.(sz)⌝
                                 ** vaddr (↦_m,1) mvs
                                 ** vaddr (⊨_m,Dynamic,1) Ptrofs.zero),
                    (fun vret => ⌜vret = Vundef↑⌝)
    )))%I.

  Definition memcpy_resource (vaddr vaddr': val) (m_src m_dst: metadata) (mvs_src mvs_dst: list memval) : iProp :=
    if Val.eq vaddr' vaddr then vaddr (↦_m_dst,1) mvs_dst
    else vaddr' (↦_m_src,1) mvs_src ** vaddr (↦_m_dst,1) mvs_dst.

  Definition memcpy_spec: fspec :=
    (mk_simple
       (fun '(vaddr, vaddr', m_src, m_dst, mvs_dst) => (
            (ord_pure 0%nat),
            (fun varg => ∃ al sz mvs_src,
                         ⌜varg = (al, sz, [vaddr; vaddr'])↑
                         /\ List.length mvs_src = List.length mvs_dst
                         /\ List.length mvs_dst = sz
                         /\ (al | sz)⌝
                         ** memcpy_resource vaddr vaddr' m_src m_dst mvs_src mvs_dst),
            (fun vret => ⌜vret = Vundef↑⌝ ** memcpy_resource vaddr vaddr' m_src m_dst mvs_dst mvs_dst)
    )))%I.

  Definition capture_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '() => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = [Vnullptr]↑⌝),
            (fun vret => ⌜vret = (Vnullptr)↑⌝ )
          )%I.

  Definition capture_hoare2 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, q, ofs, tg) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = [vaddr]↑⌝
                         ** vaddr (⊨_m,tg,q) ofs),
            (fun vret => ∃ i, ⌜vret = (Vptrofs i)↑⌝
                         ** vaddr (⊨_m,tg,q) ofs
                         ** vaddr (≃_m) i)
          )%I.

  Definition capture_spec: fspec :=
    mk_simple (capture_hoare1 @ capture_hoare2).

  (* sealed *)
  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("salloc", salloc_spec); ("sfree", sfree_spec); 
           ("load", load_spec);
           (* ("loadbytes", loadbytes_spec);  *)
           ("store", store_spec);
           (* ("storebytes", storebytes_spec); *)
           ("sub_ptr", sub_ptr_spec); ("cmp_ptr", cmp_ptr_spec);
           ("non_null?", non_null_spec);
           ("malloc", malloc_spec); ("free", mfree_spec);
           ("memcpy", memcpy_spec);
           ("capture", capture_spec)
           ].
    Defined.

End SPEC.

Section MRS.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Variable sk: Sk.sem.
  Let skenv: SkEnv.t := Sk.load_skenv sk.

  Definition store_init_data (res : _pointstoRA) (b : block) (p : Z) (optq : option Qp) (id : init_data) : option _pointstoRA :=
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

  Fixpoint store_init_data_list (res : _pointstoRA) (b : block) (p : Z) (optq: option Qp) (idl : list init_data) {struct idl} : option _pointstoRA :=
    match idl with
    | [] => Some res
    | id :: idl' =>
        match store_init_data res b p optq id with
        | Some res' => store_init_data_list res' b (p + init_data_size id)%Z optq idl'
        | None => None
        end
    end.

  Definition alloc_global (res : Σ) (b: block) (gd : globdef clightdm_fundef type) : option Σ :=
    match gd with
    | Gfun _ => Some (GRA.embed (Auth.black (__allocated_with b Unfreeable (1/2)%Qp))
                      ⋅ GRA.embed (_has_size b 1) ⋅ res)
    | Gvar v =>
      let optq := match Globalenvs.Genv.perm_globvar v with
                  | Freeable | Writable => Some 1%Qp
                  | Readable => Some (1/2)%Qp
                  | Nonempty => None
                  end
      in
      match store_init_data_list ε b 0 optq (gvar_init v) with
      | Some res' => Some (GRA.embed (Auth.black (__allocated_with b  Unfreeable (1/2)%Qp))
                           ⋅ GRA.embed (_has_size b (init_data_list_size (gvar_init v)))
                           ⋅ GRA.embed (Auth.black res') ⋅ res)
      | None => None
      end
    end.

  Fixpoint alloc_globals (res: Σ) (b: block) (sk: list (ident * _)) : Σ :=
    match sk with
    | nil => res
    | g :: gl' => 
      let (_, gd) := g in
      match gd with
      | inl false => alloc_globals res (Pos.succ b) gl'
      | inl true => ε
      | inr gd =>
        match alloc_global res b gd with
        | Some res' => alloc_globals res' (Pos.succ b) gl'
        | None => ε
        end
      end
    end.

  Definition res_init : Σ := alloc_globals ε xH sk.

End MRS.

Section SMOD.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("salloc", mk_pure salloc_spec);
    ("sfree",   mk_pure sfree_spec);
    ("load",   mk_pure load_spec);
    (* ("loadbytes",   mk_pure loadbytes_spec); *)
    ("store",  mk_pure store_spec);
    (* ("storebytes",   mk_pure storebytes_spec); *)
    ("sub_ptr", mk_pure sub_ptr_spec);
    ("cmp_ptr", mk_pure cmp_ptr_spec);
    ("non_null?",   mk_pure non_null_spec);
    ("malloc",   mk_pure malloc_spec);
    ("free",   mk_pure mfree_spec);
    ("memcpy", mk_pure memcpy_spec);
    ("capture", mk_pure capture_spec)
    ]
  .

  Definition SMemSem sk : SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.mn := "Mem";
    SModSem.initial_mr := res_init sk ⋅ GRA.embed ((fun _ => OneShot.black) : blockaddressRA)
                          ⋅ GRA.embed ((fun b => if Coqlib.plt (Pos.of_succ_nat (List.length sk)) b then OneShot.black else OneShot.unit) : blocksizeRA);
    SModSem.initial_st := tt↑;
  |}
  .

  Import Clightdefs.ClightNotations.
  Local Open Scope clight_scope.

  Definition SMem: SMod.t := {|
    SMod.get_modsem := SMemSem;
    SMod.sk := Maps.PTree.set ($"malloc") (inr (Gfun (CExternal CEF_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))))
                (Maps.PTree.set ($"free") (inr (Gfun (CExternal CEF_free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))))
                  (Maps.PTree.set ($"memcpy") (inr (Gfun (CExternal (CEF_memcpy 1 1) (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) (tptr tvoid) cc_default))))
                    (Maps.PTree.set ($"capture") (inr (Gfun (CExternal CEF_capture (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) (tptr tvoid) cc_default))))
                      (Maps.PTree.empty _))))
  |}
  .

  Definition Mem: Mod.t := (SMod.to_tgt (fun _ => to_stb [])) SMem.

End SMOD.

Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
Global Opaque _allocated_with.
Global Opaque _has_size.
Global Opaque _has_base.