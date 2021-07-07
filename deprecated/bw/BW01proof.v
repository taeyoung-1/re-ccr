Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef BW0 BW1 SimModSem.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
(* Require Import TODOYJ. *)ProofMode.
Require Import HTactics.

Set Implicit Arguments.

Local Open Scope nat_scope.






Section AUX.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG bwRA Σ}.

  Lemma bw_ra_merge
        b0 b1
    :
      (OwnM (bw_full b0)) -∗ OwnM (bw_frag b1) -∗ (⌜b1 = b0⌝)
  .
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H" as WF. iPureIntro.
    eapply Auth.auth_included in WF. des.
    eapply Excl.extends in WF; ss.
    - des; clarify.
    - ur; ss.
  Qed.
End AUX.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG BW1.bwRA Σ}.

  Let W: Type := Any.t * Any.t.
  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      Z
      (fun n _ mp_tgt => (OwnM (bw_full (Z.odd n))) ** ⌜mp_tgt = n↑⌝)
  .

  Require Import Red.

  Theorem correct: ModSemPair.sim BW1.BWSem BW0.BWSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { ss. }
    { ss. eexists. red. econs; et.
      eapply to_semantic. iIntros "H". iSplitL "H"; [|et]. ss. }
    econs; ss.
    { unfold getF. init. harg.
      mDesAll. des; clarify.
      steps. astart 0. astop.
      mAssertPure (x = Z.odd w); subst.
      { iApply (bw_ra_merge with "INV PRE"). }
      steps. force_l. eexists. steps.
      hret _; ss.
      iModIntro. iFrame.
      iPureIntro. esplits; ss. f_equal.
      rewrite <- Z.negb_odd. rewrite negb_if. des_ifs.
    }
    econs; ss.
    { unfold flipF. init. harg.
      mDesAll. des; clarify.
      steps. astart 0. astop.
      mAssertPure (x = Z.odd w); subst.
      { iApply (bw_ra_merge with "INV PRE"). }
      steps. force_l. eexists. steps.
      hret _; ss.
      iCombine "INV" "PRE" as "H".
      iPoseProof (OwnM_Upd with "H") as "H".
      { (* TODO: make lemma *)
        instantiate (1:= bw_full (Z.odd (w+1)) ⋅ bw_frag (Z.odd (w+1))).
        eapply Auth.auth_update. rr. ii. des; ss. ur in FRAME. ur. destruct ctx0; ss; clarify.
      }
      iMod "H". iDestruct "H" as "[H0 H1]". iModIntro.
      replace (negb (Z.odd w)) with (Z.odd (w+1)); [iFrame; et|].
      rewrite Z.odd_add. ss.
    }
  Qed.

End SIMMODSEM.