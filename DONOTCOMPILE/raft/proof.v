Require Import HoareDef SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import src tgt header.
Require Import HTactics ProofMode.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Variable X: Type.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    mk_wf (fun (_: unit) _ _ => (True: iProp)%I).

  
  Definition subset (A B: list X) := forall x, In x A -> In x B.


  Theorem correct: refines2 [src.F] [tgt.F].
Proof.
  eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et.
    { ss. }
- econs; ss. init. steps. unfold f. unfold src.f. steps. 
    Admitted.

End SIMMODSEM.

