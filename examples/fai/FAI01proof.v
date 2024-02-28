Require Import HoareDef FAI0 FAI1 Mem1.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior SimModSem SimModSemFacts.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import HTactics ProofMode.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.
  Variable GlobalStb : gname -> option fspec.

  Let W : Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf _ unit
           (fun _ _ _ => ⌜True⌝%I)
  .

  Theorem correct: refines2 [FAI0.FAI] [FAI1.FAI GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et.
    { ss. }
    2: { exists tt. econs. eapply to_semantic. et. }
    econs; ss. init.
    unfold FAIF, FAI0.FAIF.
    harg. unfold FAI_pre in ACC. mDesAll. des. clarify.
    steps.

    do 2 (prep; _step; simpl).
    destruct (val_dec v (Vint 0)).
    { admit. }
    { ss. steps_safe. _force_l. steps_safe. i. steps_safe. i. steps_safe.
      force_l. unfold has_n in _ASSUME0. apply from_semantic in _ASSUME0.
      uipropall. 
       des. clarify.
      destruct c.
      3:{ ur in _ASSUME. clarify. }
      -  exists (Auth.frag (fun _b _ofs => if (dec b _b) && (dec ofs _ofs) then Excl.just (Vint (x + 1)) else f _b _ofs)).
      update c (H)
      { admit. }
      steps_safe. red. eexists. ss.
      Unshelve. all: ss.
  Admitted.
  Theorem correct: refines2 [FAI0.FAI] [FAI1.FAI].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); et.
    { ss. }
    2: { exists tt. ss. }
    econs; ss. init.
    unfold FAIF, FAI0.FAIF.
    
  Admitted.

End SIMMODSEM.