From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import ConvC2ITree.
Require Import SimSTS3.
Require Import Clight_Mem0.
Require Import IRed.
From Ordinal Require Import Ordinal Arithmetic.

(* Require Import Clightlight2ClightMatch.
Require Import Clightlight2ClightArith. *)
Require Import Clightlight2ClightGenv.
(* Require Import Clightlight2ClightLenv.
Require Import Clightlight2ClightMem. *)

From compcert Require Import Clight Clightdefs.

Lemma unbind_trigger E:
  forall [X0 X1 A : Type] (ktr0 : X0 -> itree E A) (ktr1 : X1 -> itree E A) e0 e1,
    (x <- trigger e0;; ktr0 x = x <- trigger e1;; ktr1 x) -> (X0 = X1 /\ e0 ~= e1 /\ ktr0 ~= ktr1).
Proof.
  i. eapply f_equal with (f:=_observe) in H. cbn in H.
  inv H. split; auto.
  dependent destruction H3. dependent destruction H2.
  cbv in x. subst. split; auto.
  assert (ktr0 = ktr1); clarify.
  extensionality x. eapply equal_f in x0.
  rewrite ! subst_bind in *.
  irw in x0. eauto.
Qed.

Lemma angelic_step :
  forall (X : Prop) (ktr next : itree eventE Any.t),
    ModSemL.step (trigger (Take X);;; ktr) None next -> (next = ktr /\ X).
Proof.
  i. dependent destruction H; try (irw in x; clarify; fail).
  rewrite <- bind_trigger in x. apply unbind_trigger in x.
  des. clarify.
Qed.

(* Lemma eval_exprlist_length :
  forall a b c d l1 l2
    (EE: eval_exprlist a b c d l1 l2),
    <<EELEN: List.length l1 = List.length l2>>.
Proof.
  i. induction EE; ss; clarify; eauto.
Qed. *)

  Ltac rewriter :=
    try match goal with
        | H: _ = _ |- _ => rewrite H in *; clarify
        end.

  Lemma Clight_wf_semantics types defs WF_TYPES
    :
      wf_semantics (semantics2 (mkprogram types defs (List.map (fun '(gn, _) => gn) defs) (ident_of_string "main") WF_TYPES)).
  Proof.
    econs.
    { i. inv STEP0; inv STEP1; ss; rewriter.
      { hexploit (@Csharpminor_eval_expr_determ a v v0); et. i. rewriter. }
      { hexploit (@Csharpminor_eval_expr_determ addr vaddr vaddr0); et. i. rewriter.
        hexploit (@Csharpminor_eval_expr_determ a v v0); et. i. rewriter. }
      { hexploit (@Csharpminor_eval_expr_determ a vf vf0); et. i. rewriter.
        hexploit (@Csharpminor_eval_exprlist_determ bl vargs vargs0); et. i. rewriter. }
      { hexploit (@Csharpminor_eval_exprlist_determ bl vargs vargs0); et. i. rewriter.
        hexploit external_call_determ; [eapply H0|eapply H12|..]. i. des.
        inv H1. hexploit H2; et. i. des. clarify. }
      { hexploit (@Csharpminor_eval_expr_determ a v v0); et. i. rewriter.
        inv H0; inv H12; auto. }
      { hexploit (@Csharpminor_eval_expr_determ a v v0); et. i. rewriter.
        inv H0; inv H12; et. }
      { hexploit (@Csharpminor_eval_expr_determ a v v0); et. i. rewriter. }
      { hexploit (@alloc_variables_determ (fn_vars f) e e0); et. i. des; clarify. }
      { hexploit external_call_determ; [eapply H|eapply H6|..]. i. des.
        inv H0. hexploit H1; et. i. des. clarify. }
    }
    { i. inv FINAL. inv STEP. }
    { i. inv FINAL0. inv FINAL1. ss. }
  Qed.