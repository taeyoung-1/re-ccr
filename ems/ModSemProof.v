Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Import STS Behavior.
Require Import ModSem.
Require Import SimGlobal.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Optics.

Require Import Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault
     TranslateFacts.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Any.


Set Implicit Arguments.



Section SIM.
  Let st_local: Type := (Any.t).

  Variable world: Type.

  Let W: Type := (Any.t) * (Any.t).
  Variable wf : world -> W -> Prop.
  Variable le: relation world.


  Inductive _sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, Ret v_src) (st_tgt0, Ret v_tgt)

  | sim_itree_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          sim_itree _ _ RR false false w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, trigger (Call fn varg) >>= k_tgt)

  | sim_itree_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itree_tau_src
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      i_src i_tgt
      (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)

  | sim_itree_tau_tgt
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      i_src i_tgt
      (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)

  | sim_itree_choose_src
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X k_src i_tgt
      (K: exists (x: X), _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_choose_tgt
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X i_src k_tgt
      (K: forall (x: X), _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Choose X) >>= k_tgt)

  | sim_itree_take_src
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X k_src i_tgt
      (K: forall (x: X), _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_take_tgt
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X i_src k_tgt
      (K: exists (x: X), _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Take X) >>= k_tgt)

  | sim_itree_supdate_src
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X k_src i_tgt
      (run: st_local -> st_local * X )
      (K: _sim_itree sim_itree RR true i_tgt0 w0 (fst (run st_src0), k_src (snd (run st_src0))) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (SUpdate run) >>= k_src) (st_tgt0, i_tgt)  

  | sim_itree_supdate_tgt
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X i_src k_tgt
      (run: st_local -> st_local * X )
      (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (fst (run st_tgt0), k_tgt (snd (run st_tgt0))))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, trigger (SUpdate run) >>= k_tgt)

  | sim_itree_progress
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local) i_src i_tgt
      (SIM: sim_itree _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
      (SRC: i_src0 = true)
      (TGT: i_tgt0 = true)
    :
      _sim_itree sim_itree RR true true w0 (st_src0, i_src) (st_tgt0, i_tgt)
  .

  Definition lift_rel {R_src R_tgt} (w0: world) (RR: R_src -> R_tgt -> Prop)
             (st_src0: st_local) (st_tgt0: st_local) (ret_src ret_tgt: Any.t) :=
    exists w1 : world,
      (<<WLE: le w0 w1 >> /\ <<WF: wf w1 (st_src0, st_tgt0) >> /\ <<RET: ret_src = ret_tgt >>).

  Lemma _sim_itree_ind2 (sim_itree: forall (R_src R_tgt: Type) 
                                    (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        (P: bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        (RET: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            v_src v_tgt
            (RET: RR st_src0 st_tgt0 v_src v_tgt),
            P i_src0 i_tgt0 w0 (st_src0, Ret v_src) (st_tgt0, Ret v_tgt))
        (CALL: forall
            i_src0 i_tgt0 w w0 st_src0 st_tgt0
            fn varg k_src k_tgt
            (WF: wf w0 (st_src0, st_tgt0))
            (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
                sim_itree _ _ RR false false w (st_src1, k_src vret) (st_tgt1, k_tgt vret)),
            P i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
              (st_tgt0, trigger (Call fn varg) >>= k_tgt))
        (SYSCALL: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            fn varg rvs k_src k_tgt
            (K: forall vret,
                sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
              (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt))
        (TAUSRC: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            i_src i_tgt
            (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt))
        (TAUTGT: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            i_src i_tgt
            (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt))
        (CHOOSESRC: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            X k_src i_tgt
            (K: exists (x: X), <<SIM: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
              (st_tgt0, i_tgt))
        (CHOOSETGT: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Choose X) >>= k_tgt))
        (TAKESRC: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            X k_src i_tgt
            (K: forall (x: X), <<SIM: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
              (st_tgt0, i_tgt))
        (TAKETGT: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            X i_src k_tgt
            (K: exists (x: X), <<SIM:_sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Take X) >>= k_tgt))
        (SUPDATESRC: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            X k_src i_tgt
            (run: st_local -> st_local * X )
            (K: _sim_itree sim_itree RR true i_tgt0 w0 (fst (run st_src0), k_src (snd (run st_src0))) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (fst (run st_src0), k_src (snd (run st_src0))) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (SUpdate run) >>= k_src) (st_tgt0, i_tgt))
        (SUPDATETGT: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            X i_src k_tgt
            (run: st_local -> st_local * X )
            (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (fst (run st_tgt0), k_tgt (snd (run st_tgt0))))
            (IH: P i_src0 true w0 (st_src0, i_src) (fst (run st_tgt0), k_tgt (snd (run st_tgt0)))),
            P i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, trigger (SUpdate run) >>= k_tgt))
        (PROGRESS: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local) i_src i_tgt
            (SIM: sim_itree _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (SRC: i_src0 = true)
            (TGT: i_tgt0 = true),
            P true true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      forall i_src0 i_tgt0 w0 st_src st_tgt
             (SIM: _sim_itree sim_itree RR i_src0 i_tgt0 w0 st_src st_tgt),
        P i_src0 i_tgt0 w0 st_src st_tgt.
  Proof.
    fix IH 6. i. inv SIM.
    { eapply RET; eauto. }
    { eapply CALL; eauto. }
    { eapply SYSCALL; eauto. }
    { eapply TAUSRC; eauto. }
    { eapply TAUTGT; eauto. }
    { eapply CHOOSESRC; eauto. des. esplits; eauto. }
    { eapply CHOOSETGT; eauto. }
    { eapply TAKESRC; eauto. }
    { eapply TAKETGT; eauto. des. esplits; eauto. }
    { eapply SUPDATESRC; eauto. }
    { eapply SUPDATETGT; eauto. }
    { eapply PROGRESS; eauto. }

  Qed.

  Definition sim_itree o_src o_tgt w0 : relation _ :=
    paco8 _sim_itree bot8 _ _ (lift_rel w0 (@eq Any.t)) o_src o_tgt w0.

  Lemma sim_itree_mon: monotone8 _sim_itree.
  Proof.
    ii. induction IN using _sim_itree_ind2; try (by des; econs; ss; et).
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree_mon: paco.
  Hint Resolve cpn8_wcompat: paco.

  Lemma sim_itree_ind
        R_src R_tgt (RR: st_local -> st_local -> R_src -> R_tgt -> Prop) 
        (P: bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        (RET: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            v_src v_tgt
            (RET: RR st_src0 st_tgt0 v_src v_tgt),
            P i_src0 i_tgt0 w0 (st_src0, Ret v_src) (st_tgt0, Ret v_tgt))
        (CALL: forall
            i_src0 i_tgt0 w w0 st_src0 st_tgt0
            fn varg k_src k_tgt
            (WF: wf w0 (st_src0, st_tgt0))
            (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
                paco8 _sim_itree bot8 _ _ RR false false w (st_src1, k_src vret) (st_tgt1, k_tgt vret)),
            P i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
              (st_tgt0, trigger (Call fn varg) >>= k_tgt))
        (SYSCALL: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            fn varg rvs k_src k_tgt
            (K: forall vret,
                paco8 _sim_itree bot8 _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
              (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt))
        (TAUSRC: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt))
        (TAUTGT: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt))            
        (CHOOSESRC: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            X k_src i_tgt
            (K: exists (x: X), <<SIM: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
              (st_tgt0, i_tgt))
        (CHOOSETGT: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Choose X) >>= k_tgt))
        (TAKESRC: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            X k_src i_tgt
            (K: forall (x: X), <<SIM: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
              (st_tgt0, i_tgt))
        (TAKETGT: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            X i_src k_tgt
            (K: exists (x: X), <<SIM:paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Take X) >>= k_tgt))
        (SUPDATESRC: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            X k_src i_tgt
            (run: st_local -> st_local * X )
            (K: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (fst (run st_src0), k_src (snd (run st_src0))) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (fst (run st_src0), k_src (snd (run st_src0))) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (SUpdate run) >>= k_src) (st_tgt0, i_tgt))
        (SUPDATETGT: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            X i_src k_tgt
            (run: st_local -> st_local * X )
            (K: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (fst (run st_tgt0), k_tgt (snd (run st_tgt0))))
            (IH:  P i_src0 true w0 (st_src0, i_src) (fst (run st_tgt0), k_tgt (snd (run st_tgt0)))),

            P i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, trigger (SUpdate run) >>= k_tgt))       
        (PROGRESS: forall
            i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
            i_src i_tgt
            (SIM: paco8 _sim_itree bot8 _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (SRC: i_src0 = true)
            (TGT: i_tgt0 = true),
            P true true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      forall i_src0 i_tgt0 w0 st_src st_tgt
             (SIM: paco8 _sim_itree bot8 _ _ RR i_src0 i_tgt0 w0 st_src st_tgt),
        P i_src0 i_tgt0 w0 st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM using _sim_itree_ind2.
    { eapply RET; eauto. }
    { eapply CALL; eauto. i. exploit K; eauto. i. pclearbot. eauto. }
    { eapply SYSCALL; eauto. i. exploit K; eauto. i. pclearbot. eauto. }
    { eapply TAUSRC; eauto. }
    { eapply TAUTGT; eauto. }
    { eapply CHOOSESRC; eauto. des. esplits; eauto. }
    { eapply CHOOSETGT; eauto. i. exploit K; eauto. i. des.
    pclearbot. esplits; eauto. }
    { eapply TAKESRC; eauto. i. exploit K; eauto. i. des.
      pclearbot. esplits; eauto. }
    { eapply TAKETGT; eauto. des. esplits; eauto. }
    { eapply SUPDATESRC; eauto. }
    { eapply SUPDATETGT; eauto. }
    { eapply PROGRESS; eauto. pclearbot. auto. }

  Qed.

  Variant sim_itree_indC (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_indC_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      sim_itree_indC  sim_itree RR i_src0 i_tgt0 w0 (st_src0, Ret v_src) (st_tgt0, Ret v_tgt)
  | sim_itree_indC_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          sim_itree _ _ RR false false w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      sim_itree_indC  sim_itree RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                     (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_indC_syscall
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      fn varg rvs k_src k_tgt
      (K: forall vret,
          sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itree_indC  sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                     (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itree_indC_tau_src
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      i_src i_tgt
      (K: sim_itree _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itree_indC  sim_itree RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)

  | sim_itree_indC_tau_tgt
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      i_src i_tgt
      (K: sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itree_indC  sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)

  | sim_itree_indC_choose_src
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X k_src i_tgt
      (K: exists (x: X), sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itree_indC  sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                     (st_tgt0, i_tgt)
  | sim_itree_indC_choose_tgt
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X i_src k_tgt
      (K: forall (x: X), sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itree_indC  sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (Choose X) >>= k_tgt)

  | sim_itree_indC_take_src
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X k_src i_tgt
      (K: forall (x: X), sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itree_indC  sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                     (st_tgt0, i_tgt)
  | sim_itree_indC_take_tgt
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X i_src k_tgt
      (K: exists (x: X), sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itree_indC  sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (Take X) >>= k_tgt)
  
  | sim_itree_indC_supdate_src
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X k_src i_tgt
      (run: st_local -> st_local * X )
      (K: sim_itree _ _ RR true i_tgt0 w0 (fst (run st_src0), k_src (snd (run st_src0))) (st_tgt0, i_tgt))
    :
      sim_itree_indC  sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (SUpdate run) >>= k_src) (st_tgt0, i_tgt)

  | sim_itree_indC_supdate_tgt
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X i_src k_tgt
      (run: st_local -> st_local * X )
      (K: sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (fst (run st_tgt0), k_tgt (snd (run st_tgt0))))
    :
      sim_itree_indC  sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, trigger (SUpdate run) >>= k_tgt)
  .

  Lemma sim_itree_indC_mon: monotone8 sim_itree_indC.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
  Qed.
  Hint Resolve sim_itree_indC_mon: paco.

  Lemma sim_itree_indC_spec:
    sim_itree_indC <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit K; eauto. i. des.
      esplits; eauto. eapply rclo8_base. eauto. }
    { econs 3; eauto. i. eapply rclo8_base. eauto. }
    { econs 4; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 5; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 6; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 7; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 8; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 9; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 10; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto.  }
    { econs 11; eauto. des. esplits; eauto.  eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto.  }
  Qed.

  Variant sim_itreeC (r g: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itreeC_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, Ret v_src) (st_tgt0, Ret v_tgt)
  | sim_itreeC_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          g _ _ RR false false w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itreeC_syscall
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      fn varg rvs k_src k_tgt
      (K: forall vret,
          g _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itreeC_tau_src
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      i_src i_tgt
      (K: r _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)

  | sim_itreeC_tau_tgt
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      i_src i_tgt
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)


  | sim_itreeC_choose_src
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X k_src i_tgt
      (K: exists (x: X), r _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itreeC_choose_tgt
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X i_src k_tgt
      (K: forall (x: X), r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itreeC_take_src
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X k_src i_tgt
      (K: forall (x: X), r _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itreeC_take_tgt
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X i_src k_tgt
      (K: exists (x: X), r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Take X) >>= k_tgt)
  | sim_itreeC_supdate_src
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X k_src i_tgt
      (run: st_local -> st_local * X )
      (K: r _ _ RR true i_tgt0 w0 (fst (run st_src0), k_src (snd (run st_src0))) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (SUpdate run) >>= k_src) (st_tgt0, i_tgt)

  | sim_itreeC_supdate_tgt
      i_src0 i_tgt0 w0 (st_src0: st_local) (st_tgt0: st_local)
      X i_src k_tgt
      (run: st_local -> st_local * X )
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (fst (run st_tgt0), k_tgt (snd (run st_tgt0))))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, trigger (SUpdate run) >>= k_tgt)

  .

  Lemma sim_itreeC_spec_aux:
    sim_itreeC <10= gpaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    i. inv PR.
    { gstep. econs 1; eauto. }
    { gstep. econs 2; eauto. i. gbase. eauto. }
    { gstep. econs 3; eauto. i. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 4; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 5; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 6; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 7; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 8; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 9; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 10; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 11; eauto.  gbase. eauto. }
  Qed.

  Lemma sim_itreeC_spec r g
    :
      @sim_itreeC (gpaco8 (_sim_itree) (cpn8 _sim_itree) r g) (gpaco8 (_sim_itree) (cpn8 _sim_itree) g g)
      <8=
      gpaco8 (_sim_itree) (cpn8 _sim_itree) r g.
  Proof.
    i. eapply gpaco8_gpaco; [eauto with paco|].
    eapply gpaco8_mon.
    { eapply sim_itreeC_spec_aux. eauto. }
    { auto. }
    { i. eapply gupaco8_mon; eauto. }
  Qed.

  Lemma sim_itree_progress_flag R0 R1 RR w r g st_src0 st_tgt0
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) g g R0 R1 RR false false w st_src0 st_tgt0)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR true true w st_src0 st_tgt0.
  Proof.
    gstep. destruct st_src0, st_tgt0. econs; eauto. 
  Qed.

  Lemma sim_itree_flag_mon
        (sim_itree: forall (R_src R_tgt: Type)
                           (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        R_src R_tgt (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        f_src0 f_tgt0 f_src1 f_tgt1 w st_src0 st_tgt0
        (SIM: @_sim_itree sim_itree _ _ RR f_src0 f_tgt0 w st_src0 st_tgt0)
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      @_sim_itree sim_itree _ _ RR f_src1 f_tgt1 w st_src0 st_tgt0.
  Proof.
    revert f_src1 f_tgt1 SRC TGT.
    induction SIM using _sim_itree_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. } 
    { econs 6; eauto. des. esplits; eauto. }
    { econs 7; eauto. i. exploit K; eauto. i. des. eauto. }
    { econs 8; eauto. i. exploit K; eauto. i. des. eauto. }
    { econs 9; eauto. des. esplits; eauto. }
    { econs 10; eauto. }
    { econs 11; eauto. } 
    { exploit SRC0; auto. exploit TGT0; auto. i. clarify. econs; eauto. }
  Qed.


  Definition sim_fsem: relation ( Any.t -> itree Es Any.t) :=
    (eq ==> (fun it_src it_tgt => forall w mrs_src mrs_tgt (SIMMRS: wf w (mrs_src, mrs_tgt)),
                 sim_itree false false w (mrs_src, it_src)
                           (mrs_tgt, it_tgt)))%signature
  .

  Definition sim_fnsem: relation (gname -> option (Any.t -> itree Es Any.t)) := 
   fun f g => forall s, match (f s), (g s) with
                        | Some x, Some y => sim_fsem x y
                        | None, None => True
                        | _, _ => False
                        end
    .

  Variant lflagC (r: forall (R_src R_tgt: Type)
    (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | lflagC_intro
      f_src0 f_src1 f_tgt0 f_tgt1 w st_src st_tgt
      (SIM: r _ _ RR f_src0 f_tgt0 w st_src st_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      lflagC r RR f_src1 f_tgt1 w st_src st_tgt
  .

  Lemma lflagC_mon
        r1 r2
        (LE: r1  <8= r2)
    :
      @lflagC r1  <8= @lflagC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lflagC_mon: paco.

  Lemma lflagC_spec: lflagC  <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM.
    revert x3 x4 SRC TGT. induction SIM using _sim_itree_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit K; eauto. i. des.
      esplits; eauto. eapply rclo8_base. eauto. }
    { econs 3; eauto. i. eapply rclo8_base. eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. }
    { econs 6; eauto.  des. esplits; eauto. }
    { econs 7; eauto. i. exploit K; eauto. i. des. esplits; eauto. }
    { econs 8; eauto. i. exploit K; eauto. i. des. esplits; eauto. }
    { econs 9; eauto. des. esplits; eauto. }
    { econs 10; eauto. }
    { econs 11; eauto. }
    { exploit SRC0; auto. exploit TGT0; auto. i. clarify. econs 12; eauto.
      eapply rclo8_base; auto. }
  Qed.

  Lemma sim_itree_flag_down  R0 R1 RR r g w st_src0 st_tgt0 f_src f_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR false false w st_src0 st_tgt0)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR f_src f_tgt w st_src0 st_tgt0.
  Proof.
    guclo lflagC_spec. econs; eauto.
  Qed.

  Lemma sim_itree_bot_flag_up  R0 R1 RR w st_src0 st_tgt0 f_src f_tgt
        (SIM: paco8 _sim_itree bot8 R0 R1 RR true true w st_src0 st_tgt0)
    :
      paco8 _sim_itree bot8 R0 R1 RR f_src f_tgt w st_src0 st_tgt0.
  Proof.
    ginit. remember true in SIM at 1. remember true in SIM at 1.
    clear Heqb Heqb0. revert w st_src0 st_tgt0 f_src f_tgt b b0 SIM.
    gcofix CIH. 
    i. revert f_src f_tgt.

    (* TODO: why induction using sim_itree_ind doesn't work? *)
    pattern b, b0, w, st_src0, st_tgt0.
    match goal with
    | |- ?P b b0 w st_src0 st_tgt0 => set P
    end.
    revert b b0 w st_src0 st_tgt0 SIM.
    eapply (@sim_itree_ind R0 R1 RR P); subst P; ss; i; clarify.
    { guclo sim_itree_indC_spec. econs 1; eauto. }
    { gstep. econs 2; eauto. i. gbase. eapply CIH; eauto. }
    { gstep. econs 3; eauto. i. gbase. eapply CIH; eauto. }
    { guclo sim_itree_indC_spec. econs 4; eauto. }
    { guclo sim_itree_indC_spec. econs 5; eauto. } 
    { guclo sim_itree_indC_spec. econs 6; eauto. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 7; eauto. i. hexploit K; eauto. i. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 8; eauto. i. hexploit K; eauto. i. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 9; eauto. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 10; eauto. } 
    { guclo sim_itree_indC_spec. econs 11; eauto. } 
    { eapply sim_itree_flag_down. gfinal. right.
      eapply paco8_mon; eauto. ss.
    }
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), bool -> bool -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop):
    forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), bool -> bool -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop :=
  | lbindR_intro
      f_src f_tgt w0 w1
      R_src R_tgt RR
      (st_src0 st_tgt0: st_local)
      (i_src: itree Es R_src) (i_tgt: itree Es R_tgt)
      (SIM: r _ _ RR f_src f_tgt w0 (st_src0, i_src) (st_tgt0, i_tgt))

      S_src S_tgt SS
      (k_src: ktree Es R_src S_src) (k_tgt: ktree Es R_tgt S_tgt)
      (SIMK: forall st_src1 st_tgt1 vret_src vret_tgt (SIM: RR st_src1 st_tgt1 vret_src vret_tgt), s _ _ SS false false w1 (st_src1, k_src vret_src) (st_tgt1, k_tgt vret_tgt))
    :
      lbindR r s SS f_src f_tgt w1 (st_src0, ITree.bind i_src k_src) (st_tgt0, ITree.bind i_tgt k_tgt)
  .

  Hint Constructors lbindR: core.

  Lemma lbindR_mon 
        r1 r2 s1 s2
        (LEr: r1  <8= r2) (LEs: s1  <8= s2)
    :
      lbindR r1 s1  <8= lbindR r2 s2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Definition lbindC r := lbindR r r.
  Hint Unfold lbindC: core.

  Lemma lbindC_wrespectful: wrespectful8 (_sim_itree) lbindC.
  Proof.
    econs.
    { ii. eapply lbindR_mon; eauto. }
    i. rename l into llll. inv PR; csc.
    remember (st_src0, i_src). remember(st_tgt0, i_tgt).
    revert st_src0 i_src st_tgt0 i_tgt Heqp Heqp0.
    revert k_src k_tgt SIMK. eapply GF in SIM.
    induction SIM using _sim_itree_ind2; i; clarify.
    + rewrite ! bind_ret_l. exploit SIMK; eauto. i.
      eapply sim_itree_flag_mon.
      { eapply sim_itree_mon; eauto. i. eapply rclo8_base. auto. }
      { ss. }
      { ss. }
    + rewrite ! bind_bind. econs; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. i. exploit K; eauto. i. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. i. exploit K; eauto. i. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. 
    + rewrite ! bind_bind. econs; eauto. 
    + econs; eauto. eapply rclo8_clo_base. econs; eauto.
  Qed.

  Lemma lbindC_spec: lbindC  <9= gupaco8 (_sim_itree) (cpn8 (_sim_itree)).
  Proof.
    intros. eapply wrespect8_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

End SIM.

Require Import SimGlobal.
Require Import Red IRed.

Module TAC.
  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac step := ired_both; guclo simg_safe_spec; econs; et; i.
  Ltac steps := (repeat step); ired_both.

  Ltac force := ired_both; guclo simg_indC_spec; econs; et.
End TAC.
Import TAC.


Section PRODUCT_LENS.

  (* Context {A B : Type}. *)

  Definition fstl : Lens.t Any.t Any.t :=
    (fun ab => 
      match Any.split ab with
      | Some (a, b) => (a, (fun a' => Any.pair a' b)) 
      | None => (tt↑, (fun _ => ab))
      end).

  Definition sndl : Lens.t Any.t Any.t :=
    (fun ab => 
      match Any.split ab with
      | Some (a, b) => (b, (fun b' => Any.pair a b')) 
      | None => (tt↑, (fun _ => ab))
      end).

End PRODUCT_LENS.

Module ModSemAdd.
Import ModSem.

Section ADD.
  Variable M1 M2 : t.

  Definition run_l {V} (run: Any.t -> Any.t * V): Any.t -> Any.t * V :=
    fun st => 
      match Any.split st with
      | Some (a, b) => let (a', v) := run a in (Any.pair a' b, v)
      | None => run tt↑
        (* (tt↑, snd (run tt↑)) *)
      end.
 
  Definition run_r {V} (run: Any.t -> Any.t * V): Any.t -> Any.t * V :=
    fun st => 
      match Any.split st with
      | Some (a, b) => let (b', v) := run b in (Any.pair a b', v)
      | None => run tt↑
      (* (tt↑, snd (run tt↑)) *)
      end.      

  Definition emb_l : forall T, Es T -> Es T :=
    fun T es => 
    match es with
    | inr1 (inl1 (SUpdate run)) => inr1 (inl1 (SUpdate (run_l run)))
    | _ => es
    end.   

  Definition emb_r : forall T, Es T -> Es T :=
    fun T es => 
    match es with
    | inr1 (inl1 (SUpdate run)) => inr1 (inl1 (SUpdate (run_r run)))
    | _ => es
    end. 

  Definition trans_l f : gname * (Any.t -> itree _ Any.t) :=
    (fst f, (fun args => translate emb_l ((snd f) args))).

  Definition trans_r f : gname * (Any.t -> itree _ Any.t) :=
    (fst f, (fun args => translate emb_r ((snd f) args))).   

  (* Definition add_fnsems : alist gname (Any.t -> itree _ Any.t) :=
    (List.map trans_l M1.(fnsems)) ++ (List.map trans_r M2.(fnsems)). *)

  Definition add_fnsems : gname -> option (Any.t -> itree _ Any.t) :=
    fun fn =>
      match M1.(fnsems) fn, M2.(fnsems) fn with
      | Some fn_body, None => Some (fun args => translate emb_l (fn_body args))
      | None, Some fn_body => Some (fun args => translate emb_r (fn_body args))
      | Some _, Some _ => Some (fun args => triggerUB)
      | _, _ => None
      end.

  Definition add : t :=
  {|
    init_st := Any.pair (init_st M1) (init_st M2);
    fnsems := add_fnsems;
    (* idea: maintain linked-status? (boolean) *)
  |}.

End ADD.

Section PROOF.

Definition swap (ab: Any.t) : Any.t :=
  match Any.split ab with
  | Some (a, b) => Any.pair b a
  | None => ab (* or UB? *)
  end.

Definition swap_state {X} (f: Any.t -> Any.t * X): Any.t -> Any.t * X  :=
  (fun ba => let '(ab', t) := f (swap ba) in ((swap ab'), t)).

Definition swap_Es T (es: Es T) : Es T :=
  match es with
  | inr1 (inl1 (SUpdate f)) => inr1 (inl1 (SUpdate (swap_state f)))
  | inr1 (inr1 x) => inr1 (inr1 x)
  | inl1 y => inl1 y
  end.  
  
Definition swap_ems {R} (itl: itree Es R) (itr: itree Es R) :=
  itr = translate swap_Es itl.

(* Definition assoc oa'bc: Any.t :=
  match oa'bc with
  | Some a'bc => 
    match Any.split a'bc with
    | Some (a, bc) => 
      match Any.split bc with
      | Some (b, c) => Some (Any.pair (Any.pair a b) c)
      | None => Some (a'bc)
      end
    | None => Some (a'bc)
    end
  | None => None
  end. *)




(* Definition assoc' (a'bc: Any.t): Any.t :=
  match Any.split a'bc with
  | Some (a, bc) => 
      match Any.split bc with
      | Some (b, c) => Any.pair (Any.pair a b) c
      | None => a'bc
      end
    |None => a'bc
  end
  . *)
  
  Definition assoc (abc: Any.t) (abc': Any.t): Prop :=
  match Any.split abc with
  | Some (ab, c) => 
      match Any.split ab with
      | Some (a, b) => abc' = Any.pair a (Any.pair b c)
      | None => False
      end
    |None => False
  end
  . 

  (* Lemma assoc_any (a b c: Any.t) :
    assoc (Any.pair (Any.pair a b) c) (Any.pair a (Any.pair b c))
  .
  Proof.
    unfold assoc. rewrite ! Any.pair_split. refl.
  Qed.

  (* Definition assoc (abc: Any.t) (abc': Any.t): Prop :=
  match Any.split abc with
  | Some (a, bc) => 
      match Any.split bc with
      | Some (b, c) => abc' = Any.pair (Any.pair a b) c
      | None => True
      end
    |None => True
  end
  . 
  *)

  Lemma assoc_any (a b c: Any.t) :
    assoc (Any.pair a (Any.pair b c)) (Any.pair (Any.pair a b) c)
  .
  Proof.
    unfold assoc. rewrite ! Any.pair_split. refl.
  Qed. *)


  Definition is_pair: Any.t -> Any.t :=
    fun x => match Any.split x with
            | Some (_, _) => x
            | None => tt↑
            end.

(* Definition assoc_state_0 T (f: Any.t -> Any.t * T): Any.t -> Any.t * T :=
  (fun ab'c => 
    match Any.split ab'c with
    | Some (ab, c) => 
        match Any.split ab with
        | Some (a, b) => 
            let '(a'bc, t) := f (Any.pair a (Any.pair b c)) in
            (assoc' a'bc, t)
        | None => 
            (* (ab'c, snd (f ab)) *)
            (Any.pair tt↑ c, snd (f tt↑))
        end
    | None => f tt↑
      (* (ab'c, snd (f ab'c)) *)
    end). *)

Definition assoc_any_l (abc: Any.t): option Any.t :=
  match Any.split abc with
  | None => None
  | Some (a, bc) => 
      match Any.split bc with
      | None => None
      | Some (b, c) => Some (Any.pair (Any.pair a b) c)
      end
  end.

  Definition assoc_any_r (abc: Any.t): option Any.t :=
    match Any.split abc with
    | None => None
    | Some (ab, c) => 
        match Any.split ab with
        | None => None
        | Some (a, b) => Some (Any.pair a (Any.pair b c))
        end
    end.
    
Definition assoc_state V (f: Any.t -> Any.t * V): Any.t -> Any.t * V :=
  fun abc =>
    match assoc_any_r abc with
    | None => f tt↑
        (* (tt↑, snd (f tt↑)) *)
    | Some abc' => 
        let '(r, v) := f abc' in 
        match assoc_any_l r with
        | None => f tt↑
          (* (tt↑, v) *)
        | Some r' => (r', v)
        end
    end.


(* Definition assoc_state T (f: Any.t -> Any.t * T): Any.t -> Any.t * T :=
  fun abc =>
    match Any.split abc with
    | None => (tt↑, snd (f tt↑))
    | Some (ab, c) =>
        match Any.split ab with
        | None => (tt↑, snd (f tt↑))
        | Some (a, b) => 
          let '(a'bc, t) := f (Any.pair a (Any.pair b c)) in
        (assoc' a'bc, t)


Definition assoc_state T (f: Any.t -> Any.t * T): Any.t -> Any.t * T :=
  (fun ab'c => 
    match Any.split ab'c with
    | Some (ab, c) => 
        match Any.split ab with
        | Some (a, b) => 
            let '(a'bc, t) := f (Any.pair a (Any.pair b c)) in
            (assoc' a'bc, t)
        | None => 
            let '(c', t) := f (Any.pair tt↑ (Any.pair tt↑ c)) in
            let c' := assoc' c' in
            let c' := match Any.split c' with
                    | Some (_, c') => c'
                    | None => c'
                    end in
            (Any.pair ab c', t)
            (* (Any.pair ab (fst (f c)), snd (f c)) *)
            (* (Any.pair tt↑ c, snd (f tt↑)) *)
        end
    | None => 
      let '(c', t) := f ab'c in
      (* let c' := assoc' c' in *)
      let c := match Any.split c' with
              | Some (_, c') => c'
              | None => c'
              end in
      (c', snd (f ab'c))
    end).     *)
(* Definition assoc_state {X} (f: Any.t -> Any.t * X): Any.t -> Any.t * X :=
  (fun ab'c => let '(a'bc, t) := f (assoc' ab'c) in (assoc a'bc, t)). *)

(* Definition assoc_run {T} (f f': Any.t -> Any.t * T) : Prop :=
  (exists a b c,
    let abc := Any.pair a (Any.pair b c) in
    let abc' := Any.pair (Any.pair a b) c in 
    assoc (fst (f abc)) (fst (f' abc')) /\ 
                snd (f abc) = snd (f' abc'))
    (* (exists abc abc', assoc abc abc' /\ assoc (fst (f abc)) (fst (f' abc')) /\ snd (f abc) = snd (f' abc')) *)

. *)

(* Definition assoc_Es T (es: Es T) (es': Es T) : Prop :=
  match es, es' with
  | (inr1 (inl1 (SUpdate f))), (inr1 (inl1 (SUpdate f')))  => assoc_run f f'
  | (inr1 (inr1 x)), (inr1 (inr1 x')) => True
  | (inl1 y), (inl1 y') => True
  | _, _ => False
  end. *)


(* Definition assoc_Es' assoc_state T (es: Es T) : Es T :=
  match es with
  | inr1 (inl1 (SUpdate f)) => inr1 (inl1 (SUpdate (assoc_state _ f)))
  | inr1 (inr1 x) => inr1 (inr1 x)
  | inl1 y => inl1 y
  end.   *)

  Definition assoc_Es T (es: Es T) : Es T :=
    match es with
    | inr1 (inl1 (SUpdate f)) => inr1 (inl1 (SUpdate (assoc_state f)))
    | _ => es
    end.

Variable it: itree Es Any.t.
Check translate (emb_l >>> emb_l) it.
Check emb_l = (emb_l >>> emb_l).

Inductive assoc_emb : IFun Es Es -> IFun Es Es -> Prop := 
  |assoc_emb_1 : assoc_emb emb_l (emb_l >>> emb_l)
  |assoc_emb_2 : assoc_emb (emb_l >>> emb_r ) (emb_r >>> emb_l)
  |assoc_emb_3 : assoc_emb (emb_r >>> emb_r) emb_r
.

Inductive assoc_ems : itree Es Any.t -> itree Es Any.t -> Prop := 
  | assoc_ems_intro emb_l emb_r it (EMB: assoc_emb emb_l emb_r) :
      assoc_ems (translate emb_l it) (translate emb_r it).




(* Definition assoc_ems {R} (itl: itree Es R) (itr: itree Es R) :=
  translate (assoc_Es) itl = itr. *)


  (* (exists f, itr = translate (assoc_Es' f) itl) . *)
  (* /\ (forall T, exists f, forall es, assoc_Es es ((assoc_Es' f) T es)).  *)

(* Print trigger. *)

(* Search translate. *)

Lemma translate_triggerUB T (f: forall T, Es T -> Es T) (g: forall T, (Any.t -> Any.t * T) -> (Any.t -> Any.t * T))
    (COND: f _ (subevent _ (Take void)) = (subevent _ (Take void)))
  :
      translate f (@triggerUB _ T _) = @triggerUB _ T _ 
.

Proof.
  unfold triggerUB.
  erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
  f_equal.
  - unfold trigger. 
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    repeat f_equal; et. 
    extensionality v. destruct v.
  - extensionality v. destruct v.
Qed. 


(* Lemma swap_swap a : swap (swap a) = a.
Proof.
  i. unfold swap.
  destruct (Any.split a) eqn:A.
  - destruct p. rewrite Any.pair_split. 
    rewrite <- Any.split_pair with (a:=a); et.
  - rewrite A. et.  
Qed. *)


Lemma swap_ems_prog X ms0 ms1 (e: callE X)
:
      swap_ems (prog (add ms1 ms0) e) (prog (add ms0 ms1) e)
.
Proof. Admitted.
  (* destruct e. s. unfold unwrapU, add_fnsems. 
  des_ifs; grind; unfold swap_ems.
  - eapply translate_triggerUB; ss.
  - erewrite <- ! (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
    f_equal.
    unfold ">>>", Cat_IFun, emb_l, emb_r, lmap. 
    extensionalities T es.
    unfold swap_Es.
    destruct es as [c|[s|e]]; et.
    destruct s.
    unfold map_lens. 
    repeat (f_equal).
    unfold swap_state. 
    extensionality x. ss.
    (* destruct x; ss. *)
    destruct (Any.split x) eqn:Xspl.
    + destruct p. unfold lens_state.
        unfold swap, Lens.set, Lens.view. s.
        unfold fstl, sndl.
        rewrite ! Xspl.
        rewrite ! Any.pair_split. ss. f_equal.
        rewrite Any.pair_split. ss.
      + unfold lens_state, swap, Lens.set, Lens.view.
        unfold fstl, sndl. rewrite ! Xspl. ss.
        rewrite Any.upcast_split. et.

  - erewrite <- ! (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
    f_equal.
    unfold ">>>", Cat_IFun, emb_l, emb_r, lmap. 
    extensionalities T es. des_ifs.
    destruct s0. s. 
    repeat (f_equal).
    unfold swap_state. 
    extensionality x. ss.
    unfold lens_state, swap, Lens.set, Lens.view. s.
    unfold fstl, sndl.
    destruct (Any.split x) eqn:Xspl.
      + destruct p. s. 
        rewrite ! Any.pair_split. ss. f_equal.
        rewrite ! Any.pair_split. et.

      + ss. rewrite ! Xspl. ss.
        rewrite Any.upcast_split. et.  
  - unfold triggerUB. grind.
    erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
    f_equal.
    + unfold trigger.
      erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
      repeat f_equal.
      extensionality v. destruct v.
    + extensionality v. destruct v.
Qed. *)



Lemma assoc_ems_prog ms0 ms1 ms2 (e: callE Any.t)

:
  assoc_ems (prog (add ms0 (add ms1 ms2)) e) (prog (add (add ms0 ms1) ms2) e)
.
Proof. Admitted.
  (* destruct e. s. 
  unfold unwrapU.
  unfold assoc_ems. 
  repeat (unfold add_fnsems; grind).
  (* splits. *)
  (* 2: {
    exists (init_st (add ms0 (add ms1 ms2))).
    exists (init_st (add (add ms0 ms1) ms2)).
    split.
    - apply assoc_any.
    - s. unfold assoc_Es' in *. inv Heq.
      unfold assoc_state. rewrite ! Any.pair_split. des_ifs.
      unfold assoc, assoc'. des_ifs; et; inv Heq1; clarify.
      + split; et. admit.
      + split; et. admit.
  }  *)
  des_ifs; grind; try (repeat (rewrite translate_triggerUB; et)). (* exists assoc_state_1 removed*)

  - erewrite <- ! (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
    f_equal.
    unfold ">>>", Cat_IFun.
    (* unfold emb_l. *)
    extensionalities T es.
    unfold emb_l.
    des_ifs. s.
    
    repeat f_equal. i.
    unfold run_l, assoc_state.
    extensionality abc.
    (* unfold assoc_state. s.
    extensionality ab'c.
    unfold lens_state. s.
    unfold Lens.set, Lens.view.
    unfold fstl. *)
    destruct (Any.split abc) eqn: ABC; cycle 1.
    + rewrite ! Any.upcast_split.
      unfold assoc_any_r. rewrite ABC. et.
    + destruct p as [ab c]. s.
      unfold assoc_any_r. rewrite ABC.
      (* unfold assoc'. *)
      destruct (Any.split ab) eqn:AB; cycle 1.
      * rewrite ! Any.upcast_split. s.
         unfold assoc_any_l, assoc_any_r.
        rewrite ABC. ss.
      * destruct p as [a b]. s. rewrite Any.pair_split.
        des_ifs; ss; rewrite ! Any.pair_split in *; clarify; rewrite ! Any.pair_split in *; clarify.
      * s. rewrite Any.pair_split. s. rewrite ! Any.pair_split. et. 
        (* admit.  *)
        (* rewrite Any.upcast_split. s. et.  *)
        (* rewrite Any.pair_split. ss. *)
    + s. 
      (* admit. *)
      (* s. rewrite AB'C. et. *)
      s. rewrite Any.upcast_split. et. 
           

  - 
    erewrite <- ! (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
    eapply translate_triggerUB.
    unfold ">>>".
    unfold Cat_IFun.
    extensionalities T es. des_ifs.

  - 
    erewrite <- ! (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
    f_equal.
    unfold ">>>", Cat_IFun, emb_l, emb_r, lmap.
    extensionalities T es. des_ifs.
    destruct s2. s.
    repeat f_equal.
    unfold assoc_state. s.
    extensionality ab'c.
    unfold lens_state. s.
    unfold Lens.set, Lens.view.
    unfold fstl, sndl.
    destruct (Any.split ab'c) eqn: AB'C.
    + destruct p as [ab c]. s.
      unfold assoc'.
      destruct (Any.split ab) eqn:AB.
      * destruct p as [a b]. s. rewrite Any.pair_split.
        des_ifs; ss; rewrite ! Any.pair_split in *; clarify; rewrite ! Any.pair_split in *; clarify.
      * s.  
        rewrite ! Any.pair_split. s. rewrite ! Any.pair_split. s.
        rewrite ! Any.pair_split. refl. 
        (* admit. *)
        (* rewrite Any.upcast_split. s. rewrite Any.upcast_split. et. *)
        (* rewrite ! Any.pair_split. ss. repeat f_equal. *)
    + 
      (* admit. *)
      (* s. rewrite AB'C. et.  *)
      s. rewrite Any.upcast_split. refl.
      (* s. rewrite Any.upcast_split. et.  *)

  - 
    erewrite <- ! (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
    f_equal.
    unfold ">>>", Cat_IFun, emb_r, lmap.
    extensionalities T es. des_ifs. 
    destruct s0. s.
    repeat f_equal. 
    unfold assoc_state, lens_state.
    extensionality ab'c.
    unfold Lens.set, Lens.view, fstl, sndl.
    destruct (Any.split ab'c) eqn: AB'C.
    + destruct p as [ab c].
      unfold assoc'.
      destruct (Any.split ab) eqn: AB.
      * destruct p as [a b]. 
        repeat (rewrite ! Any.pair_split; s).
        repeat f_equal. apply Any.split_pair in AB. et.
      * s. 
        rewrite ! Any.pair_split. s. rewrite ! Any.pair_split. s.
        rewrite ! Any.pair_split. et.
        (* rewrite Any.upcast_split. s. rewrite Any.upcast_split. s. *)
    + s. rewrite Any.upcast_split. s. et.
      (* s. rewrite AB'C. et. *)
      (* s. rewrite Any.upcast_split. s. rewrite Any.upcast_split. et. *)
         

  - 
    unfold triggerUB. grind.
    erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
    f_equal.
    + unfold trigger.
      erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
      repeat f_equal.
      extensionality v. destruct v.
    + extensionality v. destruct v.
Qed. *)

Definition assoc_st (stp: Any.t * Any.t) : Prop :=
  exists a b c, fst stp = Any.pair a (Any.pair b c) /\ 
  snd stp = Any.pair (Any.pair a b) c
.
(* Check sim_itree. *)
Hint Resolve sim_itree_mon: paco.
Hint Resolve cpn8_wcompat: paco.



Lemma add_assoc_aux
        itl itr stl str
        (ASSOC: assoc_ems itl itr)
        (STATE: assoc_st (stl, str))

  :
      sim_itree (fun _ => assoc_st) top2 false false tt (stl, itl) (str, itr).
Proof.
  destruct ASSOC, STATE. des. ss.
  (* unfold assoc_st. *)
  ginit. 
  generalize it0 as itr. 
  clarify.
  generalize x as a0.
  generalize b as b0.
  generalize c as c0.
  gcofix CIH. i.
  rewrite (itree_eta_ itr).
  destruct (observe itr).
  - erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    gstep. apply sim_itree_ret.
    unfold lift_rel. 
    exists tt. splits; et.
    unfold assoc_st. exists a0, b0, c0; et.
  - erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    gstep. 
    apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
    eapply sim_itree_progress; et.
    gfinal. left. eapply CIH; et.
  - erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    rewrite <- ! bind_trigger.
    destruct e as [c'|[s|e]].
    + (* callE *)
      gstep. destruct c', EMB. 
      (* SIMPLIFY BELOW *)
      * apply sim_itree_call; clarify.
        -- exists a0, b0, c0; et.
        -- i. destruct WF, H, H, H. ss. clarify.
         gfinal. left. eapply CIH.
      * apply sim_itree_call; clarify.
        -- eexists a0, b0, c0; et.
        -- i. unfold assoc_st in WF. des. ss. clarify.
           gfinal. left. eapply CIH.
      * apply sim_itree_call; clarify.
        -- eexists a0, b0, c0; et.
        -- i. unfold assoc_st in WF. des. ss. clarify.
           gfinal. left. eapply CIH. 
    + (* sE *)
      gstep. destruct s, EMB.
      * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
        eapply sim_itree_progress; et.
        unfold run_l, run_r. rewrite ! Any.pair_split.
        gfinal. left. destruct (run a0). eapply CIH.
      * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
        eapply sim_itree_progress; et.
        unfold run_l, run_r. rewrite ! Any.pair_split.
        gfinal. left. destruct (run b0). eapply CIH.
      * apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
        eapply sim_itree_progress; et.
        unfold run_l, run_r. rewrite ! Any.pair_split.
        gfinal. left. destruct (run c0). eapply CIH.        
    + (* eventE *)
      gstep. destruct e, EMB.
      (* Choose *)
      * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      (* Take *)
      * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH. 
      * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH. 
      * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      (* Syscall *)
      * apply sim_itree_syscall. i.
        eapply sim_itree_flag_down.
        gfinal. left. eapply CIH. 
      * apply sim_itree_syscall. i.
        eapply sim_itree_flag_down.
        gfinal. left. eapply CIH.
      * apply sim_itree_syscall. i.
        eapply sim_itree_flag_down.
        gfinal. left. eapply CIH.
Qed. 



(* Move to SimGlobal? *)
Lemma simg_map R0 R1 RR R0' R1' RR' f_src f_tgt itl itr (f0: R0 -> R0') (f1: R1 -> R1')
      (SIM: @simg R0 R1 RR f_src f_tgt itl itr)
      (IMPL: forall r0 r1, RR r0 r1 -> RR' (f0 r0) (f1 r1): Prop)
:
      @simg R0' R1' RR' f_src f_tgt (f0 <$> itl) (f1 <$> itr)
.
Proof.
  revert_until RR'.
  pcofix CIH. i.
  (* punfold SIM.  *)
  induction SIM using simg_ind; s.
  - erewrite ! (bisimulation_is_eq _ _ (map_ret _ _)). eauto with paco.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_syscall. i. right. eapply CIH; et.
    (* specialize (SIM _ _ EQ). pclearbot. et. *)
    (* edestruct SIM; et. inv H. *)
  - erewrite ! (bisimulation_is_eq _ _ (map_tau _ _)).
    pfold. apply simg_tauL; et. punfold IHSIM.
  - erewrite ! (bisimulation_is_eq _ _ (map_tau _ _)). 
    pfold. apply simg_tauR; et. punfold IHSIM.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_chooseL; et. 
    des. exists x. punfold IH.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_chooseR; et.
    i. exploit SIM. esplits. des. punfold IH.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_takeL; et.
    i. exploit SIM. esplits. des. punfold IH.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_takeR; et.
    des. exists x. punfold IH.
  - pfold. apply simg_progress; et. right. eapply CIH; et.
Qed.

Context {CONF: EMSConfig}.



Theorem add_comm
        ms0 ms1
        (P0 P1: Prop) (IMPL: P1 -> P0)
        (* (WF: wf (add ms1 ms0)) *)
  :
    <<COMM: Beh.of_program (compile (add ms0 ms1) (Some P0)) <1= Beh.of_program (compile (add ms1 ms0) (Some P1))>>
.
Proof.

  destruct (classic (P1)); cycle 1.
  { ii. eapply initial_itr_not_wf;et. }
  replace P0 with P1.
  2: { eapply prop_ext. split; auto. }
  


  unfold compile. red. apply adequacy_global_itree; et.

  unfold initial_itr, assume. i.
  rewrite ! bind_bind.
  pfold. apply simg_takeL; et. i. apply simg_takeR; et. exists x.
  apply simg_progress; et.
  rewrite ! bind_ret_l.
  left. 

  generalize (Call "main" initial_arg) as e.
  assert (REL: swap (init_st (add ms1 ms0)) = init_st (add ms0 ms1)).
  { unfold init_st, swap. ss. rewrite Any.pair_split. et. }

  revert REL.
  (* generalize (option Any.t) as X. *)
  generalize (init_st (add ms1 ms0)) as stl0.
  generalize (init_st (add ms0 ms1)) as str0.

  i. eapply simg_map.
  2: { instantiate (1 := (fun r0 r1 => snd r0 = snd r1 /\ swap (fst r0) = fst r1)).
       i. apply H0.   }
  revert_until x.
  ginit. { i. apply cpn7_wcompat. apply simg_mon. }  
  (* gcofix CIH. i. *)
  i.

  pose proof (swap_ems_prog ms0 ms1 e) as REL'.

  revert REL'.
  generalize (prog (add ms1 ms0) e) as itl.
  generalize (prog (add ms0 ms1) e) as itr.
  rewrite <- REL. (* generalize states with swap relation *)
  generalize stl0 as stl. 
  gcofix CIH'. i.
  inv REL'.
  rewrite (itree_eta_ itl).
  destruct (observe itl).
  - (* Ret *)
    erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    rewrite ! interp_Es_ret.
    gstep. apply simg_ret. et.   
  - (* Tau *)
    erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    rewrite ! interp_Es_tau.
    gstep. apply simg_tauL; et. apply simg_tauR; et. 
    apply simg_progress; et.
    gfinal. left. eapply CIH'. ss.
  - (* Vis *)
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    destruct e0 as [c|[s|e0]].
    + (* callE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es X (@prog (add ms1 ms0)) (@ITree.trigger Es X (@inl1 callE (sum1 sE eventE) X c)) stl). 
      pattern (@interp_Es X (@prog (add ms0 ms1)) (@ITree.trigger Es X (@swap_Es X (@inl1 callE (sum1 sE eventE) X c)))
      (swap stl)).
      setoid_rewrite interp_Es_callE.
      setoid_rewrite interp_Es_callE.
      rewrite ! bind_tau.
      gstep. apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      rewrite <- ! interp_Es_bind.
    
      gfinal. left. eapply CIH'.
      unfold swap_ems. erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
      f_equal. apply swap_ems_prog.

    + (* sE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es X (@prog (add ms1 ms0))
      (@ITree.trigger Es X (@inr1 callE (sum1 sE eventE) X (@inl1 sE eventE X s))) stl).
      pattern (@interp_Es X (@prog (add ms0 ms1))
      (@ITree.trigger Es X (@swap_Es X (@inr1 callE (sum1 sE eventE) X (@inl1 sE eventE X s)))) 
      (swap stl)).
      setoid_rewrite interp_Es_sE.
      grind.
      setoid_rewrite interp_Es_sE.
      grind.
      gstep. 
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      unfold swap_state in *. rewrite swap_swap in Heq0. 
      rewrite Heq in Heq0. inv Heq0.
      gfinal. left. eapply CIH'. unfold swap_ems. et.

    + (* eventE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es X (@prog (add ms1 ms0))
      (@ITree.trigger Es X (@inr1 callE (sum1 sE eventE) X (@inr1 sE eventE X e0))) stl).
      pattern (@interp_Es X (@prog (add ms0 ms1))
      (@ITree.trigger Es X (@swap_Es X (@inr1 callE (sum1 sE eventE) X (@inr1 sE eventE X e0)))) 
      (swap stl)).
      setoid_rewrite interp_Es_eventE.
      setoid_rewrite interp_Es_eventE.
      grind. 
      gstep.
      destruct e0.
      * (* Choose *)
        apply simg_chooseR; et. i. apply simg_chooseL; et. exists x0.
        grind.
        apply simg_tauL; et. apply simg_tauR; et.
        apply simg_tauL; et. apply simg_tauR; et.
        apply simg_progress; et.
        gfinal. left. apply CIH'. unfold swap_ems. et.
      * (* Take *)
        apply simg_takeL; et. i. apply simg_takeR; et. exists x0.
        grind.
        apply simg_tauL; et. apply simg_tauR; et.
        apply simg_tauL; et. apply simg_tauR; et.
        apply simg_progress; et.
        gfinal. left. apply CIH'. unfold swap_ems. et.
      * (* Syscall *)
        apply simg_syscall. i. inv EQ.
        grind. 
        gstep.
        apply simg_tauL; et. apply simg_tauR; et.
        apply simg_tauL; et. apply simg_tauR; et.
        apply simg_progress; et.
        gfinal. left. apply CIH'. unfold swap_ems. et.

Qed.



(* Lemma add_assoc' ms0 ms1 ms2:
  add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
Proof. Admitted.
  (* induction ms2; ss. unfold add. f_equal; ss.
  { eapply app_assoc. }
  { eapply app_assoc. }
Qed. *)

Lemma add_assoc_eq ms0 ms1 ms2
  :
    add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
Proof. Admitted.
  (* unfold add. ss. f_equal.
  { apply List.app_assoc. }
  { apply List.app_assoc. }
Qed. *) *)


(* Variant _wf_run_itree (wf_run_itree: itree Es Any.t -> Prop) (itr: itree Es Any.t): Prop := *)
  

(* TODO: Define aux for both comm / assoc. *)
Lemma add_assoc_aux
        ms0 ms1 ms2
  :
        paco7 _simg bot7 Any.t Any.t eq false false
        (snd <$> interp_Es (prog (add (add ms0 ms1) ms2)) (prog (add (add ms0 ms1) ms2) (Call "main" initial_arg)) (init_st (add (add ms0 ms1) ms2)))
        (snd <$> interp_Es (prog (add ms0 (add ms1 ms2))) (prog (add ms0 (add ms1 ms2)) (Call "main" initial_arg)) (init_st (add ms0 (add ms1 ms2))))
.
Proof.
 (* Admitted. *)
  generalize (Call "main" initial_arg) as e.
  (* assert (REL: assoc (init_st (add ms0 (add ms1 ms2))) (init_st (add (add ms0 ms1) ms2))).
  { unfold init_st, assoc. ss. rewrite ! Any.pair_split. et. } *)
  (* assert (REL: assoc' (init_st (add ms0 (add ms1 ms2))) = init_st (add (add ms0 ms1) ms2)). *)
  (* { unfold init_st,  assoc. ss. rewrite ! Any.pair_split. refl. } *)
  (* revert REL. *)
  (* s. *)

  (* assert (SPLIT: exists mst0 mst1 mst2,
           Any.split (init_st (add ms0 (add ms1 ms2))) = Some (mst0, Any.pair mst1 mst2)).
  { s. exists (init_st ms0), (init_st ms1), (init_st ms2).
    splits; rewrite ! Any.pair_split; et. }
  revert SPLIT. *)

  (* s. *)
  (* generalize (init_st ms0) as st0.
  generalize (init_st ms1) as st1.
  generalize (init_st ms2) as st2. *)

  generalize (init_st (add (add ms0 ms1) ms2)) as stl0.
  generalize (init_st (add ms0 (add ms1 ms2))) as str0.

  i. eapply simg_map.
  2: { instantiate (1 := (fun r0 r1 => snd r0 = snd r1 /\ assoc (fst r0) (fst r1))).
       i. apply H. }
    
  revert_until ms2.
  ginit. { i. apply cpn7_wcompat. apply simg_mon. }
  gcofix CIH. i.

  pose proof (assoc_ems_prog ms0 ms1 ms2 e) as REL'.
  revert REL'.

  generalize (prog (add (add ms0 ms1) ms2) e) as itl.
  generalize (prog (add ms0 (add ms1 ms2)) e) as itr.
  rewrite <- REL.
  revert SPLIT.
  generalize str0 as str.
  generalize mst0 as mst0'.
  generalize mst1 as mst1'.
  generalize mst2 as mst2'.


  gcofix CIH'. i.
  inv REL'.
    
  rewrite (itree_eta_ itr).
  destruct (observe itr).

  - (* Ret *)
    erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    rewrite ! interp_Es_ret.
    gstep. apply simg_ret.
    splits; et. s.
    unfold assoc, assoc'. 
    (* des_ifs. *)

    rewrite SPLIT.
    rewrite ! Any.pair_split. 
    apply Any.split_pair. rewrite SPLIT. refl.

  - (* Tau *)
    erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    rewrite ! interp_Es_tau.
    gstep. apply simg_tauL; et. apply simg_tauR; et. 
    apply simg_progress; et.
    gfinal. left. eapply CIH'. ss. et.
    unfold assoc_ems. et.
    (* exists x. et. *)
  - (* Vis *)
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    destruct e0 as [c|[s|e0]].
    + (* call E *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      Set Printing All.
      pattern (@interp_Es X (@prog (add (add ms0 ms1) ms2))
      (@ITree.trigger Es X (@assoc_Es' X (@inl1 callE (sum1 sE eventE) X c))) 
      (assoc' str)).
      pattern (@interp_Es X (@prog (add ms0 (add ms1 ms2)))
      (@ITree.trigger Es X (@inl1 callE (sum1 sE eventE) X c)) str).
      setoid_rewrite interp_Es_callE.
      setoid_rewrite interp_Es_callE.
      rewrite ! bind_tau.
      gstep. apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      rewrite <- ! interp_Es_bind.
    
      gfinal. left. eapply CIH'. et.
      ss. unfold assoc_ems.
      erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
      f_equal.
      (* admit. *)
       apply assoc_ems_prog.
    + (* sE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      Set Printing All.
      pattern (@interp_Es X (@prog (add (add ms0 ms1) ms2))
      (@ITree.trigger Es X (@assoc_Es' X (@inr1 callE (sum1 sE eventE) X (@inl1 sE eventE X s))))
      (assoc' str)). 
      pattern (@interp_Es X (@prog (add ms0 (add ms1 ms2)))
      (@ITree.trigger Es X (@inr1 callE (sum1 sE eventE) X (@inl1 sE eventE X s))) str).
      setoid_rewrite interp_Es_sE.
      grind.
      setoid_rewrite interp_Es_sE.
      grind.
      gstep. 
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      unfold assoc_state, assoc' in Heq0.
      rewrite SPLIT in Heq0.
      rewrite ! Any.pair_split in Heq0.
      hexploit SPLIT. i. apply Any.split_pair in H. des.
      rewrite H in Heq.
      rewrite Heq in Heq0.
      replace t1 with (assoc' t0).
      2: { inv Heq0. unfold assoc'. et. }
      gfinal. left.
      destruct (Any.split t0) eqn: T0.
      * destruct p. s. destruct (Any.split t3) eqn: T3.
        -- destruct p. s. apply Any.split_pair in T0, T3.
           des. clarify. 
           eapply CIH'.
           ++ rewrite Any.pair_split. et.
           ++ unfold assoc_ems. et.
        -- clarify. eapply CIH'.  

      inv Heq0. 
      destruct (Any.split t0) eqn:T0.
      * destruct p. s.
        destruct (Any.split t2) eqn:T2.
        -- destruct p. s.
           apply Any.split_pair in T0, T2. des. clarify.
           gfinal. left. apply CIH'.


      (* Do we have that 'SUpdate run' maintains the pairing status of Any.t? *)
      (* Either "pair-invariant" exists or some good associativity definition for non-splittable Any.t *)

      (* make lemma of assoc_assoc *)
      (* assert (assoc_assoc: forall x, assoc' (assoc x) = x). 
      { i. unfold assoc, assoc'. des_ifs.
        - rewrite Any.pair_split in Heq1.
          inv Heq1. inv Heq4. 
          rewrite Any.pair_split in Heq2.
          inv Heq2. rewrite <- Any.split_pair with (a:=x1); et.
          rewrite Heq3. f_equal. f_equal.
          rewrite <- Any.split_pair with (a:=t7); et.
        all: admit.
      } *)
      admit.
  + (* eventE *)
    rewrite <- ! bind_trigger, ! interp_Es_bind.
    (* Set Printing All. *)
    pattern (@interp_Es X (@prog (add (add ms0 ms1) ms2))
    (@ITree.trigger Es X (@assoc_Es' X (@inr1 callE (sum1 sE eventE) X (@inr1 sE eventE X e0))))
    (assoc' (Any.pair st0 (Any.pair st1 st2)))).
    pattern (@interp_Es X (@prog (add ms0 (add ms1 ms2)))
    (@ITree.trigger Es X (@inr1 callE (sum1 sE eventE) X (@inr1 sE eventE X e0)))
    (Any.pair st0 (Any.pair st1 st2))).
    setoid_rewrite interp_Es_eventE.
    setoid_rewrite interp_Es_eventE.
    grind.
    gstep.
    destruct e0.
    * (* Choose *)
      apply simg_chooseR; et. i. apply simg_chooseL; et. exists x.
      grind.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      gfinal. left. apply CIH'. unfold assoc_ems. et.
    * (* Take *)
      apply simg_takeL; et. i. apply simg_takeR; et. exists x.
      grind.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      gfinal. left. apply CIH'. unfold assoc_ems. et.
    * (* Syscall *)
      apply simg_syscall. i. inv EQ.
      grind. 
      gstep.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      gfinal. left. apply CIH'. unfold assoc_ems. et.
Qed. 

Lemma add_assoc_rev_aux
        ms0 ms1 ms2
  :
        paco7 _simg bot7 Any.t Any.t eq false false
        (snd <$> interp_Es (prog (add ms0 (add ms1 ms2))) (prog (add ms0 (add ms1 ms2)) (Call "main" initial_arg)) (init_st (add ms0 (add ms1 ms2))))
        (snd <$> interp_Es (prog (add (add ms0 ms1) ms2)) (prog (add (add ms0 ms1) ms2) (Call "main" initial_arg)) (init_st (add (add ms0 ms1) ms2)))
.
Proof. Admitted.
  (* generalize (Call "main" initial_arg) as e.
  assert (REL: assoc (init_st (add ms0 (add ms1 ms2))) = init_st (add (add ms0 ms1) ms2)).
  { unfold init_st. et. }
  revert REL.

  generalize (Any.t) as X.
  generalize (init_st (add ms0 (add ms1 ms2))) as stl0.
  generalize (init_st (add (add ms0 ms1) ms2)) as str0.

  i. eapply simg_map.
  2: { instantiate (1 := (fun r0 r1 => snd r0 = snd r1 /\ assoc (fst r0) = fst r1)).
       i. apply H. }
    
  revert_until ms2.
  ginit. { i. apply cpn7_wcompat. apply simg_mon. }
  gcofix CIH. i.

  pose proof (assoc_ems_prog ms0 ms1 ms2 e) as REL'.
  revert REL'.

  generalize (prog (add ms0 (add ms1 ms2)) e) as itl.
  generalize (prog (add (add ms0 ms1) ms2) e) as itr.
  rewrite <- REL.
  generalize stl0 as stl.

  gcofix CIH'. i.
  inv REL'.
    
  rewrite (itree_eta_ itl).
  destruct (observe itl).

  - (* Ret *)
    erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    rewrite ! interp_Es_ret.
    gstep. apply simg_ret. et.
  - (* Tau *)
    erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    rewrite ! interp_Es_tau.
    gstep. apply simg_tauL; et. apply simg_tauR; et. 
    apply simg_progress; et.
    gfinal. left. eapply CIH'. ss.
  - (* Vis *)
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    destruct e0 as [c|[s|e0]].
    + (* callE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es (state (add ms0 (add ms1 ms2))) X0 (@prog (add ms0 (add ms1 ms2)))
      (@ITree.trigger (Es (state (add ms0 (add ms1 ms2)))) X0 (@inl1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 c)) stl).
      pattern (@interp_Es (prod (prod (state ms0) (state ms1)) (state ms2)) X0 (@prog (add (add ms0 ms1) ms2))
      (@ITree.trigger (Es (prod (prod (state ms0) (state ms1)) (state ms2))) X0
         (@assoc_Es (state ms0) (state ms1) (state ms2) X0 (@inl1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 c)))
      (@assoc (state ms0) (state ms1) (state ms2) stl)).
      setoid_rewrite interp_Es_callE.
      setoid_rewrite interp_Es_callE.
      rewrite ! bind_tau.
      gstep. apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      rewrite <- ! interp_Es_bind.
    
      gfinal. left. eapply CIH'.
      unfold assoc_ems. erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
      f_equal. apply assoc_ems_prog.
    + (* sE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es (state (add ms0 (add ms1 ms2))) X0 (@prog (add ms0 (add ms1 ms2)))
      (@ITree.trigger (Es (state (add ms0 (add ms1 ms2)))) X0
         (@inr1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 (@inl1 (sE (state (add ms0 (add ms1 ms2)))) eventE X0 s))) stl).
      pattern (@interp_Es (prod (prod (state ms0) (state ms1)) (state ms2)) X0 (@prog (add (add ms0 ms1) ms2))
      (@ITree.trigger (Es (prod (prod (state ms0) (state ms1)) (state ms2))) X0
         (@assoc_Es (state ms0) (state ms1) (state ms2) X0
            (@inr1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 (@inl1 (sE (state (add ms0 (add ms1 ms2)))) eventE X0 s))))
      (@assoc (state ms0) (state ms1) (state ms2) stl)).

      setoid_rewrite interp_Es_sE.
      grind.
      setoid_rewrite interp_Es_sE.
      grind.
      gstep. 
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      destruct stl. destruct s4. inv Heq1.
      (* rewrite H0 in Heq. *)
      assert (SSS: (s, x) = (s1, (s0, s3), x0)). { rewrite <- H0, <- Heq. et. }
      inv SSS.
      gfinal. left.
      replace (s1, s0, s3) with (assoc (s1, (s0, s3))); et.
      eapply CIH'. unfold assoc_ems. et.
  + (* eventE *)
    rewrite <- ! bind_trigger, ! interp_Es_bind.
    Set Printing All.

    pattern  (@interp_Es (state (add ms0 (add ms1 ms2))) X0 (@prog (add ms0 (add ms1 ms2)))
    (@ITree.trigger (Es (state (add ms0 (add ms1 ms2)))) X0
       (@inr1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 (@inr1 (sE (state (add ms0 (add ms1 ms2)))) eventE X0 e0))) stl).
    pattern  (@interp_Es (prod (prod (state ms0) (state ms1)) (state ms2)) X0 (@prog (add (add ms0 ms1) ms2))
    (@ITree.trigger (Es (prod (prod (state ms0) (state ms1)) (state ms2))) X0
       (@assoc_Es (state ms0) (state ms1) (state ms2) X0
          (@inr1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 (@inr1 (sE (state (add ms0 (add ms1 ms2)))) eventE X0 e0))))
    (@assoc (state ms0) (state ms1) (state ms2) stl)).

    setoid_rewrite interp_Es_eventE.
    setoid_rewrite interp_Es_eventE.
    grind.
    gstep.
    destruct e0.
    * (* Choose *)
      apply simg_chooseR; et. i. apply simg_chooseL; et. exists x.
      grind.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      gfinal. left. apply CIH'. unfold assoc_ems. et.
    * (* Take *)
      apply simg_takeL; et. i. apply simg_takeR; et. exists x.
      grind.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      gfinal. left. apply CIH'. unfold assoc_ems. et.
    * (* Syscall *)
      apply simg_syscall. i. inv EQ.
      grind. 
      gstep.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      gfinal. left. apply CIH'. unfold assoc_ems. et.
Qed. *)


Theorem add_assoc
        ms0 ms1 ms2 P
  :
    <<COMM: Beh.of_program (compile (add ms0 (add ms1 ms2)) P) <1=
            Beh.of_program (compile (add (add ms0 ms1) ms2) P)>>
.
Proof. 

  unfold compile. red. apply adequacy_global_itree; et.
  unfold initial_itr, assume. 
  destruct P.
  - rewrite ! bind_bind. pfold.
    apply simg_takeL; et. i. apply simg_takeR; et. exists x.
    apply simg_progress; et.
    rewrite ! bind_ret_l.
    left. apply add_assoc_aux.
  - rewrite ! bind_ret_l. apply add_assoc_aux.
Qed.




Theorem add_assoc_rev
        ms0 ms1 ms2 P
  :
    <<COMM: Beh.of_program (compile (add (add ms0 ms1) ms2) P) <1=
            Beh.of_program (compile (add ms0 (add ms1 ms2)) P)>>
.
Proof.
  unfold compile. red. apply adequacy_global_itree; et.
  unfold initial_itr, assume. 
  destruct P.
  - rewrite ! bind_bind. pfold.
    apply simg_takeL; et. i. apply simg_takeR; et. exists x.
    apply simg_progress; et.
    rewrite ! bind_ret_l.
    left. apply add_assoc_rev_aux.
  - rewrite ! bind_ret_l. apply add_assoc_rev_aux.
Qed.

End PROOF.
End ModSemAdd.

Module ModAdd.
Import Mod.
Section BEH.

Context `{Sk.ld}.
Context {CONF: EMSConfig}.

(* Definition compile (md: t): semantics :=
  ModSem.compile_itree (ModSem.initial_itr md.(enclose) (Some (wf md))). *)


Definition compile (md: t): semantics :=
  ModSem.compile_itree (ModSem.initial_itr md.(enclose) (Some (wf md))).


(*** wf about modsem is enforced in the semantics ***)

Definition add (md0 md1: t): t := {|
  get_modsem := fun sk =>
                  ModSemAdd.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
  sk := Sk.add md0.(sk) md1.(sk);
|}
.


(* Definition add (md0 md1: t): t := {|
  get_modsem := fun sk =>
                  ModSem.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
  sk := Sk.add md0.(sk) md1.(sk);
|}
. *)
(* 
Lemma enclose_eq md0 md1 ms0 ms1
    (ENCL0: enclose md0 = ms0)
    (ENCL1: enclose md1 = ms1)
  :
    enclose (add md0 md1) = (ModSem.add ms0 ms1)
.
Proof.
  unfold enclose, get_modsem. simpl in *. f_equal.
  - unfold enclose in *.   *)



Theorem add_comm
        md0 md1
  :
    <<COMM: Beh.of_program (compile (add md0 md1)) <1= Beh.of_program (compile (add md1 md0))>>
.
Proof.
Admitted.
  (* unfold compile. red. apply adequacy_global_itree; et.
  unfold ModSem.initial_itr, assume.
  
  rewrite ! bind_bind.
  pfold. apply simg_takeL; et. i.
   apply simg_takeR; et.
  assert (SK: Sk.wf (Sk.add (sk md0) (sk md1))). { apply Sk.wf_comm. et. }
  exists SK.
  apply simg_progress; et.
  rewrite ! bind_ret_l.
  left.
  (* May need a lemma about enclose: 
      enclose (add md0 md1) = add ms0 ms1
  *)
  unfold enclose.



ii. unfold compile in *.
  destruct (classic (Sk.wf (sk (add md1 md0)))).
  (* 2: { eapply ModSem.initial_itr_not_wf. ss. } *)
  ss. des. assert (SK: Sk.wf (Sk.add (sk md0) (sk md1))).
  { apply Sk.wf_comm. auto. }
  rewrite Sk.add_comm; et.
  eapply ModSemAdd.add_comm; [|et].
  { i. auto. }
  {  }
Qed. *)



(* Lemma add_assoc' ms0 ms1 ms2:
  add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
Proof.
  unfold add. f_equal.
  { extensionality skenv_link. ss. apply ModSem.add_assoc'. }
  { ss. rewrite Sk.add_assoc. auto. }
Qed. *)

Theorem add_assoc
        md0 md1 md2
  :
    <<COMM: Beh.of_program (compile (add md0 (add md1 md2))) =
            Beh.of_program (compile (add (add md0 md1) md2))>>
.
Proof. Admitted.
  (* rewrite add_assoc'. ss.
Qed. *)

Theorem add_assoc_rev
        md0 md1 md2
  :
    <<COMM: Beh.of_program (compile (add (add md0 md1) md2)) =
            Beh.of_program (compile (add md0 (add md1 md2)))>>
.
Proof. Admitted.
  (* rewrite add_assoc'. ss.
Qed. *)

Lemma add_empty_r 
      md
  : 
    << EMPTY: Beh.of_program (compile (add md empty)) =
              Beh.of_program (compile md)>>
.
Proof. Admitted.

Lemma add_empty_l 
      md
  : 
    << EMPTY: Beh.of_program (compile (add empty md)) =
              Beh.of_program (compile md)>>
.
Proof. Admitted.


(* Lemma add_empty_r md: add md empty = md.
Proof.
  destruct md; ss.
  unfold add, ModSem.add. f_equal; ss.
  - extensionality skenv. destruct (get_modsem0 skenv); ss.
    repeat rewrite app_nil_r. auto.
  - eapply Sk.add_unit_r.
Qed.

Lemma add_empty_l md: add empty md = md.
Proof.
  destruct md; ss.
  unfold add, ModSem.add. f_equal; ss.
  { extensionality skenv. destruct (get_modsem0 skenv); ss. }
  { apply Sk.add_unit_l. }
Qed. *)


Definition add_list (xs: list t): t :=
  fold_right add empty xs
.

(* Lemma add_list_single: forall (x: t), add_list [x] = x.
Proof. ii; cbn. rewrite add_empty_r. refl. Qed. *)

Definition add_list_cons
          x xs
        :
          (add_list (x::xs) = (add x (add_list xs)))
.
Proof. ss. Qed.
(* 
Definition add_list_snoc
          x xs
        :
          add_list (snoc xs x) = add (add_list xs) x
.
Proof. ginduction xs; ii; ss. Admitted. *)

Definition add_list_snoc
          x xs
        :
          << SNOC: Beh.of_program (compile (add_list (snoc xs x))) = 
                   Beh.of_program (compile (add (add_list xs) x)) >>
.
Proof. Admitted.
  (* ginduction xs; ii; ss.
  { cbn. rewrite add_empty_l, add_empty_r. et. }
  { cbn. rewrite <- add_assoc'.  r in IHxs. r. f_equal.}  *)

End BEH.
End ModAdd.

Section REFINE.
  Context `{Sk.ld}.

   Definition refines {CONF: EMSConfig} (md_tgt md_src: Mod.t): Prop :=
     (* forall (ctx: list Mod.t), Beh.of_program (ModL.compile (add_list (md_tgt :: ctx))) <1= *)
     (*                           Beh.of_program (ModL.compile (add_list (md_src :: ctx))) *)
     forall (ctx: list Mod.t), Beh.of_program (ModAdd.compile (ModAdd.add (ModAdd.add_list ctx) md_tgt)) <1=
                               Beh.of_program (ModAdd.compile (ModAdd.add (ModAdd.add_list ctx) md_src))
   .

   Definition refines_strong (md_tgt md_src: Mod.t): Prop :=
     forall {CONF: EMSConfig}, refines md_tgt md_src.


   Section CONF.
   Context {CONF: EMSConfig}.

   Definition refines2 (md_tgt md_src: list Mod.t): Prop :=
     forall (ctx: list Mod.t), Beh.of_program (ModAdd.compile (ModAdd.add (ModAdd.add_list ctx) (ModAdd.add_list md_tgt))) <1=
                               Beh.of_program (ModAdd.compile (ModAdd.add (ModAdd.add_list ctx) (ModAdd.add_list md_src)))
   .

   
   (* Global Program Instance refines2_PreOrder: PreOrder refines2.
   Next Obligation.
     ii. ss.
   Qed.
   Next Obligation.
     ii. eapply H0 in PR. eapply H1 in PR. eapply PR.
   Qed. *)

   (*** vertical composition ***)
   Global Program Instance refines_PreOrder: PreOrder refines.

   Next Obligation. ii. ss. Qed.
   Next Obligation. ii. eapply H1. eapply H0. ss. Qed.


   Global Program Instance refines_strong_PreOrder: PreOrder refines_strong.
   Next Obligation. ii. ss. Qed.
   Next Obligation. ii. eapply H1. eapply H0. ss. Qed.



   (*** horizontal composition ***)
   Theorem refines_add
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines md0_tgt md0_src)
         (SIM1: refines md1_tgt md1_src)
     :
       <<SIM: refines (ModAdd.add md0_tgt md1_tgt) (ModAdd.add md0_src md1_src)>>
   .
   Proof. Admitted.
(*    
     ii. r in SIM0. r in SIM1.
     (***
ctx (a0 b0)
(ctx a0) b0
(ctx a0) b1
      ***)
     rewrite ModAdd.add_assoc in PR.
     specialize (SIM1 (snoc ctx md0_tgt)). spc SIM1. rewrite ModAdd.add_list_snoc in SIM1.  eapply SIM1 in PR.
     (***
ctx (a0 b1)
(a0 b1) ctx
a0 (b1 ctx)
(b1 ctx) a0
      ***)
     rewrite <- ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     rewrite <- ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     (***
(b1 ctx) a1
a1 (b1 ctx)
(a1 b1) ctx
ctx (a1 b1)
      ***)
     specialize (SIM0 (cons md1_src ctx)). spc SIM0. rewrite ModAdd.add_list_cons in SIM0. eapply SIM0 in PR.
     eapply ModAdd.add_comm in PR.
     rewrite ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     ss.
   Qed. *)

   Theorem refines_proper_r
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines (ModAdd.add_list mds0_tgt) (ModAdd.add_list mds0_src))
     :
       <<SIM: refines (ModAdd.add (ModAdd.add_list mds0_tgt) (ModAdd.add_list ctx)) (ModAdd.add (ModAdd.add_list mds0_src) (ModAdd.add_list ctx))>>
   .
   Proof. Admitted.
(*    
     ii. r in SIM0. rename ctx into xs. rename ctx0 into ys.
     (***
ys + (tgt + xs)
(tgt + xs) + ys
tgt + (xs + ys)
(xs + ys) + tgt
      ***)
     eapply ModAdd.add_comm in PR.
     rewrite <- ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     (***
(xs + ys) + src
src + (xs + ys)
(src + xs) + ys
ys + (src + xs)
      ***)
     specialize (SIM0 (xs ++ ys)). spc SIM0. rewrite ModAdd.add_list_app in SIM0. eapply SIM0 in PR.
     eapply ModAdd.add_comm in PR.
     rewrite ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     ss.
   Qed. *)

   Theorem refines_proper_l
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines (ModAdd.add_list mds0_tgt) (ModAdd.add_list mds0_src))
     :
       <<SIM: refines (ModAdd.add (ModAdd.add_list ctx) (ModAdd.add_list mds0_tgt)) (ModAdd.add (ModAdd.add_list ctx) (ModAdd.add_list mds0_src))>>
   .
   Proof. Admitted.
     (* ii. r in SIM0. rename ctx into xs. rename ctx0 into ys.
     (***
ys + (xs + tgt)
(ys + xs) + tgt
(ys + xs) + src
ys + (xs + src)
      ***)
     rewrite ModAdd.add_assoc' in PR.
     specialize (SIM0 (ys ++ xs)). spc SIM0. rewrite ModAdd.add_list_app in SIM0. eapply SIM0 in PR.
     rewrite <- ModAdd.add_assoc' in PR.
     ss.
   Qed.  *)

   Definition refines_closed (md_tgt md_src: Mod.t): Prop :=
     Beh.of_program (ModAdd.compile md_tgt) <1= Beh.of_program (ModAdd.compile md_src)
   .

   Global Program Instance refines_closed_PreOrder: PreOrder refines_closed.
   Next Obligation. ii; ss. Qed.
   Next Obligation. ii; ss. eapply H1. eapply H0. eauto. Qed.

   Lemma refines_close: refines <2= refines_closed.
   Proof. ii. specialize (PR nil). ss. unfold ModAdd.add_list in *. ss. rewrite ! ModAdd.add_empty_l in PR. eauto. Qed.

   (*** horizontal composition ***)
   Theorem refines2_add
         (s0 s1 t0 t1: list Mod.t)
         (SIM0: refines2 t0 s0)
         (SIM1: refines2 t1 s1)
     :
       <<SIM: refines2 (t0 ++ t1) (s0 ++ s1)>>
   .
   Proof. Admitted.
(*    
     ii. r in SIM0. r in SIM1.
     (***
ctx (a0 b0)
(ctx a0) b0
(ctx a0) b1
      ***)
     rewrite ModAdd.add_list_app in PR.
     rewrite ModAdd.add_assoc in PR.
     specialize (SIM1 (ctx ++ t0)). spc SIM1. rewrite ModAdd.add_list_app in SIM1. eapply SIM1 in PR.
     (***
ctx (a0 b1)
(a0 b1) ctx
a0 (b1 ctx)
(b1 ctx) a0
      ***)
     rewrite <- ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     rewrite <- ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     (***
(b1 ctx) a1
a1 (b1 ctx)
(a1 b1) ctx
ctx (a1 b1)
      ***)
     specialize (SIM0 (s1 ++ ctx)). spc SIM0. rewrite ModAdd.add_list_app in SIM0. eapply SIM0 in PR.
     eapply ModAdd.add_comm in PR.
     rewrite ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     rewrite ! ModAdd.add_list_app in *.
     assumption.
   Qed.  *)


   Corollary refines2_pairwise
             (mds0_src mds0_tgt: list Mod.t)
             (FORALL: List.Forall2 (fun md_src md_tgt => refines2 [md_src] [md_tgt]) mds0_src mds0_tgt)
     :
       refines2 mds0_src mds0_tgt.
   Proof.
     induction FORALL; ss.
     hexploit refines2_add.
     { eapply H0. }
     { eapply IHFORALL. }
     i. ss.
   Qed.

   Lemma refines2_eq (mds0 mds1: list Mod.t)
     :
       refines2 mds0 mds1 <-> refines (ModAdd.add_list mds0) (ModAdd.add_list mds1).
   Proof.
     split.
     { ii. eapply H0. auto. }
     { ii. eapply H0. auto. }
   Qed.

   Lemma refines2_app mhd0 mhd1 mtl0 mtl1
         (HD: refines2 mhd0 mhd1)
         (TL: refines2 mtl0 mtl1)
     :
       refines2 (mhd0++mtl0) (mhd1++mtl1).
   Proof. Admitted.
(*    
     eapply refines2_eq. rewrite ! ModAdd.add_list_app. etrans.
     { eapply refines_proper_l. eapply refines2_eq. et. }
     { eapply refines_proper_r. eapply refines2_eq. et. }
   Qed. *)

   Lemma refines2_cons mhd0 mhd1 mtl0 mtl1
         (HD: refines2 [mhd0] [mhd1])
         (TL: refines2 mtl0 mtl1)
     :
       refines2 (mhd0::mtl0) (mhd1::mtl1).
   Proof.
     eapply (refines2_app HD TL).
   Qed.

   End CONF.



   (*** horizontal composition ***)
   Theorem refines_strong_add
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines_strong md0_tgt md0_src)
         (SIM1: refines_strong md1_tgt md1_src)
     :
       <<SIM: refines_strong (ModAdd.add md0_tgt md1_tgt) (ModAdd.add md0_src md1_src)>>
   .
   Proof.
     intros CONF. eapply (@refines_add CONF); et.
   Qed.

   Theorem refines_strong_proper_r
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines_strong (ModAdd.add_list mds0_tgt) (ModAdd.add_list mds0_src))
     :
       <<SIM: refines_strong (ModAdd.add (ModAdd.add_list mds0_tgt) (ModAdd.add_list ctx)) (ModAdd.add (ModAdd.add_list mds0_src) (ModAdd.add_list ctx))>>
   .
   Proof.
     intros CONF. eapply (@refines_proper_r CONF); et.
   Qed.

   Theorem refines_strong_proper_l
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines_strong (ModAdd.add_list mds0_tgt) (ModAdd.add_list mds0_src))
     :
       <<SIM: refines_strong (ModAdd.add (ModAdd.add_list ctx) (ModAdd.add_list mds0_tgt)) (ModAdd.add (ModAdd.add_list ctx) (ModAdd.add_list mds0_src))>>
   .
   Proof.
     intros CONF. eapply (@refines_proper_l CONF); et.
   Qed.

   Lemma refines_strong_refines {CONF: EMSConfig}: refines_strong <2= refines.
   Proof. ii. eapply PR; et. Qed.
End REFINE.
