Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import ModSem.
Require Import Behavior.
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
Require Import Any.

Set Implicit Arguments.

Local Open Scope nat_scope.

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


  Definition sim_fsem: relation (Any.t -> itree Es Any.t) :=
    (eq ==> (fun it_src it_tgt => forall w mrs_src mrs_tgt (SIMMRS: wf w (mrs_src, mrs_tgt)),
                 sim_itree false false w (mrs_src, it_src)
                           (mrs_tgt, it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (Any.t -> itree Es Any.t)) := RelProd eq sim_fsem.

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


Hint Resolve sim_itree_mon: paco.
Hint Resolve cpn8_wcompat: paco.

Lemma self_sim_itree:
  forall st itr,
    sim_itree (fun _ '(src, tgt) => src = tgt) top2 false false tt (st, itr) (st, itr).
Proof.
  ginit. gcofix CIH. i. ides itr.
  { gstep. eapply sim_itree_ret; ss. }
  { guclo sim_itree_indC_spec. econs.
    guclo sim_itree_indC_spec. econs.
    eapply sim_itree_progress_flag. gbase. auto.
  }
  destruct e.
  { dependent destruction c. rewrite <- ! bind_trigger. gstep.
    eapply sim_itree_call; ss. ii. subst.
    eapply sim_itree_flag_down. gbase. auto.
  }
  destruct s.
  { rewrite <- ! bind_trigger. resub. dependent destruction s.
    { guclo sim_itree_indC_spec. econs.
      guclo sim_itree_indC_spec. econs.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
  { rewrite <- ! bind_trigger. resub. dependent destruction e.
    { guclo sim_itree_indC_spec. econs 7. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs 8. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs. i.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
Qed.


(*** desiderata: (1) state-aware simulation relation !!!! ***)
(*** (2) not whole function frame, just my function frame !!!! ***)
(*** (3) would be great if induction tactic works !!!! (study itree case study more) ***)



Module ModSemPair.
Section SIMMODSEM.

  Variable (ms_src ms_tgt: ModSem.t).

  Let W: Type := (Any.t) * (Any.t).
  Inductive sim: Prop := mk {
    world: Type;
    wf: world -> W -> Prop;
    le: world -> world -> Prop;
    le_PreOrder: PreOrder le;
    sim_fnsems: Forall2 (sim_fnsem wf le) ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems);
    sim_initial: exists w_init, wf w_init (ms_src.(ModSem.init_st), ms_tgt.(ModSem.init_st));
  }.

End SIMMODSEM.

Lemma self_sim (ms: ModSem.t):
  sim ms ms.
Proof.
  econs; et.
  - instantiate (1:=fun (_ _: unit) => True). ss.
  - instantiate (1:=(fun (_: unit) '(src, tgt) => src = tgt)). (* fun p => fst p = snd p *)
    generalize (ModSem.fnsems ms).
    induction a; ii; ss.
    econs; eauto. econs; ss. ii; clarify.
    destruct w. exploit self_sim_itree; et.
  - ss.
Qed.

End ModSemPair.








Module ModPair.
Section SIMMOD.
   Variable (md_src md_tgt: Mod.t).
   Inductive sim: Prop := mk {
     sim_modsem:
       forall sk
              (SKINCL: Sk.incl md_tgt.(Mod.sk) sk)
              (SKWF: Sk.wf sk),
         <<SIM: ModSemPair.sim (md_src.(Mod.get_modsem) sk) (md_tgt.(Mod.get_modsem) sk)>>;
     sim_sk: <<SIM: md_src.(Mod.sk) = md_tgt.(Mod.sk)>>;
   }.

End SIMMOD.

End ModPair.



Section SIMMOD.

  Context {CONF: EMSConfig}.

  Lemma Mod_add_fnsems md0 md1 sk
    :
      (ModSem.fnsems (Mod.get_modsem (Mod.add md0 md1) sk)) =
      ModSem.add_fnsems (Mod.get_modsem md0 sk) (Mod.get_modsem md1 sk).
  Proof.
    ss.
  Qed.

  Lemma Mod_add_sk md0 md1
    :
      Mod.sk (Mod.add md0 md1) = Mod.sk md0 ++ Mod.sk md1.
  Proof.
    ss.
  Qed.
(* 
  Lemma Mod_list_incl_sk (mds: list Mod.t) md
        (IN: In md mds)
    :
      Sk.incl (Mod.sk md) (Mod.sk (Mod.add_list mds)).
  Proof.
    rewrite Mod.add_list_sk. revert IN. induction mds; ss.
    i. des; clarify.
    { ii. eapply in_or_app. auto. }
    { ii. eapply in_or_app. right. eapply IHmds; et. }
  Qed.

  Lemma Mod_add_list_get_modsem (mds: list Mod.t) sk
    :
      Mod.get_modsem (Mod.add_list mds) sk
      =
      fold_right ModSem.add {| ModSem.fnsems := []; ModSem.initial_mrs := [] |}
                 (List.map (fun (md: Mod.t) => Mod.get_modsem md sk) mds).
  Proof.
    induction mds; ss. f_equal. rewrite <- IHmds. ss.
  Qed. *)

End SIMMOD.





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

Section SEMPAIR.
  Variable ms_src: ModSem.t.
  Variable ms_tgt: ModSem.t.
  (* Variable ctx: ModSem.t.
  Definition ms_src := ModSem.add ctx ms_src'.
  Definition ms_tgt := ModSem.add ctx ms_tgt'. *)
  (* Variable mn: mname. *)
  Variable world: Type.
  Variable wf: world -> Any.t * Any.t -> Prop.
  Variable le: world -> world -> Prop.
  Hypothesis le_PreOrder: PreOrder le.
  
  Hypothesis fnsems_find_iff:
    forall fn,
      (<<NONE: alist_find fn ms_src.(ModSem.fnsems) = None>>) \/
      (exists (f: _ -> itree _ _) (ctx ms_src' ms_tgt': ModSem.t),
          (<<CTX: alist_find fn ctx.(ModSem.fnsems) = Some f>>) /\
          (<<SRC: ModSem.add ctx ms_src' = ms_src>>) /\
          (<<TGT: ModSem.add ctx ms_tgt' = ms_tgt>>)) \/
      (exists (f_src f_tgt: _ -> itree _ _),
          (<<SRC: alist_find fn ms_src.(ModSem.fnsems) = Some f_src>>) /\
          (<<TGT: alist_find fn ms_tgt.(ModSem.fnsems) = Some f_tgt>>) /\
          (<<SIM: sim_fsem wf le f_src f_tgt>>)).
          
  Variant g_lift_rel
          (w0: world) st_src0 st_tgt0: Prop :=
  | g_lift_rel_intro
      w1
      (LE: le w0 w1)
      (MN: wf w1 (st_src0, st_tgt0))
      
      (* (NMN: forall mn' (NIN: mn <> mn'), st_local mn' = st_local mn') *)
  .
  Variant my_r0:
    forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop :=
  | my_r0_intro
      w0
      (itr_src itr_tgt: itree Es Any.t)
      st_src0 st_tgt0 o_src o_tgt
      (SIM: sim_itree wf le o_src o_tgt w0 (st_src0, itr_src) (st_tgt0, itr_tgt))
      (* (STATE: forall mn' (MN: mn <> mn'), st_local mn' = st_local mn') *)
    :
      my_r0 (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
                g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt)
            o_src o_tgt
            (interp_Es (ModSem.prog ms_src) (itr_src) st_src0)
            (interp_Es (ModSem.prog ms_tgt) (itr_tgt) st_tgt0)
  .

  Variant my_r1:
    forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop :=
  | my_r1_intro
        w0 st_src st_tgt fn ctx 
        (* ms_src' ms_tgt' *)
        (CTX: exists f, alist_find fn ctx.(ModSem.fnsems) = Some f)
        (* (SRC: ModSem.add ctx ms_src' = ms_src)
        (TGT: ModSem.add ctx ms_tgt' = ms_tgt) *)
        (SIM: g_lift_rel w0 st_src st_tgt)
        (itr: itree Es Any.t)
    :
      my_r1 (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
                g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt)
            false false
            (interp_Es (ModSem.prog ms_src) (itr) st_src)
            (interp_Es (ModSem.prog ms_tgt) (itr) st_tgt)
  .

  Let my_r := my_r0 \7/ my_r1.



  Let sim_lift: my_r <7= simg.
  Proof.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    gcofix CIH. i. destruct PR.

    { destruct H.

      unfold sim_itree in SIM.
      remember (st_src0, itr_src).
      remember (st_tgt0, itr_tgt).
      remember w0 in SIM at 2.
      revert st_src0 itr_src st_tgt0 itr_tgt Heqp Heqp0 Heqw.
      (* TODO: why induction using sim_itree_ind doesn't work? *)
      pattern o_src, o_tgt, w, p, p0.
      match goal with
      | |- ?P o_src o_tgt w p p0 => set P
      end.
      revert o_src o_tgt w p p0 SIM.
      eapply (@sim_itree_ind world wf le Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; clarify.
      - rr in RET. des. step. splits; auto. econs; et.
      - hexploit (fnsems_find_iff fn). i. des.
        { step. rewrite interp_Es_bind.  steps. rewrite NONE. unfold unwrapU, triggerUB. grind. step. ss. }
        { steps. rewrite <- SRC, <- TGT. s. unfold ModSem.add_fnsems.
          rewrite ! alist_find_app_o. unfold ModSem.trans_l.
          rewrite ! alist_find_map. rewrite ! CTX. grind.
          rewrite SRC, TGT.

          apply simg_progress_flag. guclo bindC_spec. econs.
          { gbase. eapply CIH.
          
          right. econs; ss. { eexists. apply CTX. } econs; et. refl.

          (* econs; ss. grind. unfold sim_fsem, "==>" in SIM. et.  *)
          }
          { i. ss. destruct vret_src, vret_tgt. des; clarify. inv SIM.
            hexploit K; et. i. des. pclearbot.
            gbase. eapply CIH. left. econs; et.
          }          
        }

        { hexploit (SIM (varg) (varg)); et. i. des. ired_both. 
          steps. grind. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
          apply simg_progress_flag.
          guclo bindC_spec. econs.
          { gbase. eapply CIH. left. econs; ss. grind. et. }
          { i. ss. destruct vret_src, vret_tgt. des; clarify. inv SIM0.
            hexploit K; et. i. des. pclearbot. ired_both.
            steps. gbase. eapply CIH. left. econs; et.
          }
        }
      - step. i. subst. apply simg_progress_flag.
        hexploit (K x_tgt). i. des. pclearbot.
        steps. gbase. eapply CIH. left. econs; et.
      - steps.
      - steps. 
      - des. force. exists x. steps. eapply IH; eauto. 
      - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
      - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
      - des. force. exists x. steps. eapply IH; eauto.
      - steps. destruct run. steps. eapply IH; eauto.
      - steps. destruct run. steps. eapply IH; eauto.
      - eapply simg_progress_flag. gbase. eapply CIH. left. econs; eauto.
    }
    { destruct H. ides itr.
    { steps. }
    { steps. eapply simg_progress_flag. gbase. eapply CIH. right. econs; et. }
    rewrite <- ! bind_trigger. destruct e.
    { resub. destruct c. hexploit (fnsems_find_iff fn0). i. des.
      {  steps.  rewrite NONE. unfold unwrapU, triggerUB. step. ss. }
      { 
        (* admit. *)
        inv SIM. steps. (* Why no tau? *)
        rewrite <- SRC. rewrite <- TGT. s.
        unfold ModSem.add_fnsems.
        rewrite ! alist_find_app_o. unfold ModSem.trans_l, ModSem.trans_r.
        rewrite ! alist_find_map. rewrite CTX0. s. 
        rewrite SRC, TGT.
        ired_both. eapply simg_progress_flag.
        guclo bindC_spec. econs.
        { gbase. eapply CIH. right. econs; et. econs; et.  }
        { i. ss. destruct vret_src, vret_tgt;et. des; clarify.
            steps. gbase. eapply CIH. right. econs; et. }
      }
      { inv SIM. hexploit (SIM0 args args); et. i. des.
        steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
        eapply simg_progress_flag.
        guclo bindC_spec. econs.
        { gbase. eapply CIH. left. econs; ss. et. }
        { i. ss. destruct vret_src, vret_tgt. des; clarify.
          steps. gbase. eapply CIH. right. econs; et.
          inv SIM. econs.
          { etrans; et. }
          { et. }
        }
      }
    }
    destruct s.
    { resub. destruct s.
      steps. grind. steps. eapply simg_progress_flag.
      gbase. eapply CIH. right.
      inv SIM.
        replace (st_tgt mn') with (st_src mn'); et.
        { econs; et. }
        { inv SIM. et. }
      
    }
    { resub. destruct e.
      { steps. force. exists x. steps. eapply simg_progress_flag.
        gbase. eapply CIH; et. right. econs; et.
      }
      { steps. force. exists x. steps. eapply simg_progress_flag.
        gbase. eapply CIH; et. right. econs; et.
      }
      { steps. subst. eapply simg_progress_flag.
        gbase. eapply CIH; et. right. econs; et. }
    }
  }
  Qed.
  (* Admitted. *)
  Context `{CONF: EMSConfig}.
  Hypothesis INIT:
    exists w, g_lift_rel w (ModSem.init_st ms_src) (ModSem.init_st ms_tgt).
  Lemma adequacy_local_aux (P Q: Prop)
        (* (wf: world -> W -> Prop)  *)
        (WF: Q -> P)
    :
      (Beh.of_program (ModSem.compile ms_tgt (Some P)))
      <1=
      (Beh.of_program (ModSem.compile ms_src (Some Q))).
  Proof. 
    eapply adequacy_global_itree; ss.
    hexploit INIT. i. 
    des. ginit.
    { eapply cpn7_wcompat; eauto with paco. }
    unfold ModSem.initial_itr, assume. generalize "main" as fn. i.
    hexploit (fnsems_find_iff fn). i. des.
    { steps. unshelve esplits; et. unfold ITree.map, unwrapU, triggerUB. steps.
      rewrite NONE. steps. ss. }
    (* { admit. } *)
    { 
      inv H. rewrite <- SRC, <- TGT in *.
      hexploit (SIM (initial_arg) (initial_arg)) ; et; cycle 1. i. des.
      steps. force. esplits; et.
      steps. unfold ITree.map, unwrapU.
      rewrite ! interp_Es_bind. rewrite ! bind_bind.
       s. unfold ModSem.add_fnsems.
      rewrite ! alist_find_app_o. unfold ModSem.trans_l.
      rewrite ! alist_find_map. rewrite CTX.
      steps. rewrite SRC, TGT.
      guclo bindC_spec. econs.
      { eapply simg_flag_down. gfinal. right. eapply sim_lift. econs; et. }
      { i. destruct vret_src, vret_tgt. des; clarify. steps. }
    }
    { 
      inv H. 
      hexploit (SIM (initial_arg) (initial_arg)) ; et; cycle 1. i. des.
      steps. force. esplits; et.
      steps. unfold ITree.map, unwrapU.
      rewrite ! interp_Es_bind. rewrite ! bind_bind.
      rewrite SRC. rewrite TGT. steps. guclo bindC_spec. econs.
      { eapply simg_flag_down. gfinal. right. eapply sim_lift. econs; et. }
      { i. destruct vret_src, vret_tgt. des; clarify. steps. }
    }
    
  (* Admitted. *)
  Qed.
  Definition wf_lift wf :=
    fun (w:world) => 
    (fun '(src, tgt) =>
      match (Any.split src), (Any.split tgt) with
      | Some (l1, r1), Some (l2, r2) => l1 = l2 /\ wf w (r1, r2)
      | _, _ => wf w (src, tgt)
      end
    ).
End SEMPAIR.


