Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export ModSemE.
Require Export AList.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.

Set Implicit Arguments.


Class EMSConfig := { finalize: Any.t -> option Any.t; initial_arg: Any.t }.



Module ModSem.
Section MODSEM.

  Record t: Type := mk {
    state : Type;
    init_st : state;
    fnsems : gname -> option (Any.t -> itree (Es state) Any.t)
  }
  .

  Program Definition wrap_fun {E} `{eventE -< E} A R 
        (f: ktree E A R):
    ktree E Any.t Any.t :=
    fun arg =>
      arg <- unwrapU (arg↓);;
      ret <- (f arg);; Ret ret↑
  .

  Fixpoint get_fnsems {E} `{eventE -< E}
          (fnsems: list (gname * (ktree E Any.t Any.t)))
          (fn: gname):
    option (ktree E Any.t Any.t) :=
    match fnsems with
    | [] => None
    | (fn_hd, body_hd)::tl =>
        if string_dec fn fn_hd then Some body_hd else get_fnsems tl fn
    end.


Section INTERP.

  Variable ms: t.

  Definition prog: callE ~> itree (Es (state ms)) :=
    fun _ '(Call fn args) =>
      sem <- (fnsems ms fn)?;;
      rv <- (sem args);;
      Ret rv
  .  

  Context `{CONF: EMSConfig}.

  Definition initial_itr (P: option Prop): itree eventE Any.t :=
    match P with
    | None => Ret tt
    | Some P' => assume (<<WF: P'>>)
    end;;; 
    snd <$> interp_Es prog (prog (Call "main" initial_arg)) (init_st ms).

  Let state: Type := itree eventE Any.t.

  Definition state_sort (st0: state): sort :=
    match (observe st0) with
    | TauF _ => demonic
    | RetF rv =>
      match (finalize rv) with
      | Some rv => final rv
      | _ => angelic
      end
    | VisF (Choose X) k => demonic
    | VisF (Take X) k => angelic
    | VisF (Syscall fn args rvs) k => vis
    end
  .

  Inductive step: state -> option event -> state -> Prop :=
  | step_tau
      itr
    :
      step (Tau itr) None itr
  | step_choose
      X k (x: X)
    :
      step (Vis (subevent _ (Choose X)) k) None (k x)
  | step_take
      X k (x: X)
    :
      step (Vis (subevent _ (Take X)) k) None (k x)
  | step_syscall
      fn args rv (rvs: Any.t -> Prop) k
      (SYSCALL: syscall_sem (event_sys fn args rv))
      (RETURN: rvs rv)
    :
      step (Vis (subevent _ (Syscall fn args rvs)) k) (Some (event_sys fn args rv)) (k rv)
  .

  Lemma step_trigger_choose_iff X k itr e
        (STEP: step (trigger (Choose X) >>= k) e itr)
    :
      exists x,
        e = None /\ itr = k x.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et.  }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
  Qed.

  Lemma step_trigger_take_iff X k itr e
        (STEP: step (trigger (Take X) >>= k) e itr)
    :
      exists x,
        e = None /\ itr = k x.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et.  }
    { eapply f_equal with (f:=observe) in H0. ss. }
  Qed.

  Lemma step_tau_iff itr0 itr1 e
        (STEP: step (Tau itr0) e itr1)
    :
      e = None /\ itr0 = itr1.
  Proof.
    inv STEP. et.
  Qed.

  Lemma step_ret_iff rv itr e
        (STEP: step (Ret rv) e itr)
    :
      False.
  Proof.
    inv STEP.
  Qed.

  Lemma step_trigger_syscall_iff fn args rvs k e itr
        (STEP: step (trigger (Syscall fn args rvs) >>= k) e itr)
    :
      exists rv, itr = k rv /\ e = Some (event_sys fn args rv)
                 /\ <<RV: rvs rv>> /\ <<SYS: syscall_sem (event_sys fn args rv)>>.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et. }
  Qed.


  Let itree_eta E R (itr0 itr1: itree E R)
      (OBSERVE: observe itr0 = observe itr1)
    :
      itr0 = itr1.
  Proof.
    rewrite (itree_eta_ itr0).
    rewrite (itree_eta_ itr1).
    rewrite OBSERVE. auto.
  Qed.

  Lemma step_trigger_choose X k x
    :
      step (trigger (Choose X) >>= k) None (k x).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Choose X) k)
    end; ss.
    { econs. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.

  Lemma step_trigger_take X k x
    :
      step (trigger (Take X) >>= k) None (k x).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Take X) k)
    end; ss.
    { econs. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.

  Lemma step_trigger_syscall fn args (rvs: Any.t -> Prop) k rv
        (RV: rvs rv) (SYS: syscall_sem (event_sys fn args rv))
    :
      step (trigger (Syscall fn args rvs) >>= k) (Some (event_sys fn args rv)) (k rv).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Syscall fn args rvs) k)
    end; ss.
    { econs; et. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.


  Program Definition compile_itree: itree eventE Any.t -> semantics :=
    fun itr =>
      {|
        STS.state := state;
        STS.step := step;
        STS.initial_state := itr;
        STS.state_sort := state_sort;
      |}
  .
  Next Obligation. inv STEP; inv STEP0; ss. csc. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.

  Definition compile P: semantics:=
    compile_itree (initial_itr P).

  Lemma initial_itr_not_wf P
        (WF: ~ P)
        tr
    :
      Beh.of_program (compile_itree (initial_itr (Some P))) tr.
  Proof.
    eapply Beh.ub_top. pfold. econsr; ss; et. rr. ii; ss.
    unfold initial_itr, assume in *. rewrite bind_bind in STEP.
    eapply step_trigger_take_iff in STEP. des. subst. ss.
  Qed.

  Lemma compile_not_wf P
        (WF: ~ P)
        tr
    :
      Beh.of_program (compile (Some P)) tr.
  Proof.
    eapply initial_itr_not_wf; et.
  Qed.

End INTERP.

(* Lemma itr_snd
        (S0 S1 A: Type)
        (st0: S0) (st1: S1) (a: A)
        (itr0: itree eventE (S0 * A)) (itr1: itree eventE (S1 * A)) 
        (I0: itr0 = Ret (st0, a))
        (I1: itr1 = Ret (st1, a))
:
  snd <$> itr0 = snd <$> itr1
.
Proof. 
  simpl. rewrite I0, I1. unfold ITree.map. rewrite bind_ret_l. rewrite bind_ret_l. et.
Qed. *)


(* Lemma interp_Es_vis
T R st p (st0: st)
(* (e: Es Σ) *)
(c: callE T) (k: T -> itree (Es st) R)
:
interp_Es p (Vis (c|)%sum k) st0 = tau;; (interp_Es p (ITree.bind (p _ c) k) st0) 
.
Proof. 
unfold interp_Es, interp_sE.
rewrite interp_mrec_bind. grind.
Admitted.  *)

(* f_equal. 

Check interp_mrec_trigger.
change (` x : T <- ITree.trigger (c|)%sum;; k x) with (ITree.bind (ITree.trigger ((c|)%sum)) k).
grind. Qed. *)


(* 
Context {CONF: EMSConfig}.

Let add_comm_aux
    ms0 ms1 stl0 str0
    P
    (SIM: stl0 = str0)
  :
    <<COMM: Beh.of_state (compile (add ms0 ms1) P) stl0
            <1=
            Beh.of_state (compile (add ms1 ms0) P) str0>>
.
Proof.
  subst. revert str0. pcofix CIH. i. pfold.
  punfold PR. induction PR using Beh.of_state_ind; ss.
  - econs 1; et.
  - econs 2; et.
    clear CIH. clear_tac. revert st0 H.
    pcofix CIH. i. punfold H0. pfold.
    inv H0.
    + econs 1; eauto. ii. ss. exploit STEP; et. i; des. right. eapply CIH; et. pclearbot. ss.
    + econs 2; eauto. des. esplits; eauto. right. eapply CIH; et. pclearbot. ss.
  - econs 4; et. pclearbot. right. eapply CIH; et.
  - econs 5; et. rr in STEP. des. rr. esplits; et.
  - econs 6; et. ii. exploit STEP; et. i; des. clarify.
Qed. *)

(* Theorem add_comm
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
  ii. ss. r in PR. r. eapply add_comm_aux. et.
  rp; et. clear PR. ss. cbn. unfold initial_itr. f_equal.
  
  extensionality u. destruct u.
  apply bisimulation_is_eq. generalize "main" as fn.
  ginit. gcofix CIH.
  simpl. unfold ITree.map. repeat (rewrite interp_Es_bind; rewrite bind_bind).  
  unfold unwrapU. unfold add_fnsems. i.
  destruct (fnsems ms0 fn); cycle 1.
  {
    destruct (fnsems ms1 fn); cycle 1.
    - rewrite ! interp_Es_bind. rewrite ! interp_Es_triggerUB.
      gstep. unfold triggerUB. grind. 
      rewrite ! bind_trigger; s.
      econs. i. destruct v.  
    - rewrite ! interp_Es_bind. rewrite ! interp_Es_ret. rewrite ! bind_ret_l.
      rewrite ! interp_Es_bind. grind.
      generalize (i initial_arg).
      gcofix CIH'. i.
      rewrite (itree_eta_ i0). 
      destruct (observe i0).
      + rewrite (bisimulation_is_eq _ _ (translate_ret (emb_l ms1 ms0) r0)).
        rewrite (bisimulation_is_eq _ _ (translate_ret (emb_r ms0 ms1) r0)).
        rewrite ! interp_Es_ret. rewrite ! bind_ret_l.
        rewrite ! interp_Es_ret. rewrite ! bind_ret_l.
        gstep. econs. et.

      + 
        rewrite (bisimulation_is_eq _ _ (translate_tau (emb_l ms1 ms0) t0)).
        rewrite (bisimulation_is_eq _ _ (translate_tau (emb_r ms0 ms1) t0)).
        rewrite ! interp_Es_tau. rewrite ! bind_tau.
        gstep. econs. gfinal. left. apply CIH'.
      + rewrite (bisimulation_is_eq _ _ (translate_vis (emb_l ms1 ms0) _ e k)).
        rewrite (bisimulation_is_eq _ _ (translate_vis (emb_r ms0 ms1) _ e k)).
        destruct e.
        * unfold emb_l, emb_r, lmap. clear CIH'.
          rewrite ! interp_Es_vis. destruct c.
          gstep. grind. econs. gupaco.
          apply eqit_clo_bind; et. Print eqit_bind_clo.
          econs.
          { admit. }
          { admit. }
        * admit.

       
          (* right. 
          apply CIH.

          eassert (Y := (interp_Es_callE _ _ c)).
          unfold trigger in Y.
          rewrite interp_Es_bind in Y.
          unfold subevent in Y. unfold resum, ReSum_inl, ">>>" in Y. 
          unfold emb_l, lmap. unfold Cat_IFun, inl_, Inl_sum1, resum, ReSum_id, id_, Id_IFun in Y.
          rewrite Y.
          Print Subevent.vis. Check subevent.
          rewrite Y.
        rewrite (interp_Es_callE _ _ c) (emb_l ms1 ms0 (c|)%sum)). *)

    }
    {
      admit.
    }
Admitted. *)

  (* revert ms0 ms1. pcofix CIH. i.
  pfold.

  





  simpl. unfold ITree.map. repeat (rewrite interp_Es_bind; rewrite bind_bind).
  unfold unwrapU. unfold add_fnsems.
  
  
  
Qed. *)

End MODSEM.
End ModSem.


Module Mod.
Section MOD.
  Context `{Sk.ld}.

  Record t: Type := mk {
    get_modsem: Sk.t -> ModSem.t;
    sk: Sk.t;
    enclose: ModSem.t := (get_modsem (Sk.canon sk));

  }
  .
  Definition wf (md: t): Prop := <<SK: Sk.wf (md.(sk))>>.

  Definition empty: t := {|
    get_modsem := fun _ => ModSem.mk tt↑ (fun _ => None);
    sk := Sk.unit;
  |}.

End MOD.
End Mod.




Section EVENTSCOMMON.

(*** casting call, fun ***)
(* Definition ccallN {X Y} (fn: gname) (varg: X): itree Es Y := vret <- trigger (Call fn varg↑);; vret <- vret↓ǃ;; Ret vret. *)
(* Definition ccallU {X Y} (fn: gname) (varg: X): itree Es Y := vret <- trigger (Call fn varg↑);; vret <- vret↓?;; Ret vret. *)
(* Definition cfunN {X Y} (body: X -> itree Es Y): Any.t -> itree Es Any.t := *)
(*   fun varg => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑. *)
(* Definition cfunU {X Y} (body: X -> itree Es Y): Any.t -> itree Es Any.t := *)
(*   fun varg => varg <- varg↓?;; vret <- body varg;; Ret vret↑. *)

  (* Definition ccall {X Y} (fn: gname) (varg: X): itree Es Y := vret <- trigger (Call fn varg↑);; vret <- vret↓ǃ;; Ret vret. *)
  (* Definition cfun {X Y} (body: X -> itree Es Y): Any.t -> itree Es Any.t := *)
  (*   fun varg => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑. *)
  Context `{HasCallE: callE -< E}.
  Context `{HasEventE: eventE -< E}.

  Definition ccallN {X Y} (fn: gname) (varg: X): itree E Y := vret <- trigger (Call fn varg↑);; vret <- vret↓ǃ;; Ret vret.
  Definition ccallU {X Y} (fn: gname) (varg: X): itree E Y := vret <- trigger (Call fn varg↑);; vret <- vret↓?;; Ret vret.

  Definition cfunN {X Y} (body: X -> itree E Y): Any.t-> itree E Any.t :=
    fun varg => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑.
  Definition cfunU {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun varg => varg <- varg↓?;; vret <- body varg;; Ret vret↑.

End EVENTSCOMMON.

 


(* 


Module Equisatisfiability.
  Inductive pred: Type :=
  | true
  | false
  | meta (P: Prop)

  | disj: pred -> pred -> pred
  | conj: pred -> pred -> pred
  | neg: pred -> pred
  | impl: pred -> pred -> pred

  | univ (X: Type): (X -> pred) -> pred
  | exst (X: Type): (X -> pred) -> pred
  .

  (*** https://en.wikipedia.org/wiki/Negation_normal_form ***)
  Fixpoint embed (p: pred): itree eventE unit :=
    match p with
    | true => triggerUB
    | false => triggerNB
    | meta P => guarantee P

    | disj p0 p1 => b <- trigger (Choose _);; if (b: bool) then embed p0 else embed p1
    | conj p0 p1 => b <- trigger (Take _);; if (b: bool) then embed p0 else embed p1
    | neg p =>
      match p with
      | meta P => assume P
      | _ => triggerNB (*** we are assuming negation normal form ***)
      end
    | impl _ _ => triggerNB (*** we are assuming negation normal form ***)

    | @univ X k => x <- trigger (Take X);; embed (k x)
    | @exst X k => x <- trigger (Choose X);; embed (k x)
    end
  .

  (*** TODO: implication --> function call? ***)
  (***
P -> Q
~=
pname :=
  embed P

pqname :=
  (call pname) (finite times);;
  embed Q




(P -> Q) -> R
~=
pname :=
  embed P

pqname :=
  (call pname) (finite times);;
  embed Q

pqrname :=
  (call pqname) (finite times);;
  embed R
   ***)

  (* Fixpoint embed (p: pred) (is_pos: bool): itree eventE unit := *)
  (*   match p with *)
  (*   | true => triggerUB *)
  (*   | false => triggerNB *)
  (*   | meta P => guarantee P *)
  (*   | disj p0 p1 => b <- trigger (Choose _);; if (b: bool) then embed p0 is_pos else embed p1 is_pos *)
  (*   | conj p0 p1 => b <- trigger (Take _);; if (b: bool) then embed p0 is_pos else embed p1 is_pos *)
  (*   | @univ X k => x <- trigger (Take X);; embed (k x) is_pos *)
  (*   | @exst X k => x <- trigger (Choose X);; embed (k x) is_pos *)
  (*   | _ => triggerNB *)
  (*   end *)
  (* . *)
End Equisatisfiability. *)



Global Existing Instance Sk.gdefs.
Arguments Sk.unit: simpl never.
Arguments Sk.add: simpl never.
Arguments Sk.wf: simpl never.
Coercion Sk.load_skenv: Sk.t >-> SkEnv.t.
Global Opaque Sk.load_skenv.
(* Variable st: Type. *)

(*** TODO: Move to ModSem.v ***)
Lemma interp_Es_unwrapU
      S prog R (st0: S) (r: option R)
  :
    interp_Es prog (unwrapU r) st0 = r <- unwrapU r;; Ret (st0, r)
.
Proof.
  unfold unwrapU. des_ifs.
  - rewrite interp_Es_ret. grind.
  - rewrite interp_Es_triggerUB. unfold triggerUB. grind.
Qed.

Lemma interp_Es_unwrapN
      S prog R (st0: S) (r: option R)
  :
    interp_Es prog (unwrapN r) st0 = r <- unwrapN r;; Ret (st0, r)
.
Proof.
  unfold unwrapN. des_ifs.
  - rewrite interp_Es_ret. grind.
  - rewrite interp_Es_triggerNB. unfold triggerNB. grind.
Qed.

Lemma interp_Es_assume
      S prog (st0: S) (P: Prop)
  :
    interp_Es prog (assume P) st0 = assume P;;; tau;; tau;; Ret (st0, tt)
.
Proof.
  unfold assume.
  repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
  rewrite interp_Es_eventE.
  repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
  rewrite interp_Es_ret.
  refl.
Qed.

Lemma interp_Es_guarantee
      S prog (st0: S) (P: Prop)
  :
    interp_Es prog (guarantee P) st0 = guarantee P;;; tau;; tau;; Ret (st0, tt)
.
Proof.
  unfold guarantee.
  repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
  rewrite interp_Es_eventE.
  repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
  rewrite interp_Es_ret.
  refl.
Qed.





Require Import Red IRed.
Section AUX.
  Lemma interp_Es_ext
        S prog R (itr0 itr1: itree _ R) (st0: S)
    :
      itr0 = itr1 -> interp_Es prog itr0 st0 = interp_Es prog itr1 st0
  .
  Proof. i; subst; refl. Qed.

  Global Program Instance interp_Es_rdb: red_database (mk_box (@interp_Es)) :=
    mk_rdb
      1
      (mk_box interp_Es_bind)
      (mk_box interp_Es_tau)
      (mk_box interp_Es_ret)
      (mk_box interp_Es_sE)
      (mk_box interp_Es_sE)
      (mk_box interp_Es_callE)
      (mk_box interp_Es_eventE)
      (mk_box interp_Es_triggerUB)
      (mk_box interp_Es_triggerNB)
      (mk_box interp_Es_unwrapU)
      (mk_box interp_Es_unwrapN)
      (mk_box interp_Es_assume)
      (mk_box interp_Es_guarantee)
      (mk_box interp_Es_ext)
  .

End AUX.
