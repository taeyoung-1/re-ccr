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
    init_st : Any.t;
    (* fnsems : gname -> option (Any.t -> itree Es Any.t) *)
    fnsems : alist gname (Any.t -> itree Es Any.t);
  }
  .

  Record wf (ms: t): Prop := mk_wf {
    wf_fnsems: NoDup (List.map fst ms.(fnsems));
  }
  .

  Definition empty: t := {|
    init_st := tt↑;
    fnsems := [];
  |}.

  Program Definition wrap_fun {E} `{eventE -< E} A R 
        (f: ktree E A R):
    ktree E Any.t Any.t :=
    fun arg =>
          arg <- unwrapU (arg↓);;
          ret <- (f arg);; Ret (ret↑)
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

Section ADD.
  Variable M1 M2 : t.

  Definition run_l {V} (run: Any.t -> Any.t * V): Any.t -> Any.t * V :=
    fun st => 
      match Any.split st with
      | Some (a, b) => let (a', v) := run a in (Any.pair a' b, v)
      | None => run tt↑
      end.
 
  Definition run_r {V} (run: Any.t -> Any.t * V): Any.t -> Any.t * V :=
    fun st => 
      match Any.split st with
      | Some (a, b) => let (b', v) := run b in (Any.pair a b', v)
      | None => run tt↑
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

  Definition trans_l '(fn, f): gname * (Any.t -> itree _ Any.t) :=
    (fn, (fun args => translate emb_l (f args))).

  Definition trans_r '(fn, f) : gname * (Any.t -> itree _ Any.t) :=
    (fn, (fun args => translate emb_r (f args))).

  Definition add_fnsems : alist gname (Any.t -> itree _ Any.t) :=
    (List.map trans_l M1.(fnsems)) ++ (List.map trans_r M2.(fnsems)).

  Definition add : t :=
  {|
    init_st := Any.pair (init_st M1) (init_st M2);
    fnsems := add_fnsems;
  |}.

End ADD.


Section INTERP.

  Variable ms: t.

  Definition prog: callE ~> itree Es :=
    fun _ '(Call fn args) =>
      sem <- (alist_find fn ms.(fnsems))?;;
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

End MODSEM.
End ModSem.


Module Mod.
Section MOD.
  Context `{Sk.ld}.
  Context {CONF: EMSConfig}.
  

  Record t: Type := mk {
    get_modsem: Sk.t -> ModSem.t;
    sk: Sk.t;
    enclose: ModSem.t := (get_modsem (Sk.canon sk));

  }
  .
  Definition wf (md: t): Prop := (<<WF: ModSem.wf md.(enclose)>> /\ <<SK: Sk.wf (md.(sk))>>).

  Definition empty: t := {|
    get_modsem := fun _ => ModSem.mk tt↑ [];
    sk := Sk.unit;
  |}.

  Definition compile (md: t): semantics :=
    ModSem.compile_itree (ModSem.initial_itr md.(enclose) (Some (wf md))).  

  Section ADD.
   Definition add (md0 md1: t): t := {|
    get_modsem := fun sk =>
                    ModSem.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
    sk := Sk.add md0.(sk) md1.(sk);
  |}
  .

  Fixpoint add_list (xs: list t): t :=
    match xs with
    | [] => empty
    | x::l => add x (add_list l)
    end.

  End ADD.
    
End MOD.
End Mod.

Section REFINE.
  Context `{Sk.ld}.

  (* Contexts are now simplified as a single module *)

  Definition refines {CONF: EMSConfig} (md_tgt md_src: Mod.t): Prop :=
    (* forall (ctx: Mod.t), Beh.of_program (ModL.compile (add_list (md_tgt :: ctx))) <1= *)
    (*                           Beh.of_program (ModL.compile (add_list (md_src :: ctx))) *)
    forall (ctx: Mod.t), Beh.of_program (Mod.compile (Mod.add ctx md_tgt)) <1=
                              Beh.of_program (Mod.compile (Mod.add ctx md_src))
  .
  Definition refines_strong (md_tgt md_src: Mod.t): Prop :=
    forall {CONF: EMSConfig}, refines md_tgt md_src.
    
Section CONF.
  Context {CONF: EMSConfig}.

  Definition refines_closed (md_tgt md_src: Mod.t): Prop :=
    Beh.of_program (Mod.compile md_tgt) <1= Beh.of_program (Mod.compile md_src)
  .

  (* Definition refines2 (md_tgt md_src: list Mod.t): Prop :=
    forall (ctx: Mod.t), Beh.of_program (Mod.compile (Mod.add ctx (Mod.add_list md_tgt))) <1=
                              Beh.of_program (Mod.compile (Mod.add ctx (Mod.add_list md_src)))
  . *)
End CONF.

End REFINE.





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

  Definition ccallN {X Y} (fn: gname) (varg: X): itree E Y := 
    vret <- trigger (Call fn (varg↑));; 
    vret <- vret↓ǃ;; Ret vret
    .
  Definition ccallU {X Y} (fn: gname) (varg: X): itree E Y := 
    vret <- trigger (Call fn (varg↑));;
    vret <- vret↓?;; Ret vret
    .

  Definition cfunN {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun varg => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑.
  Definition cfunU {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun varg => varg <- varg↓?;; vret <- body varg;; Ret vret↑. 

End EVENTSCOMMON.

 


Global Existing Instance Sk.gdefs.
Arguments Sk.unit: simpl never.
Arguments Sk.add: simpl never.
Arguments Sk.wf: simpl never.
Coercion Sk.load_skenv: Sk.t >-> SkEnv.t.
Global Opaque Sk.load_skenv.
(* Variable st: Type. *)

(*** TODO: Move to ModSem.v ***)
Lemma interp_Es_unwrapU
      prog R st0 (r: option R)
  :
    interp_Es prog (unwrapU r) st0 = r <- unwrapU r;; Ret (st0, r)
.
Proof.
  unfold unwrapU. des_ifs.
  - rewrite interp_Es_ret. grind.
  - rewrite interp_Es_triggerUB. unfold triggerUB. grind.
Qed.

Lemma interp_Es_unwrapN
      prog R st0 (r: option R)
  :
    interp_Es prog (unwrapN r) st0 = r <- unwrapN r;; Ret (st0, r)
.
Proof.
  unfold unwrapN. des_ifs.
  - rewrite interp_Es_ret. grind.
  - rewrite interp_Es_triggerNB. unfold triggerNB. grind.
Qed.

Lemma interp_Es_assume
      prog st0 (P: Prop)
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
      prog st0 (P: Prop)
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
        prog R (itr0 itr1: itree _ R) st0
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

