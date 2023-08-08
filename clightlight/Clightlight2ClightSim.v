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

Require Import Clightlight2ClightMatch.
Require Import Clightlight2ClightArith.
Require Import Clightlight2ClightGenv.
Require Import Clightlight2ClightLenv.
Require Import Clightlight2ClightMem.

From compcert Require Import Ctypes Clight Clightdefs.

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

Section PROOF.

  Import ModSemL.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Definition compile_val md := @ModL.compile _ EMSConfigC md. 

  Let _sim_mon := Eval simpl in (fun (src: ModL.t) (tgt: Clight.program) => @sim_mon (compile_val src) (Clight.semantics2 tgt)).
  Hint Resolve _sim_mon: paco.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); pfold; econs 3; ss; clarify; eexists; exists (step_tau _); left.
  (* Ltac sim_ord := guclo _ordC_spec; econs. *)

  Definition arrow (A B: Prop): Prop := A -> B.
  Opaque arrow.

  Definition oeq [A] (a: A) b: Prop := (a = b).
  Opaque oeq. 

  Ltac to_oeq :=
    match goal with
| |- ?A = ?B => change (oeq A B)
    end.

  Ltac from_oeq :=
    match goal with
    | |- oeq ?A ?B => change (A = B)
    end.

  Ltac sim_redE :=
    to_oeq; cbn; repeat (Red.prw ltac:(_red_gen) 1 0); repeat (Red.prw ltac:(_red_gen) 2 0); from_oeq.

  Ltac to_arrow :=
    match goal with
| |- ?A -> ?B => change (arrow A B)
    end.

  Ltac from_arrow :=
    match goal with
    | |- arrow ?A ?B => change (A -> B)
    end.
  Ltac sim_redH H :=
    revert H; to_arrow; (repeat (cbn; Red.prw ltac:(_red_gen) 2 2 0)); from_arrow; intros H.

  Ltac solve_ub := des; irw in H; dependent destruction H; clarify.
  Ltac sim_triggerUB := 
    (try rename H into HH); ss; unfold triggerUB; try sim_red; pfold; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  Ltac tgt_step := pfold; econs 4; eexists; eexists; [|left].

  Ltac wrap_up := pfold; econs 7; et; right.

  Ltac dtm H H0 := eapply angelic_step in H; eapply angelic_step in H0; des; rewrite H; rewrite H0; ss.

(* 
  Fixpoint expr_ord (e: Imp.expr): Ord.t :=
    match e with
    | Imp.Var _ => 20
    | Imp.Lit _ => 20
    | Imp.Eq e0 e1 => (20 + expr_ord e1 + 20 + expr_ord e0 + 20)%ord
    | Imp.Lt e0 e1 => (20 + expr_ord e1 + 20 + expr_ord e0 + 20)%ord
    | Imp.Plus e0 e1 => (20 + expr_ord e1 + 20 + expr_ord e0 + 20)%ord
    | Imp.Minus e0 e1 => (20 + expr_ord e1 + 20 + expr_ord e0 + 20)%ord
    | Imp.Mult e0 e1 => (20 + expr_ord e1 + 20 + expr_ord e0 + 20)%ord
    end.

  Lemma expr_ord_omega e:
    (expr_ord e < Ord.omega)%ord.
  Proof.
    assert (exists n: nat, (expr_ord e <= n)%ord).
    { induction e; ss.
      { eexists. refl. }
      { eexists. refl. }
      { des. eexists.
        rewrite IHe1. rewrite IHe2.
        rewrite <- ! OrdArith.add_from_nat. refl. }
      { des. eexists.
        rewrite IHe1. rewrite IHe2.
        rewrite <- ! OrdArith.add_from_nat. refl. }
      { des. eexists.
        rewrite IHe1. rewrite IHe2.
        rewrite <- ! OrdArith.add_from_nat. refl. }
      { des. eexists.
        rewrite IHe1. rewrite IHe2.
        rewrite <- ! OrdArith.add_from_nat. refl. }
      { des. eexists.
        rewrite IHe1. rewrite IHe2.
        rewrite <- ! OrdArith.add_from_nat. refl. }
    }
    des. eapply Ord.le_lt_lt; et. eapply Ord.omega_upperbound.
  Qed.

  Definition max_fuel := (Ord.omega * Ord.omega)%ord.

  Lemma max_fuel_spec2 e0 e1 (n: Ord.t) :
    (100 + expr_ord e0 + expr_ord e1 <= 100 + max_fuel + n)%ord.
  Proof.
    rewrite ! OrdArith.add_assoc. eapply OrdArith.le_add_r.
    etrans.
    2: { eapply OrdArith.add_base_l. }
    unfold max_fuel. etrans.
    2: {
      eapply OrdArith.le_mult_r.
      eapply Ord.lt_le. eapply Ord.omega_upperbound.
    }
    instantiate (1:=2). rewrite Ord.from_nat_S. rewrite Ord.from_nat_S.
    rewrite OrdArith.mult_S. rewrite OrdArith.mult_S.
    etrans.
    2:{ rewrite OrdArith.add_assoc. eapply OrdArith.add_base_r. }
    etrans.
    { eapply OrdArith.le_add_l. eapply Ord.lt_le. eapply expr_ord_omega. }
    { eapply OrdArith.le_add_r. eapply Ord.lt_le. eapply expr_ord_omega. }
  Qed.

  Lemma max_fuel_spec2' e0 e1 (n: Ord.t) :
    (100 + expr_ord e0 + expr_ord e1 <= (100 + max_fuel) + 100 + Ord.omega + n)%ord.
  Proof.
    set (temp:=(100 + expr_ord e0 + expr_ord e1)%ord).
    do 2 rewrite OrdArith.add_assoc.
    subst temp. eapply max_fuel_spec2.
  Qed.

  Lemma max_fuel_spec1 e (n: Ord.t) :
    (100 + expr_ord e <= 100 + max_fuel + n)%ord.
  Proof.
    etrans.
    2: { eapply max_fuel_spec2. }
    eapply OrdArith.add_base_l.
    Unshelve. all: exact e.
  Qed.

  Lemma max_fuel_spec1' e (n: Ord.t) :
    (100 + expr_ord e <= (100 + max_fuel) + 100 + Ord.omega + n)%ord.
  Proof.
    do 2 (rewrite OrdArith.add_assoc). eapply max_fuel_spec1.
  Qed.

  Lemma max_fuel_spec3 (args: list Imp.expr) (n: Ord.t) :
    (100 + Ord.omega * Datatypes.length args <= 100 + max_fuel + n)%ord.
  Proof.
    rewrite ! OrdArith.add_assoc. eapply OrdArith.le_add_r.
    etrans.
    2: { eapply OrdArith.add_base_l. }
    unfold max_fuel. eapply OrdArith.le_mult_r.
    eapply Ord.lt_le. eapply Ord.omega_upperbound.
  Qed.

  Lemma max_fuel_spec3' (args: list Imp.expr) (n: Ord.t) :
    (100 + Ord.omega * Datatypes.length args <= (100 + max_fuel) + 100 + Ord.omega + n)%ord.
  Proof.
    do 2 (rewrite OrdArith.add_assoc). eapply max_fuel_spec3.
  Qed.

  Lemma max_fuel_spec4 e (args: list Imp.expr) (n: Ord.t) :
    ((100 + Ord.omega * Datatypes.length args) + 100 + (expr_ord e) <= (100 + max_fuel) + 100 + Ord.omega + n)%ord.
  Proof.
    rewrite ! OrdArith.add_assoc.
    etrans.
    2:{ repeat rewrite <- OrdArith.add_assoc. eapply OrdArith.add_base_l. }
    etrans.
    2:{ instantiate (1:= (100 + (Ord.omega * Datatypes.length args) + (100 + Ord.omega))%ord).
        rewrite <- OrdArith.add_assoc. do 2 eapply OrdArith.le_add_l.
        eapply OrdArith.le_add_r. unfold max_fuel.
        eapply OrdArith.le_mult_r. eapply Ord.lt_le. eapply Ord.omega_upperbound.
    }
    rewrite ! OrdArith.add_assoc.
    do 3 eapply OrdArith.le_add_r. eapply Ord.lt_le. eapply expr_ord_omega.
  Qed.

  Lemma max_fuel_spec4' (args: list Imp.expr) (n: Ord.t) :
    (100 + Ord.omega * Datatypes.length args <= 100 + Ord.omega * Datatypes.length args + n)%ord.
  Proof.
    apply OrdArith.add_base_l.
  Qed.
 *)



(* 
TODO: update expression simulation 
 *)

  (* Lemma step_expr
        (src: ModL.t) (tgt: Csharpminor.program)
        e te
        tcode tf tcont tge tle tm
        r rg ms mn ge le pstate ktr
        i1
        (MLE: match_le srcprog le tle)
        (CEXP: compile_expr e = te)
        (SIM:
           forall rv trv,
             eval_expr tge empty_env tle tm te trv ->
             trv = map_val srcprog rv ->
             gpaco3 (_sim (compile_val src) (semantics tgt))
                    (cpn3 (_sim (compile_val src) (semantics tgt))) rg rg i1
                    (ktr (pstate, (le, rv)))
                    (State tf tcode tcont empty_env tle tm))
    :
      gpaco3 (_sim (compile_val src) (semantics tgt))
             (cpn3 (_sim (compile_val src) (semantics tgt)))
             r rg (i1 + expr_ord e)%ord
             (r0 <- EventsL.interp_Es (prog ms) (transl_all mn (interp_imp ge (denote_expr e) le)) (pstate);; ktr r0)
             (State tf tcode tcont empty_env tle tm).
  Proof.
    generalize dependent ktr. generalize dependent te.
    move MLE before pstate. revert_until MLE. revert r rg.
    generalize dependent e. Local Opaque Init.Nat.add. induction e; i; ss; des; clarify.
    - rewrite interp_imp_expr_Var. sim_red.
      destruct (alist_find v le) eqn:AFIND; try sim_red.
      + do 2 (gstep; sim_tau). red. sim_red.
        sim_ord.
        { eapply OrdArith.add_base_l. }
        eapply SIM; auto.
        econs. inv MLE. specialize ML with (x:=v) (sv:=v0).
        hexploit ML; auto.
      + sim_triggerUB.
    - rewrite interp_imp_expr_Lit.
      do 1 (gstep; sim_tau). red.
      sim_red.
      sim_ord.
      { eapply OrdArith.add_base_l. }
      eapply SIM; eauto. econs. unfold map_val. ss.

    - rewrite interp_imp_expr_Eq.
      sim_red.
      sim_ord.
      { instantiate (1:=((i1 + 20 + expr_ord e2 + 20) + expr_ord e1)%ord).
        rewrite <- ! OrdArith.add_assoc. eapply OrdArith.add_base_l. }
      eapply IHe1; auto. clear IHe1.
      i. sim_red.
      sim_ord.
      { instantiate (1:=(i1 + 20 + expr_ord e2)%ord).
        eapply OrdArith.add_base_l. }
      eapply IHe2; auto. clear IHe2.
      i. sim_red.
      destruct (wf_val rv && wf_val rv0) eqn:WFVAL.
      2: sim_triggerUB.
      sim_red. destruct rv; destruct rv0; try sim_triggerUB.
      2,3,4: gstep; ss; unfold triggerUB; try sim_red.
      des_ifs; ss; try sim_triggerUB.
      + sim_ord.
        { eapply OrdArith.add_base_l. }
        sim_red.
        eapply SIM; eauto.
        econs; eauto.
        { econs; eauto. }
        ss. f_equal. rewrite Z.eqb_eq in Heq. clarify.
        rewrite Int64.eq_true. ss.
      + sim_ord.
        { eapply OrdArith.add_base_l. }
        sim_red.
        eapply SIM; eauto.
        econs; eauto.
        { econs; eauto. }
        ss. f_equal.
        bsimpl. des. unfold_intrange_64. bsimpl. des.
        apply sumbool_to_bool_true in WFVAL.
        apply sumbool_to_bool_true in WFVAL0.
        apply sumbool_to_bool_true in WFVAL1.
        apply sumbool_to_bool_true in WFVAL2.
        rewrite Int64.signed_eq.
        rewrite ! Int64.signed_repr.
        2,3: unfold_Int64_max_signed; unfold_Int64_min_signed; lia.
        rewrite Z.eqb_neq in Heq. unfold Coqlib.proj_sumbool. des_ifs.
    - rewrite interp_imp_expr_Lt.
      sim_red.
      sim_ord.
      { instantiate (1:=((i1 + 20 + expr_ord e2 + 20) + expr_ord e1)%ord).
        rewrite <- ! OrdArith.add_assoc. eapply OrdArith.add_base_l. }
      eapply IHe1; auto. clear IHe1.
      i. sim_red.
      sim_ord.
      { instantiate (1:=(i1 + 20 + expr_ord e2)%ord).
        eapply OrdArith.add_base_l. }
      eapply IHe2; auto. clear IHe2.
      i. sim_red.
      destruct (wf_val rv && wf_val rv0) eqn:WFVAL.
      2: sim_triggerUB.
      sim_red. destruct rv; destruct rv0; try sim_triggerUB.
      2,3,4: gstep; ss; unfold triggerUB; try sim_red.
      des_ifs; ss; try sim_triggerUB.
      + sim_ord.
        { eapply OrdArith.add_base_l. }
        sim_red.        
        eapply SIM; eauto.
        econs; eauto.
        { econs; eauto. }
        ss. f_equal.
        bsimpl. des. unfold_intrange_64. bsimpl. des.
        apply sumbool_to_bool_true in WFVAL.
        apply sumbool_to_bool_true in WFVAL0.
        apply sumbool_to_bool_true in WFVAL1.
        apply sumbool_to_bool_true in WFVAL2.
        unfold Int64.lt. rewrite ! Int64.signed_repr.
        2,3: unfold_Int64_max_signed; unfold_Int64_min_signed; lia.
        des_ifs.
      + sim_ord.
        { eapply OrdArith.add_base_l. }
        sim_red.        
        eapply SIM; eauto.
        econs; eauto.
        { econs; eauto. }
        ss. f_equal.
        bsimpl. des. unfold_intrange_64. bsimpl. des.
        apply sumbool_to_bool_true in WFVAL.
        apply sumbool_to_bool_true in WFVAL0.
        apply sumbool_to_bool_true in WFVAL1.
        apply sumbool_to_bool_true in WFVAL2.
        unfold Int64.lt. rewrite ! Int64.signed_repr.
        2,3: unfold_Int64_max_signed; unfold_Int64_min_signed; lia.
        des_ifs.

    - rewrite interp_imp_expr_Plus.
      sim_red.
      sim_ord.
      { instantiate (1:=((i1 + 20 + expr_ord e2 + 20) + expr_ord e1)%ord).
        rewrite <- ! OrdArith.add_assoc. eapply OrdArith.add_base_l. }
      eapply IHe1; auto. clear IHe1.
      i. sim_red.
      sim_ord.
      { instantiate (1:=(i1 + 20 + expr_ord e2)%ord).
        eapply OrdArith.add_base_l. }
      eapply IHe2; auto. clear IHe2.
      i. sim_red.
      unfold unwrapU. destruct (vadd rv rv0) eqn:VADD; ss; clarify.
      + sim_red.
        specialize SIM with (rv:=v) (trv:= @map_val builtins srcprog v).
        sim_ord.
        { eapply OrdArith.add_base_l. }
        apply SIM; auto.
        econs; eauto. ss. f_equal. apply map_val_vadd_comm; auto.
      + sim_triggerUB.
    - rewrite interp_imp_expr_Minus.
      sim_red.
      sim_ord.
      { instantiate (1:=((i1 + 20 + expr_ord e2 + 20) + expr_ord e1)%ord).
        rewrite <- ! OrdArith.add_assoc. eapply OrdArith.add_base_l. }
      eapply IHe1; auto. clear IHe1.
      i. sim_red.
      sim_ord.
      { instantiate (1:=(i1 + 20 + expr_ord e2)%ord).
        eapply OrdArith.add_base_l. }
      eapply IHe2; auto. clear IHe2.
      i. sim_red.
      unfold unwrapU. destruct (vsub rv rv0) eqn:VSUB; ss; clarify.
      + sim_red.
        specialize SIM with (rv:=v) (trv:= @map_val builtins srcprog v).
        sim_ord.
        { eapply OrdArith.add_base_l. }
        apply SIM; auto.
        econs; eauto. ss. f_equal. apply map_val_vsub_comm; auto.
      + sim_triggerUB.
    - rewrite interp_imp_expr_Mult.
      sim_red.
      sim_ord.
      { instantiate (1:=((i1 + 20 + expr_ord e2 + 20) + expr_ord e1)%ord).
        rewrite <- ! OrdArith.add_assoc. eapply OrdArith.add_base_l. }
      eapply IHe1; auto. clear IHe1.
      i.
      sim_red.
      sim_ord.
      { instantiate (1:=(i1 + 20 + expr_ord e2)%ord).
        eapply OrdArith.add_base_l. }
      eapply IHe2; auto. clear IHe2.
      i. sim_red.
      unfold unwrapU. destruct (vmul rv rv0) eqn:VMUL; ss; clarify.
      + sim_red.
        specialize SIM with (rv:=v) (trv:= @map_val builtins srcprog v).
        sim_ord.
        { eapply OrdArith.add_base_l. }
        apply SIM; auto.
        econs; eauto. ss. f_equal. apply map_val_vmul_comm; auto.
      + sim_triggerUB.
  Qed.

  Lemma step_exprs
        (src: ModL.t) (tgt: Csharpminor.program)
        es tes
        tcode tf tcont tge tle tm
        r rg ms mn ge le pstate ktr
        i1
        (MLE: match_le srcprog le tle)
        (CEXP: compile_exprs es = tes)
        (SIM:
           forall rvs trvs,
             (* Forall wf_val rvs -> *)
             eval_exprlist tge empty_env tle tm tes trvs ->
             trvs = List.map (map_val srcprog) rvs ->
             gpaco3 (_sim (compile_val src) (semantics tgt)) (cpn3 (_sim (compile_val src) (semantics tgt))) r rg i1
                   (ktr (pstate, (le, rvs)))
                   (State tf tcode tcont empty_env tle tm))
    :
      gpaco3 (_sim (compile_val src) (semantics tgt))
             (cpn3 (_sim (compile_val src) (semantics tgt)))
             r rg (i1 + (Ord.omega * List.length es))%ord
            (r0 <- EventsL.interp_Es (prog ms) (transl_all mn (interp_imp ge (denote_exprs es) le)) (pstate);; ktr r0)
            (State tf tcode tcont empty_env tle tm).
  Proof.
    generalize dependent ktr. generalize dependent tes.
    move MLE before pstate. revert_until MLE.
    generalize dependent es. intros es. revert r rg. induction es; i; ss; des; clarify.
    - rewrite interp_imp_Ret. sim_red. sim_ord.
      { eapply OrdArith.add_base_l. }
      eapply SIM; eauto. econs.
    - eapply gpaco3_gen_guard.
      rewrite interp_imp_bind. sim_red.
      sim_ord.
      { instantiate (1:=((i1 + (Ord.omega * Datatypes.length es)) + expr_ord a)%ord).
        rewrite OrdArith.add_assoc. eapply OrdArith.le_add_r.
        rewrite Ord.from_nat_S. rewrite OrdArith.mult_S.
        eapply OrdArith.le_add_r. eapply Ord.lt_le. eapply expr_ord_omega. }
      eapply step_expr; eauto.
      i. rewrite interp_imp_bind. sim_red.
      eapply IHes; auto.
      i. rewrite interp_imp_Ret. sim_red.
      eapply gpaco3_mon; [eapply SIM|..]; auto.
      unfold compile_exprs in H2. econs; ss; clarify; eauto.
  Qed. *)


(* Lemma compile_stmt_no_Sreturn
        src e
        (CSTMT: compile_stmt src = (Sreturn e))
    :
      False.
  Proof. destruct src; ss; uo; des_ifs; clarify. Qed. *)





  (**** At the moment, it suffices to support integer IO in our scenario,
        and we simplify all the other aspects.
        e.g., the system calls that we are aware of
        (1) behaves irrelevant from Senv.t,
        (2) does not allow arguments/return values other than integers,
        (3) produces exactly one event (already in CompCert; see: ec_trace_length),
        (4) does not change memory,
        (5) always returns without stuck,
        and (6) we also assume that it refines our notion of system call.
   ****)
  Axiom syscall_exists: forall fn sg se args_tgt m0, exists tr ret_tgt m1,
        <<TGT: external_functions_sem fn sg se args_tgt m0 tr ret_tgt m1>>
  .
  Axiom syscall_refines:
    forall fn sg args_tgt ret_tgt
           se m0 tr m1
           (TGT: external_functions_sem fn sg se args_tgt m0 tr ret_tgt m1)
    ,
      exists args_int ret_int ev,
        (<<ARGS: args_tgt = (List.map Values.Vlong args_int)>>) /\
        (<<RET: ret_tgt = (Values.Vlong ret_int)>>) /\
        let args_src := List.map Int64.signed args_int in
        let ret_src := Int64.signed ret_int in
        (<<EV: tr = [ev] /\ decompile_event ev = Some (event_sys fn args_src↑ ret_src↑)>>)
        /\ (<<SRC: syscall_sem (event_sys fn args_src↑ ret_src↑)>>)
        /\ (<<MEM: m0 = m1>>)
  .

  (* paco4
  (_sim (ModL.compile (ModL.add Mem (get_mod types defs WF_TYPES mn)))
     (semantics2
        {|
          prog_defs := defs;
          prog_public := List.map (fun '(gn, _) => gn) defs;
          prog_main := 22880918%positive;
          prog_types := types;
          prog_comp_env := x;
          prog_comp_env_eq := e0
        |})) r false false
  (` x_ : p_state * Values.val <-
   EventsL.interp_Es
     (prog
        (add
           (MemSem
              (Sk.sort
                 (Sk.add
                    [("malloc",
                     Any.upcast
                       (Cgfun
                          (Tfunction (Tcons size_t Tnil) 
                             (tptr tvoid) cc_default)));
                    ("free",
                    Any.upcast
                      (Cgfun
                         (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default)))] (get_sk defs))))
           (modsem types defs WF_TYPES mn
              (Sk.sort
                 (Sk.add
                    [("malloc",
                     Any.upcast
                       (Cgfun
                          (Tfunction (Tcons size_t Tnil) 
                             (tptr tvoid) cc_default)));
                    ("free",
                    Any.upcast
                      (Cgfun
                         (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default)))] (get_sk defs))))))
     (transl_all mn0
        (` x_ : env * temp_env * option bool * option Values.val <-
         (free_list_aux (ConvC2ITree.blocks_of_env x e);;;
          Ret (e, le, None, Some Values.Vundef));;
         (let (p, optv') := x_ in
          let (p0, _) := p in
          let (_, _) := p0 in ` v : Values.val <- unwrapU optv';; Ret v)))
     pstate;; (let (_, v) := x_ in Ret (Any.upcast v)))
  (State tf Sskip Kstop te tle tm) *)


  Lemma step_freeing_stack cprog f_table modl r b1 b2 ktr tstate ge ce e pstate mn (PSTATE: exists m: mem, pstate "Mem"%string = m↑) (EQ: ce = ge.(genv_cenv)) (EQ2: f_table = (ModL.add Mem modl).(ModL.enclose)) :
  paco4
    (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r (match (blocks_of_env ge e) with [] => b1 | _ => true end) b2
    (m <- (pstate "Mem")↓?;; m <- (Mem.free_list m (blocks_of_env ge e))?;; ktr (update pstate "Mem" m↑, ()))
    tstate
  ->
  paco4
    (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r b1 b2
    (`r0: (p_state * ()) <- (EventsL.interp_Es
      (prog f_table)
      (transl_all mn (free_list_aux (ConvC2ITree.blocks_of_env ce e))) 
      pstate);; ktr r0)
    tstate.
  Proof.
    rewrite EQ. rewrite EQ2. clear EQ ce EQ2 f_table. des. replace (ConvC2ITree.blocks_of_env ge e) with (blocks_of_env ge e) by auto.
    set (blocks_of_env _ _) as l. clearbody l. depgen m. depgen pstate. depgen b1. depgen b2. induction l.
    - i. rewrite PSTATE in H. rewrite Any.upcast_downcast in H. ss. sim_red. sim_redH H.
      replace (update pstate _ _) with pstate in H; et.
      apply func_ext. i. s. unfold update. des_ifs.
    - i. rewrite PSTATE in H. sim_redH H. des_ifs_safe. unfold ccallU. sim_tau.
      des_ifs_safe. unfold sfreeF. repeat sim_tau. rewrite PSTATE. sim_red. 
      destruct (Mem.free _) eqn: E1 in H; try (unfold unwrapU in *; des_ifs_safe; sim_triggerUB; fail).
      rewrite E1. sim_red. repeat sim_tau. sim_red. eapply IHl; ss.
      unfold update at 1. ss. sim_red. destruct (Mem.free_list _) eqn: E2.
      { sim_red. sim_redH H. des_ifs; replace (update (update _ _ _) _ _) with (update pstate "Mem" (Any.upcast m1)); et.
        all : apply func_ext; i; unfold update; des_ifs. }
      unfold unwrapU. unfold triggerUB. sim_red. sim_triggerUB.
  Qed.

  Theorem match_states_sim
          types defs WF_TYPES mn
          (modl: ModL.t) ms sk ge
          clight_prog ist cst
          (* WFDEF may not needed *)
          (WFDEF: NoDup (List.map (fun '(id, _) => id) defs))
          (WFDEF2: forall p gd , In (p, gd) defs -> exists s, ident_of_string s = p)
          (MODL: modl = ModL.add (Mod.lift Mem) (Mod.lift (get_mod types defs WF_TYPES mn)))
          (MODSEML: ms = modl.(ModL.enclose))
          (SK: sk = Sk.sort modl.(ModL.sk))
          (GENV: ge = Sk.load_skenv (Sk.sort modl.(ModL.sk)))
          (TGT: clight_prog = mkprogram types defs (List.map (fun '(gn, _) => gn) defs) (ident_of_string "main") WF_TYPES)
          (MGENV: match_ge defs ge (Genv.globalenv clight_prog))
          (MS: match_states sk (Ctypes.prog_comp_env clight_prog) ms defs ist cst)
  :
      <<SIM: sim (@ModL.compile _ EMSConfigC modl) (Clight.semantics2 clight_prog) false false ist cst>>.
  Proof.
    red. red.
    depgen ist. depgen cst. pcofix CIH. i.
    inv MS. unfold mkprogram in *. des_ifs_safe.
    set (Genv.globalenv _) as ge in MGENV. set {| genv_genv := ge; genv_cenv := x|} as gh.
    destruct tcode.
    - unfold itree_of_code, Es_to_eventE, decomp_stmt. sim_red. sim_tau. sim_red.
      destruct tcont; inv MCONT; ss; clarify.
      { unfold Es_to_eventE. sim_red. sim_triggerUB. }
      { unfold Es_to_eventE. sim_red. tgt_step; [econs|]. wrap_up. apply CIH. econs; et. }
      { unfold Es_to_eventE. sim_red. tgt_step; [econs; et|]. wrap_up. apply CIH. 
        econs; et. { econs; et. }
        unfold itree_of_code, sloop_iter_body_two, ktree_of_cont_itree, Es_to_eventE. sim_redE.
        erewrite bind_extk; et. i. des_ifs_safe. repeat (des_ifs; sim_redE; try reflexivity). }
      { unfold Es_to_eventE. sim_red. tgt_step; [econs; et|]. wrap_up. apply CIH. econs; et. }
      { unfold Es_to_eventE. sim_red. eapply step_freeing_stack; et. 
        { instantiate (1 := gh). et. }
        rewrite PSTATE. sim_red. unfold unwrapU in *.
        destruct (Mem.free_list m (blocks_of_env gh e)) eqn: STACK_FREE; try sim_triggerUB.
        inv ME. hexploit match_mem_free_list; et. i. des. 
        sim_red. tgt_step. 
        { econs; unfold is_call_cont; et. unfold semantics2, globalenv. ss.
          replace (Build_genv _ _) with gh; et. 
          replace (List.map _ _) with (blocks_of_env gh te) in TMEM; et.
          clear - ME0. unfold blocks_of_env, block_of_binding.
          set (fun id_b_ty : _ * (_ * _) => _) as f.
          set (fun _ => _) as g. 
          rewrite List.map_map. 
          set ((fun '(id, (b, ty)) => (id, (map_blk defs b, ty))) : ident * (Values.block * type) -> ident * (Values.block * type)) as h.
          replace (g ∘ f) with (f ∘ h); cycle 1.
          { unfold f, g, h. apply func_ext. i. des_ifs_safe. destruct p. inv Heq0. inv Heq. et. }
          rewrite <- (List.map_map h f). f_equal. clear -ME0.
          (* TODO: there's no property about PTree *)
          admit "property of Maps.PTree.elements". }
        tgt_step; [econs|]. pfold. econs 7;[|des_ifs|];et. right. eapply CIH.
        econs. 4: apply MM_POST. all: et.
        { change Values.Vundef with (map_val defs Values.Vundef). eapply match_update_le; et. }
        { instantiate (1 := update pstate "Mem" (Any.upcast m0)). ss. }
        { unfold itree_of_code, Es_to_eventE. rewrite unfold_decomp_stmt. sim_redE. f_equal. f_equal. sim_redE. et. } }
    -
  Qed.

  Ltac rewriter :=
    try match goal with
        | H: _ = _ |- _ => rewrite H in *; clarify
        end.

  Lemma Csharpminor_eval_expr_determ a
    :
      forall v0 v1 ge e le m
             (EXPR0: eval_expr ge e le m a v0)
             (EXPR1: eval_expr ge e le m a v1),
        v0 = v1.
  Proof.
    induction a; i; inv EXPR0; inv EXPR1; rewriter.
    { inv H0; inv H1; rewriter. }
    { exploit (IHa v2 v3); et. i. subst. rewriter. }
    { exploit (IHa1 v2 v4); et. i. subst.
      exploit (IHa2 v3 v5); et. i. subst. rewriter. }
    { exploit (IHa v2 v3); et. i. subst. rewriter. }
  Qed.

  Lemma Csharpminor_eval_exprlist_determ a
    :
      forall v0 v1 ge e le m
             (EXPR0: eval_exprlist ge e le m a v0)
             (EXPR1: eval_exprlist ge e le m a v1),
        v0 = v1.
  Proof.
    induction a; ss.
    { i. inv EXPR0. inv EXPR1. auto. }
    { i. inv EXPR0. inv EXPR1.
      hexploit (@Csharpminor_eval_expr_determ a v2 v0); et. i.
      hexploit (IHa vl vl0); et. i. clarify. }
  Qed.

  Lemma alloc_variables_determ vars
    :
      forall e0 e1 ee m m0 m1
             (ALLOC0: alloc_variables ee m vars e0 m0)
             (ALLOC1: alloc_variables ee m vars e1 m1),
        e0 = e1 /\ m0 = m1.
  Proof.
    induction vars; et.
    { i. inv ALLOC0; inv ALLOC1; auto. }
    { i. inv ALLOC0; inv ALLOC1; auto. rewriter.
      eapply IHvars; et. }
  Qed.

  Lemma Csharpminor_wf_semantics prog
    :
      wf_semantics (Csharpminor.semantics prog).
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

End PROOF.

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