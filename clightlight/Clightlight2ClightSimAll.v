From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import ConvC2ITree.
Require Import ConvC2ITreeStmt.
Require Import SimSTS3.
Require Import Clight_Mem0.
Require Import IRed.
From Ordinal Require Import Ordinal Arithmetic.

Require Import Clightlight2ClightMatch.
Require Import Clightlight2ClightMatchStmt.
Require Import Clightlight2ClightArith.
Require Import Clightlight2ClightGenv.
Require Import Clightlight2ClightLenv.
Require Import Clightlight2ClightMem.
Require Import Clightlight2ClightSim.

From compcert Require Import Ctypes Clight Clightdefs Values.

Section PROOF.

  Import ModSemL.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Let _sim_mon := Eval simpl in (fun (src: ModL.t) (tgt: Clight.program) => @sim_mon (compile_val src) (Clight.semantics2 tgt)).
  Hint Resolve _sim_mon: paco.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); try pfold; econs 3; ss; clarify; eexists; exists (step_tau _).

  Opaque arrow.

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
    (try rename H into HH); ss; unfold triggerUB; try sim_red; try pfold; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  Ltac tgt_step := try pfold; econs 4; eexists; eexists.

  Ltac wrap_up := try pfold; econs 7; et; right.

  Ltac remove_UBcase := des_ifs; try sim_red; try sim_triggerUB.

  Ltac dtm H H0 := eapply angelic_step in H; eapply angelic_step in H0; des; rewrite H; rewrite H0; ss.

  Ltac eapplyf NEXT := let X := fresh "X" in hexploit NEXT;[..|intro X; punfold X; eapply X].

  Ltac eapplyfarg NEXT ge := eapplyf NEXT; et; [instantiate (1:=ge)|..]; et. 

  Local Opaque Pos.of_nat.

  Local Opaque Pos.of_succ_nat.

  Lemma _step_freeing_stack cprog f_table modl r b ktr tstate ge ce e pstate mn m
  (EQ1: ce = ge.(genv_cenv)) 
  (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
  (PSTATE: pstate "Mem"%string = m↑) 
  (NEXT: forall m', 
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (ktr (update pstate "Mem" m'↑, ()))
      tstate)
  :
  paco4
    (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
    (`r0: (p_state * ()) <- 
      (EventsL.interp_Es (prog f_table)
        (transl_all mn (free_list_aux (ConvC2ITreeStmt.blocks_of_env ce e))) 
        pstate)
      ;; ktr r0) 
    tstate.
  Proof.
    subst. 
    replace (ConvC2ITreeStmt.blocks_of_env ge e) with (blocks_of_env ge e) by auto.
    set (blocks_of_env ge e) as l in *. clearbody l.
    depgen m. depgen pstate. induction l; i; ss.
    - sim_red. replace pstate with (update pstate "Mem" m↑).
      2:{ rewrite <- PSTATE. unfold update. apply func_ext. i. des_ifs. }
      eapply NEXT; et. 
    - des_ifs_safe. unfold ccallU. sim_red. ss. sim_tau. sim_red. unfold sfreeF.
      sim_red. rewrite PSTATE. repeat (sim_tau; sim_red). unfold unwrapU.
      remove_UBcase. repeat (sim_tau; sim_red). remove_UBcase.
      eapplyf IHl. et. { unfold update. ss. } i.
      replace (update (update _ _ _) _ _) with (update pstate "Mem" m'↑); et.
      unfold update. apply func_ext. i. des_ifs.
  Qed.

  Lemma step_freeing_stack cprog f_table modl r b ktr tstate ge sk tge ce e te pstate mn m tm
  (EQ1: ce = ge.(genv_cenv)) 
  (EQ2: tge = ge.(genv_genv)) 
  (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
  (PSTATE: pstate "Mem"%string = m↑) 
  (MGE: match_ge sk tge)
  (ME: match_e sk tge e te)
  (MM: match_mem sk tge m tm)
  (NEXT: forall m' tm', 
    Mem.free_list tm (blocks_of_env ge te) = Some tm' ->
    match_mem sk tge m' tm' ->
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (ktr (update pstate "Mem" m'↑, ()))
      tstate)
  :
  paco4
    (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
    (`r0: (p_state * ()) <- 
      (EventsL.interp_Es (prog f_table)
        (transl_all mn (free_list_aux (ConvC2ITreeStmt.blocks_of_env ce e))) 
        pstate)
      ;; ktr r0) 
    tstate.
  Proof.
    eapply _step_freeing_stack; et. i. eapply match_mem_free_list in H; et.
    des. eapplyf NEXT; et. unfold blocks_of_env, block_of_binding in *.
    apply match_env_same in ME. rewrite ME. set (fun _ => _) as f. rewrite List.map_map.
    set (fun _ => _) as g in TMEM. 
    replace (f ∘ _) with (g ∘ f); try rewrite <- List.map_map; et.
    unfold g, f, map_env_entry. eapply func_ext. i. des_ifs.
  Qed.

  Lemma step_eval_exprlist pstate ge ce f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: ce = ge.(genv_cenv)) 
    (EQ2: tge = ge.(genv_genv)) 
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    al tyl
 r b tcode tf tcont mn ktr
    (NEXT: forall vl, 
            eval_exprlist ge te tle tm al tyl (List.map (map_val sk tge) vl) ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, vl))
              (State tf tcode tcont te tle tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * list Values.val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_exprlist_c sk ce e le al tyl))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm). 
  Proof.
    depgen tyl. revert ktr. induction al; i.
    - ss. remove_UBcase. eapplyf NEXT. econs.
    - ss. remove_UBcase. eapply step_eval_expr with (ge:=ge); et. i. sim_red. eapply IHal. i.
      sim_red. eapply step_sem_cast; et. i. destruct optv; remove_UBcase. eapplyf NEXT. econs; et.
  Qed.

  Lemma step_alloc pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    lo hi
    tstate ktr b r mn
    (NEXT: forall tm' m' blk,
            Mem.alloc tm lo hi = (tm', map_blk sk tge blk) ->
            match_mem sk tge m' tm' ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, Vptr blk Ptrofs.zero))
              tstate)
:
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: p_state * val <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "salloc" (lo, hi))) 
          pstate);; ktr r0)
      tstate.
  Proof.
    unfold ccallU. sim_red. sim_tau. ss. sim_red. unfold sallocF. sim_red. repeat (sim_tau; sim_red).
    rewrite PSTATE. sim_red. unfold unwrapU. remove_UBcase. repeat (sim_tau; sim_red). rewrite Any.upcast_downcast.
    sim_red. hexploit match_mem_alloc; et. i. des. eapplyf NEXT; et. 
  Qed.

  Lemma match_update_e sk tge e te i blk t
        (MLE: match_e sk tge e te)
    :
      match_e sk tge (Maps.PTree.set i (blk, t) e) (Maps.PTree.set i (map_blk sk tge blk, t) te).
  Proof.
    econs. inv MLE. split; i.
    - destruct a. apply Maps.PTree.elements_complete in H.
      rewrite in_map_iff. destruct (Pos.eq_dec p i).
      + subst. rewrite Maps.PTree.gss in H. clarify. 
        exists (i, (blk, t)). split; et. apply Maps.PTree.elements_correct.
        rewrite Maps.PTree.gss. et.
      + rewrite Maps.PTree.gso in H; et. apply Maps.PTree.elements_correct in H.
        apply ME in H. apply in_map_iff in H. des. eexists; split; et.
        destruct x. destruct p1. ss. clarify.
        apply Maps.PTree.elements_complete in H0.
        apply Maps.PTree.elements_correct. rewrite Maps.PTree.gso; et.
    - destruct a. rewrite in_map_iff in H. des. destruct x. destruct p1.
      ss. clarify. apply Maps.PTree.elements_complete in H0.
      apply Maps.PTree.elements_correct.
      destruct (Pos.eq_dec p i).
      + subst. rewrite Maps.PTree.gss in *. clarify.
      + rewrite Maps.PTree.gso in H0; et. rewrite Maps.PTree.gso; et.
        apply Maps.PTree.elements_complete.
        apply Maps.PTree.elements_correct in H0. rewrite ME.
        change ((_, (_,_))) with (map_env_entry sk tge (p, (b, t0))). 
        apply in_map. et.
  Qed.

  Lemma update_shadow V pstate (x: string) (v v': V) : update (update pstate x v) x v' = update pstate x v'.
  Proof. unfold update. apply func_ext. i. des_ifs. Qed.

  Lemma step_alloc_variables pstate ge ce f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: ce = ge.(genv_cenv)) 
    (EQ2: tge = ge.(genv_genv)) 
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    l
 r b tstate mn ktr 
    (NEXT: forall e' te' m' tm', 
            alloc_variables ge te tm l te' tm' ->
            match_mem sk tge m' tm' ->
            match_e sk tge e' te' ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, e'))
              tstate)
  :
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * env) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (alloc_variables_c ce e l))
          pstate);; ktr r0)
      tstate.
  Proof.
    depgen e. depgen te. depgen pstate. depgen m. revert tm. depgen l. induction l; i.
    - ss. sim_red. 
      replace pstate with (update pstate "Mem" m↑) 
        by now unfold update; apply func_ext; i; des_ifs.
      eapply NEXT; et. econs; et.
    - ss. remove_UBcase. eapply step_alloc; et. i. eapply IHl; et. 
      2:{ eapply match_update_e; et. }
      i. rewrite update_shadow. eapply NEXT; et. econs; et.
  Qed.

  
  Lemma match_bind_parameter_temps
        sk tge params sle rvs sbase tbase
        (BIND_SRC: bind_parameter_temps params rvs sbase = Some sle)
        (MLE: match_le sk tge sbase tbase)
    :
      exists tle, (<<BIND_TGT: bind_parameter_temps params (List.map (map_val sk tge) rvs) tbase
                      = Some tle>>)
                  /\ (<<MLE: match_le sk tge sle tle>>).
  Proof.
    hexploit (bind_parameter_temps_exists_if_same_length params (List.map (map_val sk tge) rvs) tbase).
    - rewrite ! map_length. clear -BIND_SRC. depgen sbase.
      revert sle. depgen rvs. depgen params.
      induction params; i; ss; des_ifs.
      ss. f_equal. eapply IHparams; eauto.
    - i. des. eexists; split; et. red. depgen sbase. depgen sle. depgen rvs. revert tbase tle. depgen params.
      induction params; i; ss; des_ifs.
      eapply (match_update_le (Some i) v) in MLE. ss. inv Heq. eapply IHparams; et.
  Qed.

  Lemma norepet l : id_list_norepet_c l = true -> Coqlib.list_norepet l.
  Proof. induction l; i; econs; try eapply IHl; unfold id_list_norepet_c in *; des_ifs; inv l0; et. Qed.

  Lemma disjoint l l' : id_list_disjoint_c l l' = true -> Coqlib.list_disjoint l l'.
  Proof. 
    revert l'. induction l; i; ss.
    unfold Coqlib.list_disjoint. i. unfold id_list_disjoint_c in *. des_ifs.
    unfold Coqlib.list_disjoint in *. eapply l0; et. 
  Qed.

  Lemma step_function_entry pstate ge ce f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: ce = ge.(genv_cenv)) 
    (EQ2: tge = ge.(genv_genv)) 
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    f vl
 r b o tf tcont mn ktr dvl df
    (NEXT: forall e' le' te' tle' m' tm', 
            function_entry2 ge f (List.map (map_val sk tge) vl) tm te' tle' tm' ->
            match_mem sk tge m' tm' ->
            match_e sk tge e' te' ->
            match_le sk tge le' tle' ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, (e', le')))
              (Callstate df dvl (Kcall o tf te tle tcont) tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * (env * temp_env)) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (function_entry_c ce f vl))
          pstate);; ktr r0)
      (Callstate df dvl (Kcall o tf te tle tcont) tm). 
  Proof.
    unfold function_entry_c. remove_UBcase.
    eapply step_alloc_variables with (te := empty_env); et.
    { econs. i. ss. }
    i. sim_red. unfold unwrapU. remove_UBcase. hexploit (match_bind_parameter_temps sk ge); et.
    { instantiate (1:=create_undef_temps (fn_temps f)). econs. i. clear -H2. set (fn_temps f) as l in *. clearbody l.
      induction l; ss. destruct a. destruct (Pos.eq_dec id i); try solve [subst; rewrite Maps.PTree.gss in *; clarify].
      rewrite Maps.PTree.gso; et.
      rewrite Maps.PTree.gso in H2; et. }
    i. des. eapply NEXT; et. bsimpl. des.  
    econs; et. { apply norepet; et. } { apply norepet; et. }
    apply disjoint; et.
  Qed.

  Lemma step_bool_val pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    v ty
 r b tcode tf tcont mn ktr
    (NEXT: forall optb, 
            Cop.bool_val (map_val sk tge v) ty tm = optb ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, optb))
              (State tf tcode tcont te tle tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * option bool) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (bool_val_c v ty))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm). 
  Proof.
    unfold bool_val_c. 
    remove_UBcase; try solve [eapply NEXT; unfold Cop.bool_val; rewrite Heq; et].
    eapply step_weak_valid_pointer; et. i.
    destruct b1; sim_red;
      eapply NEXT; unfold Cop.bool_val; rewrite Heq; ss; des_ifs.
  Qed.

  Arguments Es_to_eventE /.
  Arguments itree_of_code /. 
  Arguments sloop_iter_body_two /. 
  Arguments ktree_of_cont_itree /. 

  Lemma unfold_itree_iter A B eff (f : A -> itree eff (A + B)) (x: A)  :
          ITree.iter f x = `lr : A + B <- f x;;
                           match lr with
                            | inl l => tau;; ITree.iter f l
                            | inr r => Ret r
                           end.
  Proof.
    eapply bisim_is_eq. apply unfold_iter.
  Qed.

  Lemma return_cont pstate f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    itr_cont v
    r b tstate tcont ty mn ms ce
    (MCONT: match_cont sk tge ce ms ty mn itr_cont tcont)
    (NEXT: forall itr_cont'' itr_cont',
            match_cont sk tge ce ms ty mn itr_cont' (call_cont tcont) ->
            itr_cont'' = 
              (`r0: (p_state * val) <- itr_cont' (pstate, (e, le, None, Some v));;
                let (_, retv) := r0 in Ret retv↑) ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              itr_cont''
              tstate)
  :
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * val) <- itr_cont (pstate, (e, le, None, Some v));;
        let (_, retv) := r0 in Ret retv↑)
      tstate.
  Proof.
    depgen v. induction MCONT; i.
    - rewrite ITR. ss. sim_red. eapply IHMCONT; et. 
    - rewrite ITR. ss. sim_red. eapply IHMCONT; et.
    - rewrite ITR. ss. sim_red. eapply IHMCONT; et.
    - ss. eapply NEXT; et. econs; et. 
    - rewrite ITR. ss. sim_red. eapply NEXT.
      { econs; et. }
      sim_redE. et. 
  Qed.

  Lemma call_cont_is_call_cont tcont : is_call_cont (call_cont tcont).
  Proof. induction tcont; et; ss. Qed.

  Theorem match_states_sim
          types sk defs WF_TYPES
          (modl internal_modl: ModL.t) ms
          clight_prog ist cst
          (MODL: modl = ModL.add (Mod.lift Mem) internal_modl)
          (INTERNAL: forall s fd, In (s, (Gfun fd (V := type))↑) internal_modl.(ModL.sk) -> exists f : Clight.function, fd = Internal f)
          (MODSEML: ms = modl.(ModL.enclose))
          (SK: sk = modl.(ModL.sk))
          (TGT: clight_prog = mkprogram types defs (List.map (fun '(gn, _) => gn) defs) (ident_of_string "main") WF_TYPES)
          (MS: match_states sk (Genv.globalenv clight_prog) (Ctypes.prog_comp_env clight_prog) ms ist cst)
  :
      <<SIM: sim (@ModL.compile _ EMSConfigC modl) (Clight.semantics2 clight_prog) false false ist cst>>.
  Proof.
    red. red.
    depgen ist. depgen cst. pcofix CIH. i.
    inv MS. unfold mkprogram in *. des_ifs_safe.
    set (Genv.globalenv _) as tge in *.
    set (ModL.sk (ModL.add _ _)) as sk in *.
    set (ModL.add _ _) as modl in *.
    set {| genv_genv := tge; genv_cenv := x|} as ge.
    destruct tcode.
    - ss. sim_red. 
      destruct tcont; inv MCONT; ss; clarify.
      + sim_red. sim_triggerUB.
      + sim_red. tgt_step; [econs|].
        sim_tau. wrap_up. apply CIH. econs; et.
      + sim_red. tgt_step; [econs; et|].
        sim_tau. wrap_up. apply CIH. econs; et. 
        { econs; et. }
        sim_redE. apply bind_extk. i. des_ifs_safe.
        repeat (des_ifs; sim_redE; try reflexivity).
      + sim_red. tgt_step; [econs; et|]. 
        sim_tau. sim_red. sim_tau. wrap_up. apply CIH.
        econs; et.
      + sim_red. sim_tau. sim_red. eapplyfarg step_freeing_stack ge.
        i. sim_red. tgt_step. { econs; unfold is_call_cont; et. }
        sim_tau. tgt_step; [econs|].
        econs 7;[|des_ifs|];et. right. eapply CIH.
        clear PSTATE. econs; et.
        { hexploit match_update_le; et. instantiate (2 := Vundef). ss. et. }
        { instantiate (1 := update pstate "Mem" (Any.upcast m')). ss. }
        ss. sim_redE. et.
    - ss. unfold _sassign_c. sim_red. sim_tau. sim_red.
      eapplyfarg step_eval_lvalue ge. i. subst. sim_red.
      eapply step_eval_expr with (ge := ge); et. i. subst. sim_red.
      eapply step_sem_cast; et. i.
      unfold unwrapU. des_ifs; try sim_red; try sim_triggerUB.
      eapply step_assign_loc; et. i. sim_red.
      tgt_step. { econs; et. }
      wrap_up. eapply CIH. clear PSTATE.
      econs; et.
      { instantiate (1 := update pstate "Mem" m'↑). unfold update. ss. } 
      ss. sim_redE. et.
    - ss. sim_red. sim_tau. sim_red. eapplyfarg step_eval_expr ge. i. subst. sim_red. 
      tgt_step. { econs; et. }
      wrap_up. eapply CIH. econs; et.
      { change (Maps.PTree.set i _ _) with (set_opttemp (Some i) (map_val sk ge v') tle). eapply match_update_le; et. }
      ss. sim_redE. et. 
    - ss. unfold _scall_c. remove_UBcase. sim_tau. sim_red. eapplyfarg step_eval_expr ge. i. sim_red.
      eapply step_eval_exprlist with (ge := ge); et. i. remove_UBcase. destruct (nth_error _) eqn: E; remove_UBcase.
      destruct p. destruct (Any.downcast _) eqn: E1; remove_UBcase. remove_UBcase. remove_UBcase.
      unfold ccallU. sim_red. repeat (sim_tau; sim_red).
      assert (E2: t0 = (@Gfun _ type f)↑).
      { apply Any.downcast_upcast in E1. et. }
      rewrite E2 in *. tgt_step.
      { econs; ss; et. ss. des_ifs. unfold Genv.find_funct_ptr. 
        change (Genv.globalenv _) with tge.
        inv MGE. replace b with (Pos.of_succ_nat (pred (Pos.to_nat b))) by nia.
        erewrite ELEM; et. et. }
      apply nth_error_In in E. dup E. unfold sk in E0. simpl in E0. 
      des.
      + clarify. ss. unfold mallocF. sim_red. repeat (sim_tau; sim_red).
        rewrite PSTATE. sim_red. remove_UBcase. des_ifs_safe. sim_red. unfold unwrapU. remove_UBcase.
        repeat (sim_tau; sim_red). rewrite Any.upcast_downcast. sim_red.
        apply (f_equal (Any.downcast (T := globdef fundef type))) in H2.
        do 2 rewrite Any.upcast_downcast in H2. clarify.
        destruct i. ss.
        eapply match_mem_alloc in Heq2; et. clear E. destruct Heq2 as [? [? ?]].
        eapply match_mem_store in Heq3; et. destruct Heq3 as [? [? ?]].
        assert (Zneg xH < intval < Ptrofs.modulus)%Z by now change Int64.modulus with Ptrofs.modulus; et.
        set {| Ptrofs.intval := intval; Ptrofs.intrange := H5|} as i.
        replace (Vlong _) with (Vptrofs i) in *.
        2:{ unfold Vptrofs. des_ifs_safe. unfold Ptrofs.to_int64. unfold i. ss.
            change intval with (Int64.unsigned (Int64.mkint intval intrange)).
            rewrite Int64.repr_unsigned. ss. }
        tgt_step. { eapply step_external_function. ss. econs; et. }
        tgt_step. { econs. }
        wrap_up. eapply CIH. clear PSTATE. econs; et.
        { change (Vptr _ _) with (map_val sk tge (Vptr b0 Ptrofs.zero)). eapply match_update_le; et. }
        { instantiate (1:=update pstate "Mem" m1↑). et. }
        ss. sim_redE. et.
      + clarify. ss. 
        apply (f_equal (Any.downcast (T := globdef fundef type))) in H2.
        do 2 rewrite Any.upcast_downcast in H2. clarify. clear E.
        unfold freeF. sim_red. repeat (sim_tau; sim_red).
        rewrite PSTATE. sim_red. remove_UBcase.
        * repeat (sim_tau; sim_red). tgt_step. 
          { econs. ss. replace (Vlong _) with Vnullptr; try econs; et. unfold Vnullptr. des_ifs_safe. f_equal.
            rewrite <- Int64.repr_unsigned with (i := Int64.mkint _ _). et. }
          tgt_step. { econs. }
          wrap_up. eapply CIH. econs; et.
          { change Vundef with (map_val sk tge Vundef). eapply match_update_le; et. }
          ss. sim_redE. et.
        * unfold unwrapU. remove_UBcase. remove_UBcase. repeat (sim_tau; sim_red). rewrite Any.upcast_downcast.
          eapply match_mem_load in Heq2; et. 
          eapply match_mem_free in Heq4; et. destruct Heq4 as [? [? ?]].
          destruct i0. ss.
          assert (Zneg xH < intval < Ptrofs.modulus)%Z by now change Int64.modulus with Ptrofs.modulus; et.
          set {| Ptrofs.intval := intval; Ptrofs.intrange := H3|} as ofs.
          replace (Vlong _) with (Vptrofs ofs) in Heq2.
          2:{ unfold Vptrofs. des_ifs_safe. unfold Ptrofs.to_int64. unfold ofs. ss.
              change intval with (Int64.unsigned (Int64.mkint intval intrange)).
              rewrite Int64.repr_unsigned. ss. }
          sim_red. tgt_step. { econs. ss. econs; et. ss. nia. }
          tgt_step. { econs. }
          wrap_up. eapply CIH. clear PSTATE. econs; et.
          { change Vundef with (map_val sk tge Vundef). eapply match_update_le; et. }
          { instantiate (1:=update pstate "Mem" m0↑). et. }
          ss. sim_redE. et.
      + apply INTERNAL in E0. des. subst. unfold fnsem_has_internal in WFMS.
        apply WFMS in E. des. ss. rewrite E. sim_red.
        unfold decomp_func. sim_red. eapplyfarg step_function_entry ge.
        i. sim_red. 
        tgt_step.
        { econs; et. }
        wrap_up. eapply CIH. clear PSTATE. econs; et.
        { instantiate (1 := update pstate "Mem" m'↑). et. }
        { econs; et. }
        sim_redE.
        set (prog _) as t1.
        instantiate (1:= mn0).
        apply bind_extk. i. des_ifs_safe. unfold itree_of_cont_pop. sim_redE.
        destruct o0.
        { sim_redE. apply bind_extk. i. des_ifs_safe. sim_redE. f_equal. f_equal.
          sim_redE. et. }
        destruct o1.
        { apply bind_extk. i. des_ifs_safe. sim_redE.
          apply bind_extk. i. sim_redE. f_equal. f_equal. sim_redE. et. }
        sim_redE. f_equal. f_equal. apply bind_extk. i. des_ifs_safe. sim_redE.
        apply bind_extk. i. sim_redE. f_equal. f_equal.
        sim_redE. et. 
    - (* builtin is undefined *)
      sim_triggerUB.
    - ss. sim_red. sim_tau. tgt_step. { econs. }
      wrap_up. eapply CIH. econs; et.
      { econs; et. }
      ss. sim_redE. apply bind_extk. i. des_ifs_safe.
      unfold itree_of_cont_pop.
      repeat (des_ifs; sim_redE; try reflexivity).
    - ss. sim_red. unfold _site_c. sim_red. sim_tau.
      sim_red. eapplyfarg step_eval_expr ge.
      i. sim_red. eapply step_bool_val; et. i. unfold unwrapU. remove_UBcase.
      tgt_step. { econs; et. }
      wrap_up. eapply CIH. econs; et.
      repeat (des_ifs; sim_redE; try reflexivity).
    - ss. unfold _sloop_itree. rewrite unfold_itree_iter.
      ss. unfold sloop_iter_body_one. sim_red. sim_tau.
      tgt_step. { econs. } 
      wrap_up. eapply CIH. econs; et.
      { econs; et. }
      unfold _sloop_itree.
      sim_redE. apply bind_extk. i. 
      unfold itree_of_cont_pop.
      repeat (des_ifs; progress (sim_redE; grind)).
    - ss. destruct tcont; inv MCONT; ss; clarify.
      + sim_red. sim_triggerUB.
      + sim_red. sim_tau. sim_red. tgt_step. { econs. }
        wrap_up. eapply CIH. econs; et. ss. sim_redE. et.
      + sim_tau. sim_red. tgt_step. { eapply step_break_loop1. }  
        wrap_up. eapply CIH. econs; et. ss. sim_redE. et.
      + tgt_step. { eapply step_break_loop2. }  
        sim_red. sim_tau. sim_red. wrap_up. eapply CIH. econs; et.
        ss. sim_redE. et. 
      + sim_red. sim_triggerUB.
    - ss. destruct tcont; inv MCONT; ss; clarify.
      + sim_red. sim_triggerUB.
      + sim_red. sim_tau. sim_red. tgt_step. { econs. }
        wrap_up. eapply CIH. econs; et. ss. sim_redE. et.
      + sim_red. sim_tau. sim_red. tgt_step. { econs. et. }  
        wrap_up. eapply CIH. econs; et. { econs; et. } 
        ss. apply bind_extk. i. sim_redE. des_ifs_safe.
        repeat (des_ifs; sim_redE; try reflexivity).
      + sim_red. sim_triggerUB. 
      + sim_red. sim_triggerUB.
    - ss. unfold _sreturn_c. destruct o; cycle 1.
      + sim_tau. sim_red. eapplyf return_cont; et. i.
        rewrite H0. clear H0. remember (call_cont tcont) as tcont'. 
        inv H; try solve [specialize (call_cont_is_call_cont tcont); rewrite <- H3; clarify].
        * ss. sim_red. eapply step_freeing_stack with (ge := ge); et. i.
          sim_red. sim_triggerUB.
        * ss. sim_red. eapply step_freeing_stack with (ge := ge); et. i.
          sim_red. sim_tau. sim_red. tgt_step. { econs; et. }
          tgt_step. { rewrite <- H3. econs. }
          wrap_up. eapply CIH. clear PSTATE. econs; et. 
          { change Vundef with (map_val sk tge Vundef). eapply match_update_le; et. }
          { instantiate (1 := update pstate "Mem" m'↑). et. }
          ss. sim_redE. et. 
      + sim_tau. sim_red. eapplyfarg step_eval_expr ge.
        i. sim_red. eapply step_sem_cast; et. i. unfold unwrapU.
        remove_UBcase. eapply return_cont; et. i.
        rewrite H3. clear H3 itr_cont''. remember (call_cont tcont) as tcont'. 
        inv H0; try solve [specialize (call_cont_is_call_cont tcont); rewrite <- H6; clarify].
        * ss. sim_red. eapply step_freeing_stack with (ge := ge); et. i.
          sim_red. remove_UBcase. tgt_step. { econs; et. }
          econs 1.
          2:{ ss. rewrite <- H6. econs. }
          ss. unfold state_sort. ss. rewrite Any.upcast_downcast. et.
        * ss. sim_red. eapply step_freeing_stack with (ge := ge); et. i.
          sim_red. sim_tau. sim_red. tgt_step. { econs; et. }
          tgt_step. { rewrite <- H6. econs. }
          wrap_up. eapply CIH. clear PSTATE. econs; et.
          { eapply match_update_le; et. }
          { instantiate (1 := update pstate "Mem" m'↑). et. }
          ss. sim_redE. et.
    (* switch, label, goto is undefined *)
    - ss. sim_triggerUB.
    - ss. sim_triggerUB.
    - ss. sim_triggerUB.
  Qed.


  Ltac rewriter :=
    try match goal with
        | H: _ = _ |- _ => rewrite H in *
        end; clarify.
  Ltac determ LEMMA P :=
    repeat match goal with
            | H: context G [P] |- _ =>
              lazymatch context G [P] with
              | forall _, _  => fail
              | _ => revert H
              end
            end;
    let X1 := fresh "X" in
    let X2 := fresh "X" in
    intros X1 X2;
    hexploit LEMMA; [eapply X1|eapply X2|]; i; des; repeat rewriter.

  (* Ltac determ LEMMA P :=
    repeat match goal with
            | H: context G [P] |- _ =>
              lazymatch context G [P] with
              | forall _, _  => fail
              | _ => revert H
              end
            end;
    let X1 := fresh "X" in
    let X2 := fresh "X" in
    intros X1 X2;
    hexploit LEMMA;
    let n0 := numgoals in
    try eapply X1;
    let n := numgoals in
    guard n0<n;
    let n0 := numgoals in
    try eapply X2;
    let n := numgoals in
    guard n0<n;
    let n0 := numgoals in
    try eapply X3;
    let n := numgoals in
    guard n0<n;
    let n0 := numgoals in
    try eapply X4;
    let n := numgoals in
    guard n0<n. *)

  Ltac inv_pred P :=
    repeat match goal with
            | H: context G [P] |- _ =>
              lazymatch context G [P] with
              | forall _, _  => fail
              | _ => inv H
              end
            end; repeat rewriter.

  Ltac inv_pred_safe P :=
    solve [match goal with
            | H: context G [P] |- _ =>
              lazymatch context G [P] with
              | forall _, _  => fail
              | _ => inv H
              end
            end; repeat rewriter].

  Lemma Clight_eval_determ a ge e le m
    :
      (forall v0 v1
             (EXPR0: eval_expr ge e le m a v0)
             (EXPR1: eval_expr ge e le m a v1),
        v0 = v1) /\
      (forall loc0 loc1 ofs0 ofs1 bf0 bf1
             (EXPR0: eval_lvalue ge e le m a loc0 ofs0 bf0)
             (EXPR1: eval_lvalue ge e le m a loc1 ofs1 bf1),
        loc0 = loc1 /\ ofs0 = ofs1 /\ bf0 = bf1).
  Proof.
    revert_until a.
    induction a; split; i;
      inv EXPR0; try inv_pred_safe eval_expr; try inv_pred_safe eval_lvalue;
        inv EXPR1; try inv_pred_safe eval_expr; try inv_pred_safe eval_lvalue;
         try split; rewriter; et; repeat spc IHa; des; try determ IHa eval_expr.
    { inv_pred eval_lvalue; inv_pred deref_loc. }
    { inv_pred eval_lvalue; determ IHa eval_expr; inv_pred deref_loc. }
    { determ IHa0 eval_lvalue. }
    { repeat spc IHa1. repeat spc IHa2. des. exploit (IHa1 v2 v4); et. i. subst.
      exploit (IHa2 v3 v5); et. i. subst. rewriter. }
    { inv_pred eval_lvalue; determ IHa eval_expr;
      inv_pred deref_loc; inv_pred Cop.load_bitfield. }
  Qed.

  Lemma Clight_eval_expr_determ a ge e le m
    :
      forall v0 v1
             (EXPR0: eval_expr ge e le m a v0)
             (EXPR1: eval_expr ge e le m a v1),
        v0 = v1.
  Proof. edestruct Clight_eval_determ; et. Qed.

  Lemma Clight_eval_lvalue_determ a ge e le m
    :
      forall loc0 loc1 ofs0 ofs1 bf0 bf1
             (EXPR0: eval_lvalue ge e le m a loc0 ofs0 bf0)
             (EXPR1: eval_lvalue ge e le m a loc1 ofs1 bf1),
        loc0 = loc1 /\ ofs0 = ofs1 /\ bf0 = bf1.
  Proof. edestruct Clight_eval_determ; et. Qed.

  Lemma Clight_eval_exprlist_determ a
    :
      forall v0 v1 ge e le m ty
             (EXPR0: eval_exprlist ge e le m a ty v0)
             (EXPR1: eval_exprlist ge e le m a ty v1),
        v0 = v1.
  Proof.

    induction a; ss.
    { i. inv EXPR0. inv EXPR1. auto. }
    { i. inv EXPR0. inv EXPR1.
      determ Clight_eval_expr_determ eval_expr.
      determ IHa eval_exprlist. }
  Qed.

  Lemma alloc_variables_determ vars
    :
      forall e0 e1 ge ee m m0 m1
             (ALLOC0: alloc_variables ge ee m vars e0 m0)
             (ALLOC1: alloc_variables ge ee m vars e1 m1),
        e0 = e1 /\ m0 = m1.
  Proof.
    induction vars; et.
    { i. inv ALLOC0; inv ALLOC1; auto. }
    { i. inv ALLOC0; inv ALLOC1; auto. rewriter.
      eapply IHvars; et. }
  Qed.

  Lemma Csharpminor_wf_semantics prog
    :
      wf_semantics (Clight.semantics2 prog).
  Proof.
    econs.
    { i. inv STEP0; inv STEP1; ss; rewriter;
      try split; et;
        inv_pred assign_loc; 
        try determ Clight_eval_expr_determ eval_expr; 
        try determ Clight_eval_lvalue_determ eval_lvalue;
        des; clarify.
      { inv_pred Cop.store_bitfield. }
      { determ Clight_eval_exprlist_determ eval_exprlist. }
      { determ Clight_eval_exprlist_determ eval_exprlist. 
        hexploit external_call_determ; [eapply H0|eapply H13|]. i. des.
        inv H. hexploit H1; et. i. des. clarify. }
      { determ Clight_eval_exprlist_determ eval_exprlist. 
        hexploit external_call_determ; [eapply H0|eapply H13|]. i. des.
        inv H. hexploit H1; et. }
      { inv_pred function_entry2. determ alloc_variables_determ alloc_variables. }
      { hexploit external_call_determ; [eapply H|eapply H9|]. i. des.
        inv H0. hexploit H1; et. i. des. clarify. }
      { hexploit external_call_determ; [eapply H|eapply H9|]. i. des.
        inv H0. hexploit H1; et. } }
    { i. inv FINAL. inv STEP. }
    { i. inv FINAL0. inv FINAL1. ss. }
  Qed.

End PROOF.

