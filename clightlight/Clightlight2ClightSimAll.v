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
  Ltac sim_tau := (try sim_red); pfold; econs 3; ss; clarify; eexists; exists (step_tau _); left.

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
    (try rename H into HH); ss; unfold triggerUB; try sim_red; pfold; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  Ltac tgt_step := pfold; econs 4; eexists; eexists; [|left].

  Ltac wrap_up := pfold; econs 7; et; right.

  Ltac remove_UBcase := des_ifs; try sim_red; try sim_triggerUB.

  Ltac dtm H H0 := eapply angelic_step in H; eapply angelic_step in H0; des; rewrite H; rewrite H0; ss.

  Local Opaque Pos.of_nat.

  Local Opaque Pos.of_succ_nat.


  (* (**** At the moment, it suffices to support integer IO in our scenario,
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
  . *)

  Lemma step_freeing_stack cprog f_table modl r b1 b2 ktr tstate ge ce e pstate mn (PSTATE: exists m: mem, pstate "Mem"%string = m↑) (EQ: ce = ge.(genv_cenv)) (EQ2: f_table = (ModL.add Mem modl).(ModL.enclose)) :
  paco4
    (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r (match (blocks_of_env ge e) with [] => b1 | _ => true end) b2
    (m <- (pstate "Mem")↓?;; m <- (Mem.free_list m (blocks_of_env ge e))?;; ktr (update pstate "Mem" m↑, ()))
    tstate
  ->
  paco4
    (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r b1 b2
    (`r0: (p_state * ()) <- 
      (EventsL.interp_Es (prog f_table)
        (transl_all mn (free_list_aux (ConvC2ITreeStmt.blocks_of_env ce e))) 
        pstate)
      ;; ktr r0) 
    tstate.
  Proof.
    rewrite EQ. rewrite EQ2. clear EQ ce EQ2 f_table. des. replace (ConvC2ITreeStmt.blocks_of_env ge e) with (blocks_of_env ge e) by auto.
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
    - ss. remove_UBcase. eapply NEXT. econs.
    - ss. remove_UBcase. eapply step_eval_expr with (ge:=ge); et. i. sim_red. eapply IHal. i.
      sim_red. eapply step_sem_cast; et. i. destruct optv; remove_UBcase. eapply NEXT. econs; et.
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
  Admitted.

  Lemma step_external_call pstate ge ce f_table modl cprog sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: ce = ge.(genv_cenv)) 
    (EQ2: tge = ge.(genv_genv)) 
    (EQ3: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    i extfun targs tres cc vl
 r b o tf tcont (mn: string) ktr 
    (NEXT: forall tr m' tm' vres, 
            external_call extfun ge (List.map (map_val sk tge) vl) tm tr (map_val sk tge vres) tm' ->
            match_mem sk tge m' tm' ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true true
              (ktr (update pstate "Mem" m'↑, vres↑))
              (Returnstate (map_val sk tge vres) (Kcall o tf te tle tcont) tm'))
  :
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * Any.t) <- 
        (EventsL.interp_Es
          (prog f_table)
          (i (Some mn, vl↑))
          pstate);; ktr r0)
      (Callstate (External extfun targs tres cc) (List.map (map_val sk tge) vl) (Kcall o tf te tle tcont) tm). 
  Proof.
  Admitted.
  (* axiom *)

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
  Admitted.

  Arguments Es_to_eventE /.
  Arguments itree_of_code /. 
  Arguments sloop_iter_body_two /. 
  Arguments ktree_of_cont_itree /. 
  Opaque MemSem.

  Lemma unfold_itree_iter A B eff (f : A -> itree eff (A + B)) (x: A)  :
          ITree.iter f x = `lr : A + B <- f x;;
                           match lr with
                            | inl l => tau;; ITree.iter f l
                            | inr r => Ret r
                           end.
  Proof.
    eapply bisim_is_eq. apply unfold_iter.
  Qed.

  Theorem match_states_sim
          types sk defs WF_TYPES
          (modl internal_modl external_modl: ModL.t) ms
          clight_prog ist cst
          (MODL: modl = ModL.add (Mod.lift Mem) (ModL.add external_modl internal_modl))
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
    set (ModL.sk _) as sk in *.
    set (ModL.add _ _) as modl in *.
    set {| genv_genv := tge; genv_cenv := x|} as ge.
    destruct tcode.
    - ss. sim_red. 
      destruct tcont; inv MCONT; ss; clarify.
      { sim_red. sim_triggerUB. }
      { sim_red. tgt_step; [econs|]. sim_tau. wrap_up. apply CIH. econs; et. }
      { sim_red. tgt_step; [econs; et|]. sim_tau. wrap_up. apply CIH. econs; et. { econs; et. }
        sim_redE. apply bind_extk. i. des_ifs_safe.
        repeat (des_ifs; sim_redE; try reflexivity). }
      { sim_red. tgt_step; [econs; et|]. sim_tau. sim_red. sim_tau. wrap_up. apply CIH.
        econs; et. }
      { sim_red. sim_tau. sim_red. eapply step_freeing_stack with (ge := ge); et. 
        rewrite PSTATE. sim_red. unfold unwrapU in *.
        destruct (Mem.free_list m _) eqn: STACK_FREE; try sim_triggerUB.
        inv ME. hexploit match_mem_free_list; et. i. des. 
        sim_red. tgt_step. 
        { econs; unfold is_call_cont; et. unfold semantics2, globalenv. ss.
          rewrite <- TMEM. f_equal. replace _ with ge by et. 
          set (fun _ => _) as g. clear - ME0.  
          unfold blocks_of_env, block_of_binding.
          rewrite ME0.
          set (fun id_b_ty : _ * (_ * _) => _) as f.
          set (map_env_entry _ _) as h.
          rewrite List.map_map with (f := f).
          replace (g ∘ f) with (f ∘ h); try rewrite List.map_map; et.
          unfold f, g, h. apply func_ext. i. des_ifs_safe. ss. clarify. }
        sim_tau.
        tgt_step; [econs|]. pfold. econs 7;[|des_ifs|];et. right. eapply CIH.
        econs. 5: apply MM_POST. all: et. 
        { hexploit match_update_le; et. instantiate (2 := Vundef). ss. et. }  
        { instantiate (1 := update pstate "Mem" (Any.upcast m0)). ss. }
        { et. ss. sim_redE. et. } }
    - ss. unfold _sassign_c. sim_red. sim_tau. sim_red.
      eapply step_eval_lvalue with (ge := ge); et. i. subst. sim_red. 
      eapply step_eval_expr with (ge := ge); et. i. subst. sim_red. 
      eapply step_sem_cast; et. i.
      unfold unwrapU. des_ifs; try sim_red; try sim_triggerUB.
      eapply step_assign_loc; et. i. sim_red.
      tgt_step. { econs; et. } wrap_up. eapply CIH. 
      econs. 4:{ instantiate (2 := update pstate "Mem" m'↑). unfold update. ss. } 
      all: et. ss. sim_redE. et. 
    - ss. sim_red. sim_tau. sim_red. eapply step_eval_expr with (ge := ge); et. i. subst. sim_red. 
      tgt_step. { econs; et. } wrap_up. eapply CIH. econs; et.
      { change (Maps.PTree.set i _ _) with (set_opttemp (Some i) (map_val sk ge v') tle). eapply match_update_le; et. }
      ss. sim_redE. et. 
    - ss. unfold _scall_c. remove_UBcase. sim_tau. sim_red. eapply step_eval_expr with (ge := ge); et. i. sim_red.
      eapply step_eval_exprlist with (ge := ge); et. i. remove_UBcase. destruct (nth_error _) eqn: E; remove_UBcase.
      destruct p. destruct (Any.downcast _) eqn: E1; remove_UBcase. remove_UBcase. remove_UBcase.
      unfold ccallU. sim_red. repeat (sim_tau; sim_red).
      (* rewrite app_assoc. rewrite alist_find_app_o. *)
      assert (SkEnv.blk2id (Sk.load_skenv sk) (pred (Pos.to_nat b)) = Some s).
      { Transparent Sk.load_skenv. unfold Sk.load_skenv. ss. rewrite E. ss. }
      inv MGE. apply Sk.load_skenv_wf in WFSK. apply WFSK in H0. rewrite <- (string_of_ident_of_string s) in H0.
      apply MGE0 in H0. unfold unwrapU. remove_UBcase.
      tgt_step.
      { econs; ss; et; admit "". }
      destruct f.
      + assert (exists mn, i0 = fun '(optmn, a) => transl_all mn (cfunU (decomp_func (eff := Es) sk x f) (optmn, a))).
        { admit "". }
        des. rewrite H2. ss. sim_red.
        unfold decomp_func. sim_red. eapply step_function_entry with (ge := ge); et.
        { admit "". }
        i. sim_red. 
        tgt_step.
        { econs; et. }
        wrap_up. eapply CIH. econs. 5: apply H4. all: et.
        { admit "". }
        { instantiate (1 := update pstate "Mem" m'↑). et. }
        { econs; et. }
        sim_redE.
        set (prog _) as t1.
        instantiate (1:= mn0).
        apply bind_extk. i. des_ifs_safe. unfold itree_of_cont_pop. sim_redE.
        destruct o0.
        { sim_redE. apply bind_extk. i. des_ifs_safe. sim_redE. f_equal. f_equal.
          sim_redE. rewrite Any.upcast_downcast. sim_redE. et. }
        destruct o1.
        { apply bind_extk. i. des_ifs_safe. sim_redE.
          apply bind_extk. i. sim_redE. f_equal. f_equal. sim_redE. 
          rewrite Any.upcast_downcast. sim_redE. et. }
        sim_redE. f_equal. f_equal. apply bind_extk. i. des_ifs_safe. sim_redE.
        apply bind_extk. i. sim_redE. f_equal. f_equal.
        sim_redE. rewrite Any.upcast_downcast. sim_redE. et.
      + ss. clarify.
        eapply step_external_call with (ge := ge); et.
        { admit "". }
        i. sim_red. 
        tgt_step.
        { econs. } 
        sim_tau.
        wrap_up. eapply CIH. econs. 5: eapply H3. all: et.
        { admit "". }
        { apply match_update_le; et. }
        { instantiate (1 := update pstate "Mem" m'↑). et. }
        ss. sim_redE. rewrite Any.upcast_downcast. sim_redE. et.
    - (* undefined *)
      sim_triggerUB.
    - ss. sim_red. sim_tau. tgt_step.
      { econs. }
      wrap_up. eapply CIH. econs; et.
      { econs; et. }
      ss. sim_redE. apply bind_extk. i. des_ifs_safe.
      unfold itree_of_cont_pop.
      destruct o0.
      { sim_redE. et. }
      destruct o.
      { sim_redE. et. }
      sim_redE. et.
    - ss. sim_red. unfold _site_c. sim_red. sim_tau.
      sim_red. eapply step_eval_expr with (ge := ge); et.
      i. sim_red. eapply step_bool_val; et. i. unfold unwrapU. remove_UBcase.
      tgt_step.
      { econs; et. }
      wrap_up. eapply CIH. econs; et.
      destruct b; sim_redE; et.
    - ss. unfold _sloop_itree. rewrite unfold_itree_iter.
      ss. unfold sloop_iter_body_one. sim_red. sim_tau.
      tgt_step. { econs. } 
      wrap_up. eapply CIH. econs; et.
      { econs; et. }
      unfold _sloop_itree.
      sim_redE. apply bind_extk. i. 
      unfold itree_of_cont_pop. des_ifs_safe.
      destruct o.
      { sim_redE. et. }
      destruct o0.
      { destruct b. 
        { sim_redE. do 2 f_equal. sim_redE. et. }
        sim_redE. do 2 f_equal. sim_redE. apply bind_extk. i. des_ifs_safe.
        sim_redE. destruct o; sim_redE; et.
        destruct o0. 
        { destruct b.
          { sim_redE. do 2 f_equal. sim_redE. et. }
          apply bind_extk. i. 
          des_ifs_safe. destruct o; sim_redE; et.
          do 2 f_equal. sim_redE. et. }
        sim_redE. do 2 f_equal. sim_redE. do 2 f_equal. sim_redE. et. }
      sim_redE. do 2 f_equal. sim_redE. apply bind_extk. i. des_ifs_safe.
      destruct o.
      { sim_redE; et. }
      destruct o0.
      { apply bind_extk. i. des_ifs_safe. destruct o; sim_redE; et.
        do 2 f_equal. sim_redE. et. }
      sim_redE. do 2 f_equal. sim_redE. do 2 f_equal. sim_redE. et.
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
    - 


        
        

  Admitted.


  (* Ltac rewriter :=
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
  Qed. *)