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

From compcert Require Import Ctypes Clight Clightdefs Values.

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

  Lemma _step_eval pstate ge ce f_table modl cprog defs sk le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: ce = ge.(genv_cenv)) 
    (EQ2: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge defs sk ge)
    (ME: match_e defs e te)
    (MLE: match_le defs le tle)
    (MM: match_mem defs m tm)
 r b tcode tf tcont mn a
 :
  (forall ktr1,
    (forall blk blk' ofs bf, 
      eval_lvalue ge te tle tm a blk ofs bf ->
      blk = map_blk defs blk' ->
      paco4
        (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
        (ktr1 (pstate, (blk', (ofs, bf))))
        (State tf tcode tcont te tle tm)) 
    ->
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * (Values.block * (ptrofs * bitfield))) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_lvalue_c sk ce e le a)) 
          pstate);; ktr1 r0)
      (State tf tcode tcont te tle tm)) 
  /\
  (forall ktr2,
    (forall v v', 
      eval_expr ge te tle tm a v ->
      v = map_val defs v' ->
      paco4
        (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
        (ktr2 (pstate, v'))
        (State tf tcode tcont te tle tm)) 
    ->
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * Values.val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_expr_c sk ce e le a))
          pstate);; ktr2 r0)
      (State tf tcode tcont te tle tm)). 
  Proof.
    induction a.
    - split; i; try solve [ss; try sim_red; sim_triggerUB].
      ss. sim_red. eapply H; try econs.
    - split; i; try solve [ss; try sim_red; sim_triggerUB].
      ss. sim_red. eapply H; try econs.
    - split; i; try solve [ss; try sim_red; sim_triggerUB].
      ss. sim_red. eapply H; try econs.
    - split; i; try solve [ss; try sim_red; sim_triggerUB].
      ss. sim_red. eapply H; try econs.
    - split; i.
      + ss.  admit "stubborn case".
        (* des_ifs; sim_red; try solve [sim_triggerUB].
        * eapply H; et. econs. inv ME. apply ME0. et.
        * eapply H; et. econs 2. inv ME.
          { destruct (Maps.PTree.get i te) eqn:E; et. 
            (* TODO: find appropriate env property *)
            admit "stack block has 1:1 property". }
          inv MGE. unfold Genv.find_symbol. eapply S2B_MATCH in Heq0.
          (* TODO: FILL THE BLANK *)
          admit "Heq0 is equal to conclusion". *)
      + ss. des_ifs; sim_red; try solve [sim_triggerUB].
        * unfold deref_loc_c. des_ifs.
          2:{ sim_red. eapply H; et. { econs. { econs. inv ME. apply ME0. et. } { econs 2; et. } } }
          2:{ sim_red. eapply H; et. { econs. { econs. inv ME. apply ME0. et. } { econs 3; et. } } }
          2:{ sim_red. sim_triggerUB. }
          unfold ccallU. sim_red. ss. sim_tau. unfold loadF. sim_red. sim_tau.
          sim_red. sim_tau. sim_red. sim_tau. sim_red. rewrite PSTATE.
          rewrite Any.upcast_downcast. sim_red. unfold unwrapU.
          des_ifs; try sim_red; try solve [sim_triggerUB]. sim_tau. sim_red.
          rewrite Any.upcast_downcast. sim_red. eapply H; et. econs.
          { econs. inv ME. apply ME0. et. }
          { econs; et. 
            (* TODO: make match_load lemma *)
           admit "need_match_load lemma". }
        * unfold deref_loc_c. des_ifs.
          2:{ sim_red. eapply H; et. { admit "same probelm with stubborn case". } }
          2:{ sim_red. eapply H; et. { admit "same probelm with stubborn case". } }
          2:{ sim_red. sim_triggerUB. }
          unfold ccallU. sim_red. ss. sim_tau. unfold loadF. sim_red. sim_tau.
          sim_red. sim_tau. sim_red. sim_tau. sim_red. rewrite PSTATE.
          rewrite Any.upcast_downcast. sim_red. unfold unwrapU.
          des_ifs; try sim_red; try solve [sim_triggerUB]. sim_tau. sim_red.
          rewrite Any.upcast_downcast. sim_red. eapply H; et. 
          admit "same probelm with stubborn case".
        * unfold deref_loc_c. destruct (access_mode t0).
          2:{ sim_red. eapply H; et. { admit "same probelm with stubborn case". } }
          2:{ sim_red. eapply H; et. { admit "same probelm with stubborn case". } }
          2:{ sim_red. sim_triggerUB. }
          unfold ccallU. sim_red. ss. sim_tau. unfold loadF. sim_red. sim_tau.
          sim_red. sim_tau. sim_red. sim_tau. sim_red. rewrite PSTATE.
          rewrite Any.upcast_downcast. sim_red. unfold unwrapU.
          destruct (Mem.load _ _ _ _); try sim_red; try solve [sim_triggerUB]. sim_tau. sim_red.
          rewrite Any.upcast_downcast. sim_red. eapply H; et. 
          admit "same probelm with stubborn case".
    - split; i; try solve [ss; try sim_red; sim_triggerUB].
      ss. unfold unwrapU. des_ifs; try sim_red; try sim_triggerUB.
      eapply H; et. econs. inv MLE. eapply ML. et.
    - des. split; i.
      + ss. sim_red. eapply IHa0. i. destruct v'; try sim_red; try sim_triggerUB.
        eapply H; et. econs. subst. et.
      + ss. sim_red. eapply IHa0. i. destruct v'; try sim_red; try sim_triggerUB.
        subst. unfold deref_loc_c. destruct (access_mode t0) eqn : E.
        2:{ sim_red. eapply H; et. econs. { econs. ss. et. } { econs 2. et. } } 
        2:{ sim_red. eapply H; et. econs. { econs. ss. et. } { econs 3. et. } }
        2:{ sim_red. sim_triggerUB. }
        unfold ccallU. sim_red. ss. sim_tau. unfold loadF. sim_red. sim_tau.
        sim_red. sim_tau. sim_red. sim_tau. sim_red. rewrite PSTATE.
        rewrite Any.upcast_downcast. sim_red. unfold unwrapU.
        destruct (Mem.load _ _ _ _) eqn: E1; try sim_red; try solve [sim_triggerUB]. sim_tau. sim_red.
        rewrite Any.upcast_downcast. sim_red. eapply H; et. 
        econs. { econs. et. } 
        { econs; et. ss. admit "memory load match". }
    - des. split; i; try solve [ss; try sim_red; sim_triggerUB].
      ss. sim_red. eapply IHa. i. subst. destruct bf; try sim_red; try sim_triggerUB.
      eapply H; et. { econs. et. }
    - des. split; i; try solve [ss; try sim_red; sim_triggerUB].
      ss. sim_red. eapply IHa0. i. subst. sim_red.
      admit "have to make unary op lemma".
    - des. split; i; try solve [ss; try sim_red; sim_triggerUB].
      ss. sim_red. eapply IHa3. i. subst. sim_red.
      eapply IHa0. i. subst. sim_red.
      admit "have to make binary op lemma".
    - des. split; i; try solve [ss; try sim_red; sim_triggerUB].
      ss. sim_red. eapply IHa0.
      admit "have to make sem_cast lemma".
    - des. split; i.
      + ss. sim_red. eapply IHa0. i. subst. des_ifs; try sim_red; try sim_triggerUB.
        { unfold unwrapU. des_ifs; try sim_red; try sim_triggerUB.
          des_ifs; try sim_red; try sim_triggerUB. eapply H; et. 
          econs; et. }
        { unfold unwrapU. des_ifs; try sim_red; try sim_triggerUB.
          des_ifs; try sim_red; try sim_triggerUB. eapply H; et.
          econs 5; et. }
      + ss. sim_red. eapply IHa0. i. subst. des_ifs; try sim_red; try sim_triggerUB.
        { unfold unwrapU. des_ifs; try sim_red; try sim_triggerUB.
          des_ifs; try sim_red; try sim_triggerUB.
          admit "deref_loc lemma needed". }
        { unfold unwrapU. des_ifs; try sim_red; try sim_triggerUB.
          des_ifs; try sim_red; try sim_triggerUB.
          admit "deref_loc lemma needed". }
    - des. split; i; try solve [ss; sim_red; sim_triggerUB].
      ss. sim_red. eapply H; et. unfold Vptrofs. des_ifs_safe. simpl.
      econs.
    - des. split; i; try solve [ss; sim_red; sim_triggerUB].
      ss. sim_red. eapply H; et. unfold Vptrofs. des_ifs_safe. simpl.
      econs.
  Qed.
    

  Lemma step_eval_lvalue pstate ge ce f_table modl cprog defs sk le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: ce = ge.(genv_cenv)) 
    (EQ2: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge defs sk ge)
    (ME: match_e defs e te)
    (MLE: match_le defs le tle)
    (MM: match_mem defs m tm)
 r b tcode tf tcont mn a ktr
    (NEXT: forall blk blk' ofs bf, 
            eval_lvalue ge te tle tm a blk ofs bf ->
            blk = map_blk defs blk' ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, (blk', (ofs, bf))))
              (State tf tcode tcont te tle tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * (Values.block * (ptrofs * bitfield))) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_lvalue_c sk ce e le a)) 
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof. hexploit _step_eval; et. i. des. et. Qed.

  Lemma step_eval_expr pstate ge ce f_table modl cprog defs sk le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: ce = ge.(genv_cenv)) 
    (EQ2: f_table = (ModL.add Mem modl).(ModL.enclose))
    (MGE: match_ge defs sk ge)
    (ME: match_e defs e te)
    (MLE: match_le defs le tle)
    (MM: match_mem defs m tm)
 r b tcode tf tcont mn a ktr
    (NEXT: forall v v', 
            eval_expr ge te tle tm a v ->
            v = map_val defs v' ->
            paco4
              (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
              (ktr (pstate, v'))
              (State tf tcode tcont te tle tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add Mem modl)) (semantics2 cprog)) r true b
      (`r0: (p_state * Values.val) <- 
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_expr_c sk ce e le a))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm). 
  Proof. hexploit _step_eval; et. i. des. et. Qed.
          


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
        (transl_all mn (free_list_aux (ConvC2ITree.blocks_of_env ce e))) 
        pstate)
      ;; ktr r0) 
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


  Arguments Es_to_eventE /.
  Arguments itree_of_code /. 
  Arguments sloop_iter_body_two /. 
  Arguments ktree_of_cont_itree /. 

  Theorem match_states_sim
          types defs WF_TYPES mn
          (modl: ModL.t) ms sk
          clight_prog ist cst
          (* WFDEF may not needed *)
          (WFDEF: NoDup (List.map (fun '(id, _) => id) defs))
          (WFDEF2: forall p gd , In (p, gd) defs -> exists s, ident_of_string s = p)
          (MODL: modl = ModL.add (Mod.lift Mem) (Mod.lift (get_mod types defs WF_TYPES mn)))
          (MODSEML: ms = modl.(ModL.enclose))
          (SK: sk = Sk.sort modl.(ModL.sk))
          (TGT: clight_prog = mkprogram types defs (List.map (fun '(gn, _) => gn) defs) (ident_of_string "main") WF_TYPES)
          (MGENV: match_ge defs sk (Genv.globalenv clight_prog))
          (MS: match_states sk (Ctypes.prog_comp_env clight_prog) ms defs ist cst)
  :
      <<SIM: sim (@ModL.compile _ EMSConfigC modl) (Clight.semantics2 clight_prog) false false ist cst>>.
  Proof.
    red. red.
    depgen ist. depgen cst. pcofix CIH. i.
    inv MS. unfold mkprogram in *. des_ifs_safe.
    set (Genv.globalenv _) as ge in MGENV. set {| genv_genv := ge; genv_cenv := x|} as gh.
    destruct tcode.
    - ss. sim_red. sim_tau. sim_red.
      destruct tcont; inv MCONT; ss; clarify.
      { sim_red. sim_triggerUB. }
      { sim_red. tgt_step; [econs|]. wrap_up. apply CIH. econs; et. }
      { sim_red. tgt_step; [econs; et|]. wrap_up. apply CIH. econs; et. { econs; et. } sim_redE.
        erewrite bind_extk; et. i. des_ifs_safe. repeat (des_ifs; sim_redE; try reflexivity). }
      { sim_red. tgt_step; [econs; et|]. wrap_up. apply CIH. econs; et. }
      { sim_red. eapply step_freeing_stack; et. 
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
        { ss. sim_redE. f_equal. f_equal. sim_redE. et. } }
    - ss. unfold _sassign_c. sim_red. sim_tau. sim_red. eapply step_eval_lvalue; et.
      1,2 : admit "fuck you". i. subst. sim_red. eapply step_eval_expr; et.
      1,2 : admit "fuck you". i. subst. sim_red. 

  Admitted.

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