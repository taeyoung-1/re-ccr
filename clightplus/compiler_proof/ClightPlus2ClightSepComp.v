From compcert Require Import Coqlib Behaviors Integers Floats AST Globalenvs Ctypes Cop Clight Clightdefs.

Require Import CoqlibCCR.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import IRed.

Require Import ClightPlusMem0.
Require Import ClightPlusExprgen ClightPlusgen ClightPlusSkel.

Require Import ClightPlus2ClightMatchEnv.
Require Import ClightPlus2ClightArith.
Require Import ClightPlus2ClightLenv.
Require Import ClightPlus2ClightMem.
Require Import ClightPlus2ClightMatchStmt.

Require Import STS2SmallStep.
Require Import ClightPlus2ClightSimExpr.
Require Import ClightPlus2ClightSimStmt.
Require Import ClightPlus2ClightSim.

Require Import ClightPlus2ClightGenv.
(* Require Import ClightPlus2ClightLink. *)

Require Import Admit.

Section PROOFSINGLE.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0. (* these are itree normalization tactic *)
  Ltac sim_tau := (try sim_red); try pfold; econs 3; ss; clarify; eexists; exists (ModSemL.step_tau _).

  Ltac solve_ub := des; irw in H; dependent destruction H; clarify.
  Ltac sim_triggerUB := 
    (try rename H into HH); ss; unfold triggerUB; try sim_red; try pfold; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  Let arrow (A B: Prop): Prop := A -> B.
  Opaque arrow.

  Let oeq [A] (a: A) b: Prop := (a = b).
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

  Ltac tgt_step := try pfold; econs 4; eexists; eexists.

  Ltac wrap_up := try pfold; econs 7; et; right.

  Definition compile_val mdl := @ModL.compile _ EMSConfigC mdl.

  Definition clightp_sem sk_mem md := compile_val (ModL.add (Mod.lift (Mem sk_mem)) (Mod.lift md)).

  Definition clightp_initial_state sk_mem md := (clightp_sem sk_mem md).(STS.initial_state).

  Local Opaque ident_of_string.
  Arguments Es_to_eventE /.
  Arguments itree_of_stmt /.
  Arguments sloop_iter_body_two /.
  Arguments ktree_of_cont_itree /.

  (* mem initialization condition : every Gvar has aligned and every Gvar address is in genv *)
  (* src align <-> tgt align is valid, Gvar is remain in both *)
  (* second condition makes src valid addr -> tgt valid addr but not inverse *)
  (* so, src init succ -> tgt init succ *)
  (* compiler should check whether src init is a success *)
  Lemma compile_init_mem_success clight_prog mn md sk_mem:
    compile clight_prog mn = Some md ->
    mem_skel clight_prog = Some sk_mem ->
    exists m tm,
    load_mem (Sk.canon (Sk.add sk_mem (Mod.sk md))) = Some m 
    /\ Genv.init_mem clight_prog = Some tm
    /\ match_mem (Sk.canon (Sk.add sk_mem (Mod.sk md))) (globalenv clight_prog) m tm.
  Proof.
  Admitted.


  (* The thm is targeting closed program *)
  Theorem single_compile_behavior_improves
          clight_prog md sk_mem mn left_st right_st
          (COMP: compile clight_prog mn = Some md)
          (MEMSKEL: mem_skel clight_prog = Some sk_mem)
          (SINIT: left_st = clightp_initial_state sk_mem md)
          (TINIT: Clight.initial_state clight_prog right_st)
        :
          <<IMPROVES: @improves2 _ (Clight.semantics2 clight_prog) left_st right_st>>.
  Proof.
    eapply adequacy; eauto.
    { apply Clight_wf_semantics. }
    red. ss; clarify. unfold clightp_initial_state. ss; clarify. inv TINIT.
    unfold ModSemL.initial_itr. unfold ge in *. clear ge.
    rename H into INIT_TMEM, H0 into TMAINN_TBLOCK, H1 into TBLOCK_TMAINF, H2 into TMAIN_TYPE, f into tmainf.

    (* remove not-wf-(mem+md) case *)
    unfold ModL.wf_bool. destruct ModL.wf_dec; ss; [|sim_triggerUB].
    grind. unfold ITree.map. sim_red.

    (* if we find "main" in md, prog_main clight_prog in clight_prog, two functions should have same compilation relation *)
    destruct (alist_find "main" _) eqn:SMAINN_MAINF;[|sim_triggerUB].
    rewrite alist_find_map_snd in SMAINN_MAINF. uo; des_ifs; ss.
    hexploit in_tgt_prog_defs_decomp; et. i. des. clarify.
    hexploit in_tgt_prog_main; et. i. rewrite H in *.
    hexploit tgt_genv_match_symb_def; et. { unfold Genv.find_funct_ptr in TBLOCK_TMAINF. des_ifs. }
    i. clarify. rename f into tmainf.

    unfold cfunU. sim_red. unfold decomp_func. sim_red.
    change (paco4 (_sim _ _) bot4) with (sim (clightp_sem sk_mem md) (semantics2 clight_prog)).
    eapply sim_bot_flag_up with (b0 := true) (b1 := false).

    set (sort _) as sk_init in *.
    hexploit compile_match_genv; et. i.
    hexploit compile_init_mem_success; et. i. des. rewrite H3 in INIT_TMEM. clarify.
    eapply step_function_entry with (modl:=md) (ge:=globalenv clight_prog) (sk:=sk_init); et.
    { unfold get_ce. ss. econs. split; i.
      - apply alist_find_some_iff; et. rewrite CoqlibC.NoDup_norepet. apply Maps.PTree.elements_keys_norepet.
      - eapply alist_find_some; et. }
    { unfold sk_init. ss. rewrite H2. et. }
    i. pfold. econs 4. { i. inv H9. et. } { eexists. econs. et. }
    i. inv STEP. ss. unfold hide in H5. inv H5. inv H14.
    rewrite H13 in *. clarify. hexploit alloc_variables_determ;[apply H12|apply H17|].
    i. des. clarify. econs 8; et. left.

    eapply match_states_sim; et.
    { i. ss. clear - COMP H14. unfold compile, get_sk in COMP. des_ifs. ss.
      clear - H14. apply in_map_iff in H14. des. destruct x. ss. clarify.
      apply filter_In in H0. des. ss. des_ifs. et. }
    { i. clear -MEMSKEL H14. unfold mem_skel, get_sk in MEMSKEL. des_ifs.
      apply in_map_iff in H14. des. destruct x. ss. clarify. bsimpl. des.
      apply incl_filter in H0. rewrite forallb_forall in Heq3.
      hexploit Heq3; et. i. ss. destruct Pos.eq_dec; clarify. }
    { i. clear -MEMSKEL H14. unfold mem_skel, get_sk in MEMSKEL. des_ifs.
      apply in_map_iff in H14. des. destruct x. ss. clarify. bsimpl. des.
      apply incl_filter in H0. rewrite forallb_forall in Heq3.
      hexploit Heq3; et. i. ss. destruct Pos.eq_dec; clarify. }
    { i. clear -MEMSKEL H14. unfold mem_skel, get_sk in MEMSKEL. des_ifs.
      apply in_map_iff in H14. des. destruct x. ss. clarify. bsimpl. des.
      apply incl_filter in H0. rewrite forallb_forall in Heq3.
      hexploit Heq3; et. i. ss. destruct Pos.eq_dec; clarify. }
    { set (update _ _ _) as init_pstate. econs; et. 
      { instantiate (1:=get_ce clight_prog). unfold get_ce. ss. econs. split; i.
        - apply alist_find_some_iff; et. rewrite CoqlibC.NoDup_norepet. apply Maps.PTree.elements_keys_norepet.
        - eapply alist_find_some; et. }
      { instantiate (1:= init_pstate). unfold init_pstate. unfold update. ss. }
      { admit "internal_proof". }
      (* { unfold fnsem_has_internal. i. apply Sk.sort_incl_rev in H5. ss. des; clarify.
        { apply Any.upcast_inj in H5. des. apply JMeq_eq in EQ0. clarify. }
        { apply Any.upcast_inj in H5. des. apply JMeq_eq in EQ0. clarify. }
        exists mn.
        admit "relation between decomp_fundef and get_sk". } *)
      { econs; et. }
      instantiate (1 := mn). 
      admit "itree eq". }
  Qed.

  Theorem single_compile_program_improves
          (types: list Ctypes.composite_definition)
          (defs: list (AST.ident * AST.globdef Clight.fundef Ctypes.type))
          (public: list AST.ident)
          (WF_TYPES: Clightdefs.wf_composites types)
          mn clight_prog
          (WFDEF_NODUP: NoDup (List.map fst defs))
          (WFDEF_EXT: forall a, In a Mem.(Mod.sk) -> In a (List.map (fun '(p, gd) => (string_of_ident p, gd↑)) defs))
          (COMP: clight_prog = mkprogram types defs public (ident_of_string "main") WF_TYPES)
    :
      <<IMPROVES: improves2_program (clightligt_sem types defs WF_TYPES mn) (Clight.semantics2 clight_prog)>>.
  Proof.
    red. unfold improves2_program. i. inv BEH.
    { hexploit single_compile_behavior_improves.
      1,2,3: et. 1: refl. 1: ss; et. unfold improves2, clightlight_initial_state. i.
      eapply H1; et. }
    (* initiall wrong case, for us only when main is not found *)
    exists (Tr.ub). split; red; eauto.
    2:{ pfold. econs 4; eauto.
        - ss.
        - unfold Behaviors.behavior_prefix. exists (Behaviors.Goes_wrong Events.E0). ss.
    }
    Print Clight.initial_state.
    ss. unfold ModSemL.initial_itr.
    pfold. econs 6; ss; eauto.
    unfold Beh.inter. ss. unfold assume. grind.
    apply ModSemL.step_trigger_take_iff in STEP. des. clarify. split; eauto.
    red. unfold ITree.map; ss.
    unfold unwrapU. des_ifs.
    (* main do not exists, ub *)
    2:{ sim_red. unfold triggerUB. grind. econs 6; ss. grind. ss. apply ModSemL.step_trigger_take_iff in STEP. des. clarify. }

    (* found main, contradiction *)
    exfalso.
    rename Heq into FSEM.
    grind. rewrite alist_find_find_some in FSEM. rewrite find_map in FSEM.
    match goal with
    | [ FSEM: o_map (?a) _ = _ |- _ ] => destruct a eqn:FOUND; ss; clarify
    end.
    destruct p as [? ?]; ss; clarify. rewrite find_map in FOUND.
    uo. des_ifs_safe.
    eapply found_itree_clight_function in Heq. des; clarify.
    assert (exists f, In (p0, Gfun (Internal f)) defs).
    { clear -Heq0 Heq. set (Sk.sort _) as sk in *. clearbody sk.
      revert_until defs. induction defs; et.
      i. ss. destruct a. destruct g.
      - destruct f.
        + ss. destruct Heq0.
          * clarify. et. 
          * eapply IHdefs in H; et. des. et.
        + eapply IHdefs in Heq0; et. des. et.
      - eapply IHdefs in Heq0; et. des. et. }
    des. replace defs with (mkprogram types defs public (ident_of_string "main") WF_TYPES).(AST.prog_defs) in H0 by solve_mkprogram.
    hexploit Globalenvs.Genv.find_symbol_exists; et. i. des.
    hexploit tgt_genv_find_def_by_blk; eauto. 1:{ admit "provable". }
    i. assert (exists m, Genv.init_mem (mkprogram types defs public (ident_of_string "main") WF_TYPES) = Some m) by admit "hypothesis".
    des. 
    specialize H with (Callstate (Internal f) [] Kstop m).
    eapply H.
    econs; ss; eauto.
    { solve_mkprogram. ss. replace (ident_of_string "main") with p0 by admit "provable". et. }
    { unfold Genv.find_funct_ptr. rewrite H3. et. }
    admit "hypothesis".
    Unshelve. inv Heq0.
  Qed.

End PROOFSINGLE.
