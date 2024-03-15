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

  Definition mem_keywords := List.map ident_of_string ["malloc"; "free"; "capture"].

  Definition sk_mem (clight_prog: Clight.program) := List.map (map_fst string_of_ident) (List.filter (fun x => in_dec Pos.eq_dec (fst x) mem_keywords) (prog_defs clight_prog)).

  Local Opaque ident_of_string.
  Arguments Es_to_eventE /.
  Arguments itree_of_stmt /.
  Arguments sloop_iter_body_two /.
  Arguments ktree_of_cont_itree /.

  Lemma asdf' clight_prog mn md str gd:
    compile clight_prog mn = Some md ->
    In (str, gd) (Sk.canon (Sk.add (sk_mem clight_prog) (Mod.sk md))) ->
    In (ident_of_string str, gd) (prog_defs clight_prog).
  Proof.
    i. unfold compile in H. unfold get_sk in H. des_ifs. ss. bsimpl. des.
    let x := type of Sk.le_canon_rev in
    let y := eval red in x in
    eapply (Sk.le_canon_rev: x) in H0.
    ss. apply in_map with (f:=(map_fst ident_of_string)) in H0. ss.
    unfold Sk.add in H0. ss. rewrite map_app in H0. rewrite List.in_app_iff in H0.
    unfold sk_mem in H0. clear - H0 Heq1. revert_until clight_prog.
    generalize (prog_defs clight_prog). clear. induction l; i; ss; try tauto.
    des_ifs.
    - ss. bsimpl. des.
      + left. destruct a. ss. clarify. rewrite string_of_ident_of_string in H1. f_equal; et.
      + right. eapply IHl; et.
      + left. destruct a. ss. clarify. rewrite string_of_ident_of_string in H1. f_equal; et.
      + right. eapply IHl; et.
    - ss. bsimpl. des; clarify.
      + left. destruct a. ss. clarify. rewrite string_of_ident_of_string in H1. f_equal; et.
      + left. destruct a. ss. clarify. rewrite string_of_ident_of_string in H1. f_equal; et.
      + right. eapply IHl; et.
      + right. eapply IHl; et.
      + left. destruct a. ss. clarify. rewrite string_of_ident_of_string in H1. f_equal; et.
      + left. destruct a. ss. clarify. rewrite string_of_ident_of_string in H1. f_equal; et.
      + right. eapply IHl; et.
      + right. eapply IHl; et.
    - ss. bsimpl. des; clarify.
      + left. destruct a. ss. clarify. rewrite string_of_ident_of_string in H1. f_equal; et.
      + right. eapply IHl; et.
      + right. eapply IHl; et.
    - ss. bsimpl. des; clarify.
      + left. destruct a. ss. clarify. rewrite string_of_ident_of_string in H1. f_equal; et.
      + left. destruct a. ss. clarify. rewrite string_of_ident_of_string in H1. f_equal; et.
      + right. eapply IHl; et.
      + right. eapply IHl; et.
      + right. eapply IHl; et.
      + right. eapply IHl; et.
    - ss. bsimpl. des; clarify.
      + right. eapply IHl; et.
      + left. destruct a. ss. clarify. unfold chk_ident in Heq1. destruct Pos.eq_dec; clarify. rewrite <- e in H1. f_equal; et.
      + right. eapply IHl; et.
    - ss. bsimpl. des; clarify.
      + right. eapply IHl; et.
      + right. eapply IHl; et.
  Qed.

  Lemma asdf clight_prog mn md idx str:
    compile clight_prog mn = Some md ->
    SkEnv.blk2id (load_skenv (Sk.canon (Sk.add (sk_mem clight_prog) (Mod.sk md)))) idx = Some str ->
    exists tb, Genv.find_symbol (Genv.globalenv clight_prog) (ident_of_string str) = Some tb.
  Proof.
    i. hexploit in_env_in_sk; et. i. des. clear H0.
    apply Genv.find_symbol_exists with (g:=def).
    eapply asdf'; et.
  Qed.

  (* This single thm will be used in final thm. *)
  Theorem single_compile_behavior_improves
          clight_prog md mn left_st right_st
          (COMP: compile clight_prog mn = Some md)
          (SINIT: left_st = clightp_initial_state (sk_mem clight_prog) md)
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
    change (paco4 (_sim _ _) bot4) with (sim (clightp_sem (sk_mem clight_prog) md) (semantics2 clight_prog)).
    eapply sim_bot_flag_up with (b0 := true) (b1 := false).

    set (sort _) as sk_init in *.
    eapply step_function_entry with (modl:=md) (tm:=m0) (ge:=globalenv clight_prog) (sk:=sk_init); et.
    { unfold sk_init. econs.
      - change sort with (@Sk.canon _). apply Sk.wf_canon. unfold ModL.wf in w. ss. des. et.
      - i. unfold ModL.wf in w. ss. des. apply Sk.wf_canon in SK.
        hexploit load_skenv_wf; et. i. unfold SkEnv.wf in H2. red in H2. rewrite H2 in H1.
        hexploit asdf; et. i. clear H2.
        des. unfold map_blk. destruct le_dec; cycle 1.
        { replace (Init.Nat.pred _) with idx by nia. ss. rewrite H1.
          des_ifs. unfold fundef in *. clarify. }
        exfalso. assert (List.length (sort (Sk.add (sk_mem clight_prog) (Mod.sk md))) <= idx) by nia.
        Local Transparent load_skenv. ss. uo. des_ifs.
        apply nth_error_None in H2. clarify.
      - i. fold sk_init in H1.
        assert (SkEnv.blk2id (load_skenv sk_init) n = Some s) by now ss; uo; des_ifs.
        hexploit asdf; et. i. des.
        assert (Genv.find_symbol (Genv.globalenv clight_prog) (ident_of_string s) = Some (map_blk sk_init (Genv.globalenv clight_prog) (Pos.of_succ_nat n))).
        { unfold map_blk. destruct le_dec; cycle 1.
          { replace (Init.Nat.pred _) with n by nia. rewrite H2.
            des_ifs. unfold fundef in *. clarify. }
          exfalso. assert (List.length sk_init <= n) by nia. ss. uo. des_ifs.
          apply nth_error_None in H4. clarify. }
        clear H3.
        assert (Maps.PTree.get (ident_of_string s) (prog_defmap clight_prog) = Some gd).
        { unfold prog_defmap. ss. apply Maps.PTree_Properties.of_list_norepet; et. 
          { unfold compile, get_sk in COMP. des_ifs. destruct list_norepet_dec; clarify. }
          apply nth_error_in in H1. unfold sk_init in H1. eapply asdf'; et. }
        rewrite Genv.find_def_symbol in H3. des. clarify. }
    { admit "". }
    { admit "". }
    i. pfold. econs 4. { i. inv H5. et. } { eexists. econs. et. }
    i. inv STEP. econs 8; et. left. 

    eapply match_states_sim; eauto.
    { i. ss. clear - H5. depgen s. revert fd. induction defs; i; ss.
      des_ifs; et.
      { ss. des; et. clarify. apply Any.upcast_inj in H0. des.
        apply JMeq_eq in EQ0. clarify. et. }
      { ss. des; et. clarify. apply Any.upcast_inj in H0. des.
        apply JMeq_eq in EQ0. clarify. } }
    { set (update _ _ _) as init_pstate. econs; et. 
      { admit "global proof". }
      { instantiate (1:= init_pstate). unfold init_pstate. unfold update. ss. }
      { unfold fnsem_has_internal. i. apply Sk.sort_incl_rev in H5. ss. des; clarify.
        { apply Any.upcast_inj in H5. des. apply JMeq_eq in EQ0. clarify. }
        { apply Any.upcast_inj in H5. des. apply JMeq_eq in EQ0. clarify. }
        exists mn.
        admit "relation between decomp_fundef and get_sk". }
      { econs; et. }
      instantiate (1 := mn).
      ss. unfold itree_stop, kstop_itree, itree_of_cont_pop. ss. sim_redE.
      unfold sge_init. ss.
      set (EventsL.interp_Es _ _ _) as s. 
      set (EventsL.interp_Es _ _ _) as s'.
      assert (s = s').
      { unfold s, s'. sim_redE. unfold prog_comp_env, mkprogram. des_ifs. } 
      rewrite H5. apply bind_extk. i. sim_redE. des_ifs_safe. sim_redE.
      clear FIND_ITREE.
      destruct o.
      { sim_redE. unfold mkprogram.  des_ifs_safe. ss. apply bind_extk. i. des_ifs_safe. sim_redE.


        apply bind_extk. i. des_ifs_safe. sim_redE. et. }
      { destruct o0.
        { des_ifs_safe. sim_redE. apply bind_extk. i. des_ifs_safe. sim_redE. apply bind_extk.
          i. des_ifs_safe. sim_redE. apply bind_extk.
          i. des_ifs_safe. sim_redE. et. }
        { sim_redE. do 2 f_equal. des_ifs_safe. sim_redE.
          unfold mkprogram. des_ifs. ss. apply bind_extk.
          i. des_ifs_safe. sim_redE. apply bind_extk.
          i. des_ifs_safe. sim_redE. et. } } }
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
