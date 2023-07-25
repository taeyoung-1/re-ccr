From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import SimSTS3.
Require Import Clight_Mem0.
Require Import IRed.
From Ordinal Require Import Ordinal Arithmetic.
Require Import ConvC2ITree.

Require Import Clightlight2ClightMatch.
Require Import Clightlight2ClightArith.
Require Import Clightlight2ClightGenv.
(* Require Import Clightlight2ClightLenv. *)
Require Import Clightlight2ClightMem.
Require Import Clightlight2ClightLink.
(* Require Import Clightlight2ClightSim.  *)

Section PROOFSINGLE.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Create HintDb ord_step2.
  Hint Resolve Nat.lt_succ_diag_r OrdArith.lt_from_nat OrdArith.lt_add_r: ord_step2.
  Hint Extern 1000 => lia: ord_step2.
  Ltac ord_step2 := eauto with ord_step2.

  Ltac solve_mkprogram := unfold mkprogram, build_composite_env' in *; des_ifs; eauto.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0. (* these are itree normalization tactic *)
  Ltac sim_tau := (try sim_red); econs 3; ss; clarify; eexists; exists (ModSemL.step_tau _); eexists; split; [ord_step2|auto].
  (* Ltac sim_triggerUB := unfold triggerUB; (try sim_red); econs 5; i; ss; auto; *)
  (*                       dependent destruction STEP; try (irw in x; clarify; fail). *)
  Ltac solve_ub := des; irw in H; dependent destruction H; clarify. (* how to end with ub *)
  Ltac sim_triggerUB := (try rename H into HH); pfold; ss; unfold triggerUB; try sim_red; econs 5; i; ss; auto;
                        [solve_ub | dependent destruction STEP; try (irw in x; clarify; fail)].

  Ltac dtm H H0 := eapply angelic_step in H; eapply angelic_step in H0; des; rewrite H; rewrite H0; ss.

(*
  Definition imp_sem (src : Imp.programL) := compile_val (ModL.add (Mod.lift (Mem (fun _ => false))) (ImpMod.get_modL src)).

  Definition imp_initial_state (src : Imp.programL) := (imp_sem src).(initial_state).
 *)

(** Why does final value determines sort of state? *)
(** The reason why Vint is special is just "int main(void)"? *)

  Definition compile_val md := @ModL.compile _ EMSConfigC md. 

  Definition clightligt_sem types defs WF_COMP mn := compile_val (ModL.add (Mod.lift Mem) (Mod.lift (get_mod types defs WF_COMP mn))).

  Definition clightlight_initial_state types defs WF_COMP mn := (clightligt_sem types defs WF_COMP mn).(initial_state).
  Opaque ident_of_string.

  Definition has_malloc (defs: list (_ * AST.globdef Clight.fundef Ctypes.type)) :=
     In (ident_of_string "malloc", Gfun (External EF_malloc (Ctypes.Tcons tulong Ctypes.Tnil) (tptr tvoid) cc_default)) defs.

  Definition has_free (defs: list (_ * AST.globdef Clight.fundef Ctypes.type)) :=
     In (ident_of_string "free", Gfun (External EF_free (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tvoid cc_default)) defs.

  
  Theorem single_compile_behavior_improves
          (types: list Ctypes.composite_definition)
          (defs: list (AST.ident * AST.globdef Clight.fundef Ctypes.type))
          (WF_TYPES: Clightdefs.wf_composites types) mn modl clight_prog
          (NO_REP: Coqlib.list_norepet (List.map fst defs))
          (HAS_MALLOC: has_malloc defs)
          (HAS_FREE: has_free defs)
          (LEFT_COMP: modl = ModL.add (Mod.lift Mem) (Mod.lift (get_mod types defs WF_TYPES mn)))
          (RIGHT_COMP: clight_prog = mkprogram types defs (List.map (fun '(gn, _) => gn) defs) (ident_of_string "main") WF_TYPES)
          left_st right_st
          (LEFT_INIT: left_st = clightlight_initial_state types defs WF_TYPES mn)
          (RIGHT_INIT: Clight.initial_state clight_prog right_st)
        :
          <<IMPROVES: @improves2 _ (Clight.semantics2 clight_prog) left_st right_st>>.
  Proof.
    eapply adequacy; eauto.
    { apply Ordinal.Ord.lt_well_founded. }
    { admit "I have to prove well formedness of Clight compile result". }
    instantiate (1:= (Ord.omega * Ord.omega + Ord.omega + 1)%ord).
    red. ginit.
    { instantiate (1:= (cpn3 (_sim (clightligt_sem types defs WF_TYPES mn) (semantics2 clight_prog)))).
      econs. { red. i. econs.    }  }
     rewrite LEFT_INIT. unfold clightlight_initial_state in *. ss; clarify. inv RIGHT_INIT.
    unfold ModSemL.initial_itr.
    rename ge into tge, H into INIT_MEM, H0 into MAIN_BLOCK, H1 into FIND_MAINF, H2 into MAIN_TYPE, f into tmaindef.
    gstep. econs 5; eauto; unfold assume. 
    { ss. grind. dtm H H0. }
    grind. eapply angelic_step in STEP. des; clarify.
    eexists; split; [ord_step2|].

    left. unfold ITree.map. sim_red. 
    set (sge_init:= Sk.sort _) in *.
    destruct (alist_find "main" _) eqn:FOUNDMAIN; ss; grind; [|sim_triggerUB].
    repeat match goal with | [ H : false = false |- _ ] => clear H end.
    
    rewrite alist_find_find_some in FOUNDMAIN. rewrite find_map in FOUNDMAIN.
    rewrite find_map in FOUNDMAIN. uo; des_ifs; ss. inv H0. clear H1. 
    hexploit found_itree_clight_function; eauto. i. des. subst. rewrite string_of_ident_of_string.
    clear Heq0. rename H0 into FIND_ITREE.
    hexploit decomp_fundefs_decomp_func; eauto. i. des. rename H0 into FIND_TFUNC.
    set (_main := prog_main _) in *.
    assert (_main = ident_of_string "main") by now solve_mkprogram. clearbody _main. subst.
    hexploit tgt_genv_match_symb_def; [> try (unfold tge in *; solve_mkprogram; fail) ..|]; eauto.
    { des_ifs. clear Heq. unfold Globalenvs.Genv.find_funct_ptr in *. des_ifs. 
      unfold tge, mkprogram, build_composite_env' in Heq. des_ifs. clear Heq0.
      rewrite e in e0. inv e0. eauto. }
    i. inv H. rename f into tmain. 
    unfold cfunU. rewrite Any.upcast_downcast. unfold decomp_func. grind.
    clear Heq. rename x into ce, e into EQ. sim_red.
    unfold function_entry_c.
    destruct (id_list_norepet_c _ && id_list_norepet_c _ && id_list_disjoint_c _ _); [|sim_triggerUB].
    sim_red.
    induction (fn_vars tmain); cycle 1.
    { ss. destruct a. unfold ccallU. sim_red; ss. pfold; econs 3; ss; grind.
      eexists. exists (ModSemL.step_tau _). eexists. 
     }
    - ss. sim_red. unfold triggerUB. ired. pfold; econs 5; ss; grind.
      { i. solve_ub. } 
      { i. dependent destruction STEP; irw in x; ss. injection x. i. simpl_depind. ss. }
    - ss. destruct a. unfold ccallU; sim_red. ss. pfold; econs 3; ss; grind.
      { eexists. exists (ModSemL.step_tau _). eexists.
        split; ord_step2. left. rewrite Any.upcast_downcast. sim_red.
        unfold sallocF. sim_red.
      left. 

(*     assert (MAINPARAM: fn_params smain = []).
    { depgen Heq. clear. i. remember (fn_params smain) as m. clear Heqm. depgen l. induction m; i; ss; clarify. }
    rename l into sle, Heq into INITARGS. rewrite MAINPARAM in INITARGS. ss. clarify.
    rewrite interp_imp_tau. sim_red.

    unfold Genv.find_funct_ptr in TMAIN2. subst tge. rewrite TGTMAIN in TMAIN2. clarify.
    set (tge:=Genv.globalenv tgt) in *. *)
    pfold. econs 4; ss. eexists. eexists.
    { rewrite <- NoDup_norepeat in WF_MAIN. apply Coqlib.list_norepet_app in WF_MAIN; des. subst tmainf.
      rewrite MAINPARAM in *. eapply step_internal_function; ss; eauto; try econs. }
    eexists; split; [ord_step2|auto]. left. ss.

    unfold ModL.wf in WF. des.

    pfold. econs 6; ss; eauto. eexists. eexists.
    { eapply step_seq. }
    eexists. exists (ModSemL.step_tau _). exists ((100 + max_fuel) + 100 + Ord.omega + 100)%ord. left.
    rewrite interp_imp_bind. grind. sim_red.
    assert (MATCHGE: match_ge src (Sk.load_skenv (Sk.sort (ModL.sk (ModL.add (Mem (fun _ => false)) (ImpMod.get_modL src))))) (Genv.globalenv tgt)).
    { econs. i. simpl in H. rewrite Sk.add_unit_l in H.
      unfold map_blk. rewrite COMP0. hexploit Sk.env_found_range; eauto. i. unfold src_init_nb, int_len.
      rewrite <- sksort_same_len in H0. ss. unfold sk_len. des.
      hexploit (Sk.sort_wf SK). i. rewrite Sk.add_unit_l in H1.
      apply Sk.load_skenv_wf in H1.
      apply H1 in H. unfold get_sge. ss. rewrite H. unfold get_tge. des_ifs; try lia.
      hexploit found_in_src_in_tgt; eauto. i. des. unfold get_tge in H2. clarify.
    }
    ss. rewrite Sk.add_unit_l in MATCHGE. rewrite Sk.add_unit_l in WF0.

    unfold imp_sem in *. 
    eapply match_states_sim; eauto.
    { apply map_blk_after_init. }
    { apply map_blk_inj. }
    ss. rewrite Sk.add_unit_l.
    match goal with
    | [ |- match_states ?_ge ?_ms _ _ _ ] => replace _ge with sge; auto
    end.
    match goal with
    | [ |- match_states ?_ge ?_ms _ _ _ ] => set (ms:=_ms) in *
    end.
    ss.
    econs; eauto.
    { eapply init_lenv_match; eauto. rewrite map_app. ss. }
    { clarify. }
    { econs; ss.
      { unfold src_init_nb, sk_len. rewrite <- sksort_same_len. lia. }
      { apply Genv.init_mem_genv_next in TMINIT. rewrite <- TMINIT. unfold Genv.globalenv. ss.
        rewrite Genv.genv_next_add_globals. ss. rewrite Genv_advance_next_length. ss.
        rewrite length_elements_PTree_norepet; eauto. rewrite map_blk_after_init; eauto.
        2:{ unfold src_init_nb, sk_len. rewrite <- sksort_same_len. lia. }
        unfold ext_len. subst tgds.
        rewrite Pos2Nat.inj_1. rewrite Nat.add_1_r. rewrite <- Pos.of_nat_succ. f_equal.
        rewrite gdefs_preserves_length. repeat rewrite <- Nat.add_assoc. do 3 f_equal.
        unfold Sk.wf in SK. ss.
        rewrite Sk.add_unit_l in SK.
        hexploit wfprog_defsL_length; eauto. i. des.
        unfold sk_len in *.
        match goal with | [ |- _ = ?x ] => replace x with (int_len src) end.
        { unfold int_len. ss. }
        rewrite <- sksort_same_len. sym. apply Nat.sub_add. auto.
      }
      i. uo; des_ifs. unfold NW in H. clarify. rename s into gn, Heq0 into SGENV.
      set (tblk:=map_blk src blk) in *. unfold map_ofs in *. rewrite! Z.mul_0_r.
      hexploit found_gvar_in_src_then_tgt; eauto. i. des. rename H into FOUNDTGV.
      hexploit Genv.init_mem_characterization; eauto.
      { unfold Genv.find_var_info. rewrite FOUNDTGV. clarify. }
      i. des. rename H into TMPERM, H0 into TMPERM0, H1 into TMLSID, H2 into TMLB.
      subst tblk. inv MATCHGE.
      assert (SKFOUND: SkEnv.blk2id sge blk = Some gn).
      { subst sge. Local Transparent Sk.load_skenv. unfold Sk.load_skenv. ss. rewrite SGENV. uo; ss. Local Opaque Sk.load_skenv. }
      assert (WFSKENV: Sk.wf (defsL src)); auto.
      apply Sk.sort_wf in WFSKENV. apply Sk.load_skenv_wf in WFSKENV. apply WFSKENV in SKFOUND. clear WFSKENV.
      apply MG in SKFOUND. apply nth_error_In in SGENV. apply WFPROG2 in SGENV.
      hexploit compiled_gvar_props; eauto. i. des. clarify.
      assert (TMLSID0: false = false); auto. apply TMLSID in TMLSID0; clear TMLSID.
      assert (TMLB0: false = false); auto. apply TMLB in TMLB0; clear TMLB.
      rewrite H0 in *. ss. des. clear TMLSID1. split; auto.
      unfold Genv.perm_globvar in TMPERM. des_ifs. split.
      2:{ unfold NW. lia. }
      split; eauto. ss. apply Z.divide_0_r. }
    { ss. }
    { ss.
      match goal with
      | [ |- match_code _ _ _ ?i0 ?s0 ] =>
        replace i0 with ((fun '(p, (le, _)) => itree_of_imp_ret sge le ms mn (p)) : (_ * (lenv * val)) -> _);
          replace s0 with [exit_stmt]; eauto
      end.
      { econs 1. }
      extensionality x. unfold itree_of_imp_ret, itree_of_imp_cont. grind. destruct p0. rewrite interp_imp_expr_Var. grind. }
    { ss.
      match goal with
      | [ |- match_stack _ _ _ _ ?i0 ?s0 ] =>
        replace i0 with ((itree_of_imp_pop_bottom ms mn) : (_ * (lenv * val)) -> _);
          replace s0 with (Some ret_call_main); eauto
      end.
      { econs 1. }
      extensionality x. unfold itree_of_imp_pop_bottom. grind. sim_red. Red.prw ltac:(_red_gen) 1 0. ss.
    }
  Qed.

  Theorem single_compile_program_improves
          (src: Imp.programL) (tgt: Csharpminor.program)
          (WFPROG: incl (name1 src.(defsL)) ((name1 src.(prog_varsL)) ++ (name2 src.(prog_funsL))))
          (WFPROG3: forall blk name,
              let modl := ModL.add (Mod.lift (Mem (fun _ => false))) (ImpMod.get_modL src) in
              let ge := (Sk.load_skenv (Sk.sort modl.(ModL.sk))) in
              (ge.(SkEnv.blk2id) blk = Some name) -> call_ban name = false)
          (WFPROG2 : forall gn gv, In (gn, Sk.Gvar gv) (Sk.sort (defsL src)) -> In (gn, gv) (prog_varsL src))
          (COMP: Imp2Csharpminor.compile src = OK tgt)
    :
      <<IMPROVES: improves2_program (imp_sem src) (Csharpminor.semantics tgt)>>.
  Proof.
    red. unfold improves2_program. i. inv BEH.
    { eapply single_compile_behavior_improves; eauto. }
    (* initiall wrong case, for us only when main is not found *)
    exists (Tr.ub). split; red; eauto.
    2:{ pfold. econs 4; eauto.
        - ss.
        - unfold behavior_prefix. exists (Goes_wrong E0). ss.
    }
    rename H into NOINIT.
    unfold imp_sem in *. ss. unfold ModSemL.initial_itr.
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
    destruct p as [mn [fn ff]]; ss; clarify.
    rewrite Sk.add_unit_l in FOUND.
    eapply found_imp_function in FOUND. des; clarify.
    hexploit in_tgt_prog_defs_ifuns; eauto. i.
    des. rename H into COMPF. clear FOUND.
    assert (COMPF2: In (compile_iFun (mn, ("main", ff))) (prog_defs tgt)); auto.
    eapply Globalenvs.Genv.find_symbol_exists in COMPF.
    destruct COMPF as [b TGTFG].
    assert (TGTGFIND: Globalenvs.Genv.find_def (Globalenvs.Genv.globalenv tgt) b = Some (snd (compile_iFun (mn, ("main", ff))))).
    { hexploit tgt_genv_find_def_by_blk; eauto. }

    unfold compile in COMP. des_ifs.
    match goal with [ H: Genv.find_symbol (Genv.globalenv ?_tgt) _ = _ |- _ ] => set (tgt:=_tgt) in * end.
    hexploit (Genv.init_mem_exists tgt); eauto.
    { i. subst tgt; ss. hexploit perm_elements_PTree_norepeat_in_in; eauto.
      i. apply H0 in H. clear H0. apply decomp_gdefs in H. des; ss; clarify; eauto.
      { unfold bts in BTS1. apply Coqlib.list_in_map_inv in BTS1. des. destruct fd; ss; clarify. destruct x0; ss; clarify. }
      { destruct fd. unfold compile_eFun in SYS; ss; clarify. }
      { destruct fd. unfold compile_eFun in EFS; ss; clarify. }
      { depgen EVS. clear. i. unfold compile_eVar in EVS. ss; clarify. }
      { depgen IFS. clear. i. destruct fd as [mn [fn ff]]. unfold compile_iFun in IFS; ss; clarify. }
      { depgen IVS. clear. i. unfold compile_iVar in IVS. destruct vd; ss; clarify. split; ss; eauto.
        - split; eauto. apply Z.divide_0_r.
        - i. des; eauto; clarify. }
    }
    i. des. unfold compile_iFun in *; ss; clarify.
    match goal with
    | [ H: Genv.find_def _ _ = Some (Gfun ?_fdef) |- _ ] => set (fdef:=_fdef) in * end.
    specialize NOINIT with (Callstate fdef [] Kstop m).
    apply NOINIT.
    econs; ss; eauto.
    unfold Genv.find_funct_ptr. rewrite TGTGFIND. ss.
  Qed.

End PROOFSINGLE.



