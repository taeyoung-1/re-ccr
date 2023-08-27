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
Require Import ConvC2ITree.
Require Import ConvC2ITreeStmt.

Require Import Clightlight2ClightMatch.
Require Import Clightlight2ClightArith.
Require Import Clightlight2ClightGenv.
Require Import Clightlight2ClightLenv.
Require Import Clightlight2ClightMem.
Require Import Clightlight2ClightLink.
Require Import Clightlight2ClightSim. 
Require Import Clightlight2ClightMatchStmt.
Require Import Clightlight2ClightSimAll. 

Section PROOFSINGLE.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Ltac solve_mkprogram := unfold mkprogram, build_composite_env' in *; des_ifs; eauto.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0. (* these are itree normalization tactic *)
  Ltac sim_tau := (try sim_red); try pfold; econs 3; ss; clarify; eexists; exists (ModSemL.step_tau _).
  (* Ltac sim_triggerUB := unfold triggerUB; (try sim_red); econs 5; i; ss; auto; *)
  (*                       dependent destruction STEP; try (irw in x; clarify; fail). *)
  Ltac solve_ub := des; irw in H; dependent destruction H; clarify.
  Ltac sim_triggerUB := 
    (try rename H into HH); ss; unfold triggerUB; try sim_red; try pfold; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  Ltac tgt_step := try pfold; econs 4; eexists; eexists.

  Ltac wrap_up := try pfold; econs 7; et; right.

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
          (* (HAS_MALLOC: has_malloc defs)
          (HAS_FREE: has_free defs) *)
          (LEFT_COMP: modl = ModL.add (Mod.lift Mem) (Mod.lift (get_mod types defs WF_TYPES mn)))
          (RIGHT_COMP: clight_prog = mkprogram types defs (List.map (fun '(gn, _) => gn) defs) (ident_of_string "main") WF_TYPES)
          left_st right_st
          (LEFT_INIT: left_st = clightlight_initial_state types defs WF_TYPES mn)
          (RIGHT_INIT: Clight.initial_state clight_prog right_st)
        :
          <<IMPROVES: @improves2 _ (Clight.semantics2 clight_prog) left_st right_st>>.
  Proof.
    eapply adequacy; eauto.
    { apply Csharpminor_wf_semantics. }
    red. rewrite LEFT_INIT. unfold clightlight_initial_state in *. ss; clarify. inv RIGHT_INIT.
    unfold ModSemL.initial_itr.
    rename ge into tge, H into INIT_MEM, H0 into MAIN_BLOCK, H1 into FIND_MAINF, H2 into MAIN_TYPE, f into tmaindef.
    pfold. econs 5; eauto; unfold assume. 
    { ss. grind. dtm H H0. }
    grind. eapply angelic_step in STEP. des; clarify.
    unfold ITree.map. sim_red.

    set (sge_init:= Sk.sort _) in *.
    destruct (alist_find "main" _) eqn:FOUNDMAIN;[|sim_triggerUB].
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
      unfold tge, mkprogram, build_composite_env' in Heq. des_ifs. clear Heq0 Heq8.
      rewrite e in e0. inv e0. eauto. }
    i. inv H. rename f into tmain. 
    unfold cfunU. sim_red. unfold decomp_func. sim_red.
    pfold_reverse.
    unfold build_composite_env'. des_ifs. 
    eapply step_function_entry; et; ss.
    { instantiate (1:= (Build_genv tge x)). ss. }
    { instantiate (1:=(ModL.add Mem (get_mod types defs WF_TYPES mn)).(ModL.sk)). admit "". }
    { instantiate (1:=m0). clear -INIT_MEM. admit "". }
    i. tgt_step.
    { econs. set (Smallstep.globalenv _) as ge'. ss.
      assert (ge' = Build_genv tge x). { admit "". }
      rewrite H3. et. }

    unfold ModL.wf in WF. des. econs 7; et. left. 

    eapply match_states_sim; eauto.
    { admit "". }
    { admit "". }
    Unshelve. et.
  Qed.

  (* Theorem single_compile_program_improves
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
  Qed. *)

End PROOFSINGLE.



