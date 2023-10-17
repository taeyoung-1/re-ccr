From compcert Require Import Coqlib Behaviors Integers Floats AST Globalenvs Ctypes Cop Clight Clightdefs.

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

  Ltac dtm H H0 := eapply angelic_step in H; eapply angelic_step in H0; des; rewrite H; rewrite H0; ss.

(*
  Definition imp_sem (src : Imp.programL) := compile_val (ModL.add (Mod.lift (Mem (fun _ => false))) (ImpMod.get_modL src)).

  Definition imp_initial_state (src : Imp.programL) := (imp_sem src).(initial_state).
 *)

(** Why does final value determines sort of state? *)
(** The reason why Vint is special is just "int main(void)"? *)

  Definition compile_val md := @ModL.compile _ EMSConfigC md. 

  Definition clightligt_sem types defs WF_COMP mn := compile_val (ModL.add (Mod.lift Mem) (Mod.lift (get_mod types defs WF_COMP mn))).

  Definition clightlight_initial_state types defs WF_COMP mn := (clightligt_sem types defs WF_COMP mn).(STS.initial_state).
  Opaque ident_of_string.
  
  Lemma NoDup_norepeat :
    forall A (l : list A), Coqlib.list_norepet l <-> NoDup l.
  Proof.
    split; induction l; i; ss; eauto.
    - econs.
    - inv H. econs; eauto.
    - econs.
    - inv H. econs; eauto.
  Qed.

  Arguments Es_to_eventE /.
  Arguments itree_of_code /. 
  Arguments sloop_iter_body_two /. 
  Arguments ktree_of_cont_itree /. 

  Theorem single_compile_behavior_improves
          (types: list Ctypes.composite_definition)
          (defs: list (AST.ident * AST.globdef Clight.fundef Ctypes.type))
          (public: list AST.ident)
          (WF_TYPES: Clightdefs.wf_composites types) 
          mn clight_prog
          (WFDEF_NODUP: NoDup (List.map fst defs))
          (WFDEF_EXT: forall a, In a Mem.(Mod.sk) -> In a (List.map (fun '(p, gd) => (string_of_ident p, gd↑)) defs))
          (COMP: clight_prog = mkprogram types defs public (ident_of_string "main") WF_TYPES)
          left_st right_st
          (SINIT: left_st = clightlight_initial_state types defs WF_TYPES mn)
          (TINIT: Clight.initial_state clight_prog right_st)
        :
          <<IMPROVES: @improves2 _ (Clight.semantics2 clight_prog) left_st right_st>>.
  Proof.
    eapply adequacy; eauto.
    { apply Csharpminor_wf_semantics. }
    red. rewrite SINIT. unfold clightlight_initial_state in *. ss; clarify. inv TINIT.
    unfold ModSemL.initial_itr.
    rename ge into tge, H into INIT_TMEM, H0 into MAIN_TBLOCK, H1 into FIND_TMAINF, H2 into MAIN_TYPE, f into tmain.
    set (Build_genv tge (let (ce, _) := build_composite_env' types WF_TYPES in ce)) as ge.
    pfold. econs 5; eauto; unfold assume.
    { ss. grind. dtm H H0. }
    grind. eapply angelic_step in STEP. des; clarify.
    unfold ITree.map. sim_red.

    set (sge_init:= Sk.sort _) in *.
    destruct (alist_find "main" _) eqn:FOUNDMAIN;[|sim_triggerUB]. ss.
    repeat match goal with | [ H : false = false |- _ ] => clear H end.
    
    rewrite alist_find_find_some in FOUNDMAIN. rewrite find_map in FOUNDMAIN.
    rewrite find_map in FOUNDMAIN. uo; des_ifs; ss. inv H0. clear H1. 
    unfold ModL.wf in WF. des. inv WF0. clear wf_initial_mrs.
    apply found_itree_clight_function in Heq0. des. rename Heq1 into FIND_ITREE.
    hexploit decomp_fundefs_decomp_func; eauto. i. des. rename H0 into FIND_TFUNC.
    assert (WF_IDENT: NoDup (List.map string_of_ident (List.map fst defs))).
    { admit "". }
    hexploit Globalenvs.Genv.find_symbol_inversion; et. i.
    replace (prog_defs_names _) with (List.map fst defs) in H0.
    2:{ unfold mkprogram. des_ifs. }
    replace (prog_main _) with (ident_of_string "main") in * by now solve_mkprogram.
    assert (In p (List.map fst defs)).
    { eapply in_map with (f := fst) in FIND_TFUNC. et. }
    assert (p = ident_of_string "main").
    { clear -H0 H1 WF_IDENT Heq0. rewrite <- string_of_ident_of_string in Heq0.
      revert_until defs. generalize (List.map fst defs).
      induction l; i; ss; et. des; subst; et; inv WF_IDENT.
      { rewrite Heq0 in H2.
        eapply in_map with (f:=string_of_ident) in H0. contradiction. }
      { rewrite <- Heq0 in H2.
        eapply in_map with (f:=string_of_ident) in H1. contradiction. }
      eapply IHl; et. }
    subst.
    hexploit tgt_genv_match_symb_def; et.
    { rewrite NoDup_norepeat. et. }
    { unfold Globalenvs.Genv.find_funct_ptr in *. des_ifs; et. }
    { unfold mkprogram. des_ifs; et. }
      
    i. clarify. rename f into tmain. 
    unfold cfunU. sim_red. unfold decomp_func. sim_red.
    pfold_reverse. 
    eapply step_function_entry with (ge := ge) (sk := sge_init); et; ss.
    { unfold sge_init, tge, mkprogram, Globalenvs.Genv.globalenv. des_ifs_safe. ss.
      clear -WFDEF_NODUP WFDEF_EXT SK wf_fnsems.
      admit "This can be proved from these hypothesis". }
    { instantiate (1 := m0). clear -INIT_TMEM. admit "This can be proved from these hypothesis". }
    i. tgt_step.
    { econs. unfold ge in H. unfold tge in H. ss. unfold mkprogram in *. des_ifs; et. }
    econs 7; et. left. 

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



