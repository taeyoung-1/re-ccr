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
(* Require Import ClightPlus2ClightSim. *)
(* Require Import ClightPlus2ClightSimAll.  *)

(* Require Import ClightPlus2ClightLink. *)
(* Require Import ClightPlus2ClightGenv. *)

Require Import Admit.

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

Section PROOFSINGLE.

  (* Ltac solve_mkprogram := unfold mkprogram, build_composite_env' in *; des_ifs; eauto. *)

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0. (* these are itree normalization tactic *)
  Ltac sim_tau := (try sim_red); try pfold; econs 3; ss; clarify; eexists; exists (ModSemL.step_tau _).
  (* Ltac sim_triggerUB := unfold triggerUB; (try sim_red); econs 5; i; ss; auto; *)
  (*                       dependent destruction STEP; try (irw in x; clarify; fail). *)
  Ltac solve_ub := des; irw in H; dependent destruction H; clarify.
  Ltac sim_triggerUB := 
    (try rename H into HH); ss; unfold triggerUB; try sim_red; try pfold; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  (* Ltac to_oeq :=
    match goal with
| |- ?A = ?B => change (oeq A B)
    end.

  Ltac from_oeq :=
    match goal with
    | |- oeq ?A ?B => change (A = B)
    end.

  Ltac sim_redE :=
    to_oeq; cbn; repeat (Red.prw ltac:(_red_gen) 1 0); repeat (Red.prw ltac:(_red_gen) 2 0); from_oeq. *)

  Ltac tgt_step := try pfold; econs 4; eexists; eexists.

  Ltac wrap_up := try pfold; econs 7; et; right.

  Ltac dtm H H0 := eapply angelic_step in H; eapply angelic_step in H0; des; rewrite H; rewrite H0; ss.

  Definition compile_val mdl := @ModL.compile _ EMSConfigC mdl. 

  Definition clightp_sem md := compile_val (ModL.add (Mod.lift Mem) (Mod.lift md)).

  Definition clightp_initial_state md := (clightp_sem md).(STS.initial_state).

  Lemma NoDup_norepeat :
    forall A (l : list A), Coqlib.list_norepet l <-> NoDup l.
  Proof.
    split; induction l; i; ss; eauto.
    - econs.
    - inv H. econs; eauto.
    - econs.
    - inv H. econs; eauto.
  Qed.

  Local Opaque ident_of_string.
  Arguments Es_to_eventE /.
  Arguments itree_of_stmt /.
  Arguments sloop_iter_body_two /.
  Arguments ktree_of_cont_itree /.

  (* THIS THM IS JUST FOR INITIALIZATION TEST *)

  Lemma in_get_fnsems_decomp clight_prog fn sk l i :
    NoDup (List.map fst l) ->
    alist_find fn (get_fnsems clight_prog sk l) = Some i ->
    exists f, i = cfunU (decomp_func sk (get_ce clight_prog) f) /\ alist_find fn l = Some (Gfun (Internal f)).
  Proof.
    ginduction l; i; ss. des_ifs_safe. inv H. destruct g as [[f|? ? ? ?]|v].
    - ss. des_ifs; cycle 1. { apply IHl; et. } esplits; et.
    - hexploit IHl; et. i. des. esplits; et. des_ifs.
      unfold rel_dec in Heq; ss. destruct dec; clarify.
      apply alist_find_some in H1. eapply in_map with (f:=fst) in H1. ss.
    - hexploit IHl; et. i. des. esplits; et. des_ifs.
      unfold rel_dec in Heq; ss. destruct dec; clarify.
      apply alist_find_some in H1. eapply in_map with (f:=fst) in H1. ss.
  Qed.

  Lemma get_sk_nodup l t : get_sk l = Some t -> NoDup (List.map fst t).
  Proof.
    revert t. induction l; unfold get_sk; i; des_ifs; ss; cycle 2.
    { apply IHl. unfold get_sk. des_ifs. inv l0. exfalso. et. } { econs. }
    bsimpl. des. destruct a. ss. rewrite Heq0 in *. clear Heq0. ss.
    des_ifs. bsimpl. des. unfold chk_ident in Heq.
    rewrite forallb_app in Heq0. bsimpl. destruct Pos.eq_dec; clarify.
    clear Heq Heq1. rewrite list_norepet_app in l1. des. clear l2 l3.
    rewrite (List.map_map _ fst).
    replace (_ ∘ _) with (string_of_ident ∘ (@fst ident (globdef Clight.fundef type))).
    2:{ extensionalities. destruct H. ss. }
    rewrite <- (List.map_map _ string_of_ident).
    econs.
    - ii. apply n. apply in_map with (f:=ident_of_string) in H. rewrite <- e in H.
      apply in_app. left. eassert (X: List.map fst (List.filter def_filter l) = _); [|rewrite X; et].
      clear - Heq0. ginduction l; ss. i. des_ifs; ss; et.
      bsimpl. des. unfold chk_ident in Heq0. destruct Pos.eq_dec; clarify. f_equal; et.
    - clear -Heq0 l1. ginduction l; i; ss. { econs. }
      des_ifs; cycle 1. { apply IHl; et. }
      inv l1. ss. bsimpl. des. econs; et.
      ii. apply H1. apply in_map with (f:=ident_of_string) in H.
      unfold chk_ident in Heq0. destruct Pos.eq_dec; clarify.
      rewrite <- e in H.
      eassert (X: List.map fst (List.filter def_filter l) = _); [|rewrite X; et].
      clear - Heq1. induction l; i; ss.
      des_ifs; et. ss. bsimpl. des. unfold chk_ident in Heq1. destruct Pos.eq_dec; clarify.
      f_equal; et.
  Qed.

  Theorem in_tgt_prog_defs_decomp clight_prog mn md fn sk i :
    compile clight_prog mn = Some md ->
    alist_find fn (ModSem.fnsems (Mod.get_modsem md sk)) = Some i ->
    exists f, i = cfunU (decomp_func sk (get_ce clight_prog) f) /\ alist_find (ident_of_string fn) (prog_defs clight_prog) = Some (Gfun (Internal f)).
  Proof.
    unfold compile. i. des_ifs. ss.
    hexploit in_get_fnsems_decomp; et. { eapply get_sk_nodup; et. } 
    i. des. clarify. esplits; et.
    clear -Heq H1. revert_until clight_prog.
    generalize (prog_defs clight_prog).
    induction l; i; ss. { unfold get_sk in Heq. des_ifs. }
    unfold get_sk in Heq. destruct list_norepet_dec; clarify.
    destruct (_ && _) eqn: ?; clarify. bsimpl. des.
    des_ifs.
    - unfold def_filter in Heq0. ss. 
      unfold rel_dec in Heq. ss. destruct dec; clarify. clear Heq.
      rewrite string_of_ident_of_string in H1.
      des_ifs; cycle 1.
      all: unfold rel_dec in Heq; ss; destruct dec; clarify.
    - exfalso.
      hexploit IHl; et.
      { ss. des_ifs. unfold get_sk. des_ifs. inv l0. clarify. }
      i. apply alist_find_some in H. apply in_map with (f:=fst) in H.
      unfold rel_dec in Heq. ss. destruct dec; clarify. clear Heq.
      inv l0. et.
    - ss. rewrite Heq0 in *. ss. bsimpl. des. unfold chk_ident in Heqb.
      destruct Pos.eq_dec; clarify. rewrite e in *.
      rewrite string_of_ident_of_string in *.
      clear Heq0. des_ifs. { unfold rel_dec in *. ss. do 2 destruct dec; clarify. }
      eapply IHl; et. unfold get_sk.
      inv l0. des_ifs. ss. destruct list_norepet_dec; clarify.
    - eapply IHl; et. unfold get_sk. ss. rewrite Heq0 in *. inv l0.
      des_ifs.
  Qed.

  Theorem in_tgt_prog_main clight_prog mn md :
    compile clight_prog mn = Some md -> prog_main clight_prog = ident_of_string "main".
  Proof. unfold compile. des_ifs. Qed.

  Lemma tgt_genv_match_symb_def
        clight_prog md mn name b gd1 gd2
        (COMP: compile clight_prog mn = Some md)
        (GFSYM: Genv.find_symbol (Genv.globalenv clight_prog) name = Some b)
        (GFDEF: Genv.find_def (Genv.globalenv clight_prog) b = Some gd1)
        (INTGT: alist_find name (prog_defs clight_prog) = Some gd2)
    :
      gd1 = gd2.
  Proof.
    unfold compile, get_sk in COMP. des_ifs_safe. apply alist_find_some in INTGT.
    change (prog_defs clight_prog) with (AST.prog_defs clight_prog) in INTGT.
    hexploit prog_defmap_norepet; eauto; ss.
    i. apply Genv.find_def_symbol in H. des. clarify.
  Qed.

  Theorem single_compile_behavior_improves
          clight_prog md mn left_st right_st
          (COMP: compile clight_prog mn = Some md)
          (SINIT: left_st = clightp_initial_state md)
          (TINIT: Clight.initial_state clight_prog right_st)
        :
          <<IMPROVES: @improves2 _ (Clight.semantics2 clight_prog) left_st right_st>>.
  Proof.
    eapply adequacy; eauto.
    { admit "apply Clight_wf_semantics.". }
    red. ss; clarify. unfold clightp_initial_state. ss; clarify. inv TINIT.
    unfold ModSemL.initial_itr.
    rename ge into tge, H into INIT_TMEM, H0 into TMAINN_TBLOCK, H1 into TBLOCK_TMAINF, H2 into TMAIN_TYPE, f into tmainf.

    (* remove not-wf-(mem+md) case *)
    unfold ModL.wf_bool. destruct ModL.wf_dec; ss; [|sim_triggerUB].
    grind. unfold ITree.map. sim_red.

    (* if we find "main" in md, prog_main clight_prog in clight_prog, two functions should have same compilation relation *)
    destruct (alist_find "main" _) eqn:SMAINN_MAINF;[|sim_triggerUB].
    rewrite alist_find_map_snd in SMAINN_MAINF. uo; des_ifs; ss.
    hexploit in_tgt_prog_defs_decomp; et. i. des. clarify.
    hexploit in_tgt_prog_main; et. i. rewrite H in *.
    hexploit tgt_genv_match_symb_def; et. { unfold Genv.find_funct_ptr in TBLOCK_TMAINF. des_ifs. et. }
    i. clarify. rename f into tmainf.

    unfold cfunU. sim_red. unfold decomp_func. sim_red.
    change (paco4 (_sim _ _) bot4) with (sim (clightp_sem md) (semantics2 clight_prog)).
    eapply sim_bot_flag_up with (b0 := true) (b1 := false).

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
