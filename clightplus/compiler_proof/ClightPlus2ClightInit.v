From compcert Require Import Coqlib Behaviors Integers Floats AST Globalenvs Ctypes Cop Clight Clightdefs.
Require Import CoqlibCCR.
Require Import ModSem.
Require Import ClightPlusExprgen ClightPlusgen ClightPlusSkel.

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
  revert t. induction l; unfold get_sk; i; des_ifs. { econs. }
  2:{ apply IHl. unfold get_sk. ss. des_ifs. ss. bsimpl. des. clarify. }
  rewrite (List.map_map _ fst).
  replace (_ ∘ _) with (string_of_ident ∘ (@fst ident (globdef Clight.fundef type))).
  2:{ extensionalities. destruct H. ss. }
  rewrite <- (List.map_map _ string_of_ident).
  ss. des_ifs. econs.
  - ss. ii. apply n. bsimpl. des. clear - Heq Heq0 Heq1 Heq3 Heq2 H.
    move Heq3 at bottom. move Heq2 at bottom. revert_until Heq1. induction l; ss; i.
    bsimpl. des. des_ifs; try tauto.
    ss. des.
    + left. bsimpl. des.
      assert (ident_of_string (string_of_ident (fst a0)) = fst a0).
      { unfold chk_ident in Heq2. des_ifs; ss; destruct Pos.eq_dec; clarify. }
      assert (ident_of_string (string_of_ident (fst a)) = fst a).
      { unfold chk_ident in Heq0. des_ifs; ss; destruct Pos.eq_dec; clarify. }
      rewrite <- H0. rewrite <- H1. f_equal; et.
    + right. bsimpl. des. apply IHl; et. 
  - hexploit IHl. { ss. bsimpl. des. unfold get_sk. des_ifs. bsimpl. destruct list_norepet_dec; clarify. }
    i. rewrite (List.map_map _ fst) in H.
    replace (_ ∘ _) with (string_of_ident ∘ (@fst ident (globdef Clight.fundef type))) in H.
    2:{ extensionalities. destruct H0. ss. }
    rewrite List.map_map. et.
Qed.

Theorem in_tgt_prog_defs_decomp clight_prog mn md fn sk i :
  compile clight_prog mn = Some md ->
  alist_find fn (ModSem.fnsems (Mod.get_modsem md sk)) = Some i ->
  exists f, i = cfunU (decomp_func sk (get_ce clight_prog) f) /\ alist_find (ident_of_string fn) (prog_defs clight_prog) = Some (Gfun (Internal f)).
Proof.
  Local Opaque call_ban.
  unfold compile. i. des_ifs. ss.
  hexploit in_get_fnsems_decomp; et. { eapply get_sk_nodup; et. } 
  i. des. clarify. esplits; et.
  clear -Heq H1. revert_until clight_prog.
  generalize (prog_defs clight_prog).
  induction l; i; ss. { unfold get_sk in Heq. des_ifs. }
  unfold get_sk in Heq. destruct list_norepet_dec; clarify.
  destruct forallb eqn: ?; clarify. ss.
  destruct (forallb chk_ident) eqn: ?; clarify. bsimpl. des.
  des_ifs.
  - unfold def_filter in Heq0.
    unfold rel_dec in Heq. ss. destruct dec; clarify. clear Heq.
    rewrite string_of_ident_of_string in H1.
    des_ifs; cycle 1.
    all: unfold rel_dec in Heq; ss; destruct dec; clarify.
  - exfalso.
    hexploit IHl; et. { unfold get_sk. inv l0. des_ifs. destruct list_norepet_dec; clarify. }
    i. apply alist_find_some in H. apply in_map with (f:=fst) in H.
    unfold rel_dec in Heq. ss. destruct dec; clarify. clear Heq.
    inv l0. et.
  - simpl in Heqb0. bsimpl. des.
    assert (ident_of_string (string_of_ident i) = i).
    { unfold chk_ident in Heqb0. destruct Pos.eq_dec; clarify. }
    clear Heqb Heq0. ss. des_ifs.
    { unfold rel_dec in *. ss. do 2 destruct dec; clarify. }
    eapply IHl; et. unfold get_sk. inv l0. des_ifs.
    destruct list_norepet_dec; clarify.
  - eapply IHl; et. unfold get_sk. inv l0. des_ifs.
    destruct list_norepet_dec; clarify.
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
  bsimpl. des. destruct list_norepet_dec; clarify.
  hexploit prog_defmap_norepet; eauto; ss.
  i. apply Genv.find_def_symbol in H. des. clarify.
Qed.

(* These theorems are conditions should satisfied in closed program *)
Require Import ClightPlus2ClightMatchEnv.
Local Opaque in_dec.
Local Opaque ident_of_string.
Local Transparent call_ban.

Lemma compile_sk_incl clight_prog mn md str gd sk_mem:
  compile clight_prog mn = Some md ->
  mem_skel clight_prog = Some sk_mem ->
  In (str, gd) (Sk.canon (Sk.add sk_mem (Mod.sk md))) ->
  In (ident_of_string str, gd) (prog_defs clight_prog).
Proof.
  i. unfold compile in H. unfold get_sk in H. des_ifs. ss. bsimpl. des.
  let x := type of Sk.le_canon_rev in
  let y := eval red in x in
  eapply (Sk.le_canon_rev: x) in H1.
  ss. apply in_map with (f:=(map_fst ident_of_string)) in H1. ss.
  unfold Sk.add in H1. ss. rewrite map_app in H1. rewrite List.in_app_iff in H1.
  unfold mem_skel in H0. des_ifs. clear - H1 Heq1. revert_until clight_prog.
  generalize (prog_defs clight_prog). clear. induction l; i; ss; try tauto.
  des_ifs.
  - ss. bsimpl. des.
    + left. destruct a. ss. clarify. unfold chk_ident in Heq1. destruct Pos.eq_dec; clarify. rewrite <- e in H1. f_equal; et.
    + right. eapply IHl; et.
    + left. destruct a. ss. clarify. unfold chk_ident in Heq1. destruct Pos.eq_dec; clarify. rewrite <- e in H1. f_equal; et.
    + right. eapply IHl; et.
  - ss. bsimpl. des; clarify.
    + left. destruct a. ss. clarify.
      destruct in_dec; clarify. unfold mem_keywords in i0. ss.
      des; clarify; rewrite string_of_ident_of_string in *; f_equal; et.
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

Lemma compile_tgt_blk_exists clight_prog mn md idx str sk_mem:
  compile clight_prog mn = Some md ->
  mem_skel clight_prog = Some sk_mem ->
  SkEnv.blk2id (load_skenv (Sk.canon (Sk.add sk_mem (Mod.sk md)))) idx = Some str ->
  exists tb, Genv.find_symbol (Genv.globalenv clight_prog) (ident_of_string str) = Some tb.
Proof.
  i. hexploit in_env_in_sk; et. i. des. clear H1.
  apply Genv.find_symbol_exists with (g:=def).
  eapply compile_sk_incl; et.
Qed.

Lemma compile_sk_wf clight_prog mn md sk_mem:
  compile clight_prog mn = Some md ->
  mem_skel clight_prog = Some sk_mem ->
  Sk.wf (Sk.canon (Sk.add sk_mem (Mod.sk md))).
Proof.
  i. apply Sk.wf_canon. unfold Sk.wf. ss. rewrite CoqlibC.NoDup_norepet.
  unfold Sk.add. ss. rewrite List.map_app. rewrite list_norepet_app.
  splits.
  - unfold mem_skel in H0. unfold compile, get_sk in H. des_ifs. destruct list_norepet_dec; clarify. bsimpl.
    clear -l Heq2. induction (prog_defs clight_prog); i; ss. { econs. }
    inv l. bsimpl. des. destruct in_dec; ss; et. destruct a. ss.
    econs; et. ii. apply H1. clear -H i.
    induction l0; i; ss. destruct in_dec; ss; clarify. 2:{ right. et. }
    destruct a; ss. des; clarify; et.
  - unfold compile, get_sk in H. des_ifs. destruct list_norepet_dec; clarify. ss.
    clear -l Heq1. revert_until clight_prog. generalize (prog_defs clight_prog).
    clear clight_prog. induction l; i; ss. { econs. }
    inv l0. des_ifs; et. ss. bsimpl. des. econs; et.
    ii. apply H1. destruct a. ss. unfold chk_ident in Heq1. destruct Pos.eq_dec; clarify.
    clear - H Heq0 e. induction l; i; ss. des_ifs; et. ss. bsimpl. des; et. destruct a. ss.
    left. rewrite e. unfold chk_ident in Heq0. destruct Pos.eq_dec; clarify. rewrite e0. f_equal; et.  
  - ii. unfold compile, get_sk in H. des_ifs. ss. unfold mem_skel in H0. des_ifs.
    bsimpl. des. clear - Heq1 Heq3 H1 H2. revert_until clight_prog. generalize (prog_defs clight_prog).
    clear clight_prog. induction l; i; ss. bsimpl. des. des_ifs; et.
    + destruct in_dec; clarify. clear -Heq3 Heq i. destruct a; ss. des_ifs; destruct in_dec; clarify.
    + ss. bsimpl. des; et. clarify. destruct in_dec; clarify. clear - Heq1 n H1. induction l; ss.
      destruct in_dec; clarify. ss. destruct H1; et. destruct a; destruct a0; ss. unfold chk_ident in Heq1.
      destruct Pos.eq_dec; clarify. clear Heq1. des; try tauto; clarify; rewrite string_of_ident_of_string in *; rewrite <- H in *; et.
    + ss. des; et. clarify. clear - Heq1 Heq0 Heq2 H2. induction l; ss. bsimpl. des.
      des_ifs; et. ss. bsimpl. des; et.
      clear - Heq0 Heq Heq1 Heq2 H2.
      destruct a; destruct a0; ss. unfold chk_ident in Heq1. destruct Pos.eq_dec in Heq1; clarify.
      des_ifs; try do 2 destruct in_dec; clarify.
      all: ss; des; clarify; rewrite H2 in *; rewrite e in *; et.
Qed.

Lemma compile_match_genv clight_prog mn md sk_mem:
  compile clight_prog mn = Some md ->
  mem_skel clight_prog = Some sk_mem ->
  match_ge (Sk.canon (Sk.add sk_mem (Mod.sk md))) (Genv.globalenv clight_prog).
Proof.
  i. econs.
  - eapply compile_sk_wf; et.
  - i. hexploit compile_sk_wf; et. i.
    hexploit load_skenv_wf; et. i. unfold SkEnv.wf in H3. red in H3. rewrite H3 in H1.
    hexploit compile_tgt_blk_exists; et. i. clear H3.
    des. unfold map_blk. destruct le_dec; cycle 1.
    { replace (Init.Nat.pred _) with idx by nia. ss. rewrite H1.
      des_ifs. unfold fundef in *. clarify. }
    exfalso. assert (List.length (Sk.canon (Sk.add sk_mem (Mod.sk md))) <= idx) by nia.
    Local Transparent load_skenv. ss. uo. des_ifs.
    apply nth_error_None in H3. clarify.
  - i. assert (SkEnv.blk2id (load_skenv (Sk.canon (Sk.add sk_mem (Mod.sk md)))) n = Some s) by now ss; uo; des_ifs.
    hexploit compile_tgt_blk_exists; et. i. des.
    assert (Genv.find_symbol (Genv.globalenv clight_prog) (ident_of_string s) = Some (map_blk (Sk.canon (Sk.add sk_mem (Mod.sk md))) (Genv.globalenv clight_prog) (Pos.of_succ_nat n))).
    { unfold map_blk. destruct le_dec; cycle 1.
      { replace (Init.Nat.pred _) with n by nia. rewrite H2.
        des_ifs. unfold fundef in *. clarify. }
      exfalso. assert (List.length (Sk.canon (Sk.add sk_mem (Mod.sk md))) <= n) by nia. ss. uo. des_ifs.
      apply nth_error_None in H4. clarify. }
    clear H2.
    assert (Maps.PTree.get (ident_of_string s) (prog_defmap clight_prog) = Some gd).
    { unfold prog_defmap. ss. apply Maps.PTree_Properties.of_list_norepet; et. 
      { unfold compile, get_sk in H. des_ifs. destruct list_norepet_dec; clarify. }
      apply nth_error_in in H1. eapply compile_sk_incl; et. }
    rewrite Genv.find_def_symbol in H2. des. clarify.
Qed.

Require Import ClightPlusMem0.

Lemma compile_init_mem_success clight_prog mn md sk_mem:
  compile clight_prog mn = Some md ->
  mem_skel clight_prog = Some sk_mem ->
  exists m tm,
  load_mem (Sk.canon (Sk.add sk_mem (Mod.sk md))) = Some m 
  /\ Genv.init_mem clight_prog = Some tm
  /\ match_mem (Sk.canon (Sk.add sk_mem (Mod.sk md))) (globalenv clight_prog) m tm.
Proof.
Admitted.
