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
