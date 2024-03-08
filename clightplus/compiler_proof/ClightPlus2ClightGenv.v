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
revert t. induction l; unfold get_sk; i; des_ifs; ss; cycle 2.
{ apply IHl. unfold get_sk. ss. des_ifs. inv l0. exfalso. et. } { econs. }
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
    { ss. des_ifs. unfold get_sk. ss. des_ifs. inv l0. clarify. }
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
