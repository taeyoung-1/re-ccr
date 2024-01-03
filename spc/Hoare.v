Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Export HoareDef STB.
Require Import Hoareproof0 Hoareproof1 Hoareproof2.
Require Import SimModSem ProofMode.

Set Implicit Arguments.



Lemma fold_right_map
      XS XI YS YI
      (xs: XS) (xi: list XI)
      (xadd: XI -> XS -> XS)

      (* (ys: YS) (yi: list YI) *)
      (yadd: YI -> YS -> YS)

      (fs: XS -> YS)
      (fi: XI -> YI)
      (HOM: forall xi xs, fs (xadd xi xs) = yadd (fi xi) (fs xs))
  :
    <<EQ: fs (fold_right xadd xs xi) = fold_right yadd (fs xs) (List.map fi xi)>>
.
Proof.
  r. ginduction xi; ii; ss.
  rewrite HOM. f_equal. eapply IHxi; et.
Qed.

(*** TODO: move to Coqlib ***)
Lemma find_app
      X (xs0 xs1: list X) (f: X -> bool) x
      (FIND: find f xs0 = Some x)
  :
    <<FIND: find f (xs0 ++ xs1) = Some x>>
.
Proof.
  revert_until xs0. induction xs0; ii; ss. des_ifs. erewrite IHxs0; et.
Qed.











Section CANCELSTB.

  Context `{Σ: GRA.t}.

  Variable md: SMod.t.

  Let sk: Sk.t := SMod.get_sk md.

  Let _ms: Sk.t -> SModSem.t := fun sk => (SMod.get_modsem md sk).
  Let _sbtb: Sk.t -> list (gname * fspecbody) := fun sk => ((SModSem.fnsems) (_ms sk)).
  Let _stb: Sk.t -> list (gname * fspec) := fun sk => List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) (_sbtb sk).

  Let ms: SModSem.t := _ms sk.
  Let sbtb: list (gname * fspecbody) := _sbtb sk.

  Variable stb: Sk.t -> gname -> option fspec.
  Hypothesis STBCOMPLETE:
    forall fn fsp (FIND: alist_find fn (_stb sk) = Some fsp), stb sk fn = Some fsp.
  Hypothesis STBSOUND:
    forall fn (FIND: alist_find fn (_stb sk) = None),
      (<<NONE: stb sk fn = None>>) \/ (exists fsp, <<FIND: stb sk fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>).

  Let md_src: Mod.t := (SMod.to_src) md.
  Let md_tgt: Mod.t := (SMod.to_tgt stb) md.



  Let W: Type := p_state.
  (* Let wf: Ord.t -> W -> W -> Prop := top3. *)

  Opaque interp_Es.

  Let ms_src: ModSem.t := Mod.enclose md_src.
  Let ms_tgt: ModSem.t := Mod.enclose md_tgt.

  Section STRONGER.
  Context {CONFS CONFT: EMSConfig}.
  Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

  Theorem adequacy_type_arg_stb
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb sk "main" = Some main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) x (@initial_arg CONFS) (@initial_arg CONFT) entry_r>>) /\
               (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
               (<<WFR: URA.wf (entry_r ⋅ (SModSem.initial_mr ms))>>) /\
               (<<RET: forall ret_src ret_tgt,
                   ((main_fsp.(postcond) x ret_src ret_tgt: iProp) -∗ ⌜ret_src = ret_tgt⌝)>>))
    :
      Beh.of_program (@Mod.compile _ CONFT md_tgt) <1=
      Beh.of_program (@Mod.compile _ CONFS md_src).
  Proof.
    ii. eapply adequacy_type_m2s; et.
    eapply adequacy_type_m2m; et.
    eapply adequacy_type_t2m; et.
    i. exploit MAINM; et. i. des. esplits; et.
    i. specialize (RET ret_src ret_tgt). uipropall.
    hexploit RET; et. i. rr in H. uipropall.
    all:ss.
  Qed.
  End STRONGER.


  Context {CONF: EMSConfig}.
  Variable entry_r: Σ.

  Hypothesis WFR: URA.wf (entry_r ⋅ SMod.get_init_st md sk).

  Hypothesis MAINM: forall (main_fsp: fspec) (MAIN: stb sk "main" = Some main_fsp),
      exists (x: main_fsp.(meta)),
        (<<PRE: Own (entry_r) -∗ main_fsp.(precond) x initial_arg initial_arg>>) /\
        (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
        (<<RET: forall ret_src ret_tgt,
            (main_fsp.(postcond) x ret_src ret_tgt: iProp) -∗ (⌜ret_src = ret_tgt⌝)>>).

  Theorem adequacy_type_stb: refines_closed md_tgt md_src.
  Proof.
    ii. eapply adequacy_type_arg_stb; et.
    i. hexploit MAINM; et. i. des. esplits; et.
    eapply to_semantic.
    - eapply PRE. 
    - eapply URA.wf_mon; et.
  Qed.

End CANCELSTB.


Section CANCEL.

  Context `{Σ: GRA.t}.

  Variable md: SMod.t.

  Let sk: Sk.t := SMod.get_sk md.
  Let stb0: Sk.t -> gname -> option fspec := fun sk => to_stb (SMod.get_stb md sk).
  Let stb1: Sk.t -> gname -> option fspec := fun sk => to_closed_stb (SMod.get_stb md sk).

  Let md_src: Mod.t := (SMod.to_src) md.
  Let md_tgt0: Mod.t := (SMod.to_tgt stb0) md.
  Let md_tgt1: Mod.t := (SMod.to_tgt stb1) md.

  Section STRONGER.
  Context {CONFS CONFT: EMSConfig}.
  Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

  Theorem adequacy_type_arg
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb0 sk "main" = Some main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) x (@initial_arg CONFS) (@initial_arg CONFT) entry_r>>) /\
               (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
               (<<WFR: URA.wf (entry_r ⋅ SMod.get_init_st md sk)>>) /\
               (<<RET: forall ret_src ret_tgt,
                   ((main_fsp.(postcond) x ret_src ret_tgt: iProp) -∗ ⌜ret_src = ret_tgt⌝)>>))
    :
      Beh.of_program (@Mod.compile _ CONFT md_tgt0) <1=
      Beh.of_program (@Mod.compile _ CONFS md_src).
  Proof.
    eapply adequacy_type_arg_stb; et.
  Qed.

  Theorem adequacy_type_arg_closed
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb1 sk "main" = Some main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) x (@initial_arg CONFS) (@initial_arg CONFT) entry_r>>) /\
               (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
               (<<WFR: URA.wf (entry_r ⋅ SMod.get_init_st md sk)>>) /\
               (<<RET: forall ret_src ret_tgt,
                   ((main_fsp.(postcond) x ret_src ret_tgt: iProp) -∗ ⌜ret_src = ret_tgt⌝)>>))
    :
      Beh.of_program (@Mod.compile _ CONFT md_tgt1) <1=
      Beh.of_program (@Mod.compile _ CONFS md_src).
  Proof.
    eapply adequacy_type_arg_stb; et.
    { unfold stb1, sk, SMod.get_stb, SMod.get_sk. unfold to_closed_stb.
      i. ss. unfold map_snd. rewrite FIND. et. }
    { unfold stb1, sk, SMod.get_stb, SMod.get_sk. unfold to_closed_stb.
      ss. i. right. unfold map_snd.
      rewrite FIND. esplits; et. }
  Qed.
  End STRONGER.

  Context {CONF: EMSConfig}.
  Variable entry_r: Σ.

  Hypothesis WFR: URA.wf (entry_r ⋅ SMod.get_init_st md sk).

  Section TYPE0.
  Hypothesis MAINM: forall (main_fsp: fspec) (MAIN: stb0 sk "main" = Some main_fsp),
      exists (x: main_fsp.(meta)),
        (<<PRE: Own (entry_r) -∗ main_fsp.(precond) x initial_arg initial_arg>>) /\
        (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
        (<<RET: forall ret_src ret_tgt,
            (main_fsp.(postcond) x ret_src ret_tgt: iProp) -∗ (⌜ret_src = ret_tgt⌝)>>).

  Theorem adequacy_type: refines_closed md_tgt0 md_src.
  Proof.
    ii. eapply adequacy_type_arg; et.
    i. hexploit MAINM; et. i. des. esplits; et.
    { eapply to_semantic.
      { uipropall. }
      { eapply URA.wf_mon; et. }
    }
  Qed.
  End TYPE0.


  Section TYPE1.
  Hypothesis MAINM: forall (main_fsp: fspec) (MAIN: stb1 sk "main" = Some main_fsp),
      exists (x: main_fsp.(meta)),
        (<<PRE: Own (entry_r) -∗ main_fsp.(precond) x initial_arg initial_arg>>) /\
        (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
        (<<RET: forall ret_src ret_tgt,
            (main_fsp.(postcond) x ret_src ret_tgt: iProp) -∗ (⌜ret_src = ret_tgt⌝)>>).

  Theorem adequacy_type_closed: refines_closed md_tgt1 md_src.
  Proof.
    ii. eapply adequacy_type_arg_closed; et.
    i. hexploit MAINM; et. i. des. esplits; et.
    { eapply to_semantic.
      { uipropall. }
      { eapply URA.wf_mon; et. }
    }
  Qed.
  End TYPE1.

End CANCEL.




Require Import Weakening.
Require Import ClassicalChoice.

Section CANCEL.

  Context `{Σ: GRA.t}.

  Variable md: SMod.t.


  Let sk: Sk.t := SMod.get_sk md.
  (* Let sk: Sk.t := Sk.sort (fold_right Sk.add Sk.unit (List.map SMod.sk md)). *)
  (* Let skenv: SkEnv.t := Sk.load_skenv sk. *)

  Let _ms: Sk.t -> SModSem.t := fun sk => (SMod.get_modsem md sk).
  Let _sbtb: Sk.t -> list (gname * fspecbody) := fun sk => ((SModSem.fnsems) (_ms sk)).
  Let _stb: Sk.t -> list (gname * fspec) := fun sk => List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) (_sbtb sk).

  Let ms: SModSem.t := _ms sk.
  Let sbtb: list (gname * fspecbody) := _sbtb sk.

  Let stb: gname -> option fspec :=
    fun fn => match alist_find fn (_stb sk) with
              | Some fsp => Some fsp
              | None => Some fspec_trivial
              end.

  Let md_src: Mod.t := (SMod.to_src) md.
  Variable md_tgt: Mod.t.


  Hypothesis WEAKEN: (fun md md_tgt => exists stb0, (<<WEAK: forall sk, stb_weaker (stb0 sk) stb>>)
                                                            /\ (<<MD: md_tgt = SMod.to_tgt stb0 md>>)) md md_tgt.

  (* Hypothesis WEAKEN: Forall2 (fun md md_tgt => exists stb0, (<<WEAK: forall sk, stb_weaker (stb0 sk) stb>>)
                                                            /\ (<<MD: md_tgt = SMod.to_tgt stb0 md>>)) md md_tgt. *)

  Opaque interp_Es.

  Let ms_src: ModSem.t := Mod.enclose md_src.
  Let ms_tgt: ModSem.t := Mod.enclose md_tgt.

  (* Let initial_mrs_eq_aux
      sk0
    :
      List.map
        (fun x =>
           (SModSem.mn (SMod.get_modsem x sk0),
            (Any.pair (SModSem.initial_st (SMod.get_modsem x sk0)) (SModSem.initial_mr (SMod.get_modsem x sk0))↑))) md =
      ModSemL.initial_mrs (ModL.get_modsem (Mod.add_list mds_tgt) sk0)
  .
  Proof.
    clear - WEAKEN.
    eapply Forall2_impl in WEAKEN; cycle 1.
    { instantiate (1:=(fun md md_tgt => exists stb0, (<<MD: md_tgt = SMod.to_tgt stb0 md>>))).
      ii. ss. des. subst. eauto. }
    induction WEAKEN; ss.
    des; subst. ss.
    f_equal; ss.
    eapply IHf.
    inv WEAKEN; ss.
  Qed.

  Lemma sk_eq: fold_right Sk.add Sk.unit (List.map SMod.sk md) = ModL.sk (Mod.add_list mds_tgt).
  Proof.
    clear - WEAKEN.
    eapply Forall2_impl in WEAKEN; cycle 1.
    { instantiate (1:=(fun md md_tgt => exists stb0, (<<MD: md_tgt = SMod.to_tgt stb0 md>>))).
      ii. ss. des. subst. eauto. }
    induction WEAKEN; ss. des; subst. ss.
    f_equal. erewrite IHf; ss.
  Qed.

  Lemma sk_eq2: fold_right Sk.add Sk.unit (List.map SMod.sk md) = (ModL.sk (Mod.add_list (List.map (SMod.to_tgt (fun _ => stb)) md))).
  Proof.
    rewrite sk_eq. clear - WEAKEN.
    eapply Forall2_impl in WEAKEN; cycle 1.
    { instantiate (1:=(fun md md_tgt => exists stb0, (<<MD: md_tgt = SMod.to_tgt stb0 md>>))).
      ii. ss. des. subst. eauto. } des.
    unfold Mod.add_list.
    erewrite fold_right_map with (fi:=ModL.sk) (fs:=ModL.sk) (yadd:=Sk.add); try refl; cycle 1.
    erewrite fold_right_map with (fi:=ModL.sk) (fs:=ModL.sk) (yadd:=Sk.add); try refl; cycle 1.
    f_equal.
    rewrite ! List.map_map.
    eapply Forall2_apply_Forall2 with (Q:=eq) (f:=ModL.sk ∘ (SMod.to_tgt (fun _ => stb))) (g:=(ModL.sk ∘ Mod.lift)) in WEAKEN.
    { eapply Forall2_eq in WEAKEN. des; ss. }
    ii. des. subst. ss.
  Qed.

  Lemma initial_mrs_eq
    :
      List.map
        (fun x =>
           (SModSem.mn (SMod.get_modsem x sk),
            (Any.pair (SModSem.initial_st (SMod.get_modsem x sk))) (SModSem.initial_mr (SMod.get_modsem x sk))↑)) md =
      ModSemL.initial_mrs (ModL.enclose (Mod.add_list mds_tgt))
  .
  Proof.
    unfold ModL.enclose.
    erewrite initial_mrs_eq_aux. repeat f_equal. unfold sk, SMod.get_sk.
    f_equal. rewrite sk_eq. ss.
  Qed.

  Lemma initial_mrs_eq2
    :
      List.map fst (ModSemL.initial_mrs ms_tgt) =
      List.map fst (ModSemL.initial_mrs (ModL.enclose (Mod.add_list (List.map (SMod.to_tgt (fun _ => stb)) md))))
  .
  Proof.
    unfold ms_tgt. rewrite <- initial_mrs_eq.
    unfold ModL.enclose. rewrite <- sk_eq2. folder.
    unfold Mod.add_list.
    match goal with
    | [ |- context[ModL.get_modsem ?x ?sk] ] =>
      replace (ModL.get_modsem x sk) with (((flip ModL.get_modsem) sk) x) by refl
    end.
    erewrite fold_right_map with (yadd:=ModSemL.add) (fi:=(flip ModL.get_modsem) sk); cycle 1.
    { refl. }
    erewrite fold_right_map with (yadd:=@List.app _) (fi:=ModSemL.initial_mrs); cycle 1.
    { refl. }
    rewrite ! List.map_map. cbn.
    clear - md. clearbody sk.
    induction md; ii; ss. f_equal; ss.
  Qed. *)

  Require Import ModSemFacts.

  Context {CONF: EMSConfig}.
  Lemma adequacy_type2 entry_r
        (WFR: URA.wf (entry_r ⋅ SMod.get_init_st md sk))
        (MAINM:
           forall (main_fsp: fspec) (MAIN: stb "main" = Some main_fsp),
           exists (x: main_fsp.(meta)),
             (<<PRE: Own entry_r -∗ main_fsp.(precond) x initial_arg initial_arg>>) /\
             (<<MEASURE: main_fsp.(measure) x = ord_top>>) /\
             (<<RET: forall ret_src ret_tgt,
                 (main_fsp.(postcond) x ret_src ret_tgt: iProp) -∗ (⌜ret_src = ret_tgt⌝)>>))
    :
      refines_closed md_tgt md_src.
  Proof.
    ii. eapply adequacy_type_arg_stb; ss.
    { instantiate (1:=fun _ => stb). unfold stb. i.
      unfold _stb, _sbtb, _ms, sk. rewrite FIND. auto. }
    { i. unfold stb, _stb, _sbtb, _ms, sk. rewrite FIND.
      right. esplits; et. }
    { i. ss. hexploit MAINM; et. i. des. esplits; et.
      eapply to_semantic; et.
      eapply URA.wf_mon; et. 
    }
    { revert x0 PR. eapply refines_close.
      inv WEAKEN. des. rewrite MD. eapply adequacy_weaken; et.
    }

  Qed.

End CANCEL.
