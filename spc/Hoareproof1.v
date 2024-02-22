Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
  Import ModSem.
Require Import ModSemFacts.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef.
Require Import SimSTS.
Require Import SimGlobal.
Require Import HoareDef.
From Ordinal Require Import Ordinal Arithmetic.

Set Implicit Arguments.

































Inductive opair: Type := mk_opair { ofst: Ord.t; osnd: Ord.t }.
(* Definition opair_lt: opair -> opair -> Prop := fun '(mk_opair x0 x1) '(mk_opair y0 y1) => (x0 < y0)%ord \/ (x0 == y0 /\ x1 < y1)%ord. *)
Inductive opair_lt: opair -> opair -> Prop :=
| intro_opair_lt
    x0 x1 y0 y1
    (LT: (x0 < y0)%ord \/ (x0 == y0 /\ x1 < y1)%ord)
  :
    opair_lt (mk_opair x0 x1) (mk_opair y0 y1)
.
Theorem wf_opair_lt: well_founded opair_lt.
Proof.
  ii. destruct a.
  revert osnd0. pattern ofst0. eapply well_founded_ind. { eapply Ord.lt_well_founded. } clear ofst0. intros ? IH0.
  intro. generalize dependent x. pattern osnd0. eapply well_founded_ind. { eapply Ord.lt_well_founded. } clear osnd0. intros ? IH1.
  econs. i. inv H. des.
  { eapply IH0; et. }
  { eapply IH1; et. i. eapply IH0; et. rewrite <- LT. ss. }
Qed.











Section CANCEL.

  (*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
  Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)



  Context `{Σ: GRA.t}.

  Variable md: SMod.t.

  Let sk: Sk.t := Sk.sort (Sk.add Sk.unit (SMod.sk md)).
  (* Let skenv: SkEnv.t := Sk.load_skenv sk. *)
  Let ms: SModSem.t := SMod.get_modsem md sk.
  Let sbtb := SModSem.fnsems ms.
  Let _stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb.

  Variable stb: gname -> option fspec.
  Hypothesis STBCOMPLETE:
    forall fn fsp (FIND: alist_find fn _stb = Some fsp), stb fn = Some fsp.
  Hypothesis STBSOUND:
    forall fn (FIND: alist_find fn _stb = None),
      (<<NONE: stb fn = None>>) \/ (exists fsp, <<FIND: stb fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>).


  Let md_mid2: Mod.t := SMod.to_mid2 stb md.
  Let md_mid: Mod.t := SMod.to_mid stb md.



  Let W: Type := p_state.
  (* Let wf: Ord.t -> W -> W -> Prop := top3. *)

  Opaque interp_Es.

  Let ms_mid2: ModSem.t := Mod.enclose md_mid2.
  Let ms_mid: ModSem.t := Mod.enclose md_mid.

  Let p_mid2 := ModSem.prog ms_mid2.
  Let p_mid := ModSem.prog ms_mid.

  Ltac _step tac :=
    match goal with
    (*** terminal cases ***)
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (triggerUB >>= _) _ ] =>
      unfold triggerUB; mred; _step tac; ss; fail
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (triggerNB >>= _) _ ] =>
      exfalso
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (triggerUB >>= _) ] =>
      exfalso
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (triggerNB >>= _) ] =>
      unfold triggerNB; mred; _step tac; ss; fail

    (*** assume/guarantee ***)
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (assume ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (assume ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar

    (*** default cases ***)
    | _ =>
      (tac; econs; auto;
       (*** some post-processing ***)
       i;
       try match goal with
           | [ |- (eq ==> _)%signature _ _ ] =>
             let v_src := fresh "v_src" in
             let v_tgt := fresh "v_tgt" in
             intros v_src v_tgt ?; subst v_tgt
           end)
    end
  .

  Ltac steps := repeat (mred; try _step ltac:(guclo simg_safe_spec); des_ifs_safe).
  Ltac steps_strong := repeat (mred; try (_step ltac:(guclo simg_indC_spec)); des_ifs_safe).

  Lemma stb_find_iff_aux fn
    :
      ((<<NONE: alist_find fn _stb = None>>) /\
       (<<FINDSRC: alist_find fn (fnsems ms_mid2) = None>>) /\
       (<<FINDMID: alist_find fn (fnsems ms_mid) = None>>)) \/

      (exists (f: fspecbody),
          (<<SOME: alist_find fn _stb = Some (f: fspec)>>) /\
          (<<FINDSRC: alist_find fn (fnsems ms_mid2) =
                      Some (fun_to_mid2 (fsb_body f))>>) /\
          (<<FINDMID: alist_find fn (fnsems ms_mid) =
                      Some (fun_to_mid stb (fsb_body f))>>)).
  Proof.
    unfold ms_mid2, ms_mid, md_mid, md_mid2, SMod.to_mid2, SMod.to_mid.
    rewrite SMod.transl_fnsems. rewrite SMod.transl_fnsems. fold sk.
    unfold _stb at 1 2. unfold sbtb, ms.
    unfold SMod.load_fnsems. rewrite ! SMod.red_do_ret2.
    rewrite ! alist_find_map. uo.
    destruct (alist_find fn (SModSem.fnsems (SMod.get_modsem md sk))) eqn:FIND.
    - right. esplits; et.
    - left. esplits; et.
  Qed.

  Lemma stb_find_iff fn
    :
      ((<<NONE: stb fn = None>> \/ (exists fsp, <<FIND: stb fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>)) /\
       (<<FINDSRC: alist_find fn (fnsems ms_mid2) = None>>) /\
       (<<FINDMID: alist_find fn (fnsems ms_mid) = None>>)) \/

      (exists (f: fspecbody),
          (<<STB: stb fn = Some (f: fspec)>>) /\
          (<<FINDSRC: alist_find fn (fnsems ms_mid2) =
                      Some (fun_to_mid2 (fsb_body f))>>) /\
          (<<FINDMID: alist_find fn (fnsems ms_mid) =
                      Some (fun_to_mid stb (fsb_body f))>>)).
  Proof.
    hexploit (stb_find_iff_aux fn). i. des.
    { left. esplits; et. }
    { right. esplits; et. }
  Qed.

  Let adequacy_type_aux__APC:
    forall at_most o0
           st_src0 st_tgt0
    ,
      simg (fun (st_src1: p_state * unit) '(st_tgt1, x) => st_tgt1 = st_tgt0)
           BB BB (Ret (st_src0, tt))
           (interp_Es p_mid ((interp_hCallE_mid stb (ord_pure o0) (_APC at_most))) st_tgt0)
  .
  Proof. Admitted.
    (* ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    (* induction *)
    intros ? ?. remember (mk_opair o0 at_most) as fuel. move fuel at top. revert at_most o0 Heqfuel.
    pattern fuel. eapply well_founded_induction. { eapply wf_opair_lt. } clear fuel.
    intros fuel IH. i.

    rewrite unfold_APC. steps.
    destruct x.
    { steps. }
    steps. hexploit (stb_find_iff s). i. des.
    { rewrite NONE. steps. }
    { rewrite FIND. steps. exfalso. eapply x1; et. }
    rewrite STB. steps. ss.
    rewrite ! alist_find_map in *.
    rewrite FINDMID. unfold fun_to_mid. steps.
   rewrite idK_spec at 1.
    guclo bindC_spec. econs.
    { unfold APC. steps. eapply simg_flag_down.
      eapply IH; auto. econs. left. auto.
    }

    i. ss. destruct vret_tgt as [? []]. destruct vret_src as [? []]. ss. des; subst.
    unfold idK. steps. eapply simg_flag_down.
    eapply IH; et. econs; et. right; split; et. refl.
  Qed. *)

  Let adequacy_type_aux_APC:
    forall o0 st_src0 st_tgt0
    ,
      simg (fun (st_src1: p_state * unit) '(st_tgt1, _) => st_tgt1 = st_tgt0)
           BB BB (Ret (st_src0, tt))
           (interp_Es p_mid ((interp_hCallE_mid stb (ord_pure o0) APC)) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    i. unfold APC. steps. eapply simg_flag_down.
    gfinal. right.
    eapply adequacy_type_aux__APC.
    Unshelve. all: try exact 0.
  Qed.

  Lemma idK_spec2: forall E A B (a: A) (itr: itree E B), itr = Ret a >>= fun _ => itr. Proof. { i. ired. ss. } Qed.

  Let adequacy_type_aux:
    forall
      o0
      A (body: itree _ A) st_src0 st_tgt0
      (SIM: st_tgt0 = st_src0)
    ,
      simg eq
           BB BB
           (interp_Es p_mid2 ((interp_hCallE_mid2 body)) st_src0)
           (interp_Es p_mid ((interp_hCallE_mid stb o0 body)) st_tgt0)
  .
  Proof. Admitted.
    (* ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    gcofix CIH. i. ides body.
    { steps. }
    { steps. eapply simg_progress_flag. gbase. eapply CIH; ss. }

    destruct e; cycle 1.
    { rewrite <- bind_trigger. resub. steps.
      destruct s; ss.
      { destruct s; resub; ss.
        steps. eapply simg_progress_flag. gbase. eapply CIH; ss; et.
      }
      { dependent destruction e; resub; ss.
        - steps. steps_strong. exists x. steps. eapply simg_progress_flag. gbase. eapply CIH; et.
        - steps. steps_strong. exists x. steps. eapply simg_progress_flag. gbase. eapply CIH; et.
        - steps_strong. eapply simg_progress_flag. gbase. eapply CIH; et.
      }
    }
    dependent destruction h.
    rewrite <- bind_trigger. resub.
    ired_both. hexploit (stb_find_iff fn). i. des.
    { rewrite NONE. steps. }
    { rewrite FIND. steps. destruct tbr.
      { exfalso. eapply x; ss. }
      steps.
      ss. rewrite ! alist_find_map in *.
      rewrite FINDSRC. steps.
    }
    rewrite STB. steps. destruct tbr.
    (* PURE *)
    { Local Opaque ord_lt. ired_both. steps.
      ss. rewrite ! alist_find_map in *.
      rewrite FINDMID. unfold fun_to_mid. ired_both.
      rewrite idK_spec2 at 1.
      guclo bindC_spec. econs.
      { eapply simg_flag_down. gfinal. right. eapply paco7_mon. { eapply adequacy_type_aux_APC. } ii; ss. }
      i. steps. steps_strong. exists x2. steps. eapply simg_progress_flag.
      gbase. eapply CIH. ss.
    }

    (* IMPURE *)
    { Local Opaque ord_lt. unfold guarantee. steps.
      ss. rewrite ! alist_find_map in *.
      rewrite FINDMID. rewrite FINDSRC.
      unfold fun_to_mid2, cfunN, fun_to_mid. steps.
      guclo bindC_spec. econs.
      { eapply simg_progress_flag. gbase. eapply CIH. ss. }
      i. subst. steps.
      steps.
      eapply simg_progress_flag. gbase. eapply CIH. ss.
    }
    Unshelve. all: ss.
  Qed. *)

  Lemma sk_eq:
    Mod.sk md_mid = Mod.sk md_mid2.
  Proof. ss. Qed.

  Lemma initial_mrs_eq:
    init_st ms_mid = init_st ms_mid2.
  Proof. ss. Qed.

  Lemma fns_eq:
    (List.map fst (fnsems (Mod.enclose (md_mid))))
    =
    (List.map fst (fnsems (Mod.enclose (md_mid2)))).
  Proof.
    pose proof sk_eq. unfold Mod.enclose.
    unfold md_mid2, md_mid, Mod.enclose.
    unfold md_mid2, md_mid in H. rewrite H.
    generalize (Mod.sk ((SMod.to_mid2 stb) md)). i.
    ss. rewrite ! List.map_map. f_equal. 
    extensionality fnsb. destruct fnsb as [fn sb]. ss.
  Qed.

  Context `{CONF: EMSConfig}.
  Definition midConf: EMSConfig := {| finalize := finalize; initial_arg := Any.pair ord_top↑ initial_arg |}.
  Theorem adequacy_type_m2m:
    Beh.of_program (@Mod.compile _ midConf md_mid) <1=
    Beh.of_program (Mod.compile md_mid2).
  Proof. Admitted.
    (* eapply adequacy_global_itree; ss.
    ginit.
    { eapply cpn7_wcompat; eauto with paco. }
    unfold ModSem.initial_itr, ModSem.initial_itr. Local Opaque ModSem.prog. ss.
    unfold ITree.map. steps.
    Local Transparent ModSem.prog.
    unfold ModSem.prog at 4.
    unfold ModSem.prog at 2.
    Local Opaque ModSem.prog.
    ss. steps_strong.
    esplits; et.
    { des. inv x. split.
      { inv H. econs.
        rewrite fns_eq. auto. 
      }
      { ss. }
    }
    steps.

    (* stb main *)
    hexploit (stb_find_iff "main"). i. des.
    { ss. rewrite FINDSRC. steps. }
    { ss. rewrite FINDSRC. steps. }

    fold ms_mid2. fold ms_mid. ss.
    rewrite FINDSRC. rewrite FINDMID. steps.
    unfold fun_to_mid2, fun_to_mid, cfunN. steps.
    guclo bindC_spec. econs.
    { eapply simg_flag_down. gfinal. right. eapply adequacy_type_aux. ss. }
    { i. subst. steps. }
  Qed. *)

End CANCEL.
