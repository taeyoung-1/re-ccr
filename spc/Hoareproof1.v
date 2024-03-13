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

  Variable mds: list SMod.t.

  Let sk: Sk.t := Sk.sort (fold_right Sk.add Sk.unit (List.map SMod.sk mds)).
  (* Let skenv: SkEnv.t := Sk.load_skenv sk. *)
  Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) sk) mds).
  Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss).
  Let _stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb.
  
  Variable stb: gname -> option fspec.
  Hypothesis STBCOMPLETE:
    forall fn fsp (FIND: alist_find fn _stb = Some fsp), stb fn = Some fsp.
  Hypothesis STBSOUND:
    forall fn (FIND: alist_find fn _stb = None),
      (<<NONE: stb fn = None>>) \/ (exists fsp, <<FIND: stb fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>).

  Let mds_mid2: list Mod.t := List.map (SMod.to_mid2 stb) mds.
  Let mds_mid: list Mod.t := List.map (SMod.to_mid stb) mds.

  Let md_mid2: Mod.t := Mod.add_list mds_mid2.
  Let md_mid: Mod.t := Mod.add_list mds_mid.



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

      (exists (f: fspecbody) (run_: RUN),
              (* (emb: forall T, Es T -> Es T), *)
          (<<SOME: alist_find fn _stb = Some (f: fspec)>>) /\
          (<<FINDSRC: alist_find fn (fnsems ms_mid2) =
                      Some ((translate (emb_ run_)  (T:=Any.t)) ∘ fun_to_mid2 (fsb_body f))>>) /\
          (<<FINDMID: alist_find fn (fnsems ms_mid) =
                      Some ((translate (emb_ run_) (T:=Any.t)) ∘ fun_to_mid stb (fsb_body f))>>)).
  Proof.
    unfold ms_mid2, ms_mid, md_mid, md_mid2, mds_mid, mds_mid2, SMod.to_mid2, SMod.to_mid.
    rewrite SMod.transl_fnsems. rewrite SMod.transl_fnsems. fold sk.
    unfold _stb at 1 2. unfold sbtb, mss. rewrite alist_find_map.
    generalize mds. induction mds0; ss; auto. unfold SMod.get_fnsems.


    rewrite ! alist_find_app_o. erewrite ! SMod.red_do_ret2. uo. 
    destruct (alist_find fn (SModSem.fnsems (SMod.get_modsem a sk))) eqn: AFIND.
    { 
      right. destruct mds0.
      { 
        rewrite ! alist_find_map. uo.  rewrite AFIND.
        exists f. exists run_id. 
        (* esplits; et.
        { unfold run_id. f_equal. apply func_ext. i. erewrite (bisimulation_is_eq _ _ (translate_id _ _ _)). } *)
        esplits; et; (f_equal; apply func_ext; i; rewrite <- emb_run_id; rewrite emb_id_eq; refl).
      }
      { 
        unfold trans_l, trans_r. rewrite ! alist_find_app_o.
        rewrite ! alist_find_map. uo. rewrite AFIND.
        esplits; et. 
      }
    }
    { 
      destruct mds0. 
      { s. rewrite ! alist_find_map. uo. rewrite AFIND. left. esplits; et. }
      { 
        s. unfold trans_l, trans_r. rewrite ! alist_find_app_o.
        rewrite ! alist_find_map. uo. rewrite AFIND. 
        s in IHmds0. unfold SMod.get_fnsems, trans_l, trans_r in IHmds0.
        rewrite ! alist_find_app_o in IHmds0. erewrite ! SMod.red_do_ret2 in IHmds0.
        des.
        { 
          left. esplits; et; unfold SMod.get_fnsems; rewrite SMod.red_do_ret2.
          - rewrite FINDSRC. refl.
          - rewrite FINDMID. refl.        
        }
        {
          right. exists f. esplits; et; unfold SMod.get_fnsems; rewrite SMod.red_do_ret2. 
          - rewrite FINDSRC.
            f_equal. apply func_ext. i. erewrite <- (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
            replace emb_r with (emb_ run_r); ss.
            repeat f_equal. unfold emb_. unfold ">>>", Cat_IFun. extensionalities. des_ifs.
          - rewrite FINDMID.
            f_equal. apply func_ext. i. erewrite <- (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
            repeat f_equal. unfold emb_, emb_r, ">>>", Cat_IFun. extensionalities. des_ifs.
        }
      }
    }
  Qed. 
          

  Lemma stb_find_iff fn
    :
      ((<<NONE: stb fn = None>> \/ (exists fsp, <<FIND: stb fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>)) /\
       (<<FINDSRC: alist_find fn (fnsems ms_mid2) = None>>) /\
       (<<FINDMID: alist_find fn (fnsems ms_mid) = None>>)) \/

      (exists (f: fspecbody) (run_: RUN),
          (<<STB: stb fn = Some (f: fspec)>>) /\
          (<<FINDSRC: alist_find fn (fnsems ms_mid2) =
                      Some ((translate (emb_ run_) (T:=Any.t)) ∘ fun_to_mid2 (fsb_body f))>>) /\
          (<<FINDMID: alist_find fn (fnsems ms_mid) =
                      Some ((translate (emb_ run_) (T:=Any.t)) ∘ fun_to_mid stb (fsb_body f))>>)).
  Proof.
    hexploit (stb_find_iff_aux fn). i. des.
    { left. esplits; et. }
    { right. esplits; et. }
  Qed.


  (************** Temporary tactics. ***************)
  (* Ltac steps := repeat (mred; try _step ltac:(guclo simg_safe_spec); des_ifs_safe). *)

  Ltac a1 := try rewrite ! Any.pair_split.
  Ltac a2 := try rewrite ! Any.upcast_downcast.

  Ltac t1 := try rewrite ! translate_emb_bind.
  Ltac t2 := try rewrite ! translate_emb_ret.
  Ltac t3 := try rewrite ! translate_emb_tau.
  Ltac t4 := try rewrite translate_emb_callE.
  Ltac t5 := try rewrite translate_emb_eventE.
  Ltac t6 := try rewrite translate_emb_sE.
  Ltac t7 := try rewrite translate_emb_triggerUB.
  Ltac t8 := try rewrite translate_emb_triggerNB.

  Ltac tset := t1; t2; t3; t4; t5; t6; t7; t8.

  Ltac m1 := try rewrite ! interp_mid_bind.
  Ltac m2 := try rewrite ! interp_mid_ret.
  Ltac m3 := try rewrite ! interp_mid_tau.
  Ltac m4 := try rewrite interp_mid_hcall.
  Ltac m5 := try rewrite interp_mid_triggere.
  Ltac m6 := try rewrite interp_mid_triggerp.

  Ltac mset := m1; m2; m3; m4; m5; m6.

  Ltac n1 := try rewrite ! interp_mid2_bind.
  Ltac n2 := try rewrite ! interp_mid2_ret.
  Ltac n3 := try rewrite ! interp_mid2_tau.
  Ltac n4 := try rewrite interp_mid2_hcall.
  Ltac n5 := try rewrite interp_mid2_triggere.
  Ltac n6 := try rewrite interp_mid2_triggerp.

  Ltac nset := n1; n2; n3; n4; n5; n6.


  Ltac h1 := try rewrite ! interp_hEs_tgt_bind.
  Ltac h2 := try rewrite ! interp_hEs_tgt_ret.
  Ltac h3 := try rewrite ! interp_hEs_tgt_tau.
  Ltac h4 := try rewrite ! interp_hEs_tgt_hapc.
  Ltac h5 := try rewrite interp_hEs_tgt_triggere.
  Ltac h6 := try rewrite interp_hEs_tgt_triggerp.

  Ltac hset := h1; h2; h3; h4; h5; h6.


  Ltac tstep := repeat (unfold guarantee; a1; a2; tset; steps).
  Ltac mstep := repeat (unfold guarantee; a1; a2; tset; mset; steps).
  Ltac nstep := repeat (unfold guarantee; a1; a2; tset; mset; nset; steps).
  Ltac hstep := repeat (unfold guarantee; a1; a2; tset; mset; nset; hset; steps).


  (* emb too general. Need a property that it only changes SUpdate event. *)
  Let adequacy_type_aux__APC:
    forall at_most o0
           st_src0 st_tgt0 run_
    ,
      simg (fun (st_src1: p_state * unit) '(st_tgt1, x) => st_tgt1 = st_tgt0)
           false false (Ret (st_src0, tt))
           (interp_Es p_mid (translate (emb_ run_) (interp_hCallE_mid stb (ord_pure o0) (_APC at_most))) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    (* induction *)
    intros ? ?. remember (mk_opair o0 at_most) as fuel. move fuel at top. revert at_most o0 Heqfuel.
    pattern fuel. eapply well_founded_induction. { eapply wf_opair_lt. } clear fuel.
    intros fuel IH. i.
    rewrite unfold_APC.
    mstep.
    destruct x.
    { mstep. } 
    mstep.
    hexploit (stb_find_iff s). i. des.
    { rewrite NONE. mstep. }
    { rewrite FIND. mstep. unfold unwrapU. steps. eapply x1; et. }
    rewrite STB. hstep.
    rewrite FINDMID. unfold fun_to_mid. hstep.
   rewrite idK_spec at 1.
    guclo bindC_spec. econs.
    { 
      unfold APC. mstep.
      eapply simg_flag_down.
      eapply IH; auto. econs. left. auto.
    }
    i. ss. destruct vret_tgt as [? []]. destruct vret_src as [? []]. ss. des; subst.
    unfold idK.
    mstep.
    eapply simg_flag_down.
    eapply IH; et. econs; et. right; split; et. refl.
  Qed.

  Let adequacy_type_aux_APC:
    forall o0 st_src0 st_tgt0 run_
    ,
      simg (fun (st_src1: p_state * unit) '(st_tgt1, _) => st_tgt1 = st_tgt0)
           false false (Ret (st_src0, tt))
           (interp_Es p_mid (translate (emb_ run_) (interp_hCallE_mid stb (ord_pure o0) APC)) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    i. unfold APC.
    mstep.
    eapply simg_flag_down.
    gfinal. right.
    eapply adequacy_type_aux__APC.
    Unshelve. all: try exact 0.
  Qed.

  Lemma idK_spec2: forall E A B (a: A) (itr: itree E B), itr = Ret a >>= fun _ => itr. Proof. { i. ired. ss. } Qed.

  Let adequacy_type_aux:
    forall
      o0 run_
      A (body: itree _ A) st_src0 st_tgt0
      (SIM: st_tgt0 = st_src0)
    ,
      simg eq
           false false
           (interp_Es p_mid2 (translate (emb_ run_) (interp_hCallE_mid2 body)) st_src0)
           (interp_Es p_mid (translate (emb_ run_) (interp_hCallE_mid stb o0 body)) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    gcofix CIH. i. ides body.
    { nstep. } 
    { nstep. eapply simg_progress_flag. gbase. eapply CIH; ss. } 

    destruct e; cycle 1.
    { rewrite <- bind_trigger. resub. nstep.
      destruct s; ss.
      { destruct s; resub; ss.
        nstep. eapply simg_progress_flag. gbase. eapply CIH; ss; et.
      }
      {
         dependent destruction e; resub; ss; nstep; steps_strong.
        - exists x. nstep.  
          eapply simg_progress_flag. gbase. eapply CIH; et.
        - exists x. nstep. 
          eapply simg_progress_flag. gbase. eapply CIH; et.
        - eapply simg_progress_flag. gbase. eapply CIH; et.
      }
    }
    dependent destruction h.
    rewrite <- bind_trigger. resub.
    nstep. 
    ired_both. hexploit (stb_find_iff fn). i. des.
    { rewrite NONE. nstep. }
    { rewrite FIND. nstep. destruct tbr.
      { exfalso. eapply x; ss. }
      nstep.
      ss. rewrite FINDSRC. nstep.
    }
    rewrite STB. nstep. destruct tbr.
    (* PURE *)
    { Local Opaque ord_lt. ired_both. nstep.
      ss. 
      rewrite FINDMID. unfold fun_to_mid. ired_both.
      hstep.




      rewrite idK_spec2 at 1.
      guclo bindC_spec. econs.
      { eapply simg_flag_down. gfinal. right. eapply paco7_mon. { eapply adequacy_type_aux_APC. } ii; ss. }
      i. nstep.
      steps_strong. exists x2. nstep. eapply simg_progress_flag.
      gbase. eapply CIH. ss.
    }

    (* IMPURE *)
    { Local Opaque ord_lt. nstep.
      ss. 
      rewrite FINDMID. rewrite FINDSRC.
      unfold fun_to_mid2, cfunN, fun_to_mid. tstep.



      guclo bindC_spec. econs.
      { eapply simg_progress_flag. gbase. eapply CIH with (A:=Any.t). ss. }
      i. subst. tstep.
      eapply simg_progress_flag. gbase. eapply CIH. ss.
    }
    Unshelve. all: ss.
  Qed.


  Require Import ModSemFacts.

  Lemma sk_eq:
    Mod.sk md_mid = Mod.sk md_mid2.
  Proof. 
    unfold md_mid, md_mid2, mds_mid, mds_mid2.
    rewrite ! ModFacts.add_list_sk. f_equal.
    generalize mds. clear. i.  induction mds; ss.
    rewrite IHl. ss.
  Qed.

  Lemma initial_mrs_eq:
    init_st ms_mid = init_st ms_mid2.
  Proof.
    pose proof sk_eq.
    unfold ms_mid, ms_mid2, md_mid, md_mid2, mds_mid, mds_mid2, Mod.enclose.
    unfold md_mid, md_mid2, mds_mid, mds_mid2 in H. rewrite H.
    generalize (Mod.sk (Mod.add_list (List.map (SMod.to_mid2 stb) mds))). i.
    rewrite ! ModFacts.add_list_initial_mrs.
    generalize mds. clear. i. 
    induction mds; et.
    destruct l; ss.
    rewrite IHl. ss.
  Qed.

  Lemma fns_eq:
    (List.map fst (fnsems (Mod.enclose (md_mid))))
    =
    (List.map fst (fnsems (Mod.enclose (md_mid2)))).
  Proof.
    pose proof sk_eq. unfold Mod.enclose.
    unfold md_mid2, md_mid, mds_mid2, mds_mid, Mod.enclose.
    unfold md_mid2, md_mid, mds_mid2, mds_mid in H. rewrite H.
    generalize (Mod.sk (Mod.add_list (List.map (SMod.to_mid2 stb) mds))). i.
    rewrite ! ModFacts.add_list_fns. rewrite ! List.map_map. f_equal. 
    f_equal. extensionality sm. ss. rewrite ! List.map_map. f_equal.
    extensionality fnsb. destruct fnsb as [fn sb]. ss.
  Qed.

  Context `{CONF: EMSConfig}.
  Definition midConf: EMSConfig := {| finalize := finalize; initial_arg := Any.pair ord_top↑ initial_arg |}.
  Theorem adequacy_type_m2m:
    Beh.of_program (@Mod.compile _ midConf md_mid) <1=
    Beh.of_program (Mod.compile md_mid2).
  Proof.
    eapply adequacy_global_itree; ss.
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
      { ss. rewrite sk_eq. et. }
    }
    steps.

    (* stb main *)
    hexploit (stb_find_iff "main"). i. des.
    { unfold ms_mid2 in FINDSRC. rewrite FINDSRC. steps. }
    { unfold ms_mid2 in FINDSRC. rewrite FINDSRC. steps. }

    fold ms_mid2. fold ms_mid. 
    rewrite FINDSRC. rewrite FINDMID. hstep.
    unfold fun_to_mid2, fun_to_mid, cfunN. hstep.
    guclo bindC_spec. econs.
    { eapply simg_flag_down. gfinal. right. eapply adequacy_type_aux. ss. rewrite initial_mrs_eq. et. }
    { i. subst. steps. }
  Qed.

End CANCEL.
