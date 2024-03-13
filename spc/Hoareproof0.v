Require Import ProofMode.
Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import ModSemFacts.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef.
Require Import SimSTS.
Require Import SimGlobal.
From Ordinal Require Import Ordinal Arithmetic.
Require Import List.
Require Import Red IRed.


Set Implicit Arguments.

Local Open Scope nat.

















Module TAC.
  Ltac _step :=
    match goal with
    (*** terminal cases ***)
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (triggerUB >>= _) _ ] =>
      unfold triggerUB; mred; _step; ss; fail
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (triggerNB >>= _) ] =>
      unfold triggerNB; mred; _step; ss; fail
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (triggerNB >>= _) _ ] =>
      exfalso
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (triggerUB >>= _) ] =>
      exfalso

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
      (guclo simg_indC_spec; econs; eauto; try (by ss);
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
  Ltac seal_left :=
    match goal with
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_src
    end.
  Ltac seal_right :=
    match goal with
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_tgt
    end.
  Ltac unseal_left :=
    match goal with
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (@Seal.sealing _ _ ?i_src) ?i_tgt ] => unseal i_src
    end.
  Ltac unseal_right :=
    match goal with
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?i_src (@Seal.sealing _ _ ?i_tgt) ] => unseal i_tgt
    end.
  Ltac force_l := seal_right; _step; unseal_right.
  Ltac force_r := seal_left; _step; unseal_left.
  Ltac deflag := eapply simg_progress_flag.
  (* Ltac mstep := gstep; econs; eauto; [eapply from_nat_lt; ss|]. *)
End TAC.
Import TAC.


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

  Let _mss: Sk.t -> list SModSem.t := fun sk => (List.map ((flip SMod.get_modsem) sk) mds).
  Let _sbtb: Sk.t -> list (gname * fspecbody) := fun sk => (List.flat_map (SModSem.fnsems) (_mss sk)).
  Let _stb: Sk.t -> list (gname * fspec) := fun sk => List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) (_sbtb sk).

  Let mss: list SModSem.t := _mss sk.
  Let sbtb: list (gname * fspecbody) := _sbtb sk.

  Variable stb: Sk.t -> gname -> option fspec.
  Hypothesis STBCOMPLETE:
    forall fn fsp (FIND: alist_find fn (_stb sk) = Some fsp), stb sk fn = Some fsp.
  Hypothesis STBSOUND:
    forall fn (FIND: alist_find fn (_stb sk) = None),
      (<<NONE: stb sk fn = None>>) \/ (exists fsp, <<FIND: stb sk fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>).

  (* Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) sk) mds). *)
  (* Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss). *)
  (* Let stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb. *)

  Let mds_mid: list Mod.t := List.map (SMod.to_mid (stb sk)) mds.
  Let mds_tgt: list Mod.t := List.map (SMod.to_tgt stb) mds.


  Let md_mid: Mod.t := Mod.add_list mds_mid.
  Let md_tgt: Mod.t := Mod.add_list mds_tgt.

  Let ms_mid: ModSem.t := Mod.enclose md_mid.
  Let ms_tgt: ModSem.t := Mod.enclose md_tgt.


  Import ModSem.

  Lemma sk_eq:
    Mod.sk md_tgt = Mod.sk md_mid.
  Proof. 
    unfold md_tgt, md_mid, mds_tgt, mds_mid.
    rewrite ! ModFacts.add_list_sk. f_equal.
    generalize mds. clear. i. induction mds0; ss. 
    rewrite IHmds0. ss.
  Qed.

  (* Lemma fst_initial_mrs_eq:
    init_st ms_tgt = init_st ms_mid.
  Proof.
    pose proof sk_eq.
    unfold ms_mid, ms_tgt, md_mid, md_tgt, mds_mid, mds_tgt, Mod.enclose.
    unfold md_mid, md_tgt, mds_mid, mds_tgt in H. rewrite H.
    generalize (Mod.sk (Mod.add_list (List.map (SMod.to_mid (stb sk)) mds))). i.
    rewrite ! ModFacts.add_list_initial_mrs.
    generalize mds. clear. i. 
    induction mds0; et.
    destruct mds0.
    - s.
    rewrite IHmds0. ss.
  Qed. *)

  Lemma fns_eq:
    (List.map fst (fnsems (Mod.enclose (md_tgt))))
    =
    (List.map fst (fnsems (Mod.enclose (md_mid)))).
  Proof.
    pose proof sk_eq. unfold Mod.enclose.
    unfold md_tgt, md_mid, mds_tgt, mds_mid, Mod.enclose.
    unfold md_tgt, md_mid, mds_tgt, mds_mid in H. rewrite H.
    generalize (Mod.sk (Mod.add_list (List.map (SMod.to_mid (stb sk)) mds))). i.
    rewrite ! ModFacts.add_list_fns. rewrite ! List.map_map. f_equal. 
    f_equal. extensionality sm. ss. rewrite ! List.map_map. f_equal.
    extensionality fnsb. destruct fnsb as [fn sb]. ss.
  Qed.


  Lemma stb_find_iff_aux fn
    :
      ((<<NONE: alist_find fn (_stb sk) = None>>) /\
       (<<FINDMID: alist_find fn (ModSem.fnsems ms_mid) = None>>) /\
       (<<FINDTGT: alist_find fn (ModSem.fnsems ms_tgt) = None>>)) \/

      (exists (f: fspecbody) (run_: RUN),
          (<<STB: alist_find fn (_stb sk) = Some (f: fspec)>>) /\
          (<<SBTB: alist_find fn sbtb = Some f>>) /\
          (<<FINDMID: alist_find fn (ModSem.fnsems ms_mid) =
                      Some ((translate (emb_ run_)  (T:=Any.t)) ∘ fun_to_mid (stb sk) (fsb_body f))>>) /\
          (<<FINDTGT: alist_find fn (ModSem.fnsems ms_tgt) =
                      Some ((translate (emb_ run_)  (T:=Any.t)) ∘ fun_to_tgt (stb sk) f)>>)).
          (* (<<MIN: List.In (SModSem.mn (SMod.get_modsem md sk)) (List.map fst ms_tgt.(ModSemL.initial_mrs))>>)). *)
  Proof.
    unfold ms_mid, ms_tgt, md_tgt, md_mid, mds_tgt, mds_mid, SMod.to_mid, md_tgt, SMod.to_tgt.
    rewrite ! SMod.transl_fnsems. fold sk. 
    (* rewrite SMod.transl_init_st.  *)
    unfold _stb at 1 2. unfold sbtb, _sbtb, _mss. rewrite alist_find_map.
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
          - rewrite FINDMID. refl.
          - rewrite FINDTGT. refl.        
        }
        {
          right. exists f. esplits; et; unfold SMod.get_fnsems; rewrite SMod.red_do_ret2. 
          - rewrite FINDMID.
            f_equal. apply func_ext. i. erewrite <- (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
            replace emb_r with (emb_ run_r); ss.
            repeat f_equal. unfold emb_. unfold ">>>", Cat_IFun. extensionalities. des_ifs.
          - rewrite FINDTGT.
            f_equal. apply func_ext. i. erewrite <- (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
            repeat f_equal. unfold emb_, emb_r, ">>>", Cat_IFun. extensionalities. des_ifs.
        }
      }
    }
  Qed.

  Lemma stb_find_iff fn
    :
      ((<<NONE: stb sk fn = None>> \/ (exists fsp, <<FIND: stb sk fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>)) /\
       (<<FINDMID: alist_find fn (ModSem.fnsems ms_mid) = None>>) /\
       (<<FINDTGT: alist_find fn (ModSem.fnsems ms_tgt) = None>>)) \/

      (exists (f: fspecbody) (run_: RUN),
          (<<STB: stb sk fn = Some (f: fspec)>>) /\
          (<<SBTB: alist_find fn sbtb = Some f>>) /\
          (<<FINDMID: alist_find fn (ModSem.fnsems ms_mid) =
                      Some ((translate (emb_ run_)  (T:=Any.t)) ∘ fun_to_mid (stb sk) (fsb_body f))>>) /\
          (<<FINDTGT: alist_find fn (ModSem.fnsems ms_tgt) =
                      Some ((translate (emb_ run_)  (T:=Any.t)) ∘ fun_to_tgt (stb sk) f)>>)). 
  Proof.
    hexploit (stb_find_iff_aux fn). i. des.
    { left. esplits; et. }
    { right. esplits; et. }
  Qed.

  Let W: Type := (p_state).


  Let r_state: Type := Σ.
  (* Let r_state: Type := mname -> Σ. *)

  Let zip_state (mp: p_state) (mr: r_state): p_state :=
    Any.pair mp mr↑.

  (* Let rsum_minus : Σ -> Σ := 
    fun mrs_tgt => 

  Let rsum_minus (mn: mname): r_state -> Σ :=
    fun mrs_tgt => (fold_left (⋅) (List.map (update mrs_tgt mn ε) (List.map fst ms_tgt.(ModSemL.initial_mrs))) ε). *)

  (* Let rsum: r_state -> Σ :=
    fun mrs_tgt => (fold_left (⋅) (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε). *)



  (* Lemma fold_left_add (r: Σ) rs
    :
      fold_left URA.add rs r = (fold_left URA.add rs ε) ⋅ r.
  Proof.
    revert r. induction rs; ss.
    { i. rewrite URA.unit_idl. auto. }
    i. rewrite IHrs. rewrite (IHrs (ε ⋅ a)). r_solve.
  Qed. *)

  (* Let rsum_update mn (mrs: r_state) r (mns: list mname) r0
      (MIN: List.In mn mns)
      (NODUP: NoDup mns)
    :
      (fold_left (⋅) (List.map (update mrs mn r) mns) r0) ⋅ (mrs mn)
      =
      (fold_left (⋅) (List.map mrs mns) r0) ⋅ r.
  Proof.
    revert mn mrs r r0 MIN NODUP. induction mns; ss. i.
    inv NODUP. des.
    { subst. rewrite fold_left_add. rewrite (fold_left_add (r0 ⋅ mrs mn)).
      rewrite <- ! URA.add_assoc. f_equal.
      { f_equal. apply map_ext_in. i.
        unfold update. des_ifs. }
      { unfold update. des_ifs. r_solve. }
    }
    { rewrite IHmns; et.
      rewrite fold_left_add. rewrite (fold_left_add (r0 ⋅ mrs a)).
      unfold update. des_ifs. }
  Qed. *)

  (* Lemma rsum_minus_update mn0 mn1 mrs r
        (MIN0: List.In mn0 (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (MIN1: List.In mn1 (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      rsum_minus mn0 mrs ⋅ r = rsum_minus mn1 (update mrs mn0 r) ⋅ update mrs mn0 r mn1.
  Proof.
    unfold rsum_minus.
    revert MIN0 MIN1 NODUP. generalize (List.map fst (ModSemL.initial_mrs ms_tgt)). i.
    rewrite rsum_update; et.
    transitivity (fold_left (⋅) (List.map (update (update mrs mn0 ε) mn0 r) l) ε ⋅ (update mrs mn0 ε mn0)).
    { rewrite rsum_update; et. }
    { f_equal.
      { f_equal. f_equal. extensionality mn. unfold update. des_ifs. }
      { unfold update. des_ifs. }
    }
  Qed. *)

  (* Lemma rsum_minus_rsum mn mrs
        (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (IN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      rsum_minus mn mrs ⋅ mrs mn = rsum mrs.
  Proof.
    unfold rsum_minus, rsum. revert NODUP IN.
    setoid_rewrite <- (List.map_map fst mrs).
    generalize (map fst (ModSemL.initial_mrs ms_tgt)) as mns.
    i. rewrite rsum_update; et. r_solve.
  Qed. *)

  (* Lemma initial_mrs_exist
        (NODUP: List.NoDup (map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      exists (initial_mrs: r_state),
        (<<INITIALZIP:
           zip_state (ModSemL.initial_p_state ms_mid) initial_mrs =
           ModSemL.initial_p_state ms_tgt>>) /\
        (<<INITIALRSUM:
           forall mn (MIN: List.In mn (map fst ms_tgt.(ModSemL.initial_mrs))),
             rsum_minus mn initial_mrs ⋅ initial_mrs mn = fold_left URA.add (List.map SModSem.initial_mr mss) ε>>).
  Proof.
    exists (fun mn =>
              match alist_find mn (SMod.load_initial_mrs
                                     (Sk.sort (foldr Sk.add Sk.unit (map SMod.sk mds))) mds
                                     SModSem.initial_mr) with
              | Some r => r
              | _ => ε
              end).
    split.
    { revert NODUP.
      unfold ModSemL.initial_p_state, zip_state.
      unfold ms_mid, ms_tgt.
      unfold mds_mid, mds_tgt, SMod.to_mid, SMod.to_tgt. ss.
      rewrite ! SMod.transl_initial_mrs.
      change (alist string Sk.gdef) with Sk.t.
      generalize (Sk.sort (fold_right Sk.add Sk.unit (map SMod.sk mds))).
      intros sk0. i. red. extensionality mn.
      unfold SMod.load_initial_mrs.
      rewrite ! SMod.red_do_ret. clear. induction mds; ss.
      rewrite ! eq_rel_dec_correct. des_ifs.
    }
    { ii. rewrite rsum_minus_rsum; et. fold sk. unfold rsum. clear mn MIN.
      f_equal. revert NODUP.
      unfold mss, _ms, ms_tgt, mds_tgt, SMod.to_tgt.
      rewrite ! SMod.transl_initial_mrs.
      unfold SMod.load_initial_mrs.
      rewrite ! SMod.red_do_ret.
      rewrite ! List.map_map. ss. fold sk. generalize sk. clear. i.
      eapply map_ext_in. i. des_ifs.
      { eapply alist_find_some in Heq.
        eapply in_map_iff in Heq. des. clarify.
        destruct (classic (a = x)).
        { subst. auto. }
        eapply NoDup_inj_aux in H0; et. ss.
        exfalso. eapply H0. et.
      }
      { exfalso. eapply alist_find_none in Heq.
        eapply (in_map (fun x => (SModSem.mn (SMod.get_modsem x sk), SModSem.initial_mr (SMod.get_modsem x sk)))) in H; et.
      }
    }
  Qed. *)

  (* Local Opaque rsum rsum_minus. *)


  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac mred := repeat (cbn; ired_both).

  Ltac steps := repeat (mred; try _step; des_ifs_safe).


  (* Let zip_state_get st mrs mn
      (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      zip_state st mrs mn = Any.pair (st mn) (mrs mn)↑.
  Proof.
    unfold zip_state. des_ifs.
    eapply in_map_iff in MIN. des. destruct x. subst.
    eapply alist_find_none in Heq.
    exfalso. eapply Heq. et.
  Qed. *)

  (* Let zip_state_mput st mrs mn r
      (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      update (zip_state st mrs) mn (Any.pair (st mn) (Any.upcast r))
      =
      zip_state st (update mrs mn r).
  Proof.
    extensionality mn0.
    unfold update, zip_state. des_ifs.
    eapply in_map_iff in MIN. des. destruct x. subst.
    eapply alist_find_none in Heq.
    exfalso. eapply Heq. et.
  Qed. *)


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

  Ltac n1 := try rewrite ! interp_tgt_bind.
  Ltac n2 := try rewrite ! interp_tgt_ret.
  Ltac n3 := try rewrite ! interp_tgt_tau.
  Ltac n4 := try rewrite interp_tgt_hcall.
  Ltac n5 := try rewrite interp_tgt_triggere.
  Ltac n6 := try rewrite interp_tgt_triggerp.

  Ltac nset := n1; n2; n3; n4; n5; n6.


  Ltac h1 := try rewrite ! interp_hEs_tgt_bind.
  Ltac h2 := try rewrite ! interp_hEs_tgt_ret.
  Ltac h3 := try rewrite ! interp_hEs_tgt_tau.
  Ltac h4 := try rewrite ! interp_hEs_tgt_hapc.
  Ltac h5 := try rewrite interp_hEs_tgt_triggere.
  Ltac h6 := try rewrite interp_hEs_tgt_triggerp.

  Ltac hset := h1; h2; h3; h4; h5; h6.


  Ltac tstep := repeat (unfold guarantee; a1; a2; tset; steps).
  Ltac mstep := repeat (unfold guarantee; a1; a2; tset; nset; steps).
  Ltac nstep := repeat (unfold guarantee; a1; a2; tset; mset; nset; steps).
  Ltac hstep := repeat (unfold guarantee; a1; a2; tset; mset; nset; hset; steps).


  Definition run_tgt: RUN := 
  fun _ run x =>
    match Any.split x with
    | Some (st, mr) => ((Any.pair (run st).1 mr), (run st).2)
    | None => run tt↑
    end.

  Hypothesis RUN_TGT: forall X x run (run_: RUN), run_ X (run_tgt run) x = run_tgt (run_ X run) x. 

  Hypothesis RUN_STATE: forall X x run (run_: RUN), snd (run_ X run x) = snd (run x).

  Hypothesis RUN_PUT: forall x (run_: RUN), run_ unit (rPut x) = rPut x.

  Let adequacy_type_aux:
    forall RT
           mr0 frs 
           ctx0
           st_src0 st_tgt0 (i0: itree (hCallE +' sE +' eventE) RT)
           cur
           (run_: RUN)
           (ZIP: st_tgt0 = zip_state st_src0 mr0)
           (CTX: ctx0 = frs)
           (* (CTX: ctx0 = frs ⋅ mr0) *)
    ,
      simg (fun '(st_src1, v_src) '(st_tgt1, v_tgt) =>
              exists mrs1,
                (<<ZIP: st_tgt1 = zip_state st_src1 mrs1>>) /\
                
                (<<RET: (v_tgt: Σ * RT) = (frs, v_src)>>))
                (* (<<RET: (v_tgt: Σ * RT) = (frs ⋅ mrs1, v_src)>>)) *)
           false false
           (interp_Es (ModSem.prog ms_mid) (translate (emb_ run_) (interp_hCallE_mid (stb sk) cur i0)) st_src0)
           (interp_Es (ModSem.prog ms_tgt) (translate (emb_ run_) (interp_hCallE_tgt (stb sk) cur i0 ctx0)) st_tgt0)
  .
  Proof.
  (* Admitted. *)
    Opaque subevent.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    gcofix CIH. i; subst.
    ides i0; try rewrite ! unfold_interp; cbn; mred.
    { nstep. }
    { nstep. deflag. gbase. eapply CIH; [..|M]; Mskip et. ss. }
    rewrite <- bind_trigger. destruct e; cycle 1.
    {
      destruct s; ss.
      {
        destruct s; ss.
        resub. nstep. unfold pupdate. nstep. deflag.
        
        unfold zip_state in Heq0.
        replace (λ st : Any.t, match Any.split st with
        | Some p => let (x, mr) := p in (Any.pair (run x).1 mr, (run x).2)
        | None => run (Any.upcast ())
        end) with (run_tgt run) in Heq0; ss.
        rewrite RUN_TGT in Heq0. unfold run_tgt in Heq0.
        
        rewrite Any.pair_split in Heq0. 
        rewrite Heq in Heq0. clarify.
        gbase. eapply CIH; ss. 
      }
      { dependent destruction e.
        - resub. repeat (try nset; try tset). rewrite ! interp_Es_bind. rewrite interp_Es_eventE. grind. force_r. nstep. esplits. nstep. deflag.
          gbase. eapply CIH; [..|M]; Mskip et. ss.
        - resub. nstep. esplits; eauto. nstep. deflag. gbase. eapply CIH; [..|M]; Mskip et. ss.
        - resub. nstep. deflag. gbase. eapply CIH; [..|M]; Mskip et. ss.
      }
    }
    dependent destruction h. resub.
    set (ModSem.prog ms_mid) as p_mid in *.
    set (ModSem.prog ms_tgt) as p_tgt in *.
    ss.
    seal_left.

    mstep. hexploit (stb_find_iff fn). i. des.
    { rewrite NONE. nstep. }
    { rewrite FIND. unfold HoareCall, ASSUME, ASSERT, mput, mget. 
      unfold unwrapN.
      mstep.
      unfold zip_state, sGet, sPut.
      mstep.
      hexploit (RUN_STATE (Any.pair st_src0 (Any.upcast mr0)) rGet run_). i.
      rewrite Heq in H. s in H.
      rewrite H.
      rewrite Any.pair_split.
      mstep.

      des; clarify. destruct tbr; ss.
      { exfalso. hexploit TRIVIAL; et. intro T. rewrite T in *. hexploit x4; ss. }
      seal_right. unseal_left. nstep. rewrite FIND. nstep. esplits; et.
      nstep. esplits; et.
      (* { destruct cur; ss. hexploit x5; ss. intro T. rewrite T in *; ss. } *)
      nstep. rewrite FINDMID. nstep.
    }
    unfold HoareCall, ASSUME, ASSERT, mput, mget.

    (*** exploiting both_tau ***)
    rewrite STB. ss.
    tset. rewrite interp_Es_ret. steps.
    tset. rewrite interp_Es_bind. rewrite interp_Es_eventE.
    grind.
    
    force_r.
    destruct (classic (tbr = true /\ forall x, f.(measure) x = ord_top)).
    { des. subst. nstep.
      unfold zip_state. unfold unwrapN, sGet, sPut. nstep.
      hexploit (RUN_STATE (Any.pair st_src0 (Any.upcast mr0)) rGet run_). i.
      rewrite Heq0 in H. s in H. rewrite H. nstep. 

      hexploit H0; et. i. rewrite H in *. ss. des. hexploit x4; ss. }
    rename H into TRIVIAL.
    unseal_left. ired_both. 
    mset. tset. ired_l. tset. rewrite interp_Es_tau.
    
    rewrite STB. nstep. esplit.
    (* { ii. subst. eapply TRIVIAL; ss. }  *)
    nstep.
    unfold zip_state, sGet, sPut. nstep.
    hexploit (RUN_STATE (Any.pair st_src0 (Any.upcast mr0)) rGet run_). i.
    rewrite Heq in H. s in H. rewrite H. rewrite Any.pair_split.
    nstep.
     
    match goal with
    | |- _ ?i_tgt => replace i_tgt with (Ret tt;;; i_tgt)
    end.
    2: { nstep. }
    deflag. guclo bindC_spec. econs.
    { instantiate (1:= fun '(st_src, o) (_: unit) => st_src = st_src0 /\ o = (f.(measure) x)).
      destruct tbr.
      { nstep. des. destruct (measure f x); ss.
        { exists n. nstep. }
        { exfalso. hexploit x4; ss. }
      }
      { nstep. des. splits; auto. symmetry. auto. }
    }
    i. destruct vret_src, vret_tgt. des; subst.

    nstep. esplits; eauto. nstep. unfold unwrapU.
    rewrite FINDMID. rewrite FINDTGT. rewrite ! bind_ret_l.

    guclo bindC_spec. econs.

    { instantiate (1:= fun '(st_src1, vret_src) '(st_tgt1, vret_tgt) =>
                         exists (mr1: r_state) rret,
                           (<<ZIP: st_tgt1 = zip_state st_src1 mr1>>) /\
                           (<<POST: f.(postcond) x vret_src vret_tgt rret>>) /\
                           (<<RWF: URA.wf (rret ⋅ (c1 ⋅ (frs) ⋅ (mr1)))>>)).
      fold sk. fold sk.
       (* set (mn0:=SModSem.mn (SMod.get_modsem md sk)) in *. *)
      fold Any_tgt in x3.
      unfold fun_to_mid, fun_to_tgt, compose. des_ifs. unfold HoareFun, ASSUME, ASSERT, mget, mput.
      rename x3 into PRECOND. rename c0 into rarg.
      nstep. exists x.
      nstep. eexists (rarg, c1 ⋅ (frs)). nstep.
      (* erewrite ! zip_state_mput; et. steps. *)
      assert (RWF0: URA.wf (rarg ⋅ ε ⋅ (c1 ⋅ (frs)) ⋅ c)).
      { r_wf x0. }
      unshelve esplits; eauto.
      unfold sGet, sPut. nstep.
      hexploit (RUN_STATE t1 rGet run_0). i.
      rewrite Heq1 in H. s in H. rewrite H.


      rewrite RUN_PUT in Heq0.
      assert (t1 = Any.pair st_src0 c↑). { unfold rPut in Heq0. clarify. }
      nstep. unfold assume. nstep. eexists.
      nstep.

      exists varg_src.
      nstep. esplits; eauto. nstep. unshelve esplits; eauto. nstep.
      deflag. guclo bindC_spec. econs.
      { gbase. eapply CIH; ss. admit. (* st_tgt form *)
      }
      { ii. ss. des_ifs_safe. des; ss. clarify.
        nstep.
        unfold zip_state. nstep.
        assert (t5 = (zip_state t1 mrs1)).
        { 
          replace (zip_state t1 mrs1) with (run_0 Any.t rGet (zip_state t1 mrs1)).2.
          2: { erewrite RUN_STATE. et. }
          rewrite Heq2. ss.
        }
        
        nstep. unfold zip_state. nstep.
        esplits; ss; et.
        { rewrite RUN_PUT in Heq3. unfold rPut in Heq3. inv Heq3. et. }
        { eapply (@URA.wf_mon _ _ c3). r_wf x3. }
      }
    }
    { ii. ss. des_ifs_safe. des. subst.
      nstep. eexists (rret, frs). nstep.
      replace t6 with (Any.pair t2 mr1↑). 
      2: {  
          replace t6 with (run_ Any.t rGet (zip_state t2 mr1)).2. 
          { rewrite RUN_STATE. ss. }
          { rewrite Heq1. ss. }
      }

      
      (* rewrite zip_state_get; et. *)
      rewrite Any.pair_split. nstep.
      unfold assume. nstep. 
      (* rewrite Any.upcast_downcast. steps. *)
      unshelve esplits; et. 

      { r_wf RWF. }
      nstep. exists t3. nstep. unshelve esplits; et.
       (* { admit. } *)
      nstep. deflag. gbase. eapply CIH; et.

    }
  Unshelve.
    all: try (by exact 0).
  Qed.

  Opaque interp_Es.

  Context {CONFS: EMSConfig}.
  Definition midConf: EMSConfig := {| finalize := finalize; initial_arg := Any.pair ord_top↑ initial_arg |}.
  Context {CONFT: EMSConfig}.
  Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

  Theorem adequacy_type_t2m
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb sk "main" = Some main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) x (@initial_arg CONFS) (@initial_arg CONFT) entry_r ∧ main_fsp.(measure) x = ord_top>>) /\
               (<<WFR: URA.wf (entry_r ⋅ fold_left (⋅) (List.map SModSem.initial_mr mss) ε)>>) /\
               (<<RET: forall ret_src ret_tgt r
                              (WFR: URA.wf r)
                              (POST: main_fsp.(postcond) x ret_src ret_tgt r),
                   ret_src = ret_tgt>>)):
    Beh.of_program (@Mod.compile _ CONFT md_tgt) <1=
    Beh.of_program (@Mod.compile _ midConf md_mid).
  Proof.
    eapply adequacy_global_itree; ss.
    ginit.
    { eapply cpn7_wcompat; eauto with paco. }
    unfold ModSem.initial_itr, ModSem.initial_itr. Local Opaque ModSem.prog. ss.
    unfold ITree.map.

    hexploit (stb_find_iff "main"). i. destruct H as [[_ ?]|?]; des; clarify.
    { Local Transparent ModSem.prog.
      seal_right. ss. unfold ms_mid in FINDMID. rewrite FINDMID. steps.
      Local Opaque ModSem.prog. }
    rename f into main_fsb. hexploit MAINM; et.
    i. des.

    unfold assume.
    steps. unfold Mod.wf in *. des.
    (* assert (NODUP: List.NoDup (map fst ms_tgt.(ModSemL.initial_mrs))).
    { inv WF. rewrite fst_initial_mrs_eq. unfold ms_mid. auto. } *)
    esplits; et.
    { inv WF. econs; auto. rewrite fns_eq. auto. }
    { rewrite sk_eq. auto. }
    

    (* hexploit initial_mrs_exist; auto. i. des. *)
    steps. fold ms_tgt ms_mid.
     (* rewrite <- INITIALZIP. *)

    Local Transparent ModSem.prog. ss.
    unfold Any_src, Any_mid, Any_tgt in *. rewrite FINDTGT. rewrite FINDMID.
    unfold fun_to_mid, fun_to_tgt, HoareFun. nstep.
     
    eexists. nstep. unfold ASSUME, ASSERT, mput, mget. nstep.
    eexists (entry_r, ε).
    (* eexists (entry_r, (SMod.get_modsem md sk).(SModSem.initial_mr)). *)
    unfold sGet, sPut.
    nstep.  

    hexploit (RUN_STATE (init_st ms_tgt) rGet run_). i.
    rewrite Heq in H. s in H. rewrite H.
    destruct (Any.split (init_st ms_tgt)).
    2: { nstep. admit. }
    
    nstep.
    destruct (Any.downcast t2).
    2: { nstep. admit. }
    unfold assume. nstep.

    assert (RWF: URA.wf (entry_r ⋅ ε ⋅ ε ⋅ fold_left URA.add (map SModSem.initial_mr mss) ε)).
    (* assert (RWF: URA.wf (entry_r ⋅ ε ⋅ ε ⋅ (SMod.get_modsem md sk).(SModSem.initial_mr))). *)


    (* assert (RWF: URA.wf (entry_r ⋅ ε ⋅ (SMod.get_modsem md sk).(SModSem.initial_mr) ⋅ (SMod.get_modsem md (Sk.sort (SMod.sk md))).(SModSem.initial_mr))). *)
    { r_wf WFR. 
      (* unfold ms, _ms.
      unfold SModSem.initial_mr.
      unfold SMod.get_modsem. *)
      (* admit. *)
        }
    unshelve esplits; et.
    { admit. }
    nstep.
    eexists. nstep. unshelve esplits; et. nstep.
    guclo bindC_spec. econs.
    { deflag. gfinal. right. fold simg.
      (* admit. *)
      eapply adequacy_type_aux; ss. admit.
    }
    i. ss.
    destruct vret_src as [mps_src v_src].
    destruct vret_tgt as [mps_tgt [? v_tgt]]. des. clarify.
    nstep.

    hexploit (RUN_STATE (zip_state mps_src mrs1) rGet run_). i.
    rewrite Heq1 in H. s in H. rewrite H.

    unfold zip_state. nstep.
    { eapply RET; [|et]. eapply URA.wf_mon.
      instantiate (1:=(c1 ⋅ ε ⋅ c)).
      r_wf x0. }
    Unshelve. all: try (exact 0).
  Qed.

End CANCEL.
