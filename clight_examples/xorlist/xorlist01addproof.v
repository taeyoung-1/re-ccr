Require Import Coqlib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import SimModSem.
Require Import PCM.
Require Import HoareDef.
Require Import STB.
Require Import HTactics ProofMode.
Require Import HSim IProofMode.
Require Import ClightDmExprgen ClightDmgen.
Require Import ClightDmMem1.
Require Import CIProofMode.
Require Import xorlist.
Require Import xorlist0.
Require Import xorlist1.
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Clightdefs.

Section LEMMA.

  Lemma f_bind_ret_r E R A (s : A -> itree E R)
    : (fun a => ` x : R <- (s a);; Ret x) = s.
  Proof. apply func_ext. i. apply bind_ret_r. Qed.

  Lemma decode_encode_ofs i : decode_val Mint64 (encode_val Mint64 (Vptrofs i)) = Vptrofs i.
  Proof.
    pose proof (decode_encode_val_general (Vptrofs i) Mint64 Mint64).
    unfold Vptrofs in *. des_ifs.
  Qed.

  Lemma decode_encode_null : decode_val Mint64 (encode_val Mint64 Vnullptr) = Vnullptr.
  Proof.
    rewrite (decode_encode_val_general Vnullptr Mint64 Mint64). et.
  Qed.

  Lemma null_zero i : Vptrofs i = Vnullptr -> i = Ptrofs.zero.
  Proof.
    unfold Vptrofs, Vnullptr. des_ifs. i. inv H. 
    rewrite <- (Ptrofs.of_int64_to_int64 Heq i).
    rewrite <- (Ptrofs.of_int64_to_int64 Heq Ptrofs.zero).
    f_equal. des_ifs. change (Ptrofs.to_int64 Ptrofs.zero) with Int64.zero.
    rewrite Heq1. f_equal. apply proof_irrel.
  Qed.

  Context `{eventE -< eff}.

  Lemma cast_ptrofs i : cast_to_ptr (Vptrofs i) = Ret (Vptrofs i).
  Proof. des_ifs. Qed.

  Lemma cast_long i : Archi.ptr64 = true -> cast_to_ptr (Vlong i) = Ret (Vlong i).
  Proof. ss. Qed.

End LEMMA.

Section PROOF.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Variable GlobalStb : Sk.sem -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb xorStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).


  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ⌜True⌝)%I.


  Let ce := map (fun '(id, p) => (string_of_ident id, p)) (Maps.PTree.elements (prog_comp_env prog)).

  Section SIMFUNS.
  Variable sk: Sk.t.
  Hypothesis SKINCL : Sk.extends (xorlist0.xor.(Mod.sk)) sk.
  Hypothesis SKWF : Sk.wf (Sk.canon sk).


  Lemma sim_add :
    sim_fnsem wf top2
      ("add", fun_to_tgt "xorlist" (GlobalStb (Sk.canon sk)) (mk_pure add_spec))
      ("add", cfunU (decomp_func (Sk.canon sk) ce f_add)).
  Proof.
    Opaque encode_val.
    Opaque cast_to_ptr.
    econs; ss. red.

    unfold prog in ce. unfold mkprogram in ce.
    destruct (build_composite_env'). ss.
    get_composite ce e.

    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply Sk.incl_incl_env in SKINCLENV.
    unfold Sk.incl_env in SKINCLENV.
    pose proof Sk.sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_delete. i; ss.
    unfold decomp_func, function_entry_c. ss.
    let H := fresh "HIDDEN" in
    set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[% PRE] %]".
    des. clarify. hred_r. unhide. hred_r. unhide.
    remove_tau. unhide. remove_tau.
    rename v into hd_hdl, v0 into tl_hdl, l into lfull, i into at_tail, i0 into item.

    hexploit SKINCLENV.
    { instantiate (2:="malloc"). ss. }
    i. des. ss. rewrite FIND. rename FIND into malloc_loc.
    hred_r. des_ifs_safe.
    rewrite cast_ptrofs.
    rename Heq1 into ptr64. rename Heq0 into get_co.
    clear Heq e. hred_r.

    replace (pred _) with blk by nia.
    erewrite SKINCLGD; et.
    hred_r. ss.
    iApply isim_apc. iExists (Some (20%nat : Ord.t)).
    rewrite co_co_sizeof.

    iApply isim_ccallU_malloc; ss; oauto.
    iSplitL "INV"; iFrame.
    { iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 p_new m_new) "[INV [[% new_point] new_ofs]]".
    set (Z.to_nat _) as si. vm_compute in si. unfold si. clear si.
    rename H3 into m_new_size.

    hred_r. unhide. remove_tau. 
    iPoseProof ((@offset_cast_ptr _ _ _ _ Es) with "new_ofs") as "%".
    rewrite H3. rename H3 into new_cast_ptr.
    hred_r. unhide. remove_tau. unhide.
    remove_tau.

    unfold full_xorlist.
    iDestruct "PRE" as (m_hd_hdl m_tl_hdl hd tl ofs_hd_hdl ofs_tl_hdl tg_hd_hdl tg_tl_hdl)
      "[[[[[[hd_hdl_point hd_hdl_ofs] %] tl_hdl_point] tl_hdl_ofs] %] LIST]".
    rename H3 into hd_hdl_align.
    rename H4 into tl_hdl_align.

    iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%".
    rewrite H3. rename H3 into hd_hdl_ptr. hred_r.

    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_hdl_point hd_hdl_ofs"; iFrame.
    { rewrite encode_val_length. et. }
    iIntros (st_src1 st_tgt1) "[INV [hd_hdl_point hd_hdl_ofs]]".
    unfold Mptr. rewrite ptr64.
    iPoseProof (xorlist_hd_ptr with "LIST") as "%". rewrite H3. rename H3 into hd_deen.

    hred_r. unhide. remove_tau. unhide. remove_tau.
    iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%".
    rewrite H3. rename H3 into tl_hdl_is_point. hred_r.

    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tl_hdl_point tl_hdl_ofs"; iFrame.
    { rewrite encode_val_length. et. }
    iIntros (st_src2 st_tgt2) "[INV [tl_hdl_point tl_hdl_ofs]]".
    unfold Mptr. rewrite ptr64. 
    iPoseProof (xorlist_tl_ptr with "LIST") as "%". rewrite H3. rename H3 into tl_deen.

    hred_r. unhide. remove_tau. unhide. remove_tau.
    iPoseProof (points_to_is_ptr with "new_point") as "%".
    rewrite H3. rename H3 into new_is_point. hred_r. rewrite new_is_point. hred_r.

    rewrite co_co_members. ss. hred_r.
    replace (Coqlib.align 0 _) with 0%Z by et.
    replace (Ptrofs.repr 0) with Ptrofs.zero by et.
    iPoseProof (add_null_r with "new_ofs") as "%".
    rewrite H3. rename H3 into new_add_r. rewrite cast_long; et. hred_r.

    replace (points_to _ _ _ _) with (points_to p_new m_new (repeat Undef 8 ++ repeat Undef 8) 1) by reflexivity.
    iPoseProof (points_to_split with "new_point") as "[new_point_item new_point_key]".

    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV new_point_item new_ofs"; iFrame.
    { iExists _. iFrame. ss. iPureIntro. split; et. exists 0. ss. }
    iIntros (st_src3 st_tgt3) "[INV [new_point_item new_ofs]]".

    hred_r. unhide. remove_tau.
    replace (Vlong (Int64.repr _)) with Vnullptr by et.

    destruct lfull.
    (* case: nil list *)
    - 
      admit "solved".
      (* ss.
      iDestruct "LIST" as "[NULL_tl NULL_hd]".
      iPoseProof (equiv_sym with "NULL_hd") as "NULL_hd". iPoseProof (null_equiv with "NULL_hd") as "%". subst.

      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src4 st_tgt4) "INV".

      hred_r. des_ifs_safe. clear Heq.
      unhide. hred_r. unhide. remove_tau.
      rewrite new_is_point. hred_r. rewrite new_is_point. hred_r.

      rewrite co_co_members. ss. hred_r.
      replace (Coqlib.align _ _) with 8%Z by et.
      replace (Vlong (Int64.repr _)) with Vnullptr by et.
      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV new_point_key new_ofs"; iFrame.
      { iExists _. iFrame. iSplit; cycle 1.  { iApply offset_slide. et. } { iPureIntro. split; ss. exists 1. ss. } }
      iIntros (st_src5 st_tgt5) "[INV [new_point_key new_ofs]]".

      hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau. unhide. remove_tau.

      rewrite new_cast_ptr. hred_r. unhide. remove_tau.
      rewrite tl_hdl_is_point. hred_r. rewrite new_cast_ptr. hred_r.

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV tl_hdl_point tl_hdl_ofs"; iFrame.
      { iExists _. iFrame. rewrite encode_val_length. iPureIntro. ss. }
      iIntros (st_src7 st_tgt7) "[INV [tl_hdl_point tl_hdl_ofs]]".

      hred_r. unhide. remove_tau. rewrite hd_hdl_ptr. hred_r.
      rewrite new_cast_ptr. hred_r.

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV hd_hdl_point hd_hdl_ofs"; iFrame.
      { iExists _. iFrame. rewrite encode_val_length. iPureIntro. ss. }
      iIntros (st_src8 st_tgt8) "[INV [hd_hdl_point hd_hdl_ofs]]".

      hred_r. remove_tau. hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret. iFrame. iSplit; ss. iSplit; ss.
      iCombine "new_point_item new_point_key" as "new_point".
      iPoseProof (points_to_collect with "new_point") as "new_point".

      replace (vlist_add _ _ _) with [Vlong item] by now unfold vlist_add; des_ifs.
      iExists _,_,_,_,_,_,_,_. iFrame.
      iSplit; ss.
      iPoseProof (offset_slide_rev with "new_ofs") as "new_ofs".
      change Vnullptr with (Vptrofs Ptrofs.zero) at 3 4.
      iPoseProof (equiv_refl_offset with "new_ofs") as "[new_ofs new_equiv]".
      iPoseProof (equiv_dup with "NULL_hd") as "[? ?]".
      iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame.
      iSplit; ss. *)
    - ss. destruct v; clarify. 
      iDestruct "LIST" as (i_prev i_next m_hd) "[[[[% prev_addr] hd_ofs] hd_point] LIST]".
      rename H3 into m_hd_size.

      iApply isim_ccallU_cmp_ptr3; ss; oauto.
      iSplitL "INV hd_ofs".
      { iFrame. iPureIntro. red. rewrite m_hd_size. ss. }
      iIntros (st_src4 st_tgt4) "[INV hd_ofs]".

      hred_r. des_ifs_safe. clear Heq. unhide. remove_tau.
      destruct Int.eq eqn: is_head.
      (* not nil, head case *)
      + 
        admit "solved".
        (* ss.
        unhide. hred_r. unhide. remove_tau. unhide. remove_tau.
        hexploit SKINCLENV.
        { instantiate (2:="encrypt"). ss. }
        i. des. ss. rewrite FIND. rename FIND into encrypt_loc.
        hred_r. rewrite cast_long; et. hred_r. des_ifs. clear e.
        iPoseProof ((@offset_cast_ptr _ _ _ _ Es) with "hd_ofs") as "%".
        rewrite H3. hred_r. rename H3 into hd_cast_ptr.

        replace (pred _) with blk0 by nia.
        erewrite SKINCLGD; et.
        hred_r. ss.
        replace (Vlong (Int64.repr _)) with Vnullptr by et.

        iApply isim_ccallU_pure; et.
        { eapply fn_has_spec_in_stb; et.
          { eapply STBINCL. stb_tac. unfold xorStb.
            unseal "stb". ss. }
          { ss. instantiate (1:=inr (inr (inl (_,_,_,_,_)))).
            ss. oauto. }
          { ss. } }
        { instantiate (1:=14). oauto. }

        ss. iSplitL "INV hd_ofs". { iFrame. ss. }
        iIntros (st_src5 st_tgt5 ret_src ret_tgt) "[INV [POST %]]".
        iDestruct "POST" as (i_hd) "[[% hd_addr] hd_ofs]".
        rewrite H4. iExists _. iSplit; ss. clear H3 H4.

        hred_r. unhide. remove_tau.
        rewrite new_is_point. hred_r.
        rewrite new_is_point. hred_r.
        rewrite co_co_members. ss. hred_r.
        rewrite cast_ptrofs. hred_r.
        replace (Coqlib.align _ _) with 8%Z by et.

        iApply isim_ccallU_store; ss; oauto.
        iSplitL "INV new_point_key new_ofs"; iFrame.
        { iExists _. iFrame. iSplit; cycle 1.
          { iApply offset_slide. ss. }
          { iPureIntro. split; ss. exists 1. ss. } }
        iIntros (st_src6 st_tgt6) "[INV [new_point_key new_ofs]]".

        hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
        hexploit SKINCLENV.
        { instantiate (2:="decrypt"). ss. }
        i. des. ss. rewrite FIND. rename FIND into decrypt_loc.
        hred_r.
        iPoseProof (points_to_is_ptr with "hd_point") as "%".
        rewrite H3. rename H3 into hd_ptr.
        hred_r. rewrite hd_ptr. hred_r.
        rewrite co_co_members. ss. hred_r.
        replace (Coqlib.align _ _) with 8%Z by et.

        iPoseProof (points_to_split with "hd_point") as "[hd_point_item hd_point_key]".
        iApply isim_ccallU_load; ss; oauto.
        iSplitL "INV hd_point_key hd_ofs".
        { iFrame. iSplit.
          { iApply offset_slide. ss. }
          { iPureIntro. split; ss. exists 1. ss. } }
        iIntros (st_src7 st_tgt7) "[INV [hd_point_key hd_ofs]]".

        unfold Mptr. rewrite ptr64.
        rewrite decode_encode_ofs. hred_r.
        rewrite cast_long; et. hred_r.
        rewrite cast_ptrofs. hred_r.
        des_ifs_safe. clear e.

        replace (pred _) with blk1 by nia.
        erewrite SKINCLGD; et.
        hred_r. ss.
        replace (Vlong (Int64.repr _)) with Vnullptr by et.

        iApply isim_ccallU_pure; et.
        { eapply fn_has_spec_in_stb; et.
          { eapply STBINCL. stb_tac. unfold xorStb.
            unseal "stb". ss. }
          { ss. instantiate (1:=(inr _)).
            ss. oauto. }
          { ss. } }
        { instantiate (1:=11). oauto. }

        ss. iSplitL "INV".
        { iFrame. ss. }
        iIntros (st_src8 st_tgt8 ret_src0 ret_tgt0) "[INV [POST %]]".
        iDestruct "POST" as "%". rewrite H4.
        iExists _. iSplit; ss. clear H3 H4.

        hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
        unhide. remove_tau.
        rewrite encrypt_loc. hred_r.
        rewrite cast_ptrofs. hred_r.
        rewrite new_cast_ptr. hred_r.
        des_ifs. clear e. hred_r.
        replace (pred _) with blk0 by nia.
        erewrite SKINCLGD; et.
        hred_r. ss.

        iPoseProof (null_equiv with "prev_addr") as "%".
        apply null_zero in H3. subst. rewrite Ptrofs.xor_zero_l.
        destruct lfull; ss.
        (* case: singleton list && delete from head *)
        * 
          admit "solved".
          (* iDestruct "LIST" as "[hd_equiv null_equiv]".
          iPoseProof (equiv_sym with "null_equiv") as "null_equiv". iPoseProof (null_equiv with "null_equiv") as "%". rewrite H3 in *. clear H3.

          iApply isim_ccallU_pure; et.
          { eapply fn_has_spec_in_stb; et.
            { eapply STBINCL. stb_tac. unfold xorStb.
              unseal "stb". ss. }
            { ss. instantiate (1:=(inr (inl (_,_,_,_,_)))).
              ss. oauto. }
            { ss. } }
          { instantiate (1:=10). oauto. }

          iPoseProof (offset_slide_rev with "new_ofs") as "new_ofs".
          ss. iSplitL "INV new_ofs".
          { iFrame. iPureIntro. ss. }
          iIntros (st_src9 st_tgt9 ret_src1 ret_tgt1) "[INV [POST %]]".
          iDestruct "POST" as (i_new) "[[% new_addr] new_ofs]".
          rewrite H4. clear H3 H4.
          iExists _. iSplit; ss.

          hred_r. unhide. remove_tau.

          iPoseProof (points_to_is_ptr with "hd_point_item") as "%".
          rewrite H3. hred_r.
          rewrite H3. hred_r.
          rewrite co_co_members. ss. hred_r.
          replace (Coqlib.align _ _) with 8%Z by et.
          rewrite cast_ptrofs. hred_r.

          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV hd_point_key hd_ofs".
          { iFrame. iExists _. iFrame.
            iPureIntro. split; ss. exists 1. ss. }
          iIntros (st_src10 st_tgt10) "[INV [hd_point_key hd_ofs]]".

          hred_r. unhide. remove_tau.
          rewrite hd_hdl_ptr. hred_r.
          rewrite new_cast_ptr. hred_r.
          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV hd_hdl_point hd_hdl_ofs".
          { iFrame. iExists _. iFrame. iPureIntro.
            rewrite encode_val_length. ss. }
          iIntros (st_src11 st_tgt11) "[INV [hd_hdl_point hd_hdl_ofs]]".

          hred_r. remove_tau. hred_l. iApply isim_choose_src.
          iExists _. iApply isim_ret.
          iFrame. iSplit; ss. iSplit; ss.
          iCombine "new_point_item new_point_key" as "new_point".
          iCombine "hd_point_item hd_point_key" as "hd_point".
          iPoseProof (points_to_collect with "new_point") as "new_point".
          iPoseProof (points_to_collect with "hd_point") as "hd_point".
          iPoseProof (offset_slide_rev with "hd_ofs") as "hd_ofs".

          iExists _,_,_,_,_,_,_,_. iFrame.
          apply Int.same_if_eq in is_head. clarify.
          iSplit; ss. unfold vlist_add.
          destruct Val.eq; ss; clarify.
          iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame. iSplit; ss.
          
          iPoseProof (equiv_dup with "hd_addr") as "[hd_addr hd_addr']".
          iCombine "hd_addr' hd_point" as "hd_point".
          iPoseProof (equiv_point_comm with "hd_point") as "hd_point".
          iPoseProof (equiv_dup with "hd_addr") as "[hd_addr hd_addr']".
          iCombine "hd_addr' hd_ofs" as "hd_ofs".
          iPoseProof (equiv_offset_comm with "hd_ofs") as "hd_ofs".
          iPoseProof (equiv_sym with "hd_addr") as "hd_addr".
          iCombine "hd_addr hd_equiv" as "hd_equiv".
          iPoseProof (equiv_trans with "hd_equiv") as "hd_equiv".
          iExists _,_,_. iFrame.
          change Vnullptr with (Vptrofs Ptrofs.zero) at 1. iFrame.
          rewrite Ptrofs.xor_zero. iFrame. ss. *)
        * destruct v; clarify.
          iDestruct "LIST" as (i_hd' i_hd_nn m_next)
            "[[[[% hd_addr'] next_ofs] next_point] LIST]".
          iCombine "hd_addr' hd_addr" as "hd_addr".
          iPoseProof (capture_unique with "hd_addr") as "%". subst.
          iDestruct "hd_addr" as "[_ hd_addr]".
          rename H3 into m_next_size.

          iPoseProof (offset_slide_rev with "new_ofs") as "new_ofs".

          iApply isim_ccallU_pure; et.
          { eapply fn_has_spec_in_stb; et.
            { eapply STBINCL. stb_tac. unfold xorStb.
              unseal "stb". ss. }
            { ss. instantiate (1:= (inl (_,_,_,_,_,_,_,_,_,_))).
              ss. oauto. }
            { ss. } }
          { instantiate (1:=10). oauto. }

          ss. iSplitL "INV new_ofs next_ofs".
          { iSplit; ss. iSplit; ss. iSplitR "next_ofs"; ss. iFrame. ss. }
          iIntros (st_src9 st_tgt9 ret_src1 ret_tgt1) "[INV [POST %]]".
          iDestruct "POST" as (i_new i_next') "[[[[% new_ofs] next_ofs] new_equiv] next_equiv]".
          rewrite H4. clear H3 H4.
          iExists _. iSplit; ss.
          iPoseProof (equiv_ii_eq with "next_equiv") as "%". symmetry in H3. subst.

          hred_r. unhide. remove_tau.
          rewrite hd_ptr. hred_r.
          rewrite hd_ptr. hred_r.
          rewrite co_co_members. ss. hred_r.
          replace (Coqlib.align _ _) with 8%Z.
          rewrite cast_ptrofs. hred_r.

          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV hd_point_key hd_ofs".
          { iFrame. iExists _. iFrame. iPureIntro. split; ss. exists 1. ss. }
          iIntros (st_src10 st_tgt10) "[INV [hd_point_key hd_ofs]]".

          hred_r. unhide. remove_tau.
          rewrite hd_hdl_ptr. hred_r.
          rewrite new_cast_ptr. hred_r.

          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV hd_hdl_point hd_hdl_ofs".
          { iFrame. iExists _. iFrame. iPureIntro. split; ss.
            rewrite encode_val_length. ss. }
          iIntros (st_src11 st_tgt11) "[INV [hd_hdl_point hd_hdl_ofs]]".

          hred_r. remove_tau. 2: ss. hred_l. iApply isim_choose_src.
          iExists _. iApply isim_ret. iSplit; ss. iSplit; ss. iSplit; ss.
          iCombine "new_point_item new_point_key" as "new_point".
          iCombine "hd_point_item hd_point_key" as "hd_point".
          iPoseProof (points_to_collect with "new_point") as "new_point".
          iPoseProof (points_to_collect with "hd_point") as "hd_point".
          iPoseProof (offset_slide_rev with "hd_ofs") as "hd_ofs".
          iPoseProof (equiv_dup with "hd_addr") as "[hd_addr hd_addr']".
          iCombine "hd_addr' hd_point" as "hd_point".
          iPoseProof (equiv_point_comm with "hd_point") as "hd_point".
          iPoseProof (equiv_dup with "hd_addr") as "[hd_addr hd_addr']".
          iCombine "hd_addr' hd_ofs" as "hd_ofs".
          iPoseProof (equiv_offset_comm with "hd_ofs") as "hd_ofs".
          unfold vlist_add.
          apply Int.same_if_eq in is_head. subst.
          destruct Val.eq; ss; clarify.
          iExists _,_,_,_,_,_,_,_. iFrame. iSplit; ss.
          iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame. iSplit; ss.
          iExists _,_,_. iFrame. iSplit; ss.
          iExists _,_,_. iFrame. iSplit; ss. 
          iApply equiv_refl_equiv.
          iApply equiv_sym. et. *)
      + 
        pose proof (Int.eq_spec at_tail Int.zero). rewrite is_head in H3.
        unfold vlist_add.
        destruct Val.eq eqn:?.
        { exfalso. clear - e H3. unfold Vzero in *. inv e. et. }
        clear H3 Heqs n.
        Local Opaque last. Local Opaque removelast. Local Opaque rev.
        iAssert (frag_xorlist 1 m_null m_null Vnullptr hd tl Vnullptr (Vlong i :: lfull))
                  with "[prev_addr hd_point hd_ofs LIST]" as "LIST". { ss. iExists _,_,_. iFrame. ss. }
        iPoseProof (rev_xorlist with "LIST") as "LIST".
        assert (len_sup: length (rev (Vlong i :: lfull)) ≥ 1).
        { rewrite rev_length. ss. nia. }
        revert len_sup. set (rev (Vlong i :: lfull)) as l.
        replace (Vlong i :: lfull) with (rev (rev (Vlong i :: lfull))) by now rewrite rev_involutive; et.
        unfold l. clear l. generalize (rev (Vlong i :: lfull)). clear i lfull.
        i. destruct l; ss; try nia.
        rename l into lnext. destruct v; clarify. rename i into tl_item.
        iDestruct "LIST" as (i_tl_next i_tl_prev m_tl_old) "[[[[% tl_next_equiv] tl_ofs] tl_point] LIST]". rename H3 into m_tl_size.

        unhide. hred_r. unhide. remove_tau. unhide. remove_tau.
        hexploit SKINCLENV.
        { instantiate (2:="encrypt"). ss. }
        i. des. ss. rewrite FIND. rename FIND into encrypt_loc.
        hred_r. rewrite cast_long; et. hred_r. des_ifs. clear e.
        iPoseProof ((@offset_cast_ptr _ _ _ _ Es) with "tl_ofs") as "%".
        rewrite H3. hred_r. rename H3 into tl_cast_ptr.

        replace (pred _) with blk0 by nia.
        erewrite SKINCLGD; et.
        hred_r. ss.
        replace (Vlong (Int64.repr _)) with Vnullptr by et.

        iApply isim_ccallU_pure; et.
        { eapply fn_has_spec_in_stb; et.
          { eapply STBINCL. stb_tac. unfold xorStb.
            unseal "stb". ss. }
          { ss. instantiate (1:=inr (inl (_,_,_,_,_))).
            ss. oauto. }
          { ss. } }
        { instantiate (1:=14). oauto. }

        ss. iSplitL "INV tl_ofs". { iFrame. ss. }
        iIntros (st_src5 st_tgt5 ret_src ret_tgt) "[INV [POST %]]".
        iDestruct "POST" as (i_tl) "[[% tl_addr] tl_ofs]".
        rewrite H4. iExists _. iSplit; ss. clear H3 H4.

        hred_r. unhide. remove_tau.
        rewrite new_is_point. hred_r.
        rewrite new_is_point. hred_r.
        rewrite co_co_members. ss. hred_r.
        rewrite cast_ptrofs. hred_r.
        replace (Coqlib.align _ _) with 8%Z by et.

        iApply isim_ccallU_store; ss; oauto.
        iSplitL "INV new_point_key new_ofs"; iFrame.
        { iExists _. iFrame. iSplit; cycle 1.
          { iApply offset_slide. ss. }
          { iPureIntro. split; ss. exists 1. ss. } }
        iIntros (st_src6 st_tgt6) "[INV [new_point_key new_ofs]]".

        hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
        hexploit SKINCLENV.
        { instantiate (2:="decrypt"). ss. }
        i. des. ss. rewrite FIND. rename FIND into decrypt_loc.
        hred_r.
        iPoseProof (points_to_is_ptr with "tl_point") as "%".
        rewrite H3. rename H3 into tl_ptr.
        hred_r. rewrite tl_ptr. hred_r.
        rewrite co_co_members. ss. hred_r.
        replace (Coqlib.align _ _) with 8%Z by et.

        iPoseProof (points_to_split with "tl_point") as "[tl_point_item tl_point_key]".
        iApply isim_ccallU_load; ss; oauto.
        iSplitL "INV tl_point_key tl_ofs".
        { iFrame. iSplit.
          { iApply offset_slide. ss. }
          { iPureIntro. split; ss. exists 1. ss. } }
        iIntros (st_src7 st_tgt7) "[INV [tl_point_key tl_ofs]]".

        unfold Mptr. rewrite ptr64.
        rewrite decode_encode_ofs. hred_r.
        rewrite cast_long; et. hred_r.
        rewrite cast_ptrofs. hred_r.
        des_ifs_safe. clear e.

        replace (pred _) with blk1 by nia.
        erewrite SKINCLGD; et.
        hred_r. ss.
        replace (Vlong (Int64.repr _)) with Vnullptr by et.

        iApply isim_ccallU_pure; et.
        { eapply fn_has_spec_in_stb; et.
          { eapply STBINCL. stb_tac. unfold xorStb.
            unseal "stb". ss. }
          { ss. instantiate (1:=(inr _)).
            ss. oauto. }
          { ss. } }
        { instantiate (1:=11). oauto. }

        ss. iSplitL "INV".
        { iFrame. ss. }
        iIntros (st_src8 st_tgt8 ret_src0 ret_tgt0) "[INV [POST %]]".
        iDestruct "POST" as "%". rewrite H4.
        iExists _. iSplit; ss. clear H3 H4.

        hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
        unhide. remove_tau.
        rewrite encrypt_loc. hred_r.
        rewrite cast_ptrofs. hred_r.
        rewrite new_cast_ptr. hred_r.
        des_ifs. clear e. hred_r.
        replace (pred _) with blk0 by nia.
        erewrite SKINCLGD; et.
        hred_r. ss.

        iPoseProof (null_equiv with "tl_next_equiv") as "%".
        apply null_zero in H3. subst. rewrite Ptrofs.xor_zero_l.
        destruct lnext; ss.
        (* case: singleton list && delete from head *)
        * 
          (* admit "solved". *)
          iDestruct "LIST" as "[tl_equiv null_equiv]".
          iPoseProof (equiv_sym with "null_equiv") as "null_equiv". iPoseProof (null_equiv with "null_equiv") as "%". rewrite H3 in *. clear H3.

          iApply isim_ccallU_pure; et.
          { eapply fn_has_spec_in_stb; et.
            { eapply STBINCL. stb_tac. unfold xorStb.
              unseal "stb". ss. }
            { ss. instantiate (1:=(inr (inl (_,_,_,_,_)))).
              ss. oauto. }
            { ss. } }
          { instantiate (1:=10). oauto. }

          iPoseProof (offset_slide_rev with "new_ofs") as "new_ofs".
          ss. iSplitL "INV new_ofs".
          { iFrame. iPureIntro. ss. }
          iIntros (st_src9 st_tgt9 ret_src1 ret_tgt1) "[INV [POST %]]".
          iDestruct "POST" as (i_new) "[[% new_addr] new_ofs]".
          rewrite H4. clear H3 H4.
          iExists _. iSplit; ss.

          hred_r. unhide. remove_tau.

          iPoseProof (points_to_is_ptr with "tl_point_item") as "%".
          rewrite H3. hred_r.
          rewrite H3. hred_r.
          rewrite co_co_members. ss. hred_r.
          replace (Coqlib.align _ _) with 8%Z by et.
          rewrite cast_ptrofs. hred_r.

          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV tl_point_key tl_ofs".
          { iFrame. iExists _. iFrame.
            iPureIntro. split; ss. exists 1. ss. }
          iIntros (st_src10 st_tgt10) "[INV [tl_point_key tl_ofs]]".

          hred_r. unhide. remove_tau.
          rewrite tl_hdl_is_point. hred_r.
          rewrite new_cast_ptr. hred_r.
          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV tl_hdl_point tl_hdl_ofs".
          { iFrame. iExists _. iFrame. iPureIntro.
            rewrite encode_val_length. ss. }
          iIntros (st_src11 st_tgt11) "[INV [tl_hdl_point tl_hdl_ofs]]".

          hred_r. remove_tau. hred_l. iApply isim_choose_src.
          iExists _. iApply isim_ret.
          iFrame. iSplit; ss. iSplit; ss.
          iCombine "new_point_item new_point_key" as "new_point".
          iCombine "tl_point_item tl_point_key" as "tl_point".
          iPoseProof (points_to_collect with "new_point") as "new_point".
          iPoseProof (points_to_collect with "tl_point") as "tl_point".
          iPoseProof (offset_slide_rev with "tl_ofs") as "tl_ofs".

          iExists _,_,_,_,_,_,_,_. iFrame. iSplit; ss.
          change (snoc _ _) with (rev [Vlong item; Vlong tl_item]).
          iApply rev_xorlist. ss.
          iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame. iSplit; ss.
          iPoseProof (equiv_dup with "tl_addr") as "[tl_addr tl_addr']".
          iCombine "tl_addr' tl_point" as "tl_point".
          iPoseProof (equiv_point_comm with "tl_point") as "tl_point".
          iPoseProof (equiv_dup with "tl_addr") as "[tl_addr tl_addr']".
          iCombine "tl_addr' tl_ofs" as "tl_ofs".
          iPoseProof (equiv_offset_comm with "tl_ofs") as "tl_ofs".
          iPoseProof (equiv_sym with "tl_addr") as "tl_addr".
          iCombine "tl_addr tl_equiv" as "tl_equiv".
          iPoseProof (equiv_trans with "tl_equiv") as "tl_equiv".
          iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero. iFrame. ss.
        * destruct v; clarify.
          iDestruct "LIST" as (i_tl' i_tl_nn m_next)
            "[[[[% tl_addr'] next_ofs] next_point] LIST]".
          iCombine "tl_addr' tl_addr" as "tl_addr".
          iPoseProof (capture_unique with "tl_addr") as "%". subst.
          iDestruct "tl_addr" as "[_ tl_addr]".
          rename H3 into m_next_size.

          iPoseProof (offset_slide_rev with "new_ofs") as "new_ofs".

          iApply isim_ccallU_pure; et.
          { eapply fn_has_spec_in_stb; et.
            { eapply STBINCL. stb_tac. unfold xorStb.
              unseal "stb". ss. }
            { ss. instantiate (1:= (inl (_,_,_,_,_,_,_,_,_,_))).
              ss. oauto. }
            { ss. } }
          { instantiate (1:=10). oauto. }

          ss. iSplitL "INV new_ofs next_ofs".
          { iSplit; ss. iSplit; ss. iSplitR "next_ofs"; ss. iFrame. ss. }
          iIntros (st_src9 st_tgt9 ret_src1 ret_tgt1) "[INV [POST %]]".
          iDestruct "POST" as (i_new i_next') "[[[[% new_ofs] next_ofs] new_equiv] next_equiv]".
          rewrite H4. clear H3 H4.
          iExists _. iSplit; ss.
          iPoseProof (equiv_ii_eq with "next_equiv") as "%". symmetry in H3. subst.

          hred_r. unhide. remove_tau.
          rewrite tl_ptr. hred_r.
          rewrite tl_ptr. hred_r.
          rewrite co_co_members. ss. hred_r.
          replace (Coqlib.align _ _) with 8%Z.
          rewrite cast_ptrofs. hred_r.

          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV tl_point_key tl_ofs".
          { iFrame. iExists _. iFrame. iPureIntro. split; ss. exists 1. ss. }
          iIntros (st_src10 st_tgt10) "[INV [tl_point_key tl_ofs]]".

          hred_r. unhide. remove_tau.
          rewrite tl_hdl_is_point. hred_r.
          rewrite new_cast_ptr. hred_r.

          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV tl_hdl_point tl_hdl_ofs".
          { iFrame. iExists _. iFrame. iPureIntro. split; ss.
            rewrite encode_val_length. ss. }
          iIntros (st_src11 st_tgt11) "[INV [tl_hdl_point tl_hdl_ofs]]".

          hred_r. remove_tau. 2: ss. hred_l. iApply isim_choose_src.
          iExists _. iApply isim_ret. iSplit; ss. iSplit; ss. iSplit; ss.
          iCombine "new_point_item new_point_key" as "new_point".
          iCombine "tl_point_item tl_point_key" as "tl_point".
          iPoseProof (points_to_collect with "new_point") as "new_point".
          iPoseProof (points_to_collect with "tl_point") as "tl_point".
          iPoseProof (offset_slide_rev with "tl_ofs") as "tl_ofs".
          iPoseProof (equiv_dup with "tl_addr") as "[tl_addr tl_addr']".
          iCombine "tl_addr' tl_point" as "tl_point".
          iPoseProof (equiv_point_comm with "tl_point") as "tl_point".
          iPoseProof (equiv_dup with "tl_addr") as "[tl_addr tl_addr']".
          iCombine "tl_addr' tl_ofs" as "tl_ofs".
          iPoseProof (equiv_offset_comm with "tl_ofs") as "tl_ofs".
          replace (snoc _ _) with (rev (Vlong item :: Vlong tl_item :: Vlong i :: lnext)).
          2:{ rewrite <- rev_involutive. f_equal.
              rewrite rev_snoc. f_equal. rewrite rev_involutive. et. }
          iExists _,_,_,_,_,_,_,_. iFrame. iSplit; ss.
          iApply rev_xorlist. ss.
          iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame. iSplit; ss.
          iExists _,_,_. iFrame. iSplit; ss.
          iExists _,_,_. iFrame. iSplit; ss. 
          iApply equiv_refl_equiv.
          iApply equiv_sym. et.
  Qed.

  End SIMFUNS.

End PROOF.