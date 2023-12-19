Require Import CoqlibCCR.
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

  Lemma decode_encode_item i : decode_val Mint64 (encode_val Mint64 (Vlong i)) = Vlong i.
  Proof. apply (decode_encode_val_general (Vlong i) Mint64 Mint64). Qed.

  Lemma decode_encode_null : decode_val Mint64 (encode_val Mint64 Vnullptr) = Vnullptr.
  Proof. rewrite (decode_encode_val_general Vnullptr Mint64 Mint64). et. Qed.

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


  Lemma sim_delete :
    sim_fnsem wf top2
      ("delete", fun_to_tgt "xorlist" (GlobalStb (Sk.canon sk)) (mk_pure delete_spec))
      ("delete", cfunU (decomp_func (Sk.canon sk) ce f_delete)).
  Proof.
    Opaque encode_val.
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
    iDestruct "PRE" as "[[% PRE] %]". unfold full_xorlist.
    iDestruct "PRE"
      as (m_hd_hdl m_tl_hdl hd_old tl_old ofs_hd_hdl ofs_tl_hdl tg_hd_hdl tg_tl_hdl)
      "[[[[[[hd_hdl_point hd_hdl_ofs] %] tl_hdl_point] tl_hdl_ofs] %] LIST]".
    des. clarify. ss. clarify. ss. hred_r.
    unhide. hred_r. unhide. remove_tau.
    rename i into from_tail. rename v into hd_handler.
    rename v0 into tl_handler. rename v1 into vreturn.
    rename l into linput. rename l0 into lreturn.
    rename Heq into del_spc. rename H5 into hd_hdl_align.
    rename H6 into tl_hdl_align.

    des_ifs_safe. hred_r. rename Heq into ptr64.
    iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%".
    rewrite H3. rename H3 into hd_hdl_ptr. hred_r.
    iApply isim_apc. iExists (Some (20%nat : Ord.t)).
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_hdl_point hd_hdl_ofs"; iFrame.
    { iPureIntro. rewrite encode_val_length. et. }
    iIntros (st_src0 st_tgt0) "[INV [hd_hdl_point hd_hdl_ofs]]".

    hred_r. replace (Vlong _) with Vnullptr by et.
    destruct linput.
    (* case: nil list *)
    - 
      (* admit "solved". *)
      unfold vlist_delete in del_spc. ss.
      assert (vreturn = Vlong Int64.zero) by des_ifs.
      assert (lreturn = []) by des_ifs. subst. clear del_spc.
      iDestruct "LIST" as "[NULL_tl NULL_hd]".
      iPoseProof (null_equiv with "NULL_tl") as "%". subst.
      iPoseProof (equiv_sym with "NULL_hd") as "H". iPoseProof (null_equiv with "H") as "%". subst.
      unfold Mptr. rewrite ptr64. rewrite decode_encode_null.
      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src1 st_tgt1) "INV".

      hred_r. destruct (Int.eq) eqn:?; ss; clarify. clear Heqb.
      unhide. remove_tau. unhide. remove_tau. rewrite ptr64. hred_r.
      hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret.
      iFrame. iSplit; ss. iSplit; ss.
      iExists _,_,_,_,_,_,_,_. iFrame. iSplit; ss.
    (* case: not nil list *)
    - ss. rename linput into lnext. destruct v; try solve [iDestruct "LIST" as "[]"]. rename i into hd_item.
      iDestruct "LIST" as (i_hd_prev i_hd_next m_hd_old) "[[[[% hd_prev_equiv] hd_ofs] hd_point] LIST]". rename H3 into m_hd_size.
      iPoseProof (decode_encode_ptr_ofs with "hd_ofs") as "%". rewrite H3. rename H3 into hd_old_deen.
      iApply isim_ccallU_cmp_ptr1; ss; oauto.
      iSplitL "INV hd_ofs"; iFrame.
      { iPureIntro. red. rewrite m_hd_size. vm_compute (size_chunk Mptr). vm_compute (Ptrofs.unsigned Ptrofs.zero). nia. }
      iIntros (st_src1 st_tgt1) "[INV hd_ofs]".

      hred_r. destruct (Int.eq) eqn: ?; ss; clarify. clear Heqb.
      unhide. remove_tau.
      destruct (Int.eq from_tail Int.zero) eqn:?.
      (* case: not nil list && delete from head *)
      + 
        (* admit "solved". *)
        pose proof (Int.eq_spec from_tail Int.zero). rewrite Heqb in H3. clear Heqb. clarify. unfold vlist_delete in del_spc. destruct Val.eq eqn:? in del_spc; ss; clarify. clear Heqs e.
        unhide. hred_r. unhide. remove_tau. rewrite hd_hdl_ptr. hred_r. 
        iApply isim_ccallU_load; ss; oauto.
        iSplitL "INV hd_hdl_point hd_hdl_ofs"; iFrame.
        { iPureIntro. rewrite encode_val_length. et. }
        iIntros (st_src2 st_tgt2) "[INV [hd_hdl_point hd_hdl_ofs]]".

        hred_r. unhide. remove_tau. unhide. remove_tau. rewrite hd_old_deen.
        iPoseProof (points_to_is_ptr with "hd_point") as "%". rewrite H3. rename H3 into hd_is_ptr. hred_r. rewrite hd_is_ptr. hred_r.
        rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
        iPoseProof (points_to_split with "hd_point") as "[hd_point_item hd_point_key]".
        change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs Ptrofs.zero). iPoseProof (add_null_r with "hd_ofs") as "%". rewrite H3. rename H3 into hd_add_null.
        iApply isim_ccallU_load; ss; oauto.
        iSplitL "INV hd_point_item hd_ofs"; iFrame.
        { iPureIntro. rewrite encode_val_length. split; et. exists 0. ss. }
        iIntros (st_src3 st_tgt3) "[INV [hd_point_item hd_ofs]]". rewrite decode_encode_item.

        hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
        hexploit SKINCLENV.
        { instantiate (2:="decrypt"). ss. }
        i. des. ss. rewrite FIND. rename FIND into decrypt_loc.
        hred_r. rewrite hd_is_ptr. hred_r. rewrite hd_is_ptr. hred_r.
        rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r. replace (Coqlib.align _ _) with 8%Z by et.

        iApply isim_ccallU_load; ss; oauto.
        iSplitL "INV hd_point_key hd_ofs"; iFrame.
        { iSplitL "hd_ofs". { iApply offset_slide; et. }
          iPureIntro. rewrite encode_val_length.
          split; et. exists 1. ss. }
        iIntros (st_src4 st_tgt4) "[INV [hd_point_key hd_ofs]]".

        hred_r. rewrite ptr64. hred_r. unfold Mptr at 8. rewrite ptr64. rewrite decode_encode_ofs. rewrite ptrofs_cast_ptr. hred_r.
        des_ifs_safe. clear e.
        replace (pred _) with blk by nia. erewrite SKINCLGD; et. hred_r. ss.

        iApply isim_ccallU_pure; et.
        { eapply fn_has_spec_in_stb; et.
          { eapply STBINCL. stb_tac. unfold xorStb.
            unseal "stb". ss. }
          { ss. instantiate(1:=inr _). ss. oauto. }
          { ss. } }
        { instantiate (1:=14). oauto. }

        ss. iSplitL "INV"; iFrame. { iSplit; ss. }
        iIntros (st_src5 st_tgt5 ret_src ret_tgt) "[INV [% %]]".
        rewrite H3. clear H3. iExists _. iSplit; ss. clarify.

        hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
        rewrite hd_hdl_ptr. hred_r. rewrite ptrofs_cast_ptr. hred_r.

        iApply isim_ccallU_store; ss; oauto.
        iSplitL "INV hd_hdl_point hd_hdl_ofs"; iFrame.
        { iExists _. iFrame. iPureIntro. rewrite encode_val_length. et. }
        iIntros (st_src6 st_tgt6) "[INV [hd_hdl_point hd_hdl_ofs]]".

        hred_r. unhide. remove_tau. unhide. remove_tau.
        replace (Vlong (Int64.repr _)) with Vnullptr by et.
        iPoseProof (null_equiv with "hd_prev_equiv") as "%".
        assert (i_hd_prev = Ptrofs.zero).
        { unfold Vptrofs, Vnullptr in *. des_ifs. replace intrange with intrange0 in * by apply proof_irrel. rewrite <- Heq0 in Heq. apply (f_equal Ptrofs.of_int64) in Heq. rewrite Ptrofs.of_int64_to_int64 in Heq; et. }
        subst. clear H3. rewrite Ptrofs.xor_zero_l.

        destruct lreturn.
        (* case: singleton list && delete from head *)
        * 
          (* admit "solved". *)
          ss. iDestruct "LIST" as "[tl_equiv NULL_next]".
          iPoseProof (equiv_sym with "NULL_next") as "H". iPoseProof (null_equiv with "H") as "%". rewrite H3. clear H3 i_hd_next.
          iApply isim_ccallU_cmp_ptr0; ss; oauto.
          iSplitL "INV"; iFrame.
          iIntros (st_src7 st_tgt7) "INV".
          
          hred_r. des_ifs_safe. clear Heq. unhide. remove_tau.
          iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%". rewrite H3. rename H3 into tl_hdl_ptr. hred_r. des_ifs_safe. hred_r. replace (Vlong (Int64.repr _)) with Vnullptr by et.

          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV tl_hdl_point tl_hdl_ofs"; iFrame.
          { iExists _. iFrame. iPureIntro. rewrite encode_val_length; et. }
          iIntros (st_src8 st_tgt8) "[INV [tl_hdl_point tl_hdl_ofs]]".

          hred_r. unhide. remove_tau.
          hexploit SKINCLENV.
          { instantiate (2:="free"). ss. }
          i. des. ss. rewrite FIND. rename FIND into free_loc. hred_r.

          iPoseProof ((@point_cast_ptr _ _ _ _ Es) with "hd_point_item") as "%".
          rewrite H3. rename H3 into hd_old_cast. hred_r. des_ifs_safe.

          replace (pred _) with blk0 by nia.
          erewrite SKINCLGD; et. hred_r. ss.
          iCombine "hd_point_item hd_point_key" as "hd_point".
          replace (Val.addl tl_old (Vlong _)) 
            with (Val.addl tl_old (Vptrofs (Ptrofs.repr (strings.length (inj_bytes (encode_int 8 (Int64.unsigned hd_item))))))) by et.
          iPoseProof (points_to_collect with "hd_point") as "hd_point".
          iPoseProof (offset_slide_rev with "hd_ofs") as "hd_ofs".

          iApply isim_ccallU_mfree; ss; oauto.
          iSplitL "INV hd_point hd_ofs"; iFrame.
          { iExists _,_. iFrame. ss. }
          iIntros (st_src9 st_tgt9) "INV". clear e.

          hred_r. unhide. remove_tau. rewrite ptr64. hred_r.
          hred_l. iApply isim_choose_src. iExists _.
          iApply isim_ret. iFrame. iSplit; ss. iSplit; ss. iExists _,_,_,_,_,_,_,_. iFrame; ss. 
        (* case: list length is more than 1 && delete from head *)
        * ss. destruct v; clarify.
          iDestruct "LIST" as (i_hd i_hd_nn m_hd_next) "[[[[% hd_equiv] hd_next_ofs] hd_next_point] LIST]". rename H3 into m_hd_next_size. rename i into hd_next_item.

          iApply isim_ccallU_cmp_ptr3; ss; oauto.
          iSplitL "INV hd_next_ofs"; iFrame.
          { iPureIntro. red. rewrite m_hd_next_size. vm_compute (Ptrofs.unsigned Ptrofs.zero). vm_compute (size_chunk Mptr). nia. }
          iIntros (st_src7 st_tgt7) "[INV hd_next_ofs]".
          
          hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau. unhide. remove_tau.
          rewrite decrypt_loc. hred_r. des_ifs_safe. hred_r. rewrite Heq. clear Heq. hred_r.
          rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
          replace (Coqlib.align _ _) with 8%Z by et.

          iPoseProof (points_to_split with "hd_next_point") as "[hd_next_point_item hd_next_point_key]".
          change (strings.length _) with 8. ss.

          iApply isim_ccallU_load; ss; oauto.
          iSplitL "INV hd_next_point_key hd_next_ofs"; iFrame.
          { iSplit. { iApply offset_slide. et. }
            iPureIntro. rewrite encode_val_length. split; et. exists 1. ss. }
          iIntros (st_src8 st_tgt8) "[INV [hd_next_point_key hd_next_ofs]]".
          unfold Mptr at 11. rewrite ptr64. rewrite decode_encode_ofs. hred_r.

          iPoseProof ((@point_cast_ptr _ _ _ _ Es) with "hd_point_item") as "%".
          rewrite H3. rename H3 into hd_old_cast. hred_r. rewrite ptrofs_cast_ptr. hred_r.

          replace (pred _) with blk by nia.
          erewrite SKINCLGD; et.
          hred_r. ss.

          iPoseProof (offset_slide_rev with "hd_ofs") as "hd_ofs".
          iApply isim_ccallU_pure; et.
          { eapply fn_has_spec_in_stb; et.
            { eapply STBINCL. stb_tac. unfold xorStb.
              unseal "stb". ss. }
            { ss. instantiate (1:=inl (_,_,_,_,_,_)).
              ss. oauto. }
            { ss. } }
          { instantiate (1:=10). oauto. }
          ss. iSplitL "INV hd_ofs"; iFrame.
          { iSplit; ss. }
          iIntros (st_src9 st_tgt9 ret_src ret_tgt0) "[INV [POST %]]".
          iDestruct "POST" as (i_ptr) "[[% hd_ofs] hd_equiv']". rewrite H4. iExists _. iSplit; ss. clear H4 H3.
          iCombine "hd_equiv' hd_equiv" as "hd_equiv". iPoseProof (capture_unique with "hd_equiv") as "%". clarify. iDestruct "hd_equiv" as "[_ hd_equiv]".

          hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
          hexploit SKINCLENV.
          { instantiate (2:="encrypt"). ss. }
          i. des. ss. rewrite FIND. rename FIND into encrypt_loc.

          hred_r. rewrite ptrofs_cast_ptr. hred_r. des_ifs_safe. clear e e0. hred_r.
          replace (pred _) with blk0 by nia.
          erewrite SKINCLGD; et. hred_r. ss.
          change (Vlong (Int64.repr _)) with Vnullptr.
          rewrite Ptrofs.xor_commut. rewrite Ptrofs.xor_assoc. rewrite Ptrofs.xor_idem. rewrite Ptrofs.xor_zero.

          destruct (Ptrofs.eq_dec i_hd_nn Ptrofs.zero).
          (* case: list length is 2 && delete from head *)
          ** 
             (* admit "solved". *)
             subst. change (Vptrofs Ptrofs.zero) with Vnullptr.
             iApply isim_ccallU_pure; et.
             { eapply fn_has_spec_in_stb; et.
               { eapply STBINCL. stb_tac. unfold xorStb.
                 unseal "stb". ss. }
               { ss. et. instantiate (1:=inr (inr (inr ()))).
                 ss. oauto. }
               { ss. } }
             { instantiate (1:=9). oauto. }
             ss.
             iSplitL "INV"; iFrame.
             { ss. }
             iIntros (st_src10 st_tgt10 ret_src0 ret_tgt1) "[INV [% %]]".
             rewrite H3. iExists _. iSplit; ss. clear H3 H4.

             hred_r. unhide. remove_tau.
             iPoseProof (points_to_is_ptr with "hd_next_point_item") as "%". rewrite H3. rename H3 into hd_next_is_ptr.

             hred_r. rewrite hd_next_is_ptr. hred_r.
             rewrite get_co. hred_r. rewrite co_co_members.
             ss. hred_r. change Vnullptr with (Vlong Int64.zero). ss. rewrite ptr64. hred_r. change (Coqlib.align _ _) with 8%Z.

             iApply isim_ccallU_store; ss; oauto.
             iSplitL "INV hd_next_point_key hd_next_ofs"; iFrame.
             { iExists _. iFrame. iPureIntro. rewrite encode_val_length. split; ss. exists 1. ss. }
             iIntros (st_src11 st_tgt11) "[INV [hd_next_point_key hd_next_ofs]]".

             hred_r. unhide. remove_tau.
             hexploit SKINCLENV.
             { instantiate (2:="free"). ss. }
             i. des. ss. rewrite FIND. rename FIND into free_loc. hred_r. 
             rewrite hd_old_cast. hred_r.
             destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
             replace (pred _) with blk1 by nia.
             erewrite SKINCLGD; et. hred_r.

             iCombine "hd_point_item hd_point_key" as "hd_point".
             iPoseProof (points_to_collect with "hd_point") as "hd_point".

             iApply isim_ccallU_mfree; ss; oauto.
             iSplitL "INV hd_point hd_ofs"; iFrame.
             { iExists _,_. iFrame. iPureIntro. ss. }
             iIntros (st_src12 st_tgt12) "INV".

             hred_r. unhide. remove_tau. rewrite ptr64. hred_r. hred_l. iApply isim_choose_src. iExists _.

             iApply isim_ret. iFrame. iSplit; ss. iSplit; ss.
             change 8%Z with (Z.of_nat (strings.length (encode_val Mint64 (Vlong hd_next_item)))).
             iCombine "hd_next_point_item hd_next_point_key" as "hd_next_point".  iPoseProof (points_to_collect with "hd_next_point") as "hd_next_point". iPoseProof (offset_slide_rev with "hd_next_ofs") as "hd_next_ofs".
             iExists _,_,_,_,_,_,_,_. iFrame. iSplit; ss.
             change (Vlong Int64.zero) with (Vptrofs Ptrofs.zero).
             iExists _,_,_. iFrame. rewrite Ptrofs.xor_idem. iFrame. iPureIntro. ss.
          (* case: list length is more than 2 && delete from head *)
          ** destruct lreturn.
             { ss. iDestruct "LIST" as "[A B]". iPoseProof (equiv_sym with "B") as "B". iPoseProof (null_equiv with "B") as "%".
               exfalso. unfold Vptrofs, Vnullptr in *. rewrite ptr64 in *. apply n.
               change Ptrofs.zero with (Ptrofs.of_int64 Int64.zero).
               rewrite <- (Ptrofs.of_int64_to_int64 ptr64 i_hd_nn). f_equal.
               inversion H3. destruct (Ptrofs.to_int64 i_hd_nn).
               destruct Int64.zero. clarify. f_equal. apply proof_irrel. }
             ss. destruct v; clarify.
             iDestruct "LIST" as (i_hd_next' i_hd_nnn m_hd_nn) "[[[[% hd_next_equiv] hd_nn_ofs] hd_nn_point] LIST]". rename H3 into m_hd_nn_size.
             iPoseProof (equiv_sym with "hd_next_equiv") as "hd_next_equiv". iPoseProof (equiv_ii_eq with "hd_next_equiv") as "%". clarify.

             iApply isim_ccallU_pure; et.
             { eapply fn_has_spec_in_stb; et.
               { eapply STBINCL. stb_tac. unfold xorStb.
                 unseal "stb". ss. }
               { ss. et. instantiate (1:=inr (inr (inl (_,_,_,_,_)))).
                 ss. oauto. }
               { ss. } }
             { instantiate (1:=9). oauto. }
             ss. iSplitL "INV hd_nn_ofs"; iFrame. { iSplit; ss. }
             iIntros (st_src10 st_tgt10 ret_src0 ret_tgt1) "[INV [POST %]]".
             iDestruct "POST" as (i_hd_nn') "[[% hd_nn_equiv'] hd_nn_ofs]".
             rewrite H4. clear H3 H4. iExists _. iSplit; ss.
             iPoseProof (equiv_sym with "hd_nn_equiv'") as "hd_nn_equiv'". iPoseProof (equiv_ii_eq with "hd_nn_equiv'") as "%". clarify.

             hred_r. unhide. remove_tau.
             iPoseProof (points_to_is_ptr with "hd_next_point_item") as "%". rewrite H3. hred_r. rewrite H3. hred_r. rename H3 into hd_next_is_ptr.
             rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r. rewrite ptrofs_cast_ptr. hred_r.

             change (Coqlib.align _ _) with 8%Z.
             iApply isim_ccallU_store; ss; oauto.
             iSplitL "INV hd_next_point_key hd_next_ofs"; iFrame.
             { iExists _. iFrame. iPureIntro. rewrite encode_val_length. split; ss. exists 1. ss. } 
             iIntros (st_src11 st_tgt11) "[INV [hd_next_point_key hd_next_ofs]]".

             hred_r. unhide. remove_tau.
             hexploit SKINCLENV.
             { instantiate (2:="free"). ss. }
             i. des. ss. rewrite FIND. rename FIND into free_loc.

             hred_r. rewrite hd_old_cast. hred_r.
             destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
             replace (pred _) with blk1 by nia.
             erewrite SKINCLGD; et. hred_r.

             iCombine "hd_point_item hd_point_key" as "hd_point". iPoseProof (points_to_collect with "hd_point") as "hd_point".
             iApply isim_ccallU_mfree; ss; oauto.
             iSplitL "INV hd_point hd_ofs"; iFrame. { iExists _,_. iFrame. iPureIntro. ss. }
             iIntros (st_src12 st_tgt12) "INV".

             hred_r. unhide. remove_tau. rewrite ptr64. hred_r. hred_l. iApply isim_choose_src. iExists _.

             iApply isim_ret. iFrame. iCombine "hd_next_point_item hd_next_point_key" as "hd_next_point". iPoseProof (points_to_collect with "hd_next_point") as "hd_next_point".
             iSplit; ss. iSplit; ss. iExists _,_,_,_,_,_,_,_. iFrame.
             iPoseProof (offset_slide_rev with "hd_next_ofs") as "hd_next_ofs".
             iSplit; ss. iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame.
             iSplit; ss. iExists _,_,_. iFrame. ss.
      (* case: not nil list && delete from tail *)
      + pose proof (Int.eq_spec from_tail Int.zero). rewrite Heqb in H3. clear Heqb. unfold vlist_delete in del_spc.
        destruct Val.eq eqn:? in del_spc.
        { exfalso. clear - e H3. unfold Vzero in *. inv e. et. }
        clear Heqs n. rename H3 into is_tail.
        Local Opaque last. Local Opaque removelast. Local Opaque rev.
        iAssert (frag_xorlist 1 m_null m_null Vnullptr hd_old tl_old Vnullptr (Vlong hd_item :: lnext))
                  with "[hd_prev_equiv hd_point hd_ofs LIST]" as "LIST". { ss. iExists _,_,_. iFrame. ss. }
        iPoseProof (rev_xorlist with "LIST") as "LIST".
        assert (len_sup: length (rev (Vlong hd_item :: lnext)) ≥ 1).
        { rewrite rev_length. ss. nia. }
        revert len_sup del_spc. set (rev (Vlong hd_item :: lnext)) as l.
        replace (Vlong hd_item :: lnext) with (rev (rev (Vlong hd_item :: lnext))) by now rewrite rev_involutive; et.
        unfold l. clear l. generalize (rev (Vlong hd_item :: lnext)). clear hd_item lnext.
        i. destruct l; ss; try nia.
        rename l into lnext. destruct v; clarify. rename i into tl_item.
        iDestruct "LIST" as (i_tl_next i_tl_prev m_tl_old) "[[[[% tl_next_equiv] tl_ofs] tl_point] LIST]". rename H3 into m_tl_size.

        unhide. hred_r. unhide. remove_tau. 
        iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%". rename H3 into tl_hdl_ptr.
        rewrite tl_hdl_ptr. hred_r. 
        iApply isim_ccallU_load; ss; oauto.
        iSplitL "INV tl_hdl_point tl_hdl_ofs"; iFrame.
        { iPureIntro. rewrite encode_val_length. et. }
        iIntros (st_src2 st_tgt2) "[INV [tl_hdl_point tl_hdl_ofs]]".

        iPoseProof (decode_encode_ptr_ofs with "tl_ofs") as "%". rewrite H3. rename H3 into tl_old_deen.

        hred_r. unhide. remove_tau. unhide. remove_tau.
        iPoseProof (points_to_is_ptr with "tl_point") as "%". rewrite H3. rename H3 into tl_is_ptr. hred_r. rewrite tl_is_ptr. hred_r.
        rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
        iPoseProof (points_to_split with "tl_point") as "[tl_point_item tl_point_key]".
        change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs Ptrofs.zero). iPoseProof (add_null_r with "tl_ofs") as "%". rewrite H3. rename H3 into tl_add_null.
        iApply isim_ccallU_load; ss; oauto.
        iSplitL "INV tl_point_item tl_ofs"; iFrame.
        { iPureIntro. rewrite encode_val_length. split; et. exists 0. ss. }
        iIntros (st_src3 st_tgt3) "[INV [tl_point_item tl_ofs]]". rewrite decode_encode_item.
        
        hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
        hexploit SKINCLENV.
        { instantiate (2:="decrypt"). ss. }
        i. des. ss. rewrite FIND. rename FIND into decrypt_loc.
        hred_r. rewrite tl_is_ptr. hred_r. rewrite tl_is_ptr. hred_r.
        rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r. replace (Coqlib.align _ _) with 8%Z by et.

        iApply isim_ccallU_load; ss; oauto.
        iSplitL "INV tl_point_key tl_ofs"; iFrame.
        { iSplitL "tl_ofs". { iApply offset_slide; et. }
          iPureIntro. rewrite encode_val_length.
          split; et. exists 1. ss. }
        iIntros (st_src4 st_tgt4) "[INV [tl_point_key tl_ofs]]".

        hred_r. rewrite ptr64. hred_r. unfold Mptr at 8. rewrite ptr64. rewrite decode_encode_ofs. rewrite ptrofs_cast_ptr. hred_r.
        des_ifs_safe. clear e.
        replace (pred _) with blk by nia. erewrite SKINCLGD; et. hred_r. ss.

        iApply isim_ccallU_pure; et.
        { eapply fn_has_spec_in_stb; et.
          { eapply STBINCL. stb_tac. unfold xorStb.
            unseal "stb". ss. }
          { ss. instantiate(1:=inr _). ss. oauto. }
          { ss. } }
        { instantiate (1:=14). oauto. }

        ss. iSplitL "INV"; iFrame. { iSplit; ss. }
        iIntros (st_src5 st_tgt5 ret_src ret_tgt) "[INV [% %]]".
        rewrite H3. clear H3. iExists _. iSplit; ss. clarify.

        hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
        rewrite tl_hdl_ptr. hred_r. rewrite ptrofs_cast_ptr. hred_r.

        iApply isim_ccallU_store; ss; oauto.
        iSplitL "INV tl_hdl_point tl_hdl_ofs"; iFrame.
        { iExists _. iFrame. iPureIntro. rewrite encode_val_length. et. }
        iIntros (st_src6 st_tgt6) "[INV [tl_hdl_point tl_hdl_ofs]]".

        hred_r. unhide. remove_tau. unhide. remove_tau.
        replace (Vlong (Int64.repr _)) with Vnullptr by et.
        iPoseProof (null_equiv with "tl_next_equiv") as "%".
        assert (i_tl_next = Ptrofs.zero).
        { unfold Vptrofs, Vnullptr in *. des_ifs. replace intrange with intrange0 in * by apply proof_irrel. rewrite <- Heq0 in Heq. apply (f_equal Ptrofs.of_int64) in Heq. rewrite Ptrofs.of_int64_to_int64 in Heq; et. }
        subst. clear H3. rewrite Ptrofs.xor_zero_l.

        destruct lnext.
        (* case: singleton list && delete from head *)
        * 
          (* admit "solved". *)
          ss. iDestruct "LIST" as "[tl_equiv NULL_prev]".
          iPoseProof (equiv_sym with "NULL_prev") as "H". iPoseProof (null_equiv with "H") as "%". rewrite H3. clear H3 i_tl_prev.
          iApply isim_ccallU_cmp_ptr0; ss; oauto.
          iSplitL "INV"; iFrame.
          iIntros (st_src7 st_tgt7) "INV".
          
          hred_r. des_ifs_safe. clear Heq. unhide. remove_tau.
          rewrite hd_hdl_ptr. hred_r. rewrite ptr64. hred_r. change (Vlong (Int64.repr _)) with Vnullptr.

          iApply isim_ccallU_store; ss; oauto.
          iSplitL "INV hd_hdl_point hd_hdl_ofs"; iFrame.
          { iExists _. iFrame. iPureIntro. rewrite encode_val_length; et. }
          iIntros (st_src8 st_tgt8) "[INV [hd_hdl_point hd_hdl_ofs]]".

          hred_r. unhide. remove_tau.
          hexploit SKINCLENV.
          { instantiate (2:="free"). ss. }
          i. des. ss. rewrite FIND. rename FIND into free_loc. hred_r.

          iPoseProof ((@point_cast_ptr _ _ _ _ Es) with "tl_point_item") as "%".
          rewrite H3. rename H3 into tl_old_cast. hred_r. des_ifs_safe.

          replace (pred _) with blk0 by nia.
          erewrite SKINCLGD; et. hred_r. ss.
          iCombine "tl_point_item tl_point_key" as "tl_point".
          iPoseProof (points_to_collect with "tl_point") as "tl_point".
          iPoseProof (offset_slide_rev with "tl_ofs") as "tl_ofs".

          iApply isim_ccallU_mfree; ss; oauto.
          iSplitL "INV tl_point tl_ofs"; iFrame.
          { iExists _,_. iFrame. ss. }
          iIntros (st_src9 st_tgt9) "INV". clear e.

          hred_r. unhide. remove_tau. rewrite ptr64. hred_r.
          hred_l. iApply isim_choose_src. iExists _.
          iApply isim_ret. iFrame. iSplit; ss. iSplit; ss. iExists _,_,_,_,_,_,_,_. iFrame; ss. 
        (* case: list length is more than 1 && delete from head *)
        * ss. destruct v; clarify.
          iDestruct "LIST" as (i_tl i_tl_pp m_tl_prev) "[[[[% tl_equiv] tl_prev_ofs] tl_prev_point] LIST]". rename H3 into m_tl_prev_size. rename i into tl_prev_item.

          iApply isim_ccallU_cmp_ptr3; ss; oauto.
          iSplitL "INV tl_prev_ofs"; iFrame.
          { iPureIntro. red. rewrite m_tl_prev_size. vm_compute (Ptrofs.unsigned Ptrofs.zero). vm_compute (size_chunk Mptr). nia. }
          iIntros (st_src7 st_tgt7) "[INV tl_prev_ofs]".
          
          hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau. unhide. remove_tau.
          rewrite decrypt_loc. hred_r. des_ifs_safe. hred_r. rewrite Heq. clear Heq. hred_r.
          rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
          replace (Coqlib.align _ _) with 8%Z by et.

          iPoseProof (points_to_split with "tl_prev_point") as "[tl_prev_point_item tl_prev_point_key]".
          change (strings.length _) with 8. ss.

          iApply isim_ccallU_load; ss; oauto.
          iSplitL "INV tl_prev_point_key tl_prev_ofs"; iFrame.
          { iSplit. { iApply offset_slide. et. }
            iPureIntro. rewrite encode_val_length. split; et. exists 1. ss. }
          iIntros (st_src8 st_tgt8) "[INV [tl_prev_point_key tl_prev_ofs]]".
          unfold Mptr at 9. rewrite ptr64. rewrite decode_encode_ofs. hred_r.

          iPoseProof ((@point_cast_ptr _ _ _ _ Es) with "tl_point_item") as "%".
          rewrite H3. rename H3 into tl_old_cast. hred_r. rewrite ptrofs_cast_ptr. hred_r.

          replace (pred _) with blk by nia.
          erewrite SKINCLGD; et.
          hred_r. ss.

          iPoseProof (offset_slide_rev with "tl_ofs") as "tl_ofs".
          iApply isim_ccallU_pure; et.
          { eapply fn_has_spec_in_stb; et.
            { eapply STBINCL. stb_tac. unfold xorStb.
              unseal "stb". ss. }
            { ss. instantiate (1:=inl (_,_,_,_,_,_)).
              ss. oauto. }
            { ss. } }
          { instantiate (1:=10). oauto. }
          ss. iSplitL "INV tl_ofs"; iFrame.
          { iSplit; ss. }
          iIntros (st_src9 st_tgt9 ret_src ret_tgt0) "[INV [POST %]]".
          iDestruct "POST" as (i_ptr) "[[% tl_ofs] tl_equiv']". rewrite H4. iExists _. iSplit; ss. clear H4 H3.
          iCombine "tl_equiv' tl_equiv" as "tl_equiv". iPoseProof (capture_unique with "tl_equiv") as "%". clarify. iDestruct "tl_equiv" as "[_ tl_equiv]".

          hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
          hexploit SKINCLENV.
          { instantiate (2:="encrypt"). ss. }
          i. des. ss. rewrite FIND. rename FIND into encrypt_loc.

          hred_r. rewrite ptrofs_cast_ptr. hred_r. des_ifs_safe. clear e e0. hred_r.
          replace (pred _) with blk0 by nia.
          erewrite SKINCLGD; et. hred_r. ss.
          change (Vlong (Int64.repr _)) with Vnullptr.
          rewrite Ptrofs.xor_commut. rewrite Ptrofs.xor_assoc. rewrite Ptrofs.xor_idem. rewrite Ptrofs.xor_zero.

          destruct (Ptrofs.eq_dec i_tl_pp Ptrofs.zero).
          (* case: list length is 2 && delete from head *)
          ** 
             (* admit "solved". *)
             subst. change (Vptrofs Ptrofs.zero) with Vnullptr.
             iApply isim_ccallU_pure; et.
             { eapply fn_has_spec_in_stb; et.
               { eapply STBINCL. stb_tac. unfold xorStb.
                 unseal "stb". ss. }
               { ss. et. instantiate (1:=inr (inr (inr ()))).
                 ss. oauto. }
               { ss. } }
             { instantiate (1:=9). oauto. }
             ss.
             iSplitL "INV"; iFrame.
             { ss. }
             iIntros (st_src10 st_tgt10 ret_src0 ret_tgt1) "[INV [% %]]".
             rewrite H3. iExists _. iSplit; ss. clear H3 H4.

             hred_r. unhide. remove_tau.
             iPoseProof (points_to_is_ptr with "tl_prev_point_item") as "%". rewrite H3. rename H3 into tl_prev_is_ptr.

             hred_r. rewrite tl_prev_is_ptr. hred_r.
             rewrite get_co. hred_r. rewrite co_co_members.
             ss. hred_r. change Vnullptr with (Vlong Int64.zero). ss. rewrite ptr64. hred_r. change (Coqlib.align _ _) with 8%Z.

             iApply isim_ccallU_store; ss; oauto.
             iSplitL "INV tl_prev_point_key tl_prev_ofs"; iFrame.
             { iExists _. iFrame. iPureIntro. rewrite encode_val_length. split; ss. exists 1. ss. }
             iIntros (st_src11 st_tgt11) "[INV [tl_prev_point_key tl_prev_ofs]]".

             hred_r. unhide. remove_tau.
             hexploit SKINCLENV.
             { instantiate (2:="free"). ss. }
             i. des. ss. rewrite FIND. rename FIND into free_loc. hred_r. 
             rewrite tl_old_cast. hred_r.
             destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
             replace (pred _) with blk1 by nia.
             erewrite SKINCLGD; et. hred_r.

             iCombine "tl_point_item tl_point_key" as "tl_point".
             iPoseProof (points_to_collect with "tl_point") as "tl_point".

             iApply isim_ccallU_mfree; ss; oauto.
             iSplitL "INV tl_point tl_ofs"; iFrame.
             { iExists _,_. iFrame. iPureIntro. ss. }
             iIntros (st_src12 st_tgt12) "INV".

             hred_r. unhide. remove_tau. rewrite ptr64. hred_r. hred_l. iApply isim_choose_src. iExists _.

             iApply isim_ret. iFrame. iSplit; ss. iSplit; ss.
             { change (Vlong tl_item :: _) with ([Vlong tl_item] ++ (Vlong tl_prev_item :: lnext)).
               rewrite rev_app_distr.
               change (rev [Vlong tl_item]) with [Vlong tl_item]. rewrite last_last. et. }
             change (Vlong tl_item :: _) with ([Vlong tl_item] ++ (Vlong tl_prev_item :: lnext)).
             rewrite rev_app_distr.
             rewrite removelast_app; et.
             change (removelast (rev _)) with (@nil val).
             rewrite app_nil_r.
             iCombine "tl_prev_point_item tl_prev_point_key" as "tl_prev_point". iPoseProof (points_to_collect with "tl_prev_point") as "tl_prev_point". iPoseProof (offset_slide_rev with "tl_prev_ofs") as "tl_next_ofs".
             iExists _,_,_,_,_,_,_,_. iFrame. iSplit; ss.
             iApply rev_xorlist. ss.
             change (Vlong Int64.zero) with (Vptrofs Ptrofs.zero).
             iExists _,_,_. iFrame. rewrite Ptrofs.xor_idem. iFrame. ss.
          (* case: list length is more than 2 && delete from head *)
          ** destruct lnext.
             { ss. iDestruct "LIST" as "[A B]". iPoseProof (equiv_sym with "B") as "B". iPoseProof (null_equiv with "B") as "%".
               exfalso. unfold Vptrofs, Vnullptr in *. rewrite ptr64 in *. apply n.
               change Ptrofs.zero with (Ptrofs.of_int64 Int64.zero).
               rewrite <- (Ptrofs.of_int64_to_int64 ptr64 i_tl_pp). f_equal.
               inversion H3. destruct (Ptrofs.to_int64 i_tl_pp).
               destruct Int64.zero. clarify. f_equal. apply proof_irrel. }
             ss. destruct v; clarify.
             iDestruct "LIST" as (i_tl_prev' i_tl_ppp m_tl_ppp) "[[[[% tl_prev_equiv] tl_pp_ofs] tl_pp_point] LIST]". rename H3 into m_tl_pp_size.
             iPoseProof (equiv_sym with "tl_prev_equiv") as "tl_prev_equiv". iPoseProof (equiv_ii_eq with "tl_prev_equiv") as "%". clarify.

             iApply isim_ccallU_pure; et.
             { eapply fn_has_spec_in_stb; et.
               { eapply STBINCL. stb_tac. unfold xorStb.
                 unseal "stb". ss. }
               { ss. et. instantiate (1:=inr (inl (_,_,_,_,_))).
                 ss. oauto. }
               { ss. } }
             { instantiate (1:=9). oauto. }
             ss. iSplitL "INV tl_pp_ofs"; iFrame. { iSplit; ss. }
             iIntros (st_src10 st_tgt10 ret_src0 ret_tgt1) "[INV [POST %]]".
             iDestruct "POST" as (i_tl_pp') "[[% tl_pp_equiv'] tl_pp_ofs]".
             rewrite H4. clear H3 H4. iExists _. iSplit; ss.
             iPoseProof (equiv_sym with "tl_pp_equiv'") as "tl_pp_equiv'". iPoseProof (equiv_ii_eq with "tl_pp_equiv'") as "%". clarify.

             hred_r. unhide. remove_tau.
             iPoseProof (points_to_is_ptr with "tl_prev_point_item") as "%". rewrite H3. hred_r. rewrite H3. hred_r. rename H3 into tl_prev_is_ptr.
             rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r. rewrite ptrofs_cast_ptr. hred_r.

             change (Coqlib.align _ _) with 8%Z.
             iApply isim_ccallU_store; ss; oauto.
             iSplitL "INV tl_prev_point_key tl_prev_ofs"; iFrame.
             { iExists _. iFrame. iPureIntro. rewrite encode_val_length. split; ss. exists 1. ss. } 
             iIntros (st_src11 st_tgt11) "[INV [tl_prev_point_key tl_prev_ofs]]".

             hred_r. unhide. remove_tau.
             hexploit SKINCLENV.
             { instantiate (2:="free"). ss. }
             i. des. ss. rewrite FIND. rename FIND into free_loc.

             hred_r. rewrite tl_old_cast. hred_r.
             destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
             replace (pred _) with blk1 by nia.
             erewrite SKINCLGD; et. hred_r.

             iCombine "tl_point_item tl_point_key" as "tl_point". iPoseProof (points_to_collect with "tl_point") as "tl_point".
             iApply isim_ccallU_mfree; ss; oauto.
             iSplitL "INV tl_point tl_ofs"; iFrame. { iExists _,_. iFrame. iPureIntro. ss. }
             iIntros (st_src12 st_tgt12) "INV".

             hred_r. unhide. remove_tau. rewrite ptr64. hred_r. hred_l. iApply isim_choose_src. iExists _.

             iApply isim_ret. iFrame. iCombine "tl_prev_point_item tl_prev_point_key" as "tl_prev_point". iPoseProof (points_to_collect with "tl_prev_point") as "tl_prev_point".
             iSplit; ss. iSplit; ss.
             { change (Vlong tl_item :: _) with ([Vlong tl_item] ++ (Vlong tl_prev_item :: Vlong i :: lnext)).
               rewrite rev_app_distr.
               change (rev [Vlong tl_item]) with [Vlong tl_item]. rewrite last_last. et. }
             change (Vlong tl_item :: _) with ([Vlong tl_item] ++ (Vlong tl_prev_item :: Vlong i :: lnext)).
             rewrite rev_app_distr.
             rewrite removelast_app; et.
             change (removelast (rev _)) with (@nil val).
             rewrite app_nil_r.
             iExists _,_,_,_,_,_,_,_. iFrame. iSplit; ss.
             iApply rev_xorlist. ss.
             change (Vlong Int64.zero) with (Vptrofs Ptrofs.zero).
             iPoseProof (offset_slide_rev with "tl_prev_ofs") as "tl_prev_ofs".
             iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame. iSplit; ss.
             iExists _,_,_. iFrame. ss.
  Qed.

  Lemma sim_encrypt :
    sim_fnsem wf top2
      ("encrypt", fun_to_tgt "xorlist" (GlobalStb (Sk.canon sk)) (mk_pure encrypt_spec))
      ("encrypt", cfunU (decomp_func (Sk.canon sk) ce f_encrypt)).
  Proof.
    (* econs; ss. red.

    unfold prog in ce. unfold mkprogram in ce.
    destruct (build_composite_env').
    get_composite ce e.

    apply isim_fun_to_tgt; auto. i; ss.
    unfold decomp_func, function_entry_c. ss.
    init_hide.

    iIntros "[INV PRE]".
    destruct x as [?|[?|?]]; ss.
    - unfold encrypt_hoare1 in *. des_ifs. ss.
      iDestruct "PRE" as "[[[% ALIVE0] ALIVE1] %]".
      clarify. hred_r. unhide. remove_tau. unhide. remove_tau. 
      iPoseProof (liveness_ptr with "ALIVE0") as "%".
      unfold cast_to_ptr in H3. rewrite H3. hred_r.

      iApply isim_apc. iExists (Some (2%nat : Ord.t)).
      iApply isim_ccallU_capture2; ss; oauto.
      iSplitL "INV ALIVE0"; iFrame.
      iIntros (st_src0 st_tgt0 i) "[INV [ALIVE0 CAP0]]".

      hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.
      iPoseProof (liveness_ptr with "ALIVE1") as "%".
      unfold cast_to_ptr in H4. rewrite H4. hred_r.

      iApply isim_ccallU_capture2; ss; oauto.
      iSplitL "INV ALIVE1"; iFrame.
      iIntros (st_src1 st_tgt1 i0) "[INV [ALIVE1 CAP1]]".

      hred_r. remove_tau. unhide. remove_tau. des_ifs_safe.
      hred_r. hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iSplits; ss.
      iFrame. iPureIntro. f_equal.
      autounfold with ptrArith in *. des_ifs_safe. f_equal.
      autorewrite with ptrArith; auto with ptrArith.
      apply lxor_size; auto with ptrArith.

    - unfold encrypt_hoare2 in *. des_ifs. ss.
      iDestruct "PRE" as "[[% ALIVE] %]".
      clarify. hred_r. unhide. remove_tau. unhide. remove_tau. 
      iPoseProof (liveness_ptr with "ALIVE") as "%".
      unfold cast_to_ptr in H3. rewrite H3. hred_r.

      iApply isim_apc. iExists (Some (2%nat : Ord.t)).
      iApply isim_ccallU_capture2; ss; oauto.
      iSplitL "INV ALIVE"; iFrame.
      iIntros (st_src0 st_tgt0 i) "[INV [ALIVE CAP]]".

      hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.
      des_ifs_safe. hred_r. rewrite <- Heq.

      iApply isim_ccallU_capture1; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src1 st_tgt1) "INV".

      hred_r. remove_tau. unhide. remove_tau. des_ifs_safe.
      hred_r. hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iSplits; ss.
      iFrame. iPureIntro. f_equal. unfold Vnullptr in Heq1.
      autounfold with ptrArith in *. des_ifs_safe. f_equal.
      autorewrite with ptrArith; auto with ptrArith.
      unfold Int64.zero.
      rewrite Int64.unsigned_repr.
      2:{ set Int64.max_unsigned. vm_compute in z0. nia. }
      rewrite Z.lxor_0_r. et.

    - unfold encrypt_hoare3 in *. des_ifs. ss.
      iDestruct "PRE" as "[[% ALIVE] %]".
      clarify. hred_r. unhide. remove_tau. unhide. remove_tau. 
      des_ifs. hred_r. rewrite <- Heq.

      iApply isim_apc. iExists (Some (2%nat : Ord.t)).
      iApply isim_ccallU_capture1; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src1 st_tgt1) "INV".

      hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.
      iPoseProof (liveness_ptr with "ALIVE") as "%".
      unfold cast_to_ptr in H3. des_ifs_safe. rewrite H3. hred_r.

      iApply isim_ccallU_capture2; ss; oauto.
      iSplitL "INV ALIVE"; iFrame.
      iIntros (st_src0 st_tgt0 i0) "[INV [ALIVE CAP]]".

      hred_r. remove_tau. unhide. remove_tau. des_ifs_safe.
      hred_r. hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iSplits; ss.
      iFrame. iPureIntro. f_equal. unfold Vnullptr in Heq2.
      autounfold with ptrArith in *. des_ifs_safe.
  Qed. *)
  Admitted.


  Lemma sim_decrypt :
    sim_fnsem wf top2
      ("decrypt", fun_to_tgt "xorlist" (GlobalStb (Sk.canon sk)) (mk_pure decrypt_spec))
      ("decrypt", cfunU (decomp_func (Sk.canon sk) ce f_decrypt)).
  Proof.
    (* econs; ss. red.

    unfold prog in ce. unfold mkprogram in ce.
    destruct (build_composite_env').
    get_composite ce e.

    apply isim_fun_to_tgt; auto. i; ss.
    unfold decomp_func, function_entry_c. ss.
    init_hide.

    iIntros "[INV PRE]".
    destruct x as [?|?]; ss.
    - unfold decrypt_hoare1 in *. des_ifs_safe. ss.
      iDestruct "PRE" as "[PRE %]".
      iDestruct "PRE" as (key) "[% ALIVE]". des. clarify.
      hred_r. unhide. remove_tau. unhide. remove_tau.
      iPoseProof (liveness_ptr with "ALIVE") as "%".
      unfold cast_to_ptr in H3. rewrite H3. hred_r.

      iApply isim_apc. iExists (Some (1%nat : Ord.t)).
      iApply isim_ccallU_capture2; ss; oauto.
      iSplitL "INV ALIVE"; iFrame.
      iIntros (st_src0 st_tgt0 i0) "[INV [ALIVE CAP]]".

      hred_r. remove_tau. unhide. remove_tau. des_ifs_safe.
      hred_r. hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret.
      iFrame. iSplit; ss. iExists _. iFrame.
      iPureIntro. f_equal.
      autounfold with ptrArith in *. des_ifs_safe.
      f_equal. unfold Ptrofs.xor.
      autorewrite with ptrArith; auto with ptrArith.
      apply lxor_size; auto with ptrArith.

    - iDestruct "PRE" as "[PRE %]".
      iDestruct "PRE" as (key) "%". des. clarify.
      hred_r. unhide. remove_tau. unhide. remove_tau.
      des_ifs. hred_r. rewrite <- Heq.

      iApply isim_apc. iExists (Some (1%nat : Ord.t)).
      iApply isim_ccallU_capture1; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src0 st_tgt0) "INV".

      hred_r. remove_tau. unhide. remove_tau.
      des_ifs_safe. hred_r.
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret.
      iFrame. iSplit; ss.
      iPureIntro. f_equal.
      autounfold with ptrArith in *. des_ifs_safe.
      f_equal. unfold Vnullptr in *. unfold Ptrofs.xor.
      des_ifs_safe.
      autorewrite with ptrArith; auto with ptrArith.
      unfold Int64.zero. autorewrite with ptrArith.
      2:{ set Int64.max_unsigned. vm_compute in z. nia. }
      rewrite Z.lxor_0_r. et.
  Qed. *)
  Admitted.

  Require Import ClightDmExprgen.



  Lemma sim_add :
    sim_fnsem wf top2
      ("add", fun_to_tgt "xorlist" (GlobalStb (Sk.canon sk)) (mk_pure add_spec))
      ("add", cfunU (decomp_func (Sk.canon sk) ce f_add)).
  Proof.
    (* econs; ss. red.

    unfold prog in ce. unfold mkprogram in ce.
    destruct (build_composite_env').
    get_composite ce e.

    apply isim_fun_to_tgt; auto. i; ss.
    unfold decomp_func, function_entry_c. ss.
    init_hide.

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[PRE %]".
    iDestruct "PRE" as (hd_old tl_old) "[[[% HD] TL] LIST]".
    ss. clarify. ss. hred_r. unhide. remove_tau. unhide.
    remove_tau. unhide.

    des_ifs_safe. remove_tau.

    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply Sk.incl_incl_env in SKINCLENV.
    unfold Sk.incl_env in SKINCLENV.
    hexploit SKINCLENV.
    { instantiate (2:="malloc"). ss. }
    i. des. ss. rewrite FIND. hred_r. des_ifs_safe. hred_r. *)

    (* des_ifs. hred_r.
    replace (pred _) with blk by nia.
    erewrite sk_incl_gd; et. hred_r.
    rewrite <- Heq3.
    iApply isim_apc. iExists (Some (10%nat : Ord.t)).
    iApply isim_ccallU_malloc; ss; oauto.
    iSplitL "INV"; iFrame.
    { rewrite co_co_sizeof. ss. }
    iIntros (st_src0 st_tgt0 vaddr m1) "[INV [[% PTO] ALIVE]]".
    rewrite co_co_sizeof in *.
    autorewrite with ptrArith in *.
    2,3: set Ptrofs.max_unsigned; vm_compute in z; nia.

    hred_r. remove_tau. unhide. remove_tau.
    iPoseProof (liveness_ptr with "ALIVE") as "%".
    unfold cast_to_ptr in H4. des_ifs_safe.
    rewrite H4. hred_r. remove_tau. unhide.
    remove_tau. unhide. remove_tau. 

    iPoseProof (points_to_is_ptr with "HD") as "%".
    rewrite H5. hred_r.

    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV HD"; iFrame.
    { rewrite encode_val_length. et. }
    iIntros (st_src1 st_tgt1) "[INV HD]".

    hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.
    iPoseProof (points_to_is_ptr with "TL") as "%".
    rewrite H6. hred_r.

    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV TL"; iFrame.
    { rewrite encode_val_length. et. }
    iIntros (st_src2 st_tgt2) "[INV TL]".

    hred_r. remove_tau. unhide. remove_tau. unhide.
    remove_tau.
    iPoseProof (points_to_is_ptr with "PTO") as "%".

    rewrite H7. hred_r.
    rewrite H7. hred_r.
    rewrite co_co_members. ss. des_ifs_safe. hred_r.
    set (Coqlib.align _ _). vm_compute in z.
    unfold z. clearbody z.

    set (Undef :: _) as ls.
    replace ls with ([] ++ ls) by et.
    assert (H': (size_rule (strings.length ls) | (Z.of_nat (strings.length (@nil memval))))%Z).
    { red. ss. exists 0. ss. }
    iPoseProof ((points_to_split _ _ _ _ _ H') with "PTO") as "[UNIT PTO]".
    ss.
    replace ls with (List.repeat Undef 8 ++ List.repeat Undef 8) by et.
    assert (H'': (size_rule (strings.length (List.repeat Undef 8)) | (Z.of_nat (strings.length (List.repeat Undef 8))))%Z).
    { red. ss. exists 1. ss. }
    iPoseProof ((points_to_split _ _ _ _ _ H'') with "PTO") as "[PTO_item PTO_key]".
    ss.
    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV PTO_item"; iFrame.
    { iExists _. iFrame. ss. }
    iIntros (st_src3 st_tgt3) "[INV PTO_item]".

    hred_r. remove_tau. unhide.
    remove_tau. des_ifs_safe. hred_r.

    destruct l.
    (* case: nil list *)
    - unfold full_xorlist, frag_xorlist at 1.
      iDestruct "LIST" as "%". des. clarify.
      pose proof (decode_encode_val_general Vnullptr Mptr Mptr).
      unfold decode_encode_val in H8.
      des_ifs_safe. rewrite H8. rewrite <- Heq4.
      replace (Vlong (Int64.repr _)) with Vnullptr.
      2:{ unfold Vnullptr. des_ifs. }

      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src4 st_tgt4) "INV".

      hred_r. des_ifs_safe. unhide. remove_tau.
      unhide. remove_tau.
      rewrite H7. hred_r.
      rewrite H7. hred_r.
      rewrite co_co_members. ss. des_ifs_safe.
      rewrite Val.addl_assoc.
      hred_r.
      replace (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)) by et.
      replace (Val.addl (Vptrofs _) (Vptrofs _)) with (Vptrofs (Ptrofs.repr 8)) by et.
      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV PTO_key"; iFrame.
      { iExists _. iFrame. ss. }
      iIntros (st_src5 st_tgt5) "[INV PTO_key]".

      hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau. unhide.
      remove_tau. rewrite H4. hred_r. remove_tau. unhide.
      remove_tau. rewrite H6. hred_r.
      des_ifs_safe. rewrite H4. hred_r.

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV TL"; iFrame.
      { iExists _. iFrame. ss. }
      iIntros (st_src6 st_tgt6) "[INV TL]".

      hred_r. remove_tau. unhide.
      remove_tau. rewrite H5. hred_r.
      des_ifs_safe. rewrite H4. hred_r.

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV HD"; iFrame.
      { iExists _. iFrame. ss. }
      iIntros (st_src7 st_tgt7) "[INV HD]".

      hred_r. remove_tau. hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret.
      iFrame. iSplit; ss. iExists _, _. iFrame. iSplit; ss.
      unfold vlist_add. destruct (Val.eq _ _); ss.
      + destruct Val.eq; clarify. iExists _, _, _, _, _, _. iFrame. iSplit; ss. 
      ss. *)
  Admitted.

  Lemma sim_search :
    sim_fnsem wf top2
      ("search", fun_to_tgt "xorlist" (GlobalStb (Sk.canon sk)) (mk_pure search_spec))
      ("search", cfunU (decomp_func (Sk.canon sk) ce f_search)).
  Proof.
  Admitted.

  End SIMFUNS.

  Opaque Sk.canon.

  Theorem correct : refines2 [xorlist0.xor] [xorlist1.xor GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf := wf) (le := top2); et; ss; cycle 1.
    { eexists. econs. apply to_semantic. iIntros. et. }
    (* each functions has simulation relation *)
    econs; cycle 1.
    econs; cycle 1.
    econs; cycle 1.
    econs; cycle 1.
    econs; et.
    all: rewrite f_bind_ret_r; unfold get_ce; replace (map _ _) with ce by et.
    - apply sim_search; et.
    - apply sim_delete; et.
    - apply sim_add; et.
    - apply sim_decrypt; et.
    - apply sim_encrypt; et.
    Unshelve. exact tt.
  Qed.

End PROOF.

