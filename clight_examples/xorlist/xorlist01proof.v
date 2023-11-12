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
From compcertip Require Import Clightdefs.

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
    iDestruct "PRE" as "[PRE %]".
    iDestruct "PRE" as (hd_old tl_old ofs_hd_old ofs_tl_old)
      "[[[[[% hd_handler_point] tl_handler_point] hd_handler_ofs] tl_handler_ofs] LIST]".
    des. clarify. ss. clarify. ss. hred_r.
    unhide. remove_tau. unhide. remove_tau. unhide.
    rename i into from_tail. rename v into hd_handler.
    rename v0 into tl_handler. rename m into md_tl.
    rename m0 into md_hd. rename v1 into vreturn.
    rename l into linput. rename l0 into lreturn.
    rename Heq into del_spc. rename H5 into ofs_hd_old_al.
    rename H6 into ofs_tl_old_al.

    des_ifs_safe. hred_r. rename Heq into ptr64.
    iPoseProof (points_to_is_ptr with "hd_handler_point") as "%".
    rewrite H3. rename H3 into hd_handler_ptr.
    iPoseProof (offset_dup with "hd_handler_ofs") as "[hd_handler_ofs hd_handler_ofs']".
    hred_r.
    iApply isim_apc. iExists (Some (20%nat : Ord.t)).
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_handler_point hd_handler_ofs'"; iFrame.
    { iExists _. iFrame. iPureIntro. rewrite encode_val_length. et. }
    iIntros (st_src0 st_tgt0) "[INV hd_handler_point]".

    hred_r. replace (Vlong _) with Vnullptr by et.
    destruct linput.
    (* case: nil list *)
    - unfold vlist_delete in del_spc. ss.
      unfold full_xorlist, frag_xorlist at 1.
      iDestruct "LIST" as "%". des. clarify.
      unfold Mptr. rewrite ptr64.
      rewrite decode_encode_null.
      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src1 st_tgt1) "INV".

      hred_r. destruct (Int.eq) eqn:?; ss; clarify. clear Heqb.
      unhide. remove_tau. unhide. remove_tau.
      hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret.
      iFrame. iSplit; ss.
      destruct (Val.eq) in del_spc; ss; clarify; ss.
      + iExists _,_,_,_,_,_. iFrame.
        iSplit; ss. iSplitL. iSplitL.
        { iPureIntro. clarify. }
        all: iLeft; iPureIntro; et.
      + iExists _,_,_,_,_,_. iFrame.
        iSplit; ss. iSplitL. iSplitL.
        { iPureIntro. clarify. }
        all: iLeft; iPureIntro; et.
    (* case: not nil list *)
    - unfold full_xorlist. rewrite unfold_frag_xorlist.
      rename linput into lnext.
      destruct v; try solve [iDestruct "LIST" as "%"; clarify].
      rename i into hd_long.
      destruct (Val.eq) eqn: ?; ss; clarify. clear e Heqs.
      iDestruct "LIST" as (p_next m_hd i_next)
       "[[[[[hd_point hd_ofs] hd_liv] %] next_info] LIST]".
      rename H3 into m_hd_size.
      iPoseProof (decode_encode_ptr with "hd_ofs") as "%".
      rewrite H3. rename H3 into hd_old_ptr.
      iApply isim_ccallU_cmp_ptr1; ss; oauto.
      iPoseProof (offset_dup with "hd_ofs") as "[hd_ofs hd_ofs']".
      iSplitL "INV hd_liv hd_ofs'"; iFrame.
      { iPureIntro. rewrite m_hd_size. vm_compute (size_chunk Mptr). nia. }
      iIntros (st_src1 st_tgt1) "INV".
      iDestruct "INV" as "[INV hd_liv]".

      hred_r. destruct (Int.eq) eqn: ?; ss; clarify. clear Heqb.
      unhide. remove_tau.
      destruct (Int.eq from_tail Int.zero) eqn:?.
      (* case: not nil list && delete from head *)
      + pose proof (Int.eq_spec from_tail Int.zero). rewrite Heqb in H3.
        clear Heqb. clarify. unfold vlist_delete in del_spc.
        destruct Val.eq eqn:? in del_spc; ss; clarify. clear Heqs e.
        unhide. remove_tau. unhide. remove_tau.
        rewrite hd_handler_ptr. hred_r. 
        iApply isim_ccallU_load; ss; oauto.
        iPoseProof (offset_dup with "hd_handler_ofs") as "[hd_handler_ofs hd_handler_ofs']".
        iSplitL "INV hd_handler_point hd_handler_ofs"; iFrame.
        { iExists _. iFrame. iPureIntro. rewrite encode_val_length. et. }
        iIntros (st_src2 st_tgt2) "[INV hd_handler_point]".
        remove_tau. unhide. remove_tau. unhide. remove_tau.

        rewrite hd_old_ptr.
        iPoseProof (points_to_is_ptr with "hd_point") as "%".
        rewrite H3. rename H3 into hd_real_ptr.
        hred_r. rewrite hd_real_ptr. hred_r. rewrite get_co.
        hred_r. rewrite co_co_members. ss. hred_r.
        iPoseProof (points_to_split with "hd_point")
          as "[hd_point_item hd_point_key]".
        iPoseProof (offset_dup with "hd_ofs") as "[hd_ofs hd_ofs']".
        iApply isim_ccallU_load; ss; oauto.
        iSplitL "INV hd_point_item hd_ofs'"; iFrame.
        { replace (Coqlib.align 0 _) with 0%Z by et.
          replace (Val.addl _ _) with hd_old by admit "".
          iExists _. iFrame. iPureIntro. split; et.
          exists 0. ss. }
        iIntros (st_src3 st_tgt3) "[INV hd_point_item]".
        replace (Coqlib.align 0 _) with 0%Z by et.
        replace (Val.addl _ (Vptrofs (Ptrofs.repr 0))) with hd_old by admit "".

        hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.
        unhide. remove_tau. 
        hexploit SKINCLENV.
        { instantiate (2:="decrypt"). ss. }
        i. des. ss. rewrite FIND. rename FIND into decrypt_loc.
        hred_r. rewrite hd_real_ptr. hred_r. rewrite hd_real_ptr. hred_r.
        rewrite get_co. hred_r.
        rewrite co_co_members. ss. hred_r.
        replace (Coqlib.align _ _) with 8%Z by et.

        iApply isim_ccallU_load; ss; oauto.
        iPoseProof (offset_dup with "hd_ofs") as "[hd_ofs hd_ofs']".
        iSplitL "INV hd_point_key hd_ofs'"; iFrame.
        { iExists _. iSplitL "hd_ofs'".
          { iApply offset_slide; et. rewrite m_hd_size.
            vm_compute (size_chunk Mptr). nia. }
          iPureIntro. unfold Mptr, Vptrofs. rewrite ptr64.
          rewrite encode_val_length.
          split; et. exists 1. nia. }
        iIntros (st_src4 st_tgt4) "[INV hd_point_key]".

        hred_r. unfold Mptr at 8 9. rewrite ptr64.
        rewrite decode_encode_ofs. des_ifs_safe.
        clear e. rewrite <- Heq. clear Heq. clear i. hred_r.
        replace (pred _) with blk by nia.
        erewrite SKINCLGD; et.
        hred_r. ss.

        iApply isim_ccallU_pure; et.
        { eapply fn_has_spec_in_stb; et.
          { eapply STBINCL. stb_tac. unfold xorStb.
            unseal "stb". ss. }
          { ss. instantiate(1:=inr _). ss. oauto. }
          { ss. } }
        
        { instantiate (1:=14). oauto. }

        ss. iSplitL "INV"; iFrame.
        { iSplit; ss. iExists _. iPureIntro. split; ss. }
        iIntros (st_src5 st_tgt5 ret_src ret_tgt) "[INV [% %]]".
        rewrite H3. clear H3. iExists _. iSplit; ss. clarify.

        hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
        rewrite hd_handler_ptr. hred_r. des_ifs_safe. rewrite <- Heq.
        clear Heq i. hred_r.

        iApply isim_ccallU_store; ss; oauto.
        iPoseProof (offset_dup with "hd_handler_ofs'") as "[hd_handler_ofs hd_handler_ofs']".
        iSplitL "INV hd_handler_point hd_handler_ofs'"; iFrame.
        { iExists _,_. iFrame. iPureIntro. split; et.
          rewrite encode_val_length. ss. }
        iIntros (st_src6 st_tgt6) "[INV hd_handler_point]".

        hred_r. unhide. remove_tau. unhide. remove_tau.
        replace (Vlong (Int64.repr _)) with Vnullptr by et.
        destruct lreturn.
        (* case: singleton list && delete from head *)
        * ss. iDestruct "LIST" as "%". des. clarify.
          destruct (i_next =? 0)%Z eqn: X; cycle 1.
          { iDestruct "next_info" as (m_next) "next_capture".
            iPoseProof (captured_pointer_notnull with "next_capture") as "%".
            clarify. }
          apply Z.eqb_eq in X. rewrite X. clear X i_next.
          replace (Vptrofs (Ptrofs.repr 0)) with Vnullptr by et.
          iApply isim_ccallU_cmp_ptr0; ss; oauto.
          iSplitL "INV"; iFrame.
          iIntros (st_src7 st_tgt7) "INV".
          
          hred_r. des_ifs_safe. clear Heq.
          unhide. remove_tau.
          iPoseProof (points_to_is_ptr with "tl_handler_point") as "%".
          rewrite H3. rename H3 into tl_handler_ptr. hred_r.
          replace (Vlong (Int64.repr _)) with Vnullptr by et.

          iApply isim_ccallU_store; ss; oauto.
          iPoseProof (offset_dup with "tl_handler_ofs") as "[tl_handler_ofs tl_handler_ofs']".
          iSplitL "INV tl_handler_point tl_handler_ofs"; iFrame.
          { iExists _,_. iFrame. iPureIntro. split; et.
            rewrite encode_val_length. ss. }
          iIntros (st_src8 st_tgt8) "[INV tl_handler_point]".

          hred_r. unhide. remove_tau.
          hexploit SKINCLENV.
          { instantiate (2:="free"). ss. }
          i. des. ss. rewrite FIND. rename FIND into free_loc. hred_r.

          iPoseProof (liveness_ptr with "hd_ofs") as "%".
          unfold cast_to_ptr in H3. rewrite ptr64 in H3.
          rewrite H3. rename H3 into hd_old_cast. hred_r.
          des_ifs_safe.
          replace (pred _) with blk0 by nia.
          erewrite SKINCLGD; et. hred_r. ss.
          iCombine "hd_point_item hd_point_key" as "hd_point".
          replace (Val.addl tl_old (Vlong _)) 
            with (Val.addl tl_old (Vptrofs (Ptrofs.repr (strings.length (inj_bytes (encode_int 8 (Int64.unsigned hd_long))))))) by et.
          iPoseProof (points_to_collect with "hd_point") as "hd_point".
          iApply isim_ccallU_mfree; ss; oauto.
          iSplitL "INV hd_point hd_liv hd_ofs".
          { iFrame. iExists _,_. iFrame.
            iPureIntro. ss. }
          iIntros (st_src9 st_tgt9) "INV".

          hred_r. unhide. remove_tau.
          pose proof (decode_encode_val_general (Vlong hd_long) Mint64 Mint64).
          unfold decode_encode_val in H3. rewrite H3. clear e H3.
          
          hred_r. hred_l. iApply isim_choose_src. iExists _.
          iApply isim_ret. iFrame. iSplit; ss.
          iExists _,_,_,_,_,_. iFrame; ss. 
          iSplit; ss. iSplitL.
          { iPureIntro. clarify. }
          unfold null_or_int. iLeft. iPureIntro. et.
        (* case: list length with more than 1 && delete from head *)
        * ss. destruct v; try solve [iDestruct "LIST" as "%"; clarify].
          iPoseProof (has_offset_notnull with "hd_ofs") as "%".
          destruct (Val.eq _ hd_old) eqn: ?; clarify. clear H3 n Heqs.
          iDestruct "LIST" as (p_new m_hd' m_new i_hd i_key)
            "[[[[[[new_point new_ofs] new_liv] %] hd_addr] next_next_info] LIST]".
          rename i into next_long. rename H3 into m_new_size.

          iPoseProof (has_offset_notnull with "new_ofs") as "%".
          destruct (i_next =? 0)%Z.
          { iDestruct "next_info" as "%". clarify. }
          iDestruct "next_info" as (m_next) "next_info".

          iCombine "new_point next_info" as "next".
          iPoseProof (replace_meta_to_alive with "next") as "[new_point new_addr]".
          iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr']".
          iPoseProof (capture_offset_comm with "new_addr'") as "comm".
          iPoseProof ("comm" with "new_ofs") as "new_ofs".
          iPoseProof (offset_dup with "new_ofs") as "[new_ofs new_ofs']".
          clear H3.

          iApply isim_ccallU_cmp_ptr3; ss; oauto.
          iSplitL "INV new_ofs' new_liv".
          { iFrame. rewrite m_new_size. vm_compute (size_chunk Mptr). iPureIntro. nia. }
          iIntros (st_src7 st_tgt7) "[INV new_liv]".
          
          hred_r. des_ifs_safe. clear e Heq.
          unhide. hred_r. unhide. remove_tau.
          unhide. remove_tau.
          rewrite decrypt_loc. hred_r. des_ifs_safe. hred_r. rewrite Heq. clear Heq.
          hred_r. rewrite get_co. hred_r. rewrite co_co_members.
          ss. hred_r.
          replace (Coqlib.align _ _) with 8%Z by et.

          iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr']".
          iPoseProof (capture_pointto_comm with "new_addr'") as "comm".
          iPoseProof ("comm" with "new_point") as "new_point".
          iPoseProof (points_to_split with "new_point") as "[new_point_item new_point_key]".
          iPoseProof (offset_dup with "new_ofs") as "[new_ofs new_ofs']".

          iApply isim_ccallU_load; ss; oauto.
          iSplitL "INV new_point_key new_ofs'"; iFrame.
          { iExists _. rewrite encode_val_length.
            iSplitL "new_ofs'"; cycle 1.
            { iPureIntro. instantiate (1:= (0 + 8)%Z). split; et. exists 1. et. }
            iApply offset_slide; try iFrame. rewrite m_new_size.
            vm_compute (size_chunk Mptr). nia. }
          iIntros (st_src8 st_tgt8) "[INV new_point_key]".
          unfold Mptr at 11. rewrite ptr64. rewrite decode_encode_ofs.
          hred_r. clear e.
          iPoseProof (liveness_ptr with "hd_ofs") as "%".
          unfold cast_to_ptr in H3. rewrite ptr64 in H3.
          rewrite H3. rename H3 into hd_old_cast. hred_r. des_ifs_safe.
          rewrite <- Heq. clear Heq i.
          hred_r.

          replace (pred _) with blk by nia.
          erewrite SKINCLGD; et.
          hred_r. ss.

          iApply isim_ccallU_pure; et.
          { eapply fn_has_spec_in_stb; et.
            { eapply STBINCL. stb_tac. unfold xorStb.
              unseal "stb". ss. }
            { ss. instantiate (1:=inl (Ptrofs.repr i_key, hd_old, m_hd, 1%Qp, Dynamic)).
              ss. oauto. }
            { ss. } }
          { instantiate (1:=10). oauto. }
          iPoseProof (offset_dup with "hd_ofs") as "[hd_ofs hd_ofs']".
          ss. iSplitL "INV hd_ofs' hd_liv"; iFrame.
          { iSplit; ss. iExists _,_. iSplit; ss. }
          iIntros (st_src9 st_tgt9 ret_src ret_tgt0) "[INV [POST %]]".
          iDestruct "POST" as (i_ptr) "[[% hd_addr'] hd_liv]".
          rewrite H4. iExists _. iSplit; ss. clear H4 H3.
          iCombine "hd_point_item hd_addr" as "hd".
          iPoseProof (replace_meta_to_alive with "hd") as "[hd_point_item hd_addr]".
          iCombine "hd_addr' hd_addr" as "hd_addr".
          iPoseProof (capture_unique with "hd_addr") as "%".
          clarify. iDestruct "hd_addr" as "[_ hd_addr]".

          hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.

          hexploit SKINCLENV.
          { instantiate (2:="encrypt"). ss. }
          i. des. ss. rewrite FIND. rename FIND into encrypt_loc.
          hred_r. des_ifs_safe. rewrite <- Heq. clear Heq i e. hred_r.
          replace (pred _) with blk0 by nia.
          erewrite SKINCLGD; et. hred_r. ss.
          change (Vlong (Int64.repr _)) with Vnullptr.
          destruct (Z.lxor i_hd i_key =? 0)%Z eqn:?.
          (* case: decrypt value is zero *)
          ** iDestruct "next_next_info" as "%". clarify.
             apply Z.eqb_eq in Heqb. apply Z.lxor_eq in Heqb.
             clarify. rewrite Ptrofs.xor_idem.
             change (Vptrofs Ptrofs.zero) with Vnullptr.
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
             hred_r. unhide. remove_tau. des_ifs_safe. hred_r. rewrite Heq.
             clear Heq. hred_r. rewrite get_co. hred_r. rewrite co_co_members.
             ss. hred_r. destruct Vnullptr eqn:?; clarify. rewrite <- Heqv.
             clear Heqv i. 
             replace (Coqlib.align _ _) with 8%Z by et. hred_r.
             iApply isim_ccallU_store; ss; oauto.
             iPoseProof (offset_dup with "new_ofs") as "[new_ofs new_ofs']".
             iSplitL "INV new_point_key new_ofs"; iFrame.
             { iExists _,_. iFrame. rewrite encode_val_length. 
               iSplitR "new_ofs".
               { iPureIntro. instantiate (1:=(0+8)%Z). split; et. exists 1. et. }
               iApply offset_slide; et. rewrite m_new_size. vm_compute (size_chunk Mptr).
               nia. }
             iIntros (st_src11 st_tgt11) "[INV next_point_key]".
             hred_r. unhide. remove_tau.
             hexploit SKINCLENV.
             { instantiate (2:="free"). ss. }
             i. des. ss. rewrite FIND. rename FIND into free_loc. hred_r. 
             rewrite hd_old_cast. hred_r.
             destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
             replace (pred _) with blk1 by nia.
             erewrite SKINCLGD; et. hred_r.
             iCombine "hd_point_item hd_point_key" as "hd_point".
             change (Val.addl tl_old (Vptrofs _)) 
               with (Val.addl tl_old (Vptrofs (Ptrofs.repr (strings.length (encode_val Mint64 (Vlong hd_long)))))).
             iPoseProof (points_to_collect with "hd_point") as "hd_point".
             iApply isim_ccallU_mfree; ss; oauto.
             iSplitL "INV hd_point hd_liv hd_ofs".
             { iFrame. iExists _,_. iFrame. iPureIntro. ss. }
             iIntros (st_src12 st_tgt12) "INV".

             hred_r. unhide. remove_tau.
             pose proof (decode_encode_val_general (Vlong hd_long) Mint64 Mint64).
             unfold decode_encode_val in H3. rewrite H3. clear H3.

             hred_r. hred_l. iApply isim_choose_src. iExists _.
             iApply isim_ret. iFrame.
             iCombine "new_point_item next_point_key" as "new_point".
             change 8%Z with (Z.of_nat (strings.length (encode_val Mint64 (Vlong next_long)))).
             iPoseProof (points_to_collect with "new_point") as "new_point". 
             iSplit; ss. 
             rewrite unfold_frag_xorlist.
             destruct lreturn; cycle 1.
             { destruct (Val.eq Vnullptr p_next) eqn:?.
               - iPoseProof (captured_pointer_notnull with "new_addr") as "%".
                 clarify.
               - destruct v; try solve [iDestruct "LIST" as "%"; clarify].
                 iDestruct "LIST" as (? ? ? ? ?)
                  "[[[[[[a b] c] d] e] f] LIST]".
                 iPoseProof (points_to_notnull with "a") as "%".
                 clarify. }
             ss. iDestruct "LIST" as "%".
             des. clarify. clear H4.
             iPoseProof (captured_address_not_zero with "new_addr") as "%".
             iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr']".
             iPoseProof (capture_pointto_comm with "new_addr'") as "comm".
             iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr']".
             iPoseProof (capture_offset_comm with "new_addr'") as "comm'".
             iPoseProof ("comm" with "new_point") as "new_point".
             iPoseProof ("comm'" with "new_ofs'") as "new_ofs".
             ss. iExists _,_,tl_old,tl_old,_,_.
             iSplitL "hd_handler_point tl_handler_point hd_handler_ofs tl_handler_ofs new_addr".
             { iFrame. iSplitL. iSplitR "new_addr".
               { iPureIntro. clarify. }
               { unfold null_or_int. iRight.
                 iExists _. iSplit; ss. iExists _. iFrame. }
               { unfold null_or_int. iLeft. ss. } }
             { iExists _,_,_. iFrame. instantiate (2:=0%Z).
               change (Vptrofs (Ptrofs.repr 0)) with Vnullptr.
               iFrame. simpl. rewrite m_new_size. ss. }
          (* case: decrypt value is not zero *)
          ** iDestruct "next_next_info" as (m_next_next) "next_next_info".
             destruct lreturn.
             { ss. iDestruct "LIST" as "%". des. clarify.
               iPoseProof (captured_pointer_notnull with "next_next_info") as "%".
               clarify. }
             ss. destruct v; try solve [iDestruct "LIST" as "%"; clarify].
             rename i into next_next_long.
             iPoseProof (captured_pointer_notnull with "new_addr") as "%".
             destruct Val.eq; clarify.
             iDestruct "LIST" as (p_next_next_next m_new' m_next_next' i_next' i_key_next)
              "[[[[[[new_next_point new_next_ofs] new_next_liv] %] new_addr'] n3_info] LIST]".
             iCombine "new_next_point next_next_info" as "n2".
             iPoseProof (replace_meta_to_alive with "n2") as "[new_next_point new_next_addr]".
             iApply isim_ccallU_pure; et.
             { eapply fn_has_spec_in_stb; et.
               { eapply STBINCL. stb_tac. unfold xorStb.
                 unseal "stb". ss. }
               { ss. et. instantiate (1:=inr (inr (inl (_,_,_,_)))).
                 ss. oauto. }
               { ss. } }
             { instantiate (1:=9). oauto. }
             ss.
             iPoseProof (offset_dup with "new_next_ofs") as "[new_next_ofs' new_next_ofs]".
             iPoseProof (capture_dup with "new_next_addr") as "[new_next_addr' new_next_addr]".
             iPoseProof (capture_offset_comm with "new_next_addr'") as "comm".
             iPoseProof ("comm" with "new_next_ofs'") as "new_next_ofs'".
             iSplitL "INV new_next_liv new_next_ofs'"; iFrame.
             { iSplit; ss. iExists _. iSplit; ss.
               instantiate (1:=0%Z).
               replace (Vptrofs (Ptrofs.xor _ _))
                with (Vptrofs (Ptrofs.repr (Z.lxor i_hd i_key))) by admit "".
               iApply "new_next_ofs'". }
             iIntros (st_src10 st_tgt10 ret_src0 ret_tgt1) "[INV [POST %]]".
             iDestruct "POST" as (i_keyhd) "[[% new_next_addr_store] new_next_liv]".
             rewrite H6. clear H6 H5. iExists _. iSplit; ss.

             hred_r. unhide. remove_tau.
             des_ifs_safe. hred_r. rewrite Heq. clear Heq.
             hred_r. rewrite get_co. hred_r. rewrite co_co_members.
             ss. hred_r. des_ifs_safe. rewrite <- Heq. clear Heq i.
             hred_r.
             change (Coqlib.align _ _) with 8%Z.
             iApply isim_ccallU_store; ss; oauto.
             iPoseProof (offset_dup with "new_ofs") as "[new_ofs new_ofs']".
             iSplitL "INV new_point_key new_ofs"; iFrame.
             { iExists _,_. iFrame. rewrite encode_val_length. 
               iSplitR "new_ofs".
               { iPureIntro. instantiate (1:=(0+8)%Z). split; et. exists 1. et. }
               iApply offset_slide; et. rewrite m_new_size. vm_compute (size_chunk Mptr).
               nia. }
             iIntros (st_src11 st_tgt11) "[INV next_point_key]".

             hred_r. unhide. remove_tau.
             hexploit SKINCLENV.
             { instantiate (2:="free"). ss. }
             i. des. ss. rewrite FIND. rename FIND into free_loc. hred_r. 
             rewrite hd_old_cast. hred_r.
             destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
             replace (pred _) with blk1 by nia.
             erewrite SKINCLGD; et. hred_r.
             iCombine "hd_point_item hd_point_key" as "hd_point".
             change (Val.addl tl_old (Vptrofs _)) 
               with (Val.addl tl_old (Vptrofs (Ptrofs.repr (strings.length (encode_val Mint64 (Vlong hd_long)))))).
             iPoseProof (points_to_collect with "hd_point") as "hd_point".
             iApply isim_ccallU_mfree; ss; oauto.
             iSplitL "INV hd_point hd_liv hd_ofs".
             { iFrame. iExists _,_. iFrame. iPureIntro. ss. }
             iIntros (st_src12 st_tgt12) "INV".

             hred_r. unhide. remove_tau.
             pose proof (decode_encode_val_general (Vlong hd_long) Mint64 Mint64).
             unfold decode_encode_val in H5. rewrite H5. clear H5.

             hred_r. hred_l. iApply isim_choose_src. iExists _.
             iApply isim_ret. iFrame.
             iCombine "new_point_item next_point_key" as "new_point".
             change 8%Z with (Z.of_nat (strings.length (encode_val Mint64 (Vlong next_long)))).
             iPoseProof (points_to_collect with "new_point") as "new_point".
             iSplit; ss. 

             iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr_rep]".
             iPoseProof (capture_pointto_comm with "new_addr_rep") as "comm".
             iPoseProof ("comm" with "new_point") as "new_point".
             iCombine "new_point new_addr'" as "new".
             iPoseProof (replace_meta_to_alive with "new") as "[new_point new_addr']".
             iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr_rep]".
             iPoseProof (capture_pointto_comm with "new_addr_rep") as "comm".
             iPoseProof ("comm" with "new_point") as "new_point".
             iCombine "new_addr new_addr'" as "new".
             iPoseProof (capture_unique with "new") as "%".
             iDestruct "new" as "[_ new_addr]".
             clarify.
             iExists _,_,_,_,_,_. iFrame.
             instantiate(1:=tl_old).
             iSplitL "".
             { iSplitL. iSplitL. iSplit; ss.
               { unfold null_or_int. iLeft. iPureIntro. ss. }
               { unfold null_or_int. iLeft. iPureIntro. ss. } }
             iExists p_new,_,_. iFrame.
             rewrite m_new_size. iSplitL "new_next_addr new_next_addr_store".
             { iSplit; ss.
               iPoseProof (captured_address_not_zero with "new_next_addr_store") as "%".
               destruct (i_keyhd =? 0)%Z eqn: ?.
               { apply Z.eqb_eq in Heqb0. exfalso. clarify. }
               { admit "capture_trans". } }
             iPoseProof (captured_address_not_zero with "new_addr") as "%".
             destruct Val.eq.
             { rewrite e in H5. clarify. }
             iExists _,_,_,_,_. iFrame.
             rewrite H4. iSplit; ss. admit "capture_refl".
      + pose proof (Int.eq_spec from_tail Int.zero). rewrite Heqb in H3.
        clear Heqb. clarify. unfold vlist_delete in del_spc.
        destruct Val.eq eqn:? in del_spc; ss; clarify. clear Heqs e.
        unhide. remove_tau. unhide. remove_tau.
        rewrite hd_handler_ptr. hred_r. 
        iApply isim_ccallU_load; ss; oauto.
        iPoseProof (offset_dup with "hd_handler_ofs") as "[hd_handler_ofs hd_handler_ofs']".
        iSplitL "INV hd_handler_point hd_handler_ofs"; iFrame.
        { iExists _. iFrame. iPureIntro. rewrite encode_val_length. et. }
        iIntros (st_src2 st_tgt2) "[INV hd_handler_point]".
        remove_tau. unhide. remove_tau. unhide. remove_tau.

        rewrite hd_old_ptr.
        iPoseProof (points_to_is_ptr with "hd_point") as "%".
        rewrite H3. rename H3 into hd_real_ptr.
        hred_r. rewrite hd_real_ptr. hred_r. rewrite get_co.
        hred_r. rewrite co_co_members. ss. hred_r.
        iPoseProof (points_to_split with "hd_point")
          as "[hd_point_item hd_point_key]".
        iPoseProof (offset_dup with "hd_ofs") as "[hd_ofs hd_ofs']".
        iApply isim_ccallU_load; ss; oauto.
        iSplitL "INV hd_point_item hd_ofs'"; iFrame.
        { replace (Coqlib.align 0 _) with 0%Z by et.
          replace (Val.addl _ _) with hd_old by admit "".
          iExists _. iFrame. iPureIntro. split; et.
          exists 0. ss. }
        iIntros (st_src3 st_tgt3) "[INV hd_point_item]".
        replace (Coqlib.align 0 _) with 0%Z by et.
        replace (Val.addl _ (Vptrofs (Ptrofs.repr 0))) with hd_old by admit "".

        hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.
        unhide. remove_tau. 
        hexploit SKINCLENV.
        { instantiate (2:="decrypt"). ss. }
        i. des. ss. rewrite FIND. rename FIND into decrypt_loc.
        hred_r. rewrite hd_real_ptr. hred_r. rewrite hd_real_ptr. hred_r.
        rewrite get_co. hred_r.
        rewrite co_co_members. ss. hred_r.
        replace (Coqlib.align _ _) with 8%Z by et.

        iApply isim_ccallU_load; ss; oauto.
        iPoseProof (offset_dup with "hd_ofs") as "[hd_ofs hd_ofs']".
        iSplitL "INV hd_point_key hd_ofs'"; iFrame.
        { iExists _. iSplitL "hd_ofs'".
          { iApply offset_slide; et. rewrite m_hd_size.
            vm_compute (size_chunk Mptr). nia. }
          iPureIntro. unfold Mptr, Vptrofs. rewrite ptr64.
          rewrite encode_val_length.
          split; et. exists 1. nia. }
        iIntros (st_src4 st_tgt4) "[INV hd_point_key]".

        hred_r. unfold Mptr at 8 9. rewrite ptr64.
        rewrite decode_encode_ofs. des_ifs_safe.
        clear e. rewrite <- Heq. clear Heq. clear i. hred_r.
        replace (pred _) with blk by nia.
        erewrite SKINCLGD; et.
        hred_r. ss.

        iApply isim_ccallU_pure; et.
        { eapply fn_has_spec_in_stb; et.
          { eapply STBINCL. stb_tac. unfold xorStb.
            unseal "stb". ss. }
          { ss. instantiate(1:=inr _). ss. oauto. }
          { ss. } }
        
        { instantiate (1:=14). oauto. }

        ss. iSplitL "INV"; iFrame.
        { iSplit; ss. iExists _. iPureIntro. split; ss. }
        iIntros (st_src5 st_tgt5 ret_src ret_tgt) "[INV [% %]]".
        rewrite H3. clear H3. iExists _. iSplit; ss. clarify.

        hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.
        rewrite hd_handler_ptr. hred_r. des_ifs_safe. rewrite <- Heq.
        clear Heq i. hred_r.

        iApply isim_ccallU_store; ss; oauto.
        iPoseProof (offset_dup with "hd_handler_ofs'") as "[hd_handler_ofs hd_handler_ofs']".
        iSplitL "INV hd_handler_point hd_handler_ofs'"; iFrame.
        { iExists _,_. iFrame. iPureIntro. split; et.
          rewrite encode_val_length. ss. }
        iIntros (st_src6 st_tgt6) "[INV hd_handler_point]".

        hred_r. unhide. remove_tau. unhide. remove_tau.
        replace (Vlong (Int64.repr _)) with Vnullptr by et.
        destruct lreturn.
        (* case: singleton list && delete from head *)
        * ss. iDestruct "LIST" as "%". des. clarify.
          destruct (i_next =? 0)%Z eqn: X; cycle 1.
          { iDestruct "next_info" as (m_next) "next_capture".
            iPoseProof (captured_pointer_notnull with "next_capture") as "%".
            clarify. }
          apply Z.eqb_eq in X. rewrite X. clear X i_next.
          replace (Vptrofs (Ptrofs.repr 0)) with Vnullptr by et.
          iApply isim_ccallU_cmp_ptr0; ss; oauto.
          iSplitL "INV"; iFrame.
          iIntros (st_src7 st_tgt7) "INV".
          
          hred_r. des_ifs_safe. clear Heq.
          unhide. remove_tau.
          iPoseProof (points_to_is_ptr with "tl_handler_point") as "%".
          rewrite H3. rename H3 into tl_handler_ptr. hred_r.
          replace (Vlong (Int64.repr _)) with Vnullptr by et.

          iApply isim_ccallU_store; ss; oauto.
          iPoseProof (offset_dup with "tl_handler_ofs") as "[tl_handler_ofs tl_handler_ofs']".
          iSplitL "INV tl_handler_point tl_handler_ofs"; iFrame.
          { iExists _,_. iFrame. iPureIntro. split; et.
            rewrite encode_val_length. ss. }
          iIntros (st_src8 st_tgt8) "[INV tl_handler_point]".

          hred_r. unhide. remove_tau.
          hexploit SKINCLENV.
          { instantiate (2:="free"). ss. }
          i. des. ss. rewrite FIND. rename FIND into free_loc. hred_r.

          iPoseProof (liveness_ptr with "hd_ofs") as "%".
          unfold cast_to_ptr in H3. rewrite ptr64 in H3.
          rewrite H3. rename H3 into hd_old_cast. hred_r.
          des_ifs_safe.
          replace (pred _) with blk0 by nia.
          erewrite SKINCLGD; et. hred_r. ss.
          iCombine "hd_point_item hd_point_key" as "hd_point".
          replace (Val.addl tl_old (Vlong _)) 
            with (Val.addl tl_old (Vptrofs (Ptrofs.repr (strings.length (inj_bytes (encode_int 8 (Int64.unsigned hd_long))))))) by et.
          iPoseProof (points_to_collect with "hd_point") as "hd_point".
          iApply isim_ccallU_mfree; ss; oauto.
          iSplitL "INV hd_point hd_liv hd_ofs".
          { iFrame. iExists _,_. iFrame.
            iPureIntro. ss. }
          iIntros (st_src9 st_tgt9) "INV".

          hred_r. unhide. remove_tau.
          pose proof (decode_encode_val_general (Vlong hd_long) Mint64 Mint64).
          unfold decode_encode_val in H3. rewrite H3. clear e H3.
          
          hred_r. hred_l. iApply isim_choose_src. iExists _.
          iApply isim_ret. iFrame. iSplit; ss.
          iExists _,_,_,_,_,_. iFrame; ss. 
          iSplit; ss. iSplitL.
          { iPureIntro. clarify. }
          unfold null_or_int. iLeft. iPureIntro. et.
        (* case: list length with more than 1 && delete from head *)
        * ss. destruct v; try solve [iDestruct "LIST" as "%"; clarify].
          iPoseProof (has_offset_notnull with "hd_ofs") as "%".
          destruct (Val.eq _ hd_old) eqn: ?; clarify. clear H3 n Heqs.
          iDestruct "LIST" as (p_new m_hd' m_new i_hd i_key)
            "[[[[[[new_point new_ofs] new_liv] %] hd_addr] next_next_info] LIST]".
          rename i into next_long. rename H3 into m_new_size.

          iPoseProof (has_offset_notnull with "new_ofs") as "%".
          destruct (i_next =? 0)%Z.
          { iDestruct "next_info" as "%". clarify. }
          iDestruct "next_info" as (m_next) "next_info".

          iCombine "new_point next_info" as "next".
          iPoseProof (replace_meta_to_alive with "next") as "[new_point new_addr]".
          iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr']".
          iPoseProof (capture_offset_comm with "new_addr'") as "comm".
          iPoseProof ("comm" with "new_ofs") as "new_ofs".
          iPoseProof (offset_dup with "new_ofs") as "[new_ofs new_ofs']".
          clear H3.

          iApply isim_ccallU_cmp_ptr3; ss; oauto.
          iSplitL "INV new_ofs' new_liv".
          { iFrame. rewrite m_new_size. vm_compute (size_chunk Mptr). iPureIntro. nia. }
          iIntros (st_src7 st_tgt7) "[INV new_liv]".
          
          hred_r. des_ifs_safe. clear e Heq.
          unhide. hred_r. unhide. remove_tau.
          unhide. remove_tau.
          rewrite decrypt_loc. hred_r. des_ifs_safe. hred_r. rewrite Heq. clear Heq.
          hred_r. rewrite get_co. hred_r. rewrite co_co_members.
          ss. hred_r.
          replace (Coqlib.align _ _) with 8%Z by et.

          iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr']".
          iPoseProof (capture_pointto_comm with "new_addr'") as "comm".
          iPoseProof ("comm" with "new_point") as "new_point".
          iPoseProof (points_to_split with "new_point") as "[new_point_item new_point_key]".
          iPoseProof (offset_dup with "new_ofs") as "[new_ofs new_ofs']".

          iApply isim_ccallU_load; ss; oauto.
          iSplitL "INV new_point_key new_ofs'"; iFrame.
          { iExists _. rewrite encode_val_length.
            iSplitL "new_ofs'"; cycle 1.
            { iPureIntro. instantiate (1:= (0 + 8)%Z). split; et. exists 1. et. }
            iApply offset_slide; try iFrame. rewrite m_new_size.
            vm_compute (size_chunk Mptr). nia. }
          iIntros (st_src8 st_tgt8) "[INV new_point_key]".
          unfold Mptr at 11. rewrite ptr64. rewrite decode_encode_ofs.
          hred_r. clear e.
          iPoseProof (liveness_ptr with "hd_ofs") as "%".
          unfold cast_to_ptr in H3. rewrite ptr64 in H3.
          rewrite H3. rename H3 into hd_old_cast. hred_r. des_ifs_safe.
          rewrite <- Heq. clear Heq i.
          hred_r.

          replace (pred _) with blk by nia.
          erewrite SKINCLGD; et.
          hred_r. ss.

          iApply isim_ccallU_pure; et.
          { eapply fn_has_spec_in_stb; et.
            { eapply STBINCL. stb_tac. unfold xorStb.
              unseal "stb". ss. }
            { ss. instantiate (1:=inl (Ptrofs.repr i_key, hd_old, m_hd, 1%Qp, Dynamic)).
              ss. oauto. }
            { ss. } }
          { instantiate (1:=10). oauto. }
          iPoseProof (offset_dup with "hd_ofs") as "[hd_ofs hd_ofs']".
          ss. iSplitL "INV hd_ofs' hd_liv"; iFrame.
          { iSplit; ss. iExists _,_. iSplit; ss. }
          iIntros (st_src9 st_tgt9 ret_src ret_tgt0) "[INV [POST %]]".
          iDestruct "POST" as (i_ptr) "[[% hd_addr'] hd_liv]".
          rewrite H4. iExists _. iSplit; ss. clear H4 H3.
          iCombine "hd_point_item hd_addr" as "hd".
          iPoseProof (replace_meta_to_alive with "hd") as "[hd_point_item hd_addr]".
          iCombine "hd_addr' hd_addr" as "hd_addr".
          iPoseProof (capture_unique with "hd_addr") as "%".
          clarify. iDestruct "hd_addr" as "[_ hd_addr]".

          hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.

          hexploit SKINCLENV.
          { instantiate (2:="encrypt"). ss. }
          i. des. ss. rewrite FIND. rename FIND into encrypt_loc.
          hred_r. des_ifs_safe. rewrite <- Heq. clear Heq i e. hred_r.
          replace (pred _) with blk0 by nia.
          erewrite SKINCLGD; et. hred_r. ss.
          change (Vlong (Int64.repr _)) with Vnullptr.
          destruct (Z.lxor i_hd i_key =? 0)%Z eqn:?.
          (* case: decrypt value is zero *)
          ** iDestruct "next_next_info" as "%". clarify.
             apply Z.eqb_eq in Heqb. apply Z.lxor_eq in Heqb.
             clarify. rewrite Ptrofs.xor_idem.
             change (Vptrofs Ptrofs.zero) with Vnullptr.
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
             hred_r. unhide. remove_tau. des_ifs_safe. hred_r. rewrite Heq.
             clear Heq. hred_r. rewrite get_co. hred_r. rewrite co_co_members.
             ss. hred_r. destruct Vnullptr eqn:?; clarify. rewrite <- Heqv.
             clear Heqv i. 
             replace (Coqlib.align _ _) with 8%Z by et. hred_r.
             iApply isim_ccallU_store; ss; oauto.
             iPoseProof (offset_dup with "new_ofs") as "[new_ofs new_ofs']".
             iSplitL "INV new_point_key new_ofs"; iFrame.
             { iExists _,_. iFrame. rewrite encode_val_length. 
               iSplitR "new_ofs".
               { iPureIntro. instantiate (1:=(0+8)%Z). split; et. exists 1. et. }
               iApply offset_slide; et. rewrite m_new_size. vm_compute (size_chunk Mptr).
               nia. }
             iIntros (st_src11 st_tgt11) "[INV next_point_key]".
             hred_r. unhide. remove_tau.
             hexploit SKINCLENV.
             { instantiate (2:="free"). ss. }
             i. des. ss. rewrite FIND. rename FIND into free_loc. hred_r. 
             rewrite hd_old_cast. hred_r.
             destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
             replace (pred _) with blk1 by nia.
             erewrite SKINCLGD; et. hred_r.
             iCombine "hd_point_item hd_point_key" as "hd_point".
             change (Val.addl tl_old (Vptrofs _)) 
               with (Val.addl tl_old (Vptrofs (Ptrofs.repr (strings.length (encode_val Mint64 (Vlong hd_long)))))).
             iPoseProof (points_to_collect with "hd_point") as "hd_point".
             iApply isim_ccallU_mfree; ss; oauto.
             iSplitL "INV hd_point hd_liv hd_ofs".
             { iFrame. iExists _,_. iFrame. iPureIntro. ss. }
             iIntros (st_src12 st_tgt12) "INV".

             hred_r. unhide. remove_tau.
             pose proof (decode_encode_val_general (Vlong hd_long) Mint64 Mint64).
             unfold decode_encode_val in H3. rewrite H3. clear H3.

             hred_r. hred_l. iApply isim_choose_src. iExists _.
             iApply isim_ret. iFrame.
             iCombine "new_point_item next_point_key" as "new_point".
             change 8%Z with (Z.of_nat (strings.length (encode_val Mint64 (Vlong next_long)))).
             iPoseProof (points_to_collect with "new_point") as "new_point". 
             iSplit; ss. 
             rewrite unfold_frag_xorlist.
             destruct lreturn; cycle 1.
             { destruct (Val.eq Vnullptr p_next) eqn:?.
               - iPoseProof (captured_pointer_notnull with "new_addr") as "%".
                 clarify.
               - destruct v; try solve [iDestruct "LIST" as "%"; clarify].
                 iDestruct "LIST" as (? ? ? ? ?)
                  "[[[[[[a b] c] d] e] f] LIST]".
                 iPoseProof (points_to_notnull with "a") as "%".
                 clarify. }
             ss. iDestruct "LIST" as "%".
             des. clarify. clear H4.
             iPoseProof (captured_address_not_zero with "new_addr") as "%".
             iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr']".
             iPoseProof (capture_pointto_comm with "new_addr'") as "comm".
             iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr']".
             iPoseProof (capture_offset_comm with "new_addr'") as "comm'".
             iPoseProof ("comm" with "new_point") as "new_point".
             iPoseProof ("comm'" with "new_ofs'") as "new_ofs".
             ss. iExists _,_,tl_old,tl_old,_,_.
             iSplitL "hd_handler_point tl_handler_point hd_handler_ofs tl_handler_ofs new_addr".
             { iFrame. iSplitL. iSplitR "new_addr".
               { iPureIntro. clarify. }
               { unfold null_or_int. iRight.
                 iExists _. iSplit; ss. iExists _. iFrame. }
               { unfold null_or_int. iLeft. ss. } }
             { iExists _,_,_. iFrame. instantiate (2:=0%Z).
               change (Vptrofs (Ptrofs.repr 0)) with Vnullptr.
               iFrame. simpl. rewrite m_new_size. ss. }
          (* case: decrypt value is not zero *)
          ** iDestruct "next_next_info" as (m_next_next) "next_next_info".
             destruct lreturn.
             { ss. iDestruct "LIST" as "%". des. clarify.
               iPoseProof (captured_pointer_notnull with "next_next_info") as "%".
               clarify. }
             ss. destruct v; try solve [iDestruct "LIST" as "%"; clarify].
             rename i into next_next_long.
             iPoseProof (captured_pointer_notnull with "new_addr") as "%".
             destruct Val.eq; clarify.
             iDestruct "LIST" as (p_next_next_next m_new' m_next_next' i_next' i_key_next)
              "[[[[[[new_next_point new_next_ofs] new_next_liv] %] new_addr'] n3_info] LIST]".
             iCombine "new_next_point next_next_info" as "n2".
             iPoseProof (replace_meta_to_alive with "n2") as "[new_next_point new_next_addr]".
             iApply isim_ccallU_pure; et.
             { eapply fn_has_spec_in_stb; et.
               { eapply STBINCL. stb_tac. unfold xorStb.
                 unseal "stb". ss. }
               { ss. et. instantiate (1:=inr (inr (inl (_,_,_,_)))).
                 ss. oauto. }
               { ss. } }
             { instantiate (1:=9). oauto. }
             ss.
             iPoseProof (offset_dup with "new_next_ofs") as "[new_next_ofs' new_next_ofs]".
             iPoseProof (capture_dup with "new_next_addr") as "[new_next_addr' new_next_addr]".
             iPoseProof (capture_offset_comm with "new_next_addr'") as "comm".
             iPoseProof ("comm" with "new_next_ofs'") as "new_next_ofs'".
             iSplitL "INV new_next_liv new_next_ofs'"; iFrame.
             { iSplit; ss. iExists _. iSplit; ss.
               instantiate (1:=0%Z).
               replace (Vptrofs (Ptrofs.xor _ _))
                with (Vptrofs (Ptrofs.repr (Z.lxor i_hd i_key))) by admit "".
               iApply "new_next_ofs'". }
             iIntros (st_src10 st_tgt10 ret_src0 ret_tgt1) "[INV [POST %]]".
             iDestruct "POST" as (i_keyhd) "[[% new_next_addr_store] new_next_liv]".
             rewrite H6. clear H6 H5. iExists _. iSplit; ss.

             hred_r. unhide. remove_tau.
             des_ifs_safe. hred_r. rewrite Heq. clear Heq.
             hred_r. rewrite get_co. hred_r. rewrite co_co_members.
             ss. hred_r. des_ifs_safe. rewrite <- Heq. clear Heq i.
             hred_r.
             change (Coqlib.align _ _) with 8%Z.
             iApply isim_ccallU_store; ss; oauto.
             iPoseProof (offset_dup with "new_ofs") as "[new_ofs new_ofs']".
             iSplitL "INV new_point_key new_ofs"; iFrame.
             { iExists _,_. iFrame. rewrite encode_val_length. 
               iSplitR "new_ofs".
               { iPureIntro. instantiate (1:=(0+8)%Z). split; et. exists 1. et. }
               iApply offset_slide; et. rewrite m_new_size. vm_compute (size_chunk Mptr).
               nia. }
             iIntros (st_src11 st_tgt11) "[INV next_point_key]".

             hred_r. unhide. remove_tau.
             hexploit SKINCLENV.
             { instantiate (2:="free"). ss. }
             i. des. ss. rewrite FIND. rename FIND into free_loc. hred_r. 
             rewrite hd_old_cast. hred_r.
             destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
             replace (pred _) with blk1 by nia.
             erewrite SKINCLGD; et. hred_r.
             iCombine "hd_point_item hd_point_key" as "hd_point".
             change (Val.addl tl_old (Vptrofs _)) 
               with (Val.addl tl_old (Vptrofs (Ptrofs.repr (strings.length (encode_val Mint64 (Vlong hd_long)))))).
             iPoseProof (points_to_collect with "hd_point") as "hd_point".
             iApply isim_ccallU_mfree; ss; oauto.
             iSplitL "INV hd_point hd_liv hd_ofs".
             { iFrame. iExists _,_. iFrame. iPureIntro. ss. }
             iIntros (st_src12 st_tgt12) "INV".

             hred_r. unhide. remove_tau.
             pose proof (decode_encode_val_general (Vlong hd_long) Mint64 Mint64).
             unfold decode_encode_val in H5. rewrite H5. clear H5.

             hred_r. hred_l. iApply isim_choose_src. iExists _.
             iApply isim_ret. iFrame.
             iCombine "new_point_item next_point_key" as "new_point".
             change 8%Z with (Z.of_nat (strings.length (encode_val Mint64 (Vlong next_long)))).
             iPoseProof (points_to_collect with "new_point") as "new_point".
             iSplit; ss. 

             iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr_rep]".
             iPoseProof (capture_pointto_comm with "new_addr_rep") as "comm".
             iPoseProof ("comm" with "new_point") as "new_point".
             iCombine "new_point new_addr'" as "new".
             iPoseProof (replace_meta_to_alive with "new") as "[new_point new_addr']".
             iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr_rep]".
             iPoseProof (capture_pointto_comm with "new_addr_rep") as "comm".
             iPoseProof ("comm" with "new_point") as "new_point".
             iCombine "new_addr new_addr'" as "new".
             iPoseProof (capture_unique with "new") as "%".
             iDestruct "new" as "[_ new_addr]".
             clarify.
             iExists _,_,_,_,_,_. iFrame.
             instantiate(1:=tl_old).
             iSplitL "".
             { iSplitL. iSplitL. iSplit; ss.
               { unfold null_or_int. iLeft. iPureIntro. ss. }
               { unfold null_or_int. iLeft. iPureIntro. ss. } }
             iExists p_new,_,_. iFrame.
             rewrite m_new_size. iSplitL "new_next_addr new_next_addr_store".
             { iSplit; ss.
               iPoseProof (captured_address_not_zero with "new_next_addr_store") as "%".
               destruct (i_keyhd =? 0)%Z eqn: ?.
               { apply Z.eqb_eq in Heqb0. exfalso. clarify. }
               { admit "capture_trans". } }
             iPoseProof (captured_address_not_zero with "new_addr") as "%".
             destruct Val.eq.
             { rewrite e in H5. clarify. }
             iExists _,_,_,_,_. iFrame.
             rewrite H4. iSplit; ss. admit "capture_refl".
    Unshelve. all: et.
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
    econs; ss. red.

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
    i. des. ss. rewrite FIND. hred_r. des_ifs_safe. hred_r.

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
  End FUN.

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

