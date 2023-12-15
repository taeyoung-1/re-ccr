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

(* TODO: match with paper code & proof *)

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


  Lemma sim_delete_hd :
    sim_fnsem wf top2
      ("delete_hd", fun_to_tgt "xorlist" (GlobalStb (Sk.canon sk)) (mk_pure delete_hd_spec))
      ("delete_hd", cfunU (decomp_func (Sk.canon sk) ce f_delete_hd)).
  Proof.
    Opaque encode_val.
    econs; ss. red.

    (* current state: 1 *)
    unfold prog in ce. unfold mkprogram in ce.
    destruct (build_composite_env'). ss.
    get_composite ce e.

    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply Sk.incl_incl_env in SKINCLENV.
    unfold Sk.incl_env in SKINCLENV.
    pose proof Sk.sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_delete_hd. i; ss.
    unfold decomp_func, function_entry_c. ss.
    let H := fresh "HIDDEN" in
    set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[% PRE] %]". unfold full_xorlist.
    iDestruct "PRE"
      as (m_hd_hdl m_tl_hdl hd_old tl_old ofs_hd_hdl ofs_tl_hdl tg_hd_hdl tg_tl_hdl)
      "[[[[[[hd_hdl_point hd_hdl_ofs] %] tl_hdl_point] tl_hdl_ofs] %] LIST]".
    clarify. hred_r. unhide. hred_r. unhide. remove_tau.
    rename v into hd_handler.  rename v0 into tl_handler.
    rename l into linput. rename H5 into hd_hdl_align.
    rename H6 into tl_hdl_align.

    (* current state: 2 *)
    unhide. hred_r. unhide. remove_tau.

    (* node hd_old = *hdH start *)
    iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%". rewrite H3. rename H3 into hd_hdl_ptr.
    hred_r. iApply isim_apc. iExists (Some (20%nat : Ord.t)).
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_hdl_point hd_hdl_ofs"; iFrame.
    { iPureIntro. rewrite encode_val_length. et. }
    iIntros (st_src0 st_tgt0) "[INV [hd_hdl_point hd_hdl_ofs]]".
    (* node hd_old = *hdH end *)

    (* if (hd_old != NULL) start *)
    hred_r. unhide. remove_tau. unhide. remove_tau.
    change Archi.ptr64 with true. hred_r.
    change (Vlong (Int64.repr _)) with Vnullptr.
    destruct linput as [|v lnext].
    (* case: nil list *)
    {
      (* admit "solved". *)
      ss.
      iDestruct "LIST" as "[NULL_tl NULL_hd]".
      iPoseProof (null_equiv with "NULL_tl") as "%". subst.
      iPoseProof (equiv_sym with "NULL_hd") as "H". iPoseProof (null_equiv with "H") as "%". subst.
      unfold Mptr. change Archi.ptr64 with true. ss. rewrite decode_encode_null.
      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src1 st_tgt1) "INV".

      hred_r. destruct (Int.eq) eqn:?; ss; clarify. clear Heqb.
      (* if (hd_old != NULL) end *)

      unhide. hred_r. unhide. remove_tau. change Archi.ptr64 with true. ss.
      change Vnullptr with (Vptrofs Ptrofs.zero).
      rewrite ptrofs_cast_ptr. hred_r.

      (* prove post condition *)
      hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret.
      iFrame. iSplit; ss. iSplit; ss.
      iExists _,_,_,_,_,_,_,_. iFrame. iSplit; ss.
    }
    (* case: not nil list *)
    ss. destruct v; try solve [iDestruct "LIST" as "[]"]. rename i into hd_item.
    iDestruct "LIST" as (i_hd_prev i_hd_next m_hd_old) "[[[[% hd_prev_equiv] hd_ofs] hd_point] LIST]". rename H3 into m_hd_size.

    iPoseProof (decode_encode_ptr_ofs with "hd_ofs") as "%". rewrite H3. rename H3 into hd_old_deen.
    iApply isim_ccallU_cmp_ptr4; ss; oauto.
    iSplitL "INV hd_ofs"; iFrame.
    { iPureIntro. red. rewrite m_hd_size. vm_compute (size_chunk Mptr). vm_compute (Ptrofs.unsigned Ptrofs.zero). nia. }
    iIntros (st_src1 st_tgt1) "[INV hd_ofs]".
    hred_r. destruct (Int.eq) eqn: ?; ss; clarify. clear Heqb.
    (* if (hd_old != NULL) end *)

    unhide. hred_r. unhide. remove_tau.

    (* item = hd_old->item start *)
    iPoseProof (points_to_is_ptr with "hd_point") as "%". rewrite H3. rename H3 into hd_is_ptr. hred_r. rewrite hd_is_ptr. hred_r.
    rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    iPoseProof (points_to_split with "hd_point") as "[hd_point_item hd_point_key]".
    change Archi.ptr64 with true. hred_r.
    change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs Ptrofs.zero). iPoseProof (add_null_r with "hd_ofs") as "%". rewrite H3. rename H3 into hd_add_null.
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_point_item hd_ofs"; iFrame.
    { iPureIntro. rewrite encode_val_length. split; et. exists 0. ss. }
    iIntros (st_src2 st_tgt2) "[INV [hd_point_item hd_ofs]]". rewrite decode_encode_item.
    (* item = hd_old->item end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* hd_new = (node* )hd_old->link start *)
    rewrite hd_is_ptr. hred_r. rewrite hd_is_ptr. hred_r.
    rewrite get_co. hred_r. rewrite co_co_members. ss.
    change Archi.ptr64 with true. hred_r.
    change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_point_key hd_ofs"; iFrame.
    { iSplit. { iApply offset_slide. et. } iPureIntro. rewrite encode_val_length. split; et. exists 1. ss. }
    iIntros (st_src3 st_tgt3) "[INV [hd_point_key hd_ofs]]". change Mptr with Mint64. rewrite decode_encode_ofs.
    (* hd_new = (node* )hd_old->link end *)

    (* hdH* = hd_new start *)
    hred_r. rewrite ptrofs_cast_ptr. hred_r. unhide. remove_tau. unhide. remove_tau.
    rewrite hd_hdl_ptr. hred_r. rewrite ptrofs_cast_ptr. hred_r.
    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV hd_hdl_point hd_hdl_ofs"; iFrame.
    { iExists _. iFrame. iPureIntro. rewrite encode_val_length. et. }
    iIntros (st_src4 st_tgt4) "[INV [hd_hdl_point hd_hdl_ofs]]".
    (* hdH* = hd_new end *)

    (* if (hd_new == NULL) start *)
    hred_r. unhide. remove_tau. unhide. remove_tau.
    change Archi.ptr64 with true. hred_r.
    replace (Vlong (Int64.repr _)) with Vnullptr by et.
    iPoseProof (null_equiv with "hd_prev_equiv") as "%".
    assert (i_hd_prev = Ptrofs.zero).
    { unfold Vptrofs, Vnullptr in *. des_ifs. replace intrange with intrange0 in * by apply proof_irrel. rewrite <- Heq1 in Heq0. apply (f_equal Ptrofs.of_int64) in Heq0. rewrite Ptrofs.of_int64_to_int64 in Heq0; et. }
    subst. clear H3. rewrite Ptrofs.xor_zero_l.

    destruct lnext.
    (* case: delete from singleton list *)
    - 
      (* admit "solved". *)
      ss. iDestruct "LIST" as "[tl_equiv NULL_next]".
      iPoseProof (equiv_sym with "NULL_next") as "H". iPoseProof (null_equiv with "H") as "%". rewrite H3. clear H3 i_hd_next.
      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src5 st_tgt5) "INV".
      hred_r. des_ifs_safe. clear Heq. unhide. remove_tau.
      (* if (hd_new == NULL) end *)

      (* tlH* = NULL start *)
      iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%". rewrite H3. rename H3 into tl_hdl_ptr.
      hred_r. change Archi.ptr64 with true. hred_r.
      change Archi.ptr64 with true. hred_r.

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV tl_hdl_point tl_hdl_ofs"; iFrame.
      { iExists _. iFrame. iPureIntro. rewrite encode_val_length; et. }
      iIntros (st_src6 st_tgt6) "[INV [tl_hdl_point tl_hdl_ofs]]".
      (* tlH* = NULL end *)

      hred_r. unhide. remove_tau.

      (* free(hd_old) start *)
      hexploit SKINCLENV.
      { instantiate (2:="free"). ss. }
      i. des. ss. rewrite FIND. rename FIND into free_loc. hred_r.

      iPoseProof ((@point_cast_ptr _ _ _ _ Es) with "hd_point_item") as "%".
      rewrite H3. rename H3 into hd_old_cast. hred_r. des_ifs_safe. clear e.

      replace (pred _) with blk by nia.
      erewrite SKINCLGD; et. hred_r.

      iCombine "hd_point_item hd_point_key" as "hd_point".
      replace (Val.addl tl_old (Vlong _)) 
        with (Val.addl tl_old (Vptrofs (Ptrofs.repr (strings.length (inj_bytes (encode_int 8 (Int64.unsigned hd_item))))))) by et.
      iPoseProof (points_to_collect with "hd_point") as "hd_point".
      iPoseProof (offset_slide_rev with "hd_ofs") as "hd_ofs".

      iApply isim_ccallU_mfree; ss; oauto.
      iSplitL "INV hd_point hd_ofs"; iFrame.
      { iExists _,_. iFrame. ss. }
      iIntros (st_src7 st_tgt7) "INV".
      (* free(hd_old) end *)

      hred_r. unhide. remove_tau. change Archi.ptr64 with true. hred_r.

      (* prove post condition *)
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iFrame. iSplit; ss. iSplit; ss. iExists _,_,_,_,_,_,_,_. iFrame; ss. 

    (* case: list length is more than 1 *)
    - ss. destruct v; clarify.
      iDestruct "LIST" as (i_hd i_hd_nn m_hd_next) "[[[[% hd_equiv] hd_next_ofs] hd_next_point] LIST]". rename H3 into m_hd_next_size. rename i into hd_next_item.

      iApply isim_ccallU_cmp_ptr3; ss; oauto.
      iSplitL "INV hd_next_ofs"; iFrame.
      { iPureIntro. red. rewrite m_hd_next_size. vm_compute (Ptrofs.unsigned Ptrofs.zero). vm_compute (size_chunk Mptr). nia. }
      iIntros (st_src5 st_tgt5) "[INV hd_next_ofs]".
      (* if (hd_new == NULL) end *)
          
      hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau.

      (* link = (node* )hd_new->link start *)
      iPoseProof (points_to_is_ptr with "hd_next_point") as "%". rewrite H3. rename H3 into hd_next_is_ptr. hred_r. rewrite hd_next_is_ptr. hred_r.
      iPoseProof (points_to_split with "hd_next_point") as "[hd_next_point_item hd_next_point_key]".
      change (strings.length _) with 8. ss.

      rewrite get_co. hred_r. rewrite co_co_members. ss.
      change Archi.ptr64 with true. hred_r.
      change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
      iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV hd_next_point_key hd_next_ofs"; iFrame.
      { iSplit. { iApply offset_slide. et. } iPureIntro. rewrite encode_val_length. split; et. exists 1. ss. }
      iIntros (st_src6 st_tgt6) "[INV [hd_next_point_key hd_next_ofs]]".
      change Mptr with Mint64. rewrite decode_encode_ofs. 
      (* hd_new = (node* )hd_old->link end *)

      hred_r. unhide. remove_tau. unhide. remove_tau.

      (* hd_new->link = link ^ (intptr_t)hd_old start *)
      iPoseProof ((@point_cast_ptr _ _ _ _ Es) with "hd_point_item") as "%".
      rewrite H3. rename H3 into hd_old_cast. hred_r.

      iApply isim_ccallU_capture2; ss; oauto.
      iSplitL "INV hd_ofs"; iFrame.
      { iApply offset_slide_rev. et. }
      iIntros (st_src7 st_tgt7 i) "[INV [hd_ofs hd_equiv']]".

      iCombine "hd_equiv' hd_equiv" as "hd_equiv". iPoseProof (capture_unique with "hd_equiv") as "%". clarify. iDestruct "hd_equiv" as "[_ hd_equiv]".

      hred_r. unhide. remove_tau.
      rewrite hd_next_is_ptr. hred_r. rewrite hd_next_is_ptr. hred_r.
      rewrite get_co. hred_r. rewrite co_co_members.
      ss. change Archi.ptr64 with true. hred_r. 
      do 2 rewrite ptrofs_cast_ptr. hred_r. des_ifs_safe.
      hred_r. change Archi.ptr64 with true. hred_r. 
      
      change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV hd_next_point_key hd_next_ofs"; iFrame.
      { iExists _. iFrame. iPureIntro. rewrite encode_val_length. split; ss. exists 1. ss. }
      iIntros (st_src8 st_tgt8) "[INV [hd_next_point_key hd_next_ofs]]".
      (* hd_new->link = link ^ (intptr_t)hd_old end *)

      hred_r. unhide. remove_tau.

      (* free(hd_old) start *)
      hexploit SKINCLENV.
      { instantiate (2:="free"). ss. }
      i. des. ss. rewrite FIND. rename FIND into free_loc. hred_r. 
      rewrite hd_old_cast. hred_r.
      destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
      replace (pred _) with blk by nia.
      erewrite SKINCLGD; et. hred_r.

      iCombine "hd_point_item hd_point_key" as "hd_point".
      iPoseProof (points_to_collect with "hd_point") as "hd_point".

      iApply isim_ccallU_mfree; ss; oauto.
      iSplitL "INV hd_point hd_ofs"; iFrame.
      { iExists _,_. iFrame. iPureIntro. ss. }
      iIntros (st_src12 st_tgt12) "INV".
      (* free(hd_old) end *)

      hred_r. unhide. remove_tau. change Archi.ptr64 with true. hred_r.

      (* prove post condition *)
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iFrame. iSplit; ss. iSplit; ss.
      change 8%Z with (Z.of_nat (strings.length (encode_val Mint64 (Vlong hd_next_item)))).
      iCombine "hd_next_point_item hd_next_point_key" as "hd_next_point".  iPoseProof (points_to_collect with "hd_next_point") as "hd_next_point". iPoseProof (offset_slide_rev with "hd_next_ofs") as "hd_next_ofs".
      iExists _,_,_,_,_,_,_,_. iFrame. iSplit; ss.
      iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l.
      iSplit; ss. replace (Vlong (Int64.xor i i0)) with (Vptrofs i_hd_nn); et.
      clear - Heq Heq0. unfold Vptrofs in *. des_ifs. f_equal.
      rewrite int64_ptrofs_xor_comm.
      rewrite Ptrofs.xor_commut. 
      rewrite <- Ptrofs.xor_assoc. 
      rewrite Ptrofs.xor_idem.
      rewrite Ptrofs.xor_zero_l. et.
  Qed.

  (* Lemma sim_encrypt :
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
  Admitted. *)

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

