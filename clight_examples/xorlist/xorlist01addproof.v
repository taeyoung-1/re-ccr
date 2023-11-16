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
    rename v into hd_hdl.
    rename v0 into tl_hdl.
    rename l into lfull.
    rename i into at_tail.
    rename i0 into item.

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

    hred_r. unhide. remove_tau. 
    iPoseProof ((@offset_cast_ptr _ _ _ _ Es) with "new_ofs") as "%".
    rewrite H4. rename H4 into new_cast_ptr.
    hred_r. unhide. remove_tau. unhide.
    remove_tau. 

    unfold full_xorlist.
    iDestruct "PRE" 
      as (m_hd_hdl m_tl_hdl m_hd m_tl p_hd p_tl 
          i_hd i_tl ofs_hd_hdl ofs_tl_hdl) "PRE".
    iDestruct "PRE" as (tg_hd_hdl tg_tl_hdl) 
      "[[[[[[[[[[hd_hdl_point hd_hdl_ofs] %] hd_addr] %]
               tl_hdl_point] tl_hdl_ofs] %] tl_addr] %] LIST]".
    rename H4 into hd_hdl_align.
    rename H5 into hd_null_case.
    rename H6 into tl_hdl_align.
    rename H7 into tl_null_case.

    iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%".
    rewrite H4. rename H4 into hd_hdl_is_point. hred_r.

    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_hdl_point hd_hdl_ofs"; iFrame.
    { rewrite encode_val_length. et. }
    iIntros (st_src1 st_tgt1) "[INV [hd_hdl_point hd_hdl_ofs]]".
    replace (decode_val Mptr (encode_val Mptr p_hd)) with p_hd by admit "captured is decode_encode".

    hred_r. unhide. remove_tau. unhide. remove_tau.
    iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%".
    rewrite H4. rename H4 into tl_hdl_is_point. hred_r.

    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tl_hdl_point tl_hdl_ofs"; iFrame.
    { rewrite encode_val_length. et. }
    iIntros (st_src2 st_tgt2) "[INV [tl_hdl_point tl_hdl_ofs]]".
    replace (decode_val Mptr (encode_val Mptr p_tl)) with p_tl by admit "captured is decode_encode".

    hred_r. unhide. remove_tau. unhide. remove_tau.
    iPoseProof (points_to_is_ptr with "new_point") as "%".
    rewrite H4. rename H4 into new_is_point.
    hred_r. rewrite new_is_point. hred_r. rewrite co_co_members. ss.
    hred_r.
    replace (Coqlib.align 0 _) with 0%Z by et.
    replace (Ptrofs.repr 0) with Ptrofs.zero by et.
    iPoseProof (add_null_r with "new_ofs") as "%".
    rewrite H4. rename H4 into new_add_r.

    replace ([Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef])
    with ([Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef] ++ [Undef;Undef;Undef;Undef;Undef;Undef;Undef;Undef]) by et.
    iPoseProof (points_to_split with "new_point") as "[new_point_item new_point_key]".
    rewrite cast_long. hred_r.

    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV new_point_item new_ofs"; iFrame.
    { iExists _. iFrame. ss.
      iPureIntro. split; et. exists 0. ss. }
    iIntros (st_src3 st_tgt3) "[INV [new_point_item new_ofs]]".

    hred_r. unhide. remove_tau.
    replace (Vlong (Int64.repr _)) with Vnullptr by et.

    destruct lfull.
    (* case: nil list *)
    - unfold frag_xorlist at 1.
      iDestruct "LIST" as "%". des. clarify.
      hexploit hd_null_case; et. i. clarify.

      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src4 st_tgt4) "INV".

      hred_r. des_ifs_safe. clear Heq.
      unhide. hred_r. unhide. remove_tau.
      rewrite new_is_point. hred_r.
      rewrite new_is_point. hred_r.
      rewrite co_co_members. ss. hred_r.
      replace (Coqlib.align _ _) with 8%Z by et.
      replace (Vlong (Int64.repr _)) with Vnullptr by et.
      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV new_point_key new_ofs"; iFrame.
      { iExists _. iFrame. iSplit; cycle 1.
        { iApply offset_slide. iFrame. }
        { iPureIntro. split; ss. exists 1. ss. } }
      iIntros (st_src5 st_tgt5) "[INV [new_point_key new_ofs]]".

      hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau. 
      unhide. remove_tau.

      iPoseProof ((offset_slide _ _ _ _ _ (Ptrofs.repr (-8)%Z)) with "new_ofs") as "new_ofs".
      replace (Val.addl (Val.addl _ _) _) with p_new.
      2:{ rewrite Val.addl_assoc. ss. }
      replace (Ptrofs.add (Ptrofs.add _ _) _) with Ptrofs.zero.
      2:{ rewrite Ptrofs.add_assoc. ss. }

      rewrite new_cast_ptr. hred_r. unhide.

      iApply isim_ccallU_capture2; ss; oauto.
      iSplitL "INV new_ofs"; try solve [iFrame].
      iIntros (st_src6 st_tgt6 i) "[INV [new_ofs new_addr]]".

      hred_r. unhide. remove_tau.
      rewrite cast_ptrofs. hred_r. unhide. remove_tau.
      rewrite tl_hdl_is_point. hred_r.
      rewrite cast_ptrofs. hred_r.

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV tl_hdl_point tl_hdl_ofs"; iFrame.
      { iExists _. iFrame. rewrite encode_val_length. iPureIntro. ss. }
      iIntros (st_src7 st_tgt7) "[INV [tl_hdl_point tl_hdl_ofs]]".

      hred_r. unhide. remove_tau.
      rewrite hd_hdl_is_point. hred_r.
      rewrite cast_ptrofs. hred_r.

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV hd_hdl_point hd_hdl_ofs"; iFrame.
      { iExists _. iFrame. rewrite encode_val_length. iPureIntro. ss. }
      iIntros (st_src8 st_tgt8) "[INV [hd_hdl_point hd_hdl_ofs]]".


      hred_r. remove_tau. hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret.
      iFrame. iSplit; ss. iSplit; ss.
      replace (Vptrofs (Ptrofs.repr 8))
        with (Vptrofs (Ptrofs.repr (length (encode_val Mptr (Vptrofs i))))) by ss.
      iCombine "new_point_item new_point_key" as "new_point".
      iPoseProof (points_to_collect with "new_point") as "new_point".
      iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr']".
      iPoseProof (capture_dup with "new_addr'") as "[new_addr' new_addr'']".
      iPoseProof (capture_offset_comm with "new_addr'") as "comm".
      iPoseProof (capture_pointto_comm with "new_addr''") as "comm'".
      iPoseProof ("comm" with "new_ofs") as "new_ofs".
      iPoseProof ("comm'" with "new_point") as "new_point".
      iPoseProof (capture_refl with "new_addr") as "new_addr".
      iPoseProof (capture_dup with "new_addr") as "[new_addr new_addr']".
      iExists _,_,_,_,_,_,_,_. iExists _,_,_,_. iFrame.
      iSplit.
      { iPureIntro. splits; ss. all: i; clarify. }
      unfold vlist_add.
      destruct (Val.eq _ _); ss.
      + iExists _,_. iSplit; ss.
        replace (Ptrofs.xor Ptrofs.zero Ptrofs.zero) with Ptrofs.zero by ss.
        replace (Vptrofs Ptrofs.zero) with Vnullptr by et.
        iFrame. ss.
      + iExists _,_. iSplit; ss.
        replace (Ptrofs.xor Ptrofs.zero Ptrofs.zero) with Ptrofs.zero by ss.
        replace (Vptrofs Ptrofs.zero) with Vnullptr by et.
        iFrame. ss.
    - 
  Admitted.

  End SIMFUNS.

End PROOF.