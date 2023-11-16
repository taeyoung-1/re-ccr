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
    hred_r. des_ifs_safe. rename Heq2 into get_co.
    rename Heq1 into ptr64. rewrite <- Heq0.
    clear Heq e Heq0 i. hred_r.

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
      ss.
  Admitted.

  End SIMFUNS.

End PROOF.