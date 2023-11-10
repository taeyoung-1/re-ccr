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
Require Import ClightDmgen.
Require Import ClightDmMem1.
Require Import CIProofMode.
Require Import xorlist.
Require Import xorlist0.
Require Import xorlist1.
Require Import CTactics.
Require Import PtrofsArith.
From Coq Require Import Program.
From compcertip Require Import Clightdefs.


Section LEMMA.

  Lemma f_bind_ret_r E R A (s : A -> itree E R)
    : (fun a => ` x : R <- (s a);; Ret x) = s.
  Proof. apply func_ext. i. apply bind_ret_r. Qed.

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

  Section FUN.
  Variable sk: Sk.t.
  Hypothesis SKINCL : Sk.extends (xorlist0.xor.(Mod.sk)) sk.
  Hypothesis SKWF : Sk.wf (Sk.canon sk).

  Arguments alist_add /.
  Arguments ClightDmgen._sassign_c /.
  Arguments ClightDmgen._scall_c /.
  Arguments ClightDmgen._site_c /.
  Arguments ClightDmExprgen.sem_xor_c /.
  Arguments ClightDmExprgen.sem_binarith_c /.
  Arguments ClightDmExprgen.sem_cast_c /.

  (* 

  Lemma val_exists i b ofs q0 z t a : Vptrofs i ⊸ (b, ofs) ** b ↱q0# (z, t, a) 
    -∗ b ↱q0# (z, t, Some (Ptrofs.unsigned i)).
  Proof. Admitted.

  Lemma add_provenance b ofs q sz tg i i'
    :
  b ↱q# (sz, tg, Some i) ** Vptrofs i' ⊸ (b, ofs) -∗ ⌜(i + ofs)%Z = Ptrofs.unsigned i'⌝.
  Proof. 
    (* iIntros "[BLK PTR]". unfold allocated_with, repr_to. des_ifs.
    iDestruct "BLK" as "[ALLOC [BL PTR']]".
    iCombine "PTR" "PTR'" as "PTR".
    iPoseProof (provenace_dup with "PTR") as "%". clarify.
    iPureIntro.
    unfold Vptrofs in *. des_ifs_safe. unfold Ptrofs.to_int64.
    do 2 autorewrite with ptrArith; auto with ptrArith. nia.
  Qed. *)
  Admitted. *)
  Definition cast_to_ptr (v: val) : itree Es val :=
    match v with
    | Vptr _ _ => Ret v
    | Vint _ => if Archi.ptr64 then triggerUB else Ret v
    | Vlong _ => if Archi.ptr64 then Ret v else triggerUB
    | _ => triggerUB
    end.

  Lemma liveness_ptr v m ofs
    : 
      v ⊨m# ofs -∗ ⌜cast_to_ptr v = Ret v⌝.
  Proof.
    iIntros "A". unfold has_offset.
    destruct v; ss; des_ifs_safe;
    iDestruct "A" as "[A %]"; clarify.
  Qed.

  Lemma points_to_is_ptr v m q mvs
    : 
      v ↦m#q≻ mvs -∗ ⌜is_ptr_val v = true⌝.
  Proof.
    iIntros "A". unfold points_to, has_offset.
    destruct v; ss; des_ifs_safe;
    iDestruct "A" as "[A B]"; clarify;
    iDestruct "B" as (ofs) "[B [C %]]"; clarify.
  Qed.

  Opaque captured_to.
  Opaque has_offset.
  Opaque points_to.
  Opaque metadata_alive.
  Opaque ccallU.
  Opaque get_sk.
  Opaque build_composite_env.

  Lemma sim_delete :
    sim_fnsem wf top2
      ("delete", fun_to_tgt "xorlist" (GlobalStb (Sk.canon sk)) (mk_pure delete_spec))
      ("delete", cfunU (decomp_func (Sk.canon sk) ce f_delete)).
  Proof.
    econs; ss. red.

    unfold prog in ce. unfold mkprogram in ce.
    destruct (build_composite_env').
    get_composite ce e.

    apply isim_fun_to_tgt; auto.
    unfold f_delete.
     i; ss.
    unfold decomp_func, function_entry_c. ss.
    init_hide.

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[PRE %]".
    iDestruct "PRE" as (hd_old tl_old ofs_hd_old ofs_tl_old) "[[[% [HD_ofs]] TL_ofs] LIST]".
    ss. clarify. ss. hred_r. unhide. remove_tau. unhide.
    remove_tau. unhide.

    des_ifs_safe. hred_r.
    iPoseProof (points_to_is_ptr with "HD") as "%".
    rewrite H3. hred_r.
    iApply isim_apc. iExists (Some (10%nat : Ord.t)).
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV HD"; iFrame.
    { rewrite encode_val_length. et. }
    iIntros (st_src1 st_tgt1) "[INV HD]".


    replace (Vlong _) with Vnullptr by et.
    destruct l.
    - unfold full_xorlist, frag_xorlist at 1.
      iDestruct "LIST" as "%". des. clarify.

    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply Sk.incl_incl_env in SKINCLENV.
    unfold Sk.incl_env in SKINCLENV.
    hexploit SKINCLENV.
    { instantiate (2:="malloc"). ss. }
    i. des. ss. rewrite FIND. hred_r. des_ifs_safe. hred_r.
  Admitted.

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

  (* need to repaired *)
  Lemma sk_incl_gd (sk0 sk1: Sk.t) gn blk gd: 
    Sk.extends sk0 sk1 ->
    SkEnv.id2blk (Sk.load_skenv (Maps.PTree.elements sk1)) gn = Some blk ->
    Maps.PTree.get (ident_of_string gn) sk0 = Some gd ->
    nth_error (Maps.PTree.elements sk1) blk = Some (ident_of_string gn, gd).
  Proof.
  Admitted.


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

