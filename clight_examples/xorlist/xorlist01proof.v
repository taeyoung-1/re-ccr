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
(* Require Import Int64Arith. *)
(* Require Import ClightProofs.
Require Import csyntax.
Require Import ClightPreambles. *)

From Coq Require Import Program.
From compcertip Require Import Clightdefs.


Section LEMMA.

  Lemma f_bind_ret_r E R A (s : A -> itree E R)
    : (fun a => ` x : R <- (s a);; Ret x) = s.
  Proof. apply func_ext. i. apply bind_ret_r. Qed.

End LEMMA.

Section PROOF.

  (* Import CTypeNotation CExpNotation CStmtNotation.
  Local Open Scope cexp_scope.
  Local Open Scope cstmt_scope.
  Local Open Scope ctypes_scope. *)
  
  (* Context `{CONF: EMSConfig}. *)
  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memphyRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.
  Context `{@GRA.inG memidRA Σ}.
  
  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb xorStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).

  Opaque get_sk.
  Opaque prog_comp_env.

  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ⌜True⌝)%I.
  
  (* Theorem correct : refines2 [xorlist0.xor] [xorlist1.xor GlobalStb].
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
    all: rewrite f_bind_ret_r.
    - apply sim_search.
    - apply sim_delete.
    - apply sim_add.
    - apply sim_decrypt.
    - apply sim_encrypt.
  Qed. *)
  Arguments alist_add /.

  Let ce := map (fun '(id, p) => (string_of_ident id, p)) (Maps.PTree.elements (prog_comp_env prog)).

  Lemma ptrofs_max : Archi.ptr64 = true -> Int64.max_unsigned = Ptrofs.max_unsigned.
  Proof. des_ifs_safe. Qed.
  
  Lemma mkint64_eq' x y : Int64.unsigned x = Int64.unsigned y -> x = y.
  Proof. i. destruct x. destruct y. apply Int64.mkint_eq. et. Qed.

  Lemma lxor_size a b
    :
  0 ≤ a ≤ Ptrofs.max_unsigned
  -> 0 ≤ b ≤ Ptrofs.max_unsigned
  -> 0 ≤ Z.lxor a b ≤ Ptrofs.max_unsigned.
  Proof.
    i. change Ptrofs.max_unsigned with (2 ^ 64 - 1) in *.
    assert (I1: 0 ≤ a < 2 ^ 64) by nia.
    assert (I2: 0 ≤ b < 2 ^ 64) by nia. clear H3 H4.
    assert (0 ≤ Z.lxor a b < 2 ^ 64); try nia.
    destruct (Coqlib.zeq a 0);
    destruct (Coqlib.zeq b 0); clarify.
    2: split.
    - rewrite Z.lxor_0_r. nia.
    - rewrite Z.lxor_nonneg. nia.
    - des.
      rewrite Z.log2_lt_pow2 in I3; try nia.
      rewrite Z.log2_lt_pow2 in I0; try nia.
      destruct (Coqlib.zeq (Z.lxor a b) 0); try nia.
      rewrite Z.log2_lt_pow2; cycle 1.
      + assert (0 ≤ Z.lxor a b); try nia. rewrite Z.lxor_nonneg. nia.
      + eapply Z.le_lt_trans; try apply Z.log2_lxor; try nia. 
  Qed.

Arguments ClightDmExprgen.sem_xor_c /.
Arguments ClightDmExprgen.sem_binarith_c /.
Arguments ClightDmExprgen.sem_cast_c /.

Create HintDb ptrArith.

Hint Unfold Vptrofs Int64.xor Ptrofs.to_int64 : ptrArith.
Hint Rewrite ptrofs_max Ptrofs.unsigned_repr Int64.unsigned_repr : ptrArith.
Hint Resolve Ptrofs.unsigned_range_2 : ptrArith.

  Lemma val_multimap v b ofs : (v ⊸ (b, ofs)) -∗ ⌜exists i, v = Vptrofs i \/ exists b ofs, v = Vptr b ofs⌝.
  Proof.
    iIntros "A". destruct v; ss; des_ifs_safe.
    - unfold Vptrofs. des_ifs_safe. iPureIntro. exists (Ptrofs.of_int64 i).
      rewrite Ptrofs.to_int64_of_int64; et.
    - iDestruct "A" as "[% %]". iPureIntro. des. clarify. et.
    Unshelve. et. 
  Qed.

  Lemma val_exists i b ofs q0 z t a : Vptrofs i ⊸ (b, ofs) ** b ↱q0# (z, t, a) 
    -∗ b ↱q0# (z, t, Some (Ptrofs.unsigned i)).
  Proof. Admitted.

  Lemma add_provenance b ofs q sz tg i i'
    :
  b ↱q# (sz, tg, Some i) ** Vptrofs i' ⊸ (b, ofs) -∗ ⌜(i + ofs)%Z = Ptrofs.unsigned i'⌝.
  Proof. 
    iIntros "[BLK PTR]". unfold allocated_with, repr_to. des_ifs.
    iDestruct "BLK" as "[ALLOC [BL PTR']]".
    iCombine "PTR" "PTR'" as "PTR".
    iPoseProof (provenace_dup with "PTR") as "%". clarify.
    iPureIntro.
    unfold Vptrofs in *. des_ifs_safe. unfold Ptrofs.to_int64.
    do 2 autorewrite with ptrArith; auto with ptrArith. nia.
  Qed.

  Lemma sim_encrypt (sk: Sk.t) :
    sim_fnsem wf top2
      ("encrypt", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure encrypt_spec))
      ("encrypt", cfunU (decomp_func sk ce f_encrypt)).
  Proof.
    Opaque repr_to.
    Opaque allocated_with.
    Opaque points_to.
    Opaque ccallU.
    econs; ss. red.
    apply isim_fun_to_tgt; auto. i; ss.
    unfold decomp_func, function_entry_c. ss.
    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[PRE %]".
    iDestruct "PRE" as (opt1 opt2) "[[[[% PTR1] ARG1] PTR2] ARG2]".
    ss. clarify. hred_r. iApply isim_tau_tgt. hred_r. iApply isim_tau_tgt.
    ss. hred_r. des_ifs_safe.
    iApply isim_apc. iExists (Some (2%nat : Ord.t)).
    iPoseProof (val_multimap with "PTR1") as "%".
    iPoseProof (val_multimap with "PTR2") as "%".
    des.
    - des_ifs. hred_r. rewrite <- Heq.
      iApply isim_ccallU_capture1; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src0 st_tgt0) "INV".
      hred_r. iApply isim_tau_tgt. hred_r. iApply isim_tau_tgt.
      hred_r. iApply isim_tau_tgt. ss. hred_r.
      des_ifs. hred_r. rewrite <- Heq2.
      iApply isim_ccallU_capture1; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src1 st_tgt1) "INV".
      hred_r. iApply isim_tau_tgt. hred_r. iApply isim_tau_tgt.
      ss. hred_r.
      des_ifs_safe. hred_r. hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iSplits; ss.
      admit.
      (* iSplitR "ARG2 PTR2". 
      iSplitR "ARG1 PTR1".
      { iPureIntro. f_equal.
        instantiate (1:=Ptrofs.unsigned i0).
        instantiate (1:=Ptrofs.unsigned i).
        autounfold with ptrArith in *. des_ifs_safe. f_equal.
        autorewrite with ptrArith.
        4:{ autorewrite with asdf; ss. auto with asdf. }
        3:{ autorewrite with asdf; ss. auto with asdf. }
        2:{ apply lxor_size; auto with asdf. }
        { f_equal. apply Z.lxor_comm. } }
      { admit. }
      { admit. } *)
    - des_ifs_safe. hred_r. iApply isim_ccallU_capture2; ss; oauto.
      iSplitL "INV ARG1 PTR1". { admit. }
      iIntros (st_src0 st_tgt0 ret) "[INV POST]".
      iDestruct "POST" as (i1) "[% POST]".
      clarify. hred_r. iApply isim_tau_tgt.
      hred_r. iApply isim_tau_tgt. hred_r.
      iApply isim_tau_tgt. ss. hred_r. des_ifs_safe.
      hred_r. rewrite <- Heq. iApply isim_ccallU_capture1; ss; oauto.
      iSplitL "INV"; ss. iIntros (st_src1 st_tgt1) "INV".
      hred_r. iApply isim_tau_tgt. hred_r.
      iApply isim_tau_tgt. ss. hred_r. des_ifs_safe.
      hred_r. hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iSplits; ss.
      admit.
    - des_ifs_safe. hred_r. rewrite <- Heq. iApply isim_ccallU_capture1; ss; oauto.
      iSplitL "INV"; ss. iIntros (st_src1 st_tgt1) "INV".
      hred_r. iApply isim_tau_tgt. hred_r.
      iApply isim_tau_tgt. ss. hred_r. iApply isim_tau_tgt.
      hred_r. des_ifs_safe. hred_r.
      iApply isim_ccallU_capture2; ss; oauto.
      iSplitL "INV ARG1 PTR1". { admit. }
      iIntros (st_src0 st_tgt0 ret) "[INV POST]".
      iDestruct "POST" as (i2) "[% POST]".
      clarify. hred_r. iApply isim_tau_tgt.
      hred_r. iApply isim_tau_tgt. ss. hred_r.
      des_ifs_safe. hred_r.
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iSplits; ss.
      admit.
    - des_ifs_safe. hred_r. iApply isim_ccallU_capture2; ss; oauto.
      iSplitL "INV PTR1 ARG1". { admit. }
      iIntros (st_src0 st_tgt0 ret) "[INV POST]".
      iDestruct "POST" as (i1) "[% LIV]".
      hred_r. iApply isim_tau_tgt. hred_r. iApply isim_tau_tgt.
      hred_r. iApply isim_tau_tgt. ss. hred_r.
      iApply isim_ccallU_capture2; ss; oauto.
      iSplitL "INV PTR2 ARG2". { admit. }
      iIntros (st_src1 st_tgt1 ret0) "[INV POST]".
      iDestruct "POST" as (i2) "[% LIV1]".
      hred_r. iApply isim_tau_tgt. hred_r. iApply isim_tau_tgt.
      hred_r. ss. hred_r. des_ifs_safe. hred_r.
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iSplits; ss.
      admit.
    Unshelve. all: et. 
  Admitted.

  Lemma sim_decrypt (sk: Sk.t) :
    sim_fnsem wf top2
      ("decrypt", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure decrypt_spec))
      ("decrypt", cfunU (decomp_func sk ce f_decrypt)).
  Proof.
  Admitted.

  Require Import ClightDmExprgen.
  From compcertip Require Import Clight.

  Lemma unfold_expr sk ce' e le expr :
    (eval_expr_c sk ce' e le expr : itree Es val)
    =
    match expr with
    | Econst_int i ty => Ret (Vint i)
    | Econst_float f ty => Ret (Vfloat f)
    | Econst_single f ty => Ret (Vsingle f)
    | Econst_long i ty => Ret (Vlong i)
    | Etempvar id ty => (alist_find (string_of_ident id) le)?
    | Eaddrof a ty =>
      _eval_lvalue_c sk ce' e (eval_expr_c sk ce' e le) a
    | Eunop op a ty =>
      v <- eval_expr_c sk ce' e le a;;
      unary_op_c op v (Clight.typeof a)
    | Ebinop op a1 a2 ty =>
      v1 <- eval_expr_c sk ce' e le a1;;
      v2 <- eval_expr_c sk ce' e le a2;;
      binary_op_c ce' op
        v1 (Clight.typeof a1)
        v2 (Clight.typeof a2)
    | Ecast a ty =>
      v <- eval_expr_c sk ce' e le a;;
      sem_cast_c v (Clight.typeof a) ty
    | Esizeof ty1 ty =>
      Ret (Vptrofs (Ptrofs.repr (sizeof ce' ty1)))
    | Ealignof ty1 ty =>
      Ret (Vptrofs (Ptrofs.repr (alignof ce' ty1)))
    | a =>
      vp <- _eval_lvalue_c sk ce' e (eval_expr_c sk ce' e le) a;;
      v <- deref_loc_c (Clight.typeof a) vp;; Ret v
    end.
  Proof. des_ifs. Qed.

  Lemma isim_ccallU_malloc
        o stb fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        I r g f_src f_tgt st_src st_tgt
        (arg: list val) itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL': stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (∃ b ofs, isim (world:=unit) top2 I "xorlist" stb o (g, g, true, true) Q None (st_src, itr_src) (st_tgt, ktr_tgt (Vptr b ofs)))
        (isim (world:=unit) top2 I "xorlist" stb o (r, g, f_src, f_tgt) Q None (st_src, itr_src) (st_tgt, ccallU "malloc" arg >>= ktr_tgt)).
  Proof. Admitted.

  Lemma isim_ccallU_load2
        o stb fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        I r g f_src f_tgt st_src st_tgt
        (arg: memory_chunk * val) itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL': stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (∃ b ofs, isim (world:=unit) top2 I "xorlist" stb o (g, g, true, true) Q None (st_src, itr_src) (st_tgt, ktr_tgt (Vptr b ofs)))
        (isim (world:=unit) top2 I "xorlist" stb o (r, g, f_src, f_tgt) Q None (st_src, itr_src) (st_tgt, ccallU "load" arg >>= ktr_tgt)).
  Proof. Admitted.

  Lemma isim_ccallU_store2
        o stb fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        I r g f_src f_tgt st_src st_tgt
        (arg: memory_chunk * val * val) itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL': stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (∃ b ofs, isim (world:=unit) top2 I "xorlist" stb o (g, g, true, true) Q None (st_src, itr_src) (st_tgt, ktr_tgt (Vptr b ofs)))
        (isim (world:=unit) top2 I "xorlist" stb o (r, g, f_src, f_tgt) Q None (st_src, itr_src) (st_tgt, ccallU "store" arg >>= ktr_tgt)).
  Proof. Admitted.

  Lemma decomp_se sk ce' retty s1 s2 e le
  :
    (decomp_stmt sk ce' retty (Clight.Ssequence s1 s2) e le : itree Es runtime_env)
    = '(e', le', bc, v) <- (tau;; decomp_stmt sk ce' retty s1 e le);;
      match v with
      | Some retval =>
        Ret (e', le', None, v)
      | None =>
        match bc with
        | None =>
          tau;; decomp_stmt sk ce' retty s2 e' le'
        | Some true =>
          tau;; Ret (e', le', bc, None)
        | Some false =>
          tau;; Ret (e', le', bc, None)
        end
      end.
  Proof. ss. Qed.
       
  Lemma sim_insert (sk: Sk.t) :
    sim_fnsem wf top2
      ("add", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure add_spec))
      ("add", cfunU (decomp_func sk ce f_add)).
  Proof.
    Opaque repr_to.
    Opaque allocated_with.
    Opaque points_to.
    Opaque ccallU.
    Opaque free_list_aux.
    Opaque ClightDmgen.blocks_of_env.
    Opaque _sassign_c.
    Opaque _sreturn_c.
    Opaque _eval_lvalue_c.
    Opaque _scall_c.
    Opaque ClightDmExprgen.eval_expr_c.
    init. harg.
    unfold decomp_func, function_entry_c.
    Opaque decomp_stmt.
    ss. des_ifs_safe. mDesAll. clarify.
    steps.
    repeat rewrite decomp_se. steps.
    hide_k.

    rewrite decomp_seq.
    Transparent decomp_stmt. steps.

    set (decomp_stmt _ _).
    Red.prw _red_gen 1 1 0.
    steps.
    hide_k. 
    steps. unhide_k.
    
    steps.
    ss. clarify. rewrite Any.upcast_downcast. ss.
    econs; ss. red.
    apply isim_fun_to_tgt; auto. i; ss.
    unfold decomp_func, function_entry_c. ss.
    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[PRE %]".
    iDestruct "PRE" as (hd_old tl_old) "[[[% HD] TL] XOR]".
    ss. clarify. rewrite Any.upcast_downcast. ss.
    rewrite bind_ret_l. rewrite bind_ret_l. 
    ss. rewrite bind_ret_l. rewrite bind_ret_l.
    rewrite bind_bind. rewrite bind_bind. 
    rewrite bind_tau. iApply isim_tau_tgt. rewrite bind_tau.
    rewrite bind_tau.
    iApply isim_tau_tgt. unfold _scall_c.
    rewrite bind_bind. rewrite bind_bind.
    unfold Cop.classify_fun. unfold Clight.typeof.
    rewrite bind_tau. iApply isim_tau_tgt.
    rewrite bind_bind.
    rewrite unfold_expr.
    unfold _eval_lvalue_c.
    assert (exists i, SkEnv.id2blk (Sk.load_skenv sk) (string_of_ident _malloc) = Some i).
    { admit "". }
    des. rewrite H3.
    replace (alist_find _ _) with (@None (Values.block * type)) by refl.
    rewrite bind_ret_l. unfold deref_loc_c.
    unfold access_mode. unfold typeof. rewrite bind_ret_l.
    rewrite bind_ret_l. unfold eval_exprlist_c.
    rewrite unfold_expr. set (sizeof _ _).
    unfold ce in z. simpl in z. unfold prog in z.
    unfold mkprogram in z. destruct (build_composite_env' _ _) in z.
    simpl in z. 
    Transparent prog_comp_env.
    unfold prog_comp_env in z. unfold build_composite_env in e.
    unfold composites in e.
    simpl in e. clarify. simpl in z.
    assert (z = 16) by refl. rewrite H4.
    do 2 rewrite bind_ret_l. unfold sem_cast_c.
    unfold Cop.classify_cast. unfold tulong. unfold typeof.
    destruct Archi.ptr64; clarify.
    destruct (Vptrofs _) eqn: E; clarify.
    do 2 rewrite bind_ret_l.
    destruct (Ptrofs.eq_dec _ _); clarify.
    assert (SkEnv.blk2id (Sk.load_skenv sk) i = Some (string_of_ident _malloc)). 
    { admit "". }
    replace (Init.Nat.pred _) with i by nia.
    assert (alist_find (string_of_ident _malloc) sk = alist_find (string_of_ident _malloc) xorlist0.xor.(Mod.sk)).
    { admit "". }
    Transparent get_sk.
    Transparent alist_find.
    simpl in H6. 
    Opaque alist_find.
    set (Gfun _) in H6.
    assert (nth_error sk i = Some (string_of_ident _malloc, g↑)).
    { admit "". }
    rewrite H7. unfold unwrapU. rewrite bind_ret_l.
    rewrite Any.upcast_downcast. rewrite bind_ret_l.
    unfold g. rewrite bind_ret_l. unfold type_of_fundef.
    destruct (type_eq _ _); clarify.
    Opaque alist_remove.
    iApply isim_ccallU_malloc.
    1,2,3:admit "".
    iExists xH, Ptrofs.zero.
    rewrite bind_ret_l.
    do 2 rewrite bind_tau. do 2 iApply isim_tau_tgt.
    rewrite bind_bind. rewrite bind_bind.
    hide_k.
    rewrite bind_ret_l. rewrite bind_ret_l.
    rewrite bind_ret_l. do 5 rewrite bind_tau.
    do 3 iApply isim_tau_tgt.
    destruct ("hd_handler" ?[ eq ] "entry") eqn: E2; clarify.
    unfold is_ptr_val. do 3 rewrite bind_bind.
    destruct (_ "hd_handler" _).
    2:{ admit "". }
    rewrite bind_ret_l.
    destruct v3. 1,2,3,4,5: admit "".
    rewrite bind_ret_l.
    unfold tptr. rewrite bind_ret_r.
    iApply isim_ccallU_load2.
    1,2,3:admit "".
    iExists xH, Ptrofs.zero.
    rewrite bind_ret_l.
    do 5 rewrite bind_tau. do 3 iApply isim_tau_tgt.
    do 4 rewrite bind_bind.
    destruct ("tl_handler" ?[ eq ] "hd") eqn: E3; clarify.
    destruct (alist_find _ _).
    rewrite bind_bind.
    rewrite bind_ret_l.
    rewrite bind_bind.
    iApply isim_ccallU_load2.
    1,2,3:admit "".
    unfold tptr. rewrite bind_ret_r.
    do 2 rewrite bind_bind. 

    ss.
    ss.
    unfold alist_remove. 
    unfold type_eq.
    
     clear. clearbody ce.
    hred_r. 

    hred_r.

    des_ifs_safe.
    hred_r.

    set (eval_expr_c _ _ _ _ _) as t.
    Set Printing All.


    unfold ClightDmExprgen.eval_expr_c.
    destruct (Cop.classify_fun _).
     ss.
     hred_r. iApply isim_tau_tgt. hred_r. iApply isim_tau_tgt.
    ss. hred_r. des_ifs_safe.
    iApply isim_apc. iExists (Some (2%nat : Ord.t)).
    iPoseProof (val_multimap with "PTR1") as "%".
    iPoseProof (val_multimap with "PTR2") as "%".
    - des_ifs_safe. hred_r. iApply isim_ccallU_capture2; ss; oauto.
  Admitted.
 
  Lemma sim_delete (sk: alist string Sk.gdef) :
    sim_fnsem wf top2
      ("delete",
        fun_to_tgt (SModSem.mn (SMod.get_modsem Sxor sk)) (GlobalStb sk)
                   {| fsb_fspec := delete_spec; fsb_body := λ _ : option string * Any.t, triggerNB |})
      ("delete", cfunU delete_body).
  Proof.
  Admitted.
 
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
    all: rewrite f_bind_ret_r.
    - apply sim_search.
    - apply sim_delete.
    - apply sim_add.
    - apply sim_decrypt.
    - apply sim_encrypt.
  Qed.

End XorProof.