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
  
  Variable GlobalStb : Sk.sem -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb xorStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).

  Variable sk: Sk.t.
  Hypothesis SKINCL : Sk.extends (xorlist0.xor.(Mod.sk)) sk.
  Hypothesis SKWF : Sk.wf (Sk.canon sk).


  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ⌜True⌝)%I.
  
  Arguments alist_add /.

  Let ce := map (fun '(id, p) => (string_of_ident id, p)) (Maps.PTree.elements (prog_comp_env prog)).


  Arguments ClightDmExprgen.sem_xor_c /.
  Arguments ClightDmExprgen.sem_binarith_c /.
  Arguments ClightDmExprgen.sem_cast_c /.


  (* Lemma val_multimap v b ofs : (v ⊸ (b, ofs)) -∗ ⌜exists i, v = Vptrofs i \/ exists b ofs, v = Vptr b ofs⌝.
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
    (* iIntros "[BLK PTR]". unfold allocated_with, repr_to. des_ifs.
    iDestruct "BLK" as "[ALLOC [BL PTR']]".
    iCombine "PTR" "PTR'" as "PTR".
    iPoseProof (provenace_dup with "PTR") as "%". clarify.
    iPureIntro.
    unfold Vptrofs in *. des_ifs_safe. unfold Ptrofs.to_int64.
    do 2 autorewrite with ptrArith; auto with ptrArith. nia.
  Qed. *)
  Admitted. *)





  (* Lemma sim_encrypt (sk: Sk.t) :
    sim_fnsem wf top2
      ("encrypt", fun_to_tgt "xorlist" (GlobalStb (Sk.canon sk)) (mk_pure encrypt_spec))
      ("encrypt", cfunU (decomp_func (Sk.canon sk) ce f_encrypt)).
  Proof.
    (* Opaque repr_to.
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
    Unshelve. all: et.  *)
  Admitted.

  Lemma sim_decrypt (sk: Sk.t) :
    sim_fnsem wf top2
      ("decrypt", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure decrypt_spec))
      ("decrypt", cfunU (decomp_func sk ce f_decrypt)).
  Proof.

  Admitted. *)

  (* Require Import ClightDmExprgen.
  From compcertip Require Import Clight. *)

  (* Lemma unfold_expr sk ce' e le expr :
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
  Proof. des_ifs. Qed. *)

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
        (arg: memory_chunk * val * val) itr_src (ktr_tgt: unit -> _)
        fuel0
        (STBINCL': stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (isim (world:=unit) top2 I "xorlist" stb o (g, g, true, true) Q None (st_src, itr_src) (st_tgt, ktr_tgt tt))
        (isim (world:=unit) top2 I "xorlist" stb o (r, g, f_src, f_tgt) Q None (st_src, itr_src) (st_tgt, ccallU "store" arg >>= ktr_tgt)).
  Proof. Admitted.

  Lemma isim_ccallU_cmp_ptr
        o stb fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        I r g f_src f_tgt st_src st_tgt
        (arg: comparison * val * val) itr_src (ktr_tgt: bool -> _)
        fuel0
        (STBINCL': stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (∀ b, isim (world:=unit) top2 I "xorlist" stb o (g, g, true, true) Q None (st_src, itr_src) (st_tgt, ktr_tgt b))
        (isim (world:=unit) top2 I "xorlist" stb o (r, g, f_src, f_tgt) Q None (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" arg >>= ktr_tgt)).
  Proof. Admitted.

  Lemma isim_ccallU_encrypt
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
        (∀ i, isim (world:=unit) top2 I "xorlist" stb o (g, g, true, true) Q None (st_src, itr_src) (st_tgt, ktr_tgt (Vlong i)))
        (isim (world:=unit) top2 I "xorlist" stb o (r, g, f_src, f_tgt) Q None (st_src, itr_src) (st_tgt, ccallU "encrypt" arg >>= ktr_tgt)).
  Proof. Admitted.

  Lemma isim_ccallU_decrypt
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
        (∀ i, isim (world:=unit) top2 I "xorlist" stb o (g, g, true, true) Q None (st_src, itr_src) (st_tgt, ktr_tgt (Vlong i)))
        (isim (world:=unit) top2 I "xorlist" stb o (r, g, f_src, f_tgt) Q None (st_src, itr_src) (st_tgt, ccallU "decrypt" arg >>= ktr_tgt)).
  Proof. Admitted.

  (* Lemma decomp_se sk ce' retty s1 s2 e le
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
  Proof. ss. Qed. *)

  Require Import ClightDmExprgen.
  (* need to repaired *)
  Lemma sk_incl_gd (sk0 sk1: Sk.t) gn blk gd: 
    Sk.extends sk0 sk1 ->
    SkEnv.id2blk (Sk.load_skenv (Maps.PTree.elements sk1)) gn = Some blk ->
    Maps.PTree.get (ident_of_string gn) sk0 = Some gd ->
    nth_error (Maps.PTree.elements sk1) blk = Some (ident_of_string gn, gd).
  Proof.
  Admitted.

  Lemma sim_insert :
    sim_fnsem wf top2
      ("add", fun_to_tgt "xorlist" (GlobalStb (Sk.canon sk)) (mk_pure add_spec))
      ("add", cfunU (decomp_func (Sk.canon sk) ce f_add)).
  Proof.
    Opaque repr_to.
    Opaque allocated_with.
    Opaque points_to.
    Opaque get_sk.
    Opaque ccallU.
    Opaque build_composite_env.
    econs; ss. red.

    unfold prog in ce. unfold mkprogram in ce.
    destruct (build_composite_env').
    get_composite ce e.
    apply isim_fun_to_tgt; auto. i; ss.
    unfold decomp_func, function_entry_c. ss.
    init_hide.

    iIntros "[INV PRE]". des_ifs_safe.
    iDestruct "PRE" as "[PRE %]".
    iDestruct "PRE" as (hd_old tl_old) "[[[% HD] TL] XOR]".
    ss. clarify. ss. hred_r.
    unhide HIDDEN. unhide HIDDEN1. unhide HIDDEN2.
    remove_tau.
    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply Sk.incl_incl_env in SKINCLENV.
    unfold Sk.incl_env in SKINCLENV.
    hexploit SKINCLENV.
    { instantiate (2:="malloc"). ss. }
    i. des. ss. rewrite FIND. hred_r. des_ifs_safe. hred_r.
    replace (pred _) with blk by nia.
    erewrite sk_incl_gd; et. hred_r.
    iApply isim_ccallU_malloc.
    1,2,3:admit "".
    iExists xH, Ptrofs.zero.
    remove_tau.
    unhide HIDDEN. unhide HIDDEN0.
    remove_tau. unhide HIDDEN1.
    unhide HIDDEN. remove_tau.
    destruct v1.
    1,2,3,4,5: admit "".
    ss. hred_r.
    iApply isim_ccallU_load2.
    1,2,3:admit "".
    iExists xH, Ptrofs.zero.
    hred_r. unhide HIDDEN1. remove_tau.
    destruct v2.
    1,2,3,4,5: admit "".
    ss. hred_r.
    iApply isim_ccallU_load2.
    1,2,3:admit "".
    iExists xH, Ptrofs.zero.
    hred_r. unhide HIDDEN0. unhide HIDDEN1. remove_tau.
    unfold _sassign_c. ss. remove_tau.
    rewrite Heq2. hred_r. rewrite co_co_members.
    des_ifs. hred_r. destruct v0.
    1,2,4,5,6: admit "".
    hred_r.
    iApply isim_ccallU_store2.
    1,2,3: admit "".
    hred_r. unhide HIDDEN. remove_tau.
    unfold _site_c. remove_tau. des_ifs.
    hred_r.
    iApply isim_ccallU_cmp_ptr.
    1,2,3: admit "".
    iIntros (b1). hred_r.
    des_ifs. 1,3,4,5,6: admit "".
    hred_r. des_ifs.
    - unhide HIDDEN0. unhide HIDDEN2. unfold _sassign_c.
      remove_tau. rewrite Heq2. hred_r. rewrite co_co_members.
      ss. des_ifs. hred_r. iApply isim_ccallU_store2.
      1,2,3: admit "".
      hred_r. unhide HIDDEN. unhide HIDDEN2. unhide HIDDEN3.
      remove_tau. unhide HIDDEN. unfold _sassign_c.
      remove_tau. iApply isim_ccallU_store2.
      1,2,3: admit "". hred_r.
      unhide HIDDEN0. unfold _sassign_c.
      remove_tau. iApply isim_ccallU_store2.
      1,2,3: admit "". hred_r.
      remove_tau. admit "".
    - unhide HIDDEN1. 
      unfold _site_c. remove_tau. des_ifs.
      1,3,4,5,6: admit "".
      hred_r. des_ifs.
      + unhide. remove_tau. unhide.
        remove_tau. unhide.
        unfold _scall_c. ss.
        hexploit SKINCLENV.
        { instantiate (2:="encrypt"). ss. }
        i. des. ss. rewrite FIND0. hred_r. des_ifs_safe.
        remove_tau. 
        replace (pred _) with blk0 by nia.
        erewrite sk_incl_gd; et. hred_r. des_ifs_safe. hred_r. ss.
        iApply isim_ccallU_encrypt.
        1,2,3: admit "".
        iIntros (i8). hred_r. unhide. unfold _sassign_c.
        remove_tau. rewrite Heq2. hred_r. rewrite co_co_members.
        ss. des_ifs. hred_r.
        iApply isim_ccallU_store2.
        1,2,3: admit "". hred_r. unhide.
        remove_tau. unhide. remove_tau. unhide.
        unfold _scall_c. ss.
        hexploit SKINCLENV.
        { instantiate (2:="decrypt"). ss. }
        i. des. ss. rewrite FIND1. hred_r.
        remove_tau. rewrite Heq2. ss. hred_r.
        rewrite co_co_members. ss. des_ifs_safe.
        hred_r. iApply isim_ccallU_load2.
        1,2,3: admit "".
        iExists xH, Ptrofs.zero.
        hred_r.
        replace (pred _) with blk1 by nia.
        erewrite sk_incl_gd; et. hred_r. ss.
        iApply isim_ccallU_decrypt.
        1,2,3: admit "".
        iIntros (i11). hred_r. unhide. remove_tau. unhide.
        remove_tau. unhide. remove_tau. unhide.
        unfold _scall_c. ss.
        des. remove_tau. rewrite FIND0. hred_r.
        replace (pred _) with blk0 by nia.
        des_ifs. hred_r.
        erewrite sk_incl_gd; et. hred_r. ss.
        iApply isim_ccallU_encrypt.
        1,2,3: admit "".
        iIntros (i12). hred_r. unhide. unfold _sassign_c.
        remove_tau. rewrite Heq2. hred_r. rewrite co_co_members. ss. 
        des_ifs_safe. hred_r. iApply isim_ccallU_store2.
        1,2,3: admit "".
        hred_r. unhide. unfold _sassign_c. remove_tau.
        iApply isim_ccallU_store2.
        1,2,3: admit "".
        remove_tau. admit "".
      + unhide. remove_tau. unhide.
        remove_tau. unhide.
        unfold _scall_c. ss.
        hexploit SKINCLENV.
        { instantiate (2:="encrypt"). ss. }
        i. des. ss. rewrite FIND0. hred_r. des_ifs_safe.
        remove_tau. 
        replace (pred _) with blk0 by nia.
        erewrite sk_incl_gd; et. hred_r. des_ifs_safe. hred_r. ss.
        iApply isim_ccallU_encrypt.
        1,2,3: admit "".
        iIntros (i8). hred_r. unhide. unfold _sassign_c.
        remove_tau. rewrite Heq2. hred_r. rewrite co_co_members.
        ss. des_ifs. hred_r.
        iApply isim_ccallU_store2.
        1,2,3: admit "". hred_r. unhide.
        remove_tau. unhide. remove_tau. unhide.
        unfold _scall_c. ss.
        hexploit SKINCLENV.
        { instantiate (2:="decrypt"). ss. }
        i. des. ss. rewrite FIND1. hred_r.
        remove_tau. rewrite Heq2. ss. hred_r.
        rewrite co_co_members. ss. des_ifs_safe.
        hred_r. iApply isim_ccallU_load2.
        1,2,3: admit "".
        iExists xH, Ptrofs.zero.
        hred_r.
        replace (pred _) with blk1 by nia.
        erewrite sk_incl_gd; et. hred_r. ss.
        iApply isim_ccallU_decrypt.
        1,2,3: admit "".
        iIntros (i11). hred_r. unhide. remove_tau. unhide.
        remove_tau. unhide. remove_tau. unhide.
        unfold _scall_c. ss.
        des. remove_tau. rewrite FIND0. hred_r.
        replace (pred _) with blk0 by nia.
        des_ifs_safe. hred_r.
        erewrite sk_incl_gd; et. hred_r. ss.
        iApply isim_ccallU_encrypt.
        1,2,3: admit "".
        iIntros (i12). hred_r. unhide. unfold _sassign_c.
        remove_tau. rewrite Heq2. hred_r. rewrite co_co_members. ss. 
        des_ifs_safe. hred_r. iApply isim_ccallU_store2.
        1,2,3: admit "".
        hred_r. unhide. unfold _sassign_c. remove_tau.
        iApply isim_ccallU_store2.
        1,2,3: admit "".
        remove_tau. admit "".
  Unshelve. all: try exact (Ord.from_nat 0).
  Qed.

  Lemma sim_delete (sk: Sk.t) :
    sim_fnsem wf top2
      ("delete", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure delete_spec))
      ("delete", cfunU (decomp_func sk ce f_delete)).
  Proof.
  Admitted.

  Lemma sim_search (sk: Sk.t) :
    sim_fnsem wf top2
      ("search", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure search_spec))
      ("search", cfunU (decomp_func sk ce f_search)).
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
    - 
    apply sim_search.
    - apply sim_delete.
    - apply sim_insert.
    - apply sim_decrypt.
    - apply sim_encrypt.
    Unshelve. exact tt.
  Qed.

End PROOF.