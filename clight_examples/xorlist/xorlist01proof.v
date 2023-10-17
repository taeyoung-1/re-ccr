(* Require Import Coqlib. *)
(* Require Import Any. *)
(* Require Import Skeleton. *)
(* Require Import PCM. *)
(* Require Import ModSem. *)
(* Require Import SimModSem. *)
(* Require Import HoareDef. *)
(* Require Import STB. *)
(* Require Import HTactics ProofMode. *)
(* Require Import ConvC2ITree. *)
(* Require Import Clight_Mem1. *)
(* Require Import ClightProofs. *)
(* Require Import ClightPreambles. *)
(* Require Import csyntax. *)
Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import HTactics ProofMode.
Require Import SimModSem.
Require Import Coq.Sorting.Sorted.
Require Import ClightProofs.
Require Import csyntax.
Require Import ConvC2ITree.
Require Import Clight_Mem1.
Require Import ClightPreambles.
Require Import xorlist0.
Require Import xorlist1.

(* From compcertip Require Import Clightdefs. *)

Section XorProof.

  Import CTypeNotation CExpNotation CStmtNotation.
  Local Open Scope cexp_scope.
  Local Open Scope cstmt_scope.
  Local Open Scope ctypes_scope.
  
  (* Context `{CONF: EMSConfig}. *)
  Context `{Σ : GRA.t}.
  Context `{H : @GRA.inG Clight_Mem1.memRA Σ}.
  Context `{H1 : @GRA.inG Clight_Mem1.memRACAP Σ}.
  
  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb xorlist1.xorStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb Clight_Mem1.MemStb) (GlobalStb sk).

  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => True)%I.

  Lemma sim_encrypt (sk: alist string Sk.gdef) :
    sim_fnsem wf top2
      ("encrypt",
        fun_to_tgt (SModSem.mn (SMod.get_modsem Sxor sk)) (GlobalStb sk)
                   {| fsb_fspec := encrypt_spec; fsb_body := λ _ : option string * Any.t, triggerNB |})
      ("encrypt", cfunU xorlist0.encrypt_body).
  Proof.
  Opaque Maps.PTree.set.
  Opaque Maps.PTree.get.
  Opaque decomp_stmt.
    init. harg. destruct x. destruct p as [[v1 v2] mvl1]. mDesAll. des.
    steps. unfold function_entry_c. steps. resolve_seq. 
    unfold is_valid_ptr in ACC. 
    destruct v1;destruct v2;mDesAll;ss;steps.
    - rewrite decomp_builtin. ss. resolve_var.
      resolve_seq.
      rewrite decomp_builtin. ss. resolve_var.
      rewrite decomp_ret. unfold _sreturn_c. steps. resolve_get. resolve_get. steps.
      unfold sem_xor_c, sem_binarith_c, sem_cast_c. steps. astop. steps. force_l. eexists. steps.
      hret tt;ss. iModIntro. iSplit;ss. iSplit;ss.
      iExists (Ptrofs.of_int64 i), (Ptrofs.of_int64 i0).
      iSplits;unfold Vptrofs in *;des_ifs_safe;repeat (rewrite Ptrofs.of_int64_to_int64;ss).
      unfold Vnullptr in *. des_ifs_safe.
    - rewrite decomp_builtin. ss. resolve_var.
      resolve_seq.
      rewrite decomp_builtin. ss. resolve_var.
      astart 1. unfold ccallU. steps. acatch. { apply MEMINCL. stb_tac. auto. }
      hcall (_, _) _ with "".
      { iModIntro. iSplits;ss. }
      { oauto. } mDesAll. des.
      steps.
      rewrite decomp_ret. unfold _sreturn_c. steps. resolve_get. resolve_get. steps.
      unfold sem_xor_c, sem_binarith_c, sem_cast_c. steps. astop. steps. force_l. eexists. steps.
      hret tt;ss. iModIntro. iSplit;ss. iSplit;ss.
      iExists (Ptrofs.of_int64 i), (Ptrofs.of_int64 i1).
      iSplitR "A1";[iSplitL "POST";[iSplitR "POST";[iSplits|]|auto]|];unfold Vptrofs in *;des_ifs_safe;repeat (rewrite Ptrofs.of_int64_to_int64;ss).
      + unfold Vnullptr in *. des_ifs_safe.
      + iExists _, _. iSplits;[..|iApply "POST"];ss.
      + iExists _. iSplits;ss.
    - rewrite decomp_builtin. ss. resolve_var.
      astart 1. unfold ccallU. steps. acatch. { apply MEMINCL. stb_tac. auto. }
      hcall (_, _) _ with "".
      { iModIntro. iSplits;ss. }
      { oauto. } mDesAll. des.
      unfold ccallU. steps. resolve_seq.
      rewrite decomp_builtin. ss. resolve_var.
      rewrite decomp_ret. unfold _sreturn_c. steps. resolve_get. resolve_get. steps.
      unfold sem_xor_c, sem_binarith_c, sem_cast_c. steps. astop. steps. force_l. eexists. steps.
      hret tt;ss. iModIntro. iSplit;ss. iSplit;ss.
      iExists (Ptrofs.of_int64 i1), (Ptrofs.of_int64 i0).
      iSplits;ss.
      iSplitR "A2";[iSplits;ss|];unfold Vptrofs in *;des_ifs_safe;repeat (rewrite Ptrofs.of_int64_to_int64;ss).
      + rewrite Int64.xor_commut. rewrite Ptrofs.xor_commut. unfold Vnullptr in *. des_ifs_safe.
      + iExists _. iSplits;ss.
    - rewrite decomp_builtin. ss. resolve_var.
      astart 2. unfold ccallU. steps. acatch. { apply MEMINCL. stb_tac. auto. }
      hcall (_, _) _ with "".
      { iModIntro. iSplits;ss. }
      { oauto. } mDesAll. des.
      steps. resolve_seq.
      rewrite decomp_builtin. ss. resolve_var.
      unfold ccallU. steps. acatch. { apply MEMINCL. stb_tac. auto. }
      hcall (_, _) _ with "".
      { iModIntro. iSplit;ss. }
      { oauto. } mDesAll. des.
      steps.
      rewrite decomp_ret. unfold _sreturn_c. steps. resolve_get. resolve_get. steps.
      unfold sem_xor_c, sem_binarith_c, sem_cast_c. steps. astop. steps. force_l. eexists. steps.
      hret tt;ss. iModIntro. iSplit;ss. iSplit;ss.
      iExists (Ptrofs.of_int64 i2), (Ptrofs.of_int64 i1).
      iSplitR "A1";[iSplitR "A2";[iSplitR "POST1";[iSplitR "POST"|]|]|];unfold Vptrofs in *;des_ifs_safe;repeat (rewrite Ptrofs.of_int64_to_int64;ss).
      + unfold Int64.xor, Ptrofs.xor. iPureIntro. f_equal. f_equal. unfold Ptrofs.to_int64. f_equal.
        do 2 rewrite Int64.unsigned_repr_eq. rewrite Ptrofs.unsigned_repr_eq.
        replace Ptrofs.modulus with Int64.modulus by auto.
        set (Ptrofs.unsigned (Ptrofs.add i a)) as x. set (Ptrofs.unsigned (Ptrofs.add i0 a2)) as y.
        admit "".
      + iExists _, _. iSplits;[..|iApply "POST"];ss.
      + iExists _, _. iSplits;[..|iApply "POST1"];ss.
      + iExists _. iSplits;ss.
      + iExists _. iSplits;ss.
        Unshelve. all: et. 
  Qed.

  Lemma sim_decrypt (sk: alist string Sk.gdef) :
    sim_fnsem wf top2
      ("decrypt",
        fun_to_tgt (SModSem.mn (SMod.get_modsem Sxor sk)) (GlobalStb sk)
                   {| fsb_fspec := decrypt_spec; fsb_body := λ _ : option string * Any.t, triggerNB |})
      ("decrypt", cfunU decrypt_body).
  Proof.
    init. harg. destruct x. destruct p as [v1 v2]. mDesAll. des.
    steps. unfold function_entry_c. steps. resolve_seq. 
    unfold is_valid_ptr in ACC. 
    destruct v2;mDesAll;ss;steps.
    - rewrite decomp_builtin. ss. resolve_var.
      rewrite decomp_ret. unfold _sreturn_c. steps. resolve_get. resolve_get. steps.
      unfold sem_xor_c, sem_binarith_c, sem_cast_c. steps. astop. steps. force_l. eexists. steps.
      hret tt;ss. iModIntro. iSplit;ss. iSplit;ss.
      iExists (Ptrofs.of_int64 i).
      iSplits;ss. rewrite Int64.xor_commut. rewrite Ptrofs.xor_commut.
      unfold Vptrofs, Vnullptr in *;des_ifs_safe. 
    - rewrite decomp_builtin. ss. resolve_var.
      astart 2. unfold ccallU. steps. acatch. { apply MEMINCL. stb_tac. auto. }
      hcall (_, _) _ with "".
      { iModIntro. iSplits;ss. }
      { oauto. } mDesAll. des.
      steps.
      rewrite decomp_ret. unfold _sreturn_c. steps. resolve_get. resolve_get. steps.
      unfold sem_xor_c, sem_binarith_c, sem_cast_c. steps. astop. steps. force_l. eexists. steps.
      hret tt;ss. iModIntro. iSplit;ss. iSplit;ss.
      iExists (Ptrofs.of_int64 i0).
      iSplitR "A1";[iSplitR "POST"|];unfold Vptrofs in *;des_ifs_safe;repeat (rewrite Ptrofs.of_int64_to_int64;ss).
      + unfold Int64.xor, Ptrofs.xor. iPureIntro. f_equal. f_equal. unfold Ptrofs.to_int64. f_equal.
        do 2 rewrite Int64.unsigned_repr_eq. rewrite Ptrofs.unsigned_repr_eq.
        replace Ptrofs.modulus with Int64.modulus by auto.
        set (Ptrofs.unsigned v1) as x. set (Ptrofs.unsigned (Ptrofs.add i a)) as y.
        admit "".
      + iExists _, _. iSplits;[..|iApply "POST"];ss.
      + iExists _. iSplits;ss.
        Unshelve. et. 
  Qed.

  Lemma sim_insert (sk: alist string Sk.gdef) :
    sim_fnsem wf top2
      ("insert",
        fun_to_tgt (SModSem.mn (SMod.get_modsem Sxor sk)) (GlobalStb sk)
                   {| fsb_fspec := insert_spec; fsb_body := λ _ : option string * Any.t, triggerNB |})
      ("insert", cfunU insert_body).
  Proof.
  Opaque Maps.PTree.set.
  Opaque Maps.PTree.get.
  Opaque decomp_stmt.
    init. harg. destruct x as [[[[[[v_head v_tail] p_head] p_tail] item] from_tail] xs].
    mDesAll. des. steps.
    unfold function_entry_c. steps. resolve_seq.

    rewrite decomp_call. unfold _scall_c. prep.
    repeat (repeat (rewrite Maps.PTree.gso;[|solve [auto]])
            ;first [rewrite Maps.PTree.gss|rewrite Maps.PTree.gempty|use_get]).
    unfold Globalenvs.Genv.find_symbol.
    Compute (length xorlist.global_definitions).
    replace (Maps.PTree.get xorlist._malloc _) with (Some 57%positive) by auto. steps.
    Transparent Globalenvs.Genv.find_funct_ptr Globalenvs.Genv.find_def fold_left Globalenvs.Genv.add_global Ctypes.prog_defs xorlist.prog Globalenvs.Genv.empty_genv Ctypes.prog_public. unfold Globalenvs.Genv.find_funct_ptr, Globalenvs.Genv.find_def in Heq.
    unfold xorlist.prog in Heq. unfold Clightdefs.mkprogram, Clightdefs.build_composite_env' in Heq.
    unfold build_composite_env in Heq. unfold add_composite_definitions in Heq. unfold xorlist.composites in Heq.
    unfold composite_of_def in Heq. Transparent Maps.PTree.get Maps.PTree.set. simpl in Heq. simpl in Heq1. Transparent xorlist.__Node. simpl in Heq1. unfold "cSet" in Heq1.
    Maps.PTree.set = 
λ (A : Type) (p : positive) (x : A) (m : Maps.PTree.tree A),
  match m with
  | Maps.PTree.Empty => Maps.PTree.Nodes (Maps.PTree.set0 p x)
  | Maps.PTree.Nodes m' => Maps.PTree.Nodes (Maps.PTree.set' p x m')
  end
PTree.set = 
fix set (A : Type) (i : positive) (v : A) (m : PTree.t A) {struct i} : PTree.t A :=
  match m with
  | PTree.Leaf =>
      match i with
      | (ii~1)%positive => PTree.Node PTree.Leaf None (set A ii v PTree.Leaf)
      | (ii~0)%positive => PTree.Node (set A ii v PTree.Leaf) None PTree.Leaf
      | 1%positive => PTree.Node PTree.Leaf (Some v) PTree.Leaf
      end
  | PTree.Node l o r =>
      match i with
      | (ii~1)%positive => PTree.Node l o (set A ii v r)
      | (ii~0)%positive => PTree.Node (set A ii v l) o r
      | 1%positive => PTree.Node l (Some v) r
      end
  end
    (* former one is newer *)
    Opaque Maps.PTree.get Maps.PTree.set.
    
    (* rewrite gempty is not working *)
    unfold sem_cast_c. steps.

    astart 2. unfold ccallU. steps. acatch. { apply MEMINCL. stb_tac. auto. }
    hcall (_, _) _ with "".
    { iModIntro. iSplits;ss.  }
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
    eapply SimModSem.adequacy_local2. econs.
    2:{ simpl. reflexivity. }
    i. econstructor 1 with (wf := wf) (le := top2).
    (* kripke order is preorder *)
    { econs. unfold Reflexive. auto. unfold Transitive. auto. }
    (* two module have same name *)
    2:{ simpl. auto. }
    (* if initial resource is well formed, initial condition is satisfied *)
    2:{ exists tt. econs. apply to_semantic. iIntros. auto. }
    (* each functions has simulation relation *)
    econs;cycle 1.
    econs;cycle 1.
    econs;cycle 1.
    econs;cycle 1.
    econs.
    - apply sim_delete.
    - apply sim_insert.
    - apply sim_decrypt.
    - apply sim_encrypt.
  Qed.

End XorProof.