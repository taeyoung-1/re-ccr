Require Import Coqlib.
Require Import Any.
Require Import ModSem.
Require Import PCM IPM.
Require Import HoareDef STB.
Require Export HSim IProofMode.
Require Import ClightDmMem1.
From compcertip Require Import AST Values Integers Memdata.

Section MEM.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.
  Variable world: Type.
  Variable le: relation world.
  Variable I: world -> Any.t -> Any.t -> iProp.

  Variable mn: mname.

  Lemma isim_ccallU_salloc
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        n itr_src (ktr_tgt: block -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** 
                  (∀ st_src st_tgt vaddr m,
                      ((inv_with le I w0 st_src st_tgt)
                        ** (⌜m.(sz) = Z.of_nat n /\ n ≤ Z.to_nat Ptrofs.max_unsigned⌝ ** vaddr ↦m#1≻ List.repeat Undef n ** vaddr ⊨m# 0 ** live_ 1# (m, Local)))
                      -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (m.(blk)))))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "salloc" n >>= ktr_tgt)).
  Proof.
    (* iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. }
      { ss. } }
    instantiate (1:=n).
    ss.
    iSplitL "H0".
    { iSplit; ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [RES %]]".
    iDestruct "RES" as (b vaddr) "[[[% STR] LIV] PTR]".
    des. clarify.
    iExists _. iSplit; ss; et.
    iApply "H1". iFrame. 
  Qed. *)
  Admitted.

  Lemma isim_ccallU_sfree
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        size b itr_src (ktr_tgt: unit -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (∃ m mvl vaddr, vaddr ↦m#1≻ mvl ** vaddr ⊨m# 0 ** live_ 1# (m, Local) ** ⌜m.(blk) = b /\ m.(sz) = size /\ Z.of_nat (List.length mvl) = m.(sz)⌝)
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt)) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt tt)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "sfree" (b, size) >>= ktr_tgt)).
  Proof.
    (* iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. des_ifs. }
      { ss. des_ifs. } }
    instantiate (1:=()).
    ss.
    iSplitL "H0".
    { iDestruct "H0" as "[INV PRE]". iFrame. iSplit; ss.
      iDestruct "PRE" as (m mvl vaddr) "[[STR PTR] %]". des.
      iExists _, _, _.
      iFrame. rewrite H3. rewrite H4. rewrite H5. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [% %]]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "H1". iFrame. 
  Qed. *)
  Admitted.

  Lemma isim_ccallU_load
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        chunk vaddr m q mvs itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (∃ ofs, vaddr ↦m#q≻ mvs ** vaddr ⊨m# ofs ** ⌜List.length mvs = size_chunk_nat chunk /\ ((size_chunk chunk) | ofs)%Z⌝)
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (vaddr ↦m#q≻ mvs)) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (decode_val chunk mvs))))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "load" (chunk, vaddr) >>= ktr_tgt)).
  Proof.
    (* iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. des_ifs_safe. destruct p. ss. }
      { ss. des_ifs_safe. destruct p. ss. } }
    instantiate (1:=(chunk, vaddr, m, q, mvs)).
    ss.
    iSplitL "H0".
    { iDestruct "H0" as "[INV [PRE %]]". iSplitL "INV"; et. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [RES %]]".
    iDestruct "RES" as (v) "[% POST]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "H1". iFrame. 
  Qed. *)
  Admitted.

  Lemma isim_ccallU_store
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        m chunk vaddr v_new itr_src (ktr_tgt: unit -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (∃ mvs_old ofs, ⌜length mvs_old = size_chunk_nat chunk /\ ((size_chunk chunk) | ofs)%Z⌝
                     ** vaddr ↦m#1≻ mvs_old
                     ** vaddr ⊨m# ofs)
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (vaddr ↦m#1≻ (encode_val chunk v_new))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt tt)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "store" (chunk, vaddr, v_new) >>= ktr_tgt)).
  Proof.
    (* iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. des_ifs_safe. destruct p0. ss. }
      { ss. des_ifs_safe. destruct p0. ss. } }
    instantiate (1:=(chunk, vaddr, m, v_new)).
    ss.
    iSplitL "H0".
    { iDestruct "H0" as "[INV PRE]". iFrame. iSplit; ss.
      iDestruct "PRE" as (mvs_old) "[% PRE]". iExists _. iSplit; ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [RES %]]".
    iDestruct "RES" as (v) "[% POST]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "H1". iFrame. 
  Qed. *)
  Admitted.

  Lemma isim_ccallU_cmp_ptr0
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        c itr_src (ktr_tgt: bool -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  **
                  (∀ st_src st_tgt,
                      (inv_with le I w0 st_src st_tgt) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (match c with Ceq | Cle | Cge => true | _ => false end))))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (c, Vnullptr, Vnullptr) >>= ktr_tgt)).
  Proof.
    iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. instantiate(1:=inl _). ss. }
      { ss. } }
    instantiate (1:=(c)).
    ss. iFrame. iSplit; et. 
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [% %]]".
    rewrite H3. des_ifs; iExists _; iSplit; et; iApply "H1"; iFrame.
  Qed.

  Lemma isim_ccallU_cmp_ptr1
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr m q ofs tg itr_src (ktr_tgt: bool -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (weak_valid m vaddr ofs ** live_ q# (m, tg))
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (live_ q# (m, tg))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt false)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (Ceq, Vnullptr, vaddr) >>= ktr_tgt)).
  Proof.
    (* iIntros "[[H0 [% H2]] H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. instantiate(1:=inr (inl _)).
        ss. unfold cmp_ptr_hoare1. des_ifs_safe. destruct p.
        ss. }
      { ss. unfold cmp_ptr_hoare1. des_ifs_safe. destruct p.
        ss. } }
    instantiate (1:=(vaddr, m, q, ofs, tg)).
    ss. iSplitL "H0 H2".
    - iFrame. iSplit; et. 
    - iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
      iDestruct "H0" as "[INV [[% AL] %]]".
      rewrite H4. iExists _. iSplit; et; iApply "H1"; iFrame.
  Qed. *)
  Admitted.

  Lemma isim_ccallU_cmp_ptr2
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr m q tg itr_src (ktr_tgt: bool -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (∃ ofs, weak_valid m vaddr ofs ** live_ q# (m, tg))
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (live_ q# (m, tg))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt true)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (Cne, Vnullptr, vaddr) >>= ktr_tgt)).
  Proof.
    (* iIntros "[[H0 [% H2]] H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. instantiate(1:=inr (inr (inl _))).
        ss. unfold cmp_ptr_hoare2. des_ifs_safe. destruct p.
        ss. }
      { ss. unfold cmp_ptr_hoare2. des_ifs_safe. destruct p.
        ss. } }
    instantiate (1:=(vaddr, m, q, ofs, tg)).
    ss. iSplitL "H0 H2".
    - iFrame. iSplit; et. 
    - iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
      iDestruct "H0" as "[INV [[% AL] %]]".
      rewrite H4. iExists _. iSplit; et; iApply "H1"; iFrame.
  Qed. *)
  Admitted.

  Lemma isim_ccallU_cmp_ptr3
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr m q ofs tg itr_src (ktr_tgt: bool -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (weak_valid m vaddr ofs ** live_ q# (m, tg))
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (live_ q# (m, tg))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt false)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (Ceq, vaddr, Vnullptr) >>= ktr_tgt)).
  Proof.
    (* iIntros "[[H0 [% H2]] H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. instantiate(1:=inr (inr (inr (inl _)))).
        ss. unfold cmp_ptr_hoare3. des_ifs_safe. destruct p.
        ss. }
      { ss. unfold cmp_ptr_hoare3. des_ifs_safe. destruct p.
        ss. } }
    instantiate (1:=(vaddr, m, q, ofs, tg)).
    ss. iSplitL "H0 H2".
    - iFrame. iSplit; et. 
    - iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
      iDestruct "H0" as "[INV [[% AL] %]]".
      rewrite H4. iExists _. iSplit; et; iApply "H1"; iFrame.
  Qed. *)
  Admitted.

  Lemma isim_ccallU_cmp_ptr4
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr m q ofs tg itr_src (ktr_tgt: bool -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (weak_valid m vaddr ofs ** live_ q# (m, tg))
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (live_ q# (m, tg))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt true)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (Cne, vaddr, Vnullptr) >>= ktr_tgt)).
  Proof.
    (* iIntros "[[H0 [% H2]] H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. instantiate(1:=inr (inr (inr (inr (inl _))))).
        ss. unfold cmp_ptr_hoare4. des_ifs_safe. destruct p.
        ss. }
      { ss. unfold cmp_ptr_hoare4. des_ifs_safe. destruct p.
        ss. } }
    instantiate (1:=(vaddr, m, q, ofs, tg)).
    ss. iSplitL "H0 H2".
    - iFrame. iSplit; et. 
    - iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
      iDestruct "H0" as "[INV [[% AL] %]]".
      rewrite H4. iExists _. iSplit; et; iApply "H1"; iFrame.
  Qed. *)
  Admitted.

  Lemma isim_ccallU_cmp_ptr5
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr0 vaddr1 c m ofs0 ofs1 q tg
        itr_src (ktr_tgt: bool -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (weak_valid m vaddr0 ofs0 ** weak_valid m vaddr1 ofs1
                      ** live_ q# (m, tg))
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (live_ q# (m, tg))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (cmp_ofs c ofs0 ofs1))))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (c, vaddr0, vaddr1) >>= ktr_tgt)).
  Proof.
    (* iIntros "[[H0 [[% H3] H2]] H1]". des. iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. instantiate(1:=inr (inr (inr (inr (inr (inl _)))))).
        ss. unfold cmp_ptr_hoare5. des_ifs_safe. destruct p0.
        ss. }
      { ss. unfold cmp_ptr_hoare5. des_ifs_safe. destruct p0.
        ss. } }
    instantiate (1:=(vaddr0, vaddr1, c, m, ofs0, ofs1, q0, q1, tg0, tg1)).
    ss. iSplitL "H0 H2 H3".
    - iFrame. iPureIntro. split; et.
    - iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
      iDestruct "H0" as "[INV [[[% AL'] AL] %]]".
      rewrite H5. iExists _. iSplit; et; iApply "H1"; iFrame.
  Qed. *)
  Admitted.

  Lemma isim_ccallU_cmp_ptr6
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr0 vaddr1 m0 m1 ofs0 ofs1 q0 q1 tg0 tg1
        itr_src (ktr_tgt: bool -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (⌜m0 #^ m1 ⌝
                      ** valid m0 vaddr0 ofs0
                      ** valid m1 vaddr1 ofs1
                      ** live_ q0# (m0, tg0)
                      ** live_ q1# (m1, tg1))
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (live_ q0# (m0, tg0) ** live_ q1# (m1, tg1))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt false)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (Ceq, vaddr0, vaddr1) >>= ktr_tgt)).
  Proof.
    (* iIntros "[[H0 [[% H3] H2]] H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. instantiate(1:=inr (inr (inr (inr (inr (inr (inl _))))))).
        ss. unfold cmp_ptr_hoare6. des_ifs. }
      { ss. unfold cmp_ptr_hoare6. des_ifs. } }
    instantiate (1:=(vaddr0, m0, ofs0, q0, tg0, vaddr1, m1, ofs1, q1, tg1)).
    ss. iSplitL "H0 H2 H3".
    - iFrame. iSplit; et. iExists _, _.
      iFrame. iPureIntro. split; et.
    - iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
      iDestruct "H0" as "[INV [[[% AL'] AL] %]]".
      rewrite H4. iExists _. iSplit; et; iApply "H1"; iFrame.
  Qed. *)
  Admitted.

  Lemma isim_ccallU_cmp_ptr7
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr0 vaddr1 m0 m1 ofs0 ofs1 q0 q1 tg0 tg1
        itr_src (ktr_tgt: bool -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (⌜m0 #^ m1 ⌝
                      ** valid m0 vaddr0 ofs0 ** valid m1 vaddr1 ofs1
                      ** live_ q0# (m0, tg0)
                      ** live_ q1# (m1, tg1))
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (live_ q0# (m0, tg0) ** live_ q1# (m1, tg1))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt true)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (Cne, vaddr0, vaddr1) >>= ktr_tgt)).
  Proof.
    (* iIntros "[[H0 [[% H3] H2]] H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. instantiate(1:=inr (inr (inr (inr (inr (inr (inr _))))))).
        ss. unfold cmp_ptr_hoare7. des_ifs. }
      { ss. unfold cmp_ptr_hoare7. des_ifs. } }
    instantiate (1:=(vaddr0, m0, ofs0, q0, tg0, vaddr1, m1, ofs1, q1, tg1)).
    ss. iSplitL "H0 H2 H3".
    - iFrame. iSplit; et. iExists _, _.
      iFrame. iPureIntro. split; et.
    - iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
      iDestruct "H0" as "[INV [[[% AL'] AL] %]]".
      rewrite H4. iExists _. iSplit; et; iApply "H1"; iFrame.
  Qed. *)
  Admitted.

  Lemma isim_ccallU_sub_ptr
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        size vaddr0 vaddr1 m ofs0 ofs1 q tg
        itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (⌜(0 < size ≤ Ptrofs.max_signed)%Z⌝
                      ** weak_valid m vaddr0 ofs0 ** weak_valid m vaddr1 ofs1
                      ** live_ q# (m, tg))
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (live_ q# (m, tg))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (Vptrofs (Ptrofs.repr (Z.div (ofs0 - ofs1) size))))))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "sub_ptr" (size, vaddr0, vaddr1) >>= ktr_tgt)).
  Proof.
    (* iIntros "[[H0 [[% H3] H2]] H1]". des. iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. des_ifs. }
      { ss. des_ifs. } }
    instantiate (1:= (vaddr0, vaddr1, size, m, ofs0, ofs1, q0, q1, tg0, tg1)).
    ss. iSplitL "H0 H2 H3".
    - iFrame. iPureIntro. splits; et.
    - iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
      iDestruct "H0" as "[INV [[[% AL'] AL] %]]".
      rewrite H7. iExists _. iSplit; et; iApply "H1"; iFrame.
  Qed. *)
  Admitted.

  Lemma isim_ccallU_non_null
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr m ofs q tg
        itr_src (ktr_tgt: bool -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (weak_valid m vaddr ofs ** live_ q# (m, tg))
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (live_ q# (m, tg))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt true)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "non_null?" vaddr >>= ktr_tgt)).
  Proof.
    (* iIntros "[[H0 [% H2]] H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. des_ifs. }
      { ss. des_ifs. } }
    instantiate (1:= (vaddr, m, q, ofs, tg)).
    ss. iSplitL "H0 H2".
    - iFrame. iPureIntro. splits; et.
    - iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
      iDestruct "H0" as "[INV [[% AL] %]]".
      rewrite H4. iExists _. iSplit; et; iApply "H1"; iFrame.
  Qed. *)
  Admitted.

  Lemma isim_ccallU_malloc
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        n itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** ⌜(Ptrofs.unsigned n > 0)%Z⌝
                  **
                  (∀ st_src st_tgt vaddr m,
                      ((inv_with le I w0 st_src st_tgt) ** (⌜m.(sz) = Ptrofs.unsigned n⌝ ** vaddr ↦m#1≻ List.repeat Undef (Z.to_nat (Ptrofs.unsigned n)) ** vaddr ⊨m# 0 ** live_ 1# (m, Dynamic))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt vaddr)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "malloc" [Vptrofs n] >>= ktr_tgt)).
  (* Proof.
    iIntros "[[H0 %] H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. }
      { ss. } }
    instantiate (1:=n).
    ss.
    iSplitL "H0".
    { iSplit; ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [RES %]]".
    iDestruct "RES" as (b vaddr) "[[[% STR] LIV] PTR]".
    des. clarify.
    iExists _. iSplit; ss; et.
    iApply "H1". iFrame. 
  Qed. *)
  Admitted.

  Lemma isim_ccallU_mfree
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (∃ m mvl, vaddr ↦m#1≻ mvl ** vaddr ⊨m# 0 ** live_ 1# (m, Dynamic) ** ⌜Z.of_nat (List.length mvl) = m.(sz)⌝)
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt)) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt Vundef)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "free" [vaddr] >>= ktr_tgt)).
  Proof.
    (* iIntros "[[H0 H2] H1]". iDestruct "H2" as (m mvl) "[[H2 H3]%]".
    iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. des_ifs. }
      { ss. des_ifs. } }
    instantiate (1:=()).
    ss.
    iSplitL "H0 H2 H3".
    { iFrame. iSplit; ss. iExists _, _, _. iFrame. iSplit; ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [% %]]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "H1". iFrame. 
  Qed. *)
  Admitted.

  Lemma isim_ccallU_memcpy
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr_dst vaddr_src m_src m_dst mvs_dst al sz itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (∃ mvs_src, ⌜List.length mvs_src = List.length mvs_dst
                     /\ List.length mvs_dst = sz
                     /\ (al | sz)%Z⌝
                     ** memcpy_resource vaddr_dst vaddr_src m_src m_dst mvs_src mvs_dst)
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (memcpy_resource vaddr_dst vaddr_src m_src m_dst mvs_dst mvs_dst)) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt Vundef)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "memcpy" (al, sz, [vaddr_dst; vaddr_src]) >>= ktr_tgt)).
  Proof.
    iIntros "[[H0 H2] H1]".
    iDestruct "H2" as (mvs_src) "[% H2]".
    iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. des_ifs. }
      { ss. des_ifs. } }
    instantiate (1:=(vaddr_dst, vaddr_src, m_src, m_dst, mvs_dst)).
    ss. iSplitL "H0 H2".
    - iFrame. iSplit; ss. iExists _,_,_. iFrame. iPureIntro.
      split; et.
    - iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
      iDestruct "H0" as "[INV [[% AL] %]]".
      rewrite H4. iExists _. iSplit; et; iApply "H1"; iFrame.
  Qed.

  Lemma isim_ccallU_capture1
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt)) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt Vnullptr)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "capture" [Vnullptr] >>= ktr_tgt)).
  Proof.
    iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:= inl _). ss. unfold capture_hoare1. des_ifs. }
      { ss. unfold capture_hoare1. des_ifs. } }
    instantiate (1:=()).
    ss.
    iSplitL "H0".
    { iSplit; ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [% %]]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "H1". iFrame.
  Qed.

  Lemma isim_ccallU_capture2
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr m q ofs tg itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** vaddr ⊨m# ofs ** live_ q# (m, tg)
                  **
                  (∀ st_src st_tgt i,
                      (((inv_with le I w0 st_src st_tgt) ** (live_ q# (m, tg) ** vaddr (≃_m) (Ptrofs.unsigned i))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (Vptrofs i)))))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "capture" [vaddr] >>= ktr_tgt)).
  Proof.
    (* iIntros "[[H0 H2] H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. instantiate (1:= inr _).
        ss. unfold capture_hoare2. des_ifs_safe. destruct p. ss. }
      { ss. unfold capture_hoare2. des_ifs_safe. destruct p. ss. } }
    instantiate (1:=(vaddr, m, q, ofs, tg)).
    ss.
    iSplitL "H0 H2".
    { iFrame. iPureIntro. et. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [RES %]]".
    iDestruct "RES" as (i) "[[% POST'] POST]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "H1". iSplitL "INV"; iFrame.
  Qed. *)
  Admitted.

End MEM.

Require Import ClightDmgen.
From compcertip Require Import Ctypes.

Ltac init_hide :=
    repeat (match goal with
    | [ |- context[@hide ?A ?a]] =>
        let H := fresh "HIDDEN" in set (H := @hide A a) at 1
    end).

Ltac unhide H :=
    unfold H in *;
    unfold hide at 1;
    init_hide;
    clear H.

Tactic Notation "unhide" constr(H) :=
  unhide H.

Tactic Notation "unhide" :=
    repeat match goal with | |- context[ITree.bind (?H _ _) _] =>
    unhide H end.

Ltac remove_tau :=
    repeat (ss; hred_r; iApply isim_tau_tgt; ss; hred_r).

Lemma unfold_build_composite_env: forall x,
  build_composite_env x =
  add_composite_definitions (Maps.PTree.empty composite) x.
Proof.
  reflexivity.
Qed.

Ltac alist_composites ce cel :=
  match cel with
  | (?name, Build_composite ?su ?mem ?attr ?size ?align ?rank _ _ _) :: ?tl =>
    pose (s_size := size);
    vm_compute in s_size;
    let s_align := fresh in
    pose (s_align := align);
    vm_compute in s_align;
    let Hco := fresh in
    (assert (Hco: exists co, alist_find name ce = Some co /\
    co_su co = su /\ co_members co = mem /\ co_attr co = attr /\
    co_sizeof co = s_size /\ co_alignof co = s_align /\ co_rank co = rank)
    by now subst ce; ss; eexists; repeat (split; try reflexivity));
    let co := fresh "co" in
    let get_co := fresh "get_co" in
    let co_co_su := fresh "co_co_su" in
    let co_co_members := fresh "co_co_members" in
    let co_co_attr := fresh "co_co_attr" in
    let co_co_sizeof := fresh "co_co_sizeof" in
    let co_co_alignof := fresh "co_co_alignof" in
    let co_co_rank := fresh "co_co_rank" in
    destruct Hco as [co [get_co
      [co_co_su [co_co_members [co_co_attr [co_co_sizeof
      [co_co_alignof co_co_rank]]]]]]];
    unfold s_size in co_co_sizeof;
    unfold s_align in co_co_alignof;
    clear s_size;
    clear s_align;
    match tl with
    | [] => idtac
    | _ => alist_composites ce tl
    end
  end.

Ltac get_composite ce e :=
  let comp_env := fresh in 
  match goal with
  | e: build_composite_env ?composites = Errors.OK _ |- _ =>
    pose (comp_env := unfold_build_composite_env composites);
    rewrite e in comp_env; ss
  end;
  let comp_env' := fresh in
  inversion comp_env as [comp_env']; clarify;
  ss; clear e; clear comp_env;
  match goal with
  | ce := ?cel |- _ => alist_composites ce cel
  end; clearbody ce.