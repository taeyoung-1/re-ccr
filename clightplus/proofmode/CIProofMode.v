Require Import CoqlibCCR.
Require Import Any.
Require Import ModSem.
Require Import PCM IPM.
Require Import HoareDef STB.
Require Export HSim IProofMode.
Require Import ClightPlusMem1.
From compcert Require Import AST Values Integers Memdata.

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
        ** ⌜(0 < n ≤ Ptrofs.max_unsigned)%Z⌝

        ** (∀ st_src st_tgt vaddr m b,
            ((inv_with le I w0 st_src st_tgt)
            ** (⌜m.(sz) = n /\ m.(blk) = Some b⌝ ** vaddr (↦_m,1) List.repeat Undef (Z.to_nat n) ** vaddr (⊨_m,Local,1) Ptrofs.zero))

            -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt b )))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "salloc" n >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. }
      { ss. } }
    instantiate (1:=n). ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss. iSplit; ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as (m vaddr b) "[[[% %] ?] ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. et.
  Qed.

  Lemma isim_ccallU_sfree
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        size ob itr_src (ktr_tgt: unit -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
        ** (∃ m mvs vaddr, 
           ⌜m.(blk) = ob /\ m.(sz) = size /\ Z.of_nat (List.length mvs) = m.(sz)⌝
           ** vaddr (↦_m,1) mvs
           ** vaddr (⊨_m,Local,1) Ptrofs.zero)
           
        
        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt))
              
            -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt tt)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "sfree" (ob, size) >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=tt). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as (m mvs vaddr) "[[% ?] ?]".
      des. clarify. iExists _,_,_. iFrame. iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? %]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

  Lemma isim_ccallU_load
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        chunk vaddr m tg q0 ofs q1 mvs itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
        ** (vaddr (↦_m,q1) mvs
            ** vaddr (⊨_m,tg,q0) ofs 
            ** ⌜List.length mvs = size_chunk_nat chunk
               /\ bytes_not_pure mvs = false
               /\ chunk <> Many64
               /\ ((size_chunk chunk) | Ptrofs.unsigned ofs)%Z⌝)
                  
        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt) 
             ** (vaddr (↦_m,q1) mvs
                ** vaddr (⊨_m,tg,q0) ofs))

             -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (decode_val chunk mvs))))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "load" (chunk, vaddr) >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=(_, _, _, _, _, _, _, _)). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as "[[? ?] %]".
      des. clarify. iFrame. iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as (v) "[[% ?] ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

  Lemma isim_ccallU_store
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        m chunk vaddr ofs tg q v_new itr_src (ktr_tgt: unit -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
        ** (∃ mvs_old, 
            ⌜length mvs_old = size_chunk_nat chunk
            /\ ((size_chunk chunk) | Ptrofs.unsigned ofs)%Z⌝
            ** vaddr (↦_m,1) mvs_old
            ** vaddr (⊨_m,tg,q) ofs)
        
        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt)
             ** (vaddr (↦_m,1) (encode_val chunk v_new)
                ** vaddr (⊨_m,tg,q) ofs))

            -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt tt)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "store" (chunk, vaddr, v_new) >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=(_, _, _, _, _, _, _)). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as (mvs_old) "[[% ?] ?]".
      des. clarify. iExists _. iFrame. iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as (mvs_new) "[[% ?] ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

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
        
        ** (∀ st_src st_tgt,
            (inv_with le I w0 st_src st_tgt)
            
           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (match c with Ceq | Cle | Cge => true | _ => false end))))
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
        ** (⌜weak_valid m ofs⌝
            ** vaddr (⊨_m,tg,q) ofs)
        
        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt)
              ** vaddr (⊨_m,tg,q) ofs)

            -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt false)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (Ceq, Vnullptr, vaddr) >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=inr (inl (_, _, _, _, _))). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as "[% ?]".
      des. clarify. iFrame. iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as "[% ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

  Lemma isim_ccallU_cmp_ptr2
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr m q tg ofs itr_src (ktr_tgt: bool -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
        ** (⌜weak_valid m ofs⌝
           ** vaddr (⊨_m,tg,q) ofs)
                  
        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt) 
             ** (vaddr (⊨_m,tg,q) ofs))
           
           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt true)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (Cne, Vnullptr, vaddr) >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=inr (inr (inl (_, _, _, _, _)))). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as "[% ?]".
      des. clarify. iFrame. iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as "[% ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

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
        ** (⌜weak_valid m ofs⌝
           ** vaddr (⊨_m,tg,q) ofs)

        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt)
             ** (vaddr (⊨_m,tg,q) ofs))
             
           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt false)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (Ceq, vaddr, Vnullptr) >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=inr (inr (inr (inl (_, _, _, _, _))))). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as "[% ?]".
      des. clarify. iFrame. iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as "[% ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

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
        ** (⌜weak_valid m ofs⌝
           ** vaddr (⊨_m,tg,q) ofs)

        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt) 
             ** (vaddr (⊨_m,tg,q) ofs))

           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt true)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (Cne, vaddr, Vnullptr) >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=inr (inr (inr (inr (inl (_,_,_,_,_)))))). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as "[% ?]".
      des. clarify. iFrame. iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as "[% ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

  Lemma isim_ccallU_cmp_ptr5
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr0 vaddr1 c m ofs0 ofs1 q0 q1 tg
        itr_src (ktr_tgt: bool -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
        ** (⌜weak_valid m ofs0 /\ weak_valid m ofs1⌝
           ** vaddr0 (⊨_m,tg,q0) ofs0
           ** vaddr1 (⊨_m,tg,q1) ofs1)

        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt) 
             ** (vaddr0 (⊨_m,tg,q0) ofs0
                ** vaddr1 (⊨_m,tg,q1) ofs1))
              
          -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (cmp_ofs c (Ptrofs.unsigned ofs0) (Ptrofs.unsigned ofs1)))))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (c, vaddr0, vaddr1) >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=inr (inr (inr (inr (inr (inl (_,_,_,_,_,_,_,_,_))))))). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as "[[% ?] ?]".
      instantiate (5:=vaddr1).
      instantiate (9:=vaddr0).
      des. clarify. iFrame. iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as "[[% ?] ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

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
        ** (⌜m0 #^ m1 /\ valid m0 ofs0 /\ valid m1 ofs1 ⌝
           ** vaddr0 (⊨_m0,tg0,q0) ofs0
           ** vaddr1 (⊨_m1,tg1,q1) ofs1)

        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt)
             ** (vaddr0 (⊨_m0,tg0,q0) ofs0
                ** vaddr1 (⊨_m1,tg1,q1) ofs1))

           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt false)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (Ceq, vaddr0, vaddr1) >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=inr (inr (inr (inr (inr (inr (inl (_,_,_,_,_,_,_,_,_,_)))))))). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as "[[% ?] ?]".
      instantiate (5:=vaddr1).
      instantiate (9:=vaddr0).
      des. clarify. iFrame. iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as "[[% ?] ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

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
         ** (⌜m0 #^ m1 /\ valid m0 ofs0 /\ valid m1 ofs1⌝
            ** vaddr0 (⊨_m0,tg0,q0) ofs0
            ** vaddr1 (⊨_m1,tg1,q1) ofs1)

        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt)
             ** (vaddr0 (⊨_m0,tg0,q0) ofs0
                ** vaddr1 (⊨_m1,tg1,q1) ofs1))
              
              
           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt true)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "cmp_ptr" (Cne, vaddr0, vaddr1) >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=inr (inr (inr (inr (inr (inr (inr (_,_,_,_,_,_,_,_,_,_)))))))). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as "[[% ?] ?]".
      instantiate (5:=vaddr1).
      instantiate (9:=vaddr0).
      des. clarify. iFrame. iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as "[[% ?] ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

  Lemma isim_ccallU_sub_ptr
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        size vaddr0 vaddr1 m ofs0 ofs1 q0 q1 tg
        itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
         ** (⌜(0 < size ≤ Ptrofs.max_signed)%Z
             /\ (Ptrofs.min_signed ≤ Ptrofs.unsigned ofs0 - Ptrofs.unsigned ofs1 ≤ Ptrofs.max_signed)%Z
             /\ weak_valid m ofs0 /\ weak_valid m ofs1⌝
            ** vaddr0 (⊨_m,tg,q0) ofs0
            ** vaddr1 (⊨_m,tg,q1) ofs1)

        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt)
            ** vaddr0 (⊨_m,tg,q0) ofs0
            ** vaddr1 (⊨_m,tg,q1) ofs1)
                
           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (Vptrofs (Ptrofs.repr (Z.quot (Ptrofs.unsigned ofs0 - Ptrofs.unsigned ofs1) size))))))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "sub_ptr" (size, vaddr0, vaddr1) >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=(_,_,_,_,_,_,_,_,_)). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as "[[% ?] ?]".
      instantiate (5:=vaddr1).
      instantiate (9:=vaddr0).
      des. clarify. iFrame. iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as "[[% ?] ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

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
        ** (⌜weak_valid m ofs⌝
            ** vaddr (⊨_m,tg,q) ofs)

        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt)
             ** vaddr (⊨_m,tg,q) ofs)

           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt true)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "non_null?" vaddr >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=(_,_,_,_,_)). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as "[% ?]".
      des. clarify. iFrame. iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as "[% ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

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

        ** (∀ st_src st_tgt vaddr m,
            ((inv_with le I w0 st_src st_tgt)
            ** (⌜m.(sz) = Ptrofs.unsigned n⌝
                ** vaddr (↦_m,1) List.repeat Undef (Z.to_nat (Ptrofs.unsigned n))
                ** vaddr (⊨_m,Dynamic,1) Ptrofs.zero)) 
                    
           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt vaddr)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "malloc" [Vptrofs n] >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as "%".
      des. clarify. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as (m vaddr) "[[% ?] ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. ss.
  Qed.

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
        ** (∃ m mvs, ⌜Z.of_nat (List.length mvs) = m.(sz)⌝
           ** vaddr (↦_m,1) mvs
           ** vaddr (⊨_m,Dynamic,1) Ptrofs.zero)
                  
        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt)) 
            
        -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt Vundef)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "free" [vaddr] >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=tt). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss.
      iDestruct "PRE" as (m mvs) "[[% ?] ?]".
      iExists _,_,_. iFrame.
      des. clarify. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as "%".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame.
  Qed.

  Lemma isim_ccallU_memcpy0
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr' vaddr m_src m_dst mvs_src (al sz: Z) tg tg' qp q q' ofs_src ofs_dst itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
         ** (∃ mvs_dst,
             ⌜List.length mvs_src = List.length mvs_dst
             /\ List.length mvs_dst = Z.to_nat sz
             /\ (al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
             /\ (al | Ptrofs.unsigned ofs_src)%Z
             /\ (al | Ptrofs.unsigned ofs_dst)%Z
             /\ (0 ≤ sz)%Z
             /\ (al | sz)%Z⌝
             ** vaddr' (⊨_m_src,tg',q') ofs_src
             ** vaddr (⊨_m_dst,tg,q) ofs_dst
             ** vaddr' (↦_m_src,qp) mvs_src
             ** vaddr (↦_m_dst,1) mvs_dst)

        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt)
            ** (vaddr' (⊨_m_src,tg',q') ofs_src ** vaddr (⊨_m_dst,tg,q) ofs_dst ** vaddr' (↦_m_src,qp) mvs_src ** vaddr (↦_m_dst,1) mvs_src))
              
           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt Vundef)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "memcpy" (al, sz, [vaddr; vaddr']) >>= ktr_tgt)).
  Proof.
    iIntros "[[H0 H2] H1]".
    iDestruct "H2" as (mvs_dst) "[[[[% H5] H4] H3] H2]".
    destruct H3 as [? [? [? [? [? [? ?]]]]]].
    iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:= inl _). ss. unfold memcpy_hoare0. des_ifs. }
      { ss. unfold memcpy_hoare0. des_ifs. } }
    instantiate (1:=(vaddr, vaddr', tg, tg', qp, q, q', ofs_src, ofs_dst, m_src, m_dst, mvs_src)).
    ss. iFrame. iSplitL "H2".
    - iSplit; ss. iExists _,_,_. iFrame. iPureIntro.
      splits; et.
    - iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
      iDestruct "H0" as "[INV [[[[[% D] C] B] A] %]]".
      subst. iExists _. iSplit; et; iApply "H1"; iFrame.
  Qed.

  Lemma isim_ccallU_memcpy1
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        vaddr m_dst mvs_dst (al sz: Z) tg q ofs_dst itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
         ** (⌜List.length mvs_dst = Z.to_nat sz
             /\ (al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
             /\ (al | Ptrofs.unsigned ofs_dst)%Z
             /\ (0 ≤ sz)%Z
             /\ (al | sz)%Z⌝
             ** vaddr (⊨_m_dst,tg,q) ofs_dst
             ** vaddr (↦_m_dst,1) mvs_dst)

        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt)
            ** (vaddr (⊨_m_dst,tg,q) ofs_dst ** vaddr (↦_m_dst,1) mvs_dst))
              
           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt Vundef)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "memcpy" (al, sz, [vaddr; vaddr]) >>= ktr_tgt)).
  Proof.
    iIntros "[[H0 H2] H1]".
    iDestruct "H2" as "[[% H5] H4]".
    destruct H3 as [? [? [? [? ?]]]].
    iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:= inr _). ss. unfold memcpy_hoare1. des_ifs. }
      { ss. unfold memcpy_hoare1. des_ifs. } }
    instantiate (1:=(vaddr, m_dst, tg, q, ofs_dst, mvs_dst)).
    ss. iFrame. iSplitR "H1".
    - iSplit; ss. iExists _,_. iPureIntro.
      splits; et.
    - iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
      iDestruct "H0" as "[INV [[[% B] A] %]]".
      subst. iExists _. iSplit; et; iApply "H1"; iFrame.
  Qed.

  Lemma isim_ccallU_capture0
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

        ** (∀ st_src st_tgt,
            ((inv_with le I w0 st_src st_tgt))
            
           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt Vnullptr)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "capture" [Vnullptr] >>= ktr_tgt)).
  Proof.
    iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:= inl _). ss. unfold capture_hoare0. des_ifs. }
      { ss. unfold capture_hoare0. des_ifs. } }
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

  Lemma isim_ccallU_capture1
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
         ** ( vaddr (⊨_m,tg,q) ofs)

        ** (∀ st_src st_tgt i,
            (((inv_with le I w0 st_src st_tgt)
              ** (vaddr (⊨_m,tg,q) ofs 
                  ** vaddr (≃_m) (Vptrofs i)))
            
           -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (Vptrofs i)))))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "capture" [vaddr] >>= ktr_tgt)).
  Proof.
    iIntros "[[INV PRE] POST]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:=inr (_,_,_,_,_)). ss. }
      { ss. } }
    ss.
    iSplitL "INV PRE".
    { iFrame. iSplit; ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "POST'".
    iDestruct "POST'" as "[? [POST' %]]".
    iDestruct "POST'" as (i) "[[% ?] ?]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "POST". iFrame. 
  Qed.

End MEM.

Require Import ClightPlusgen.
From compcert Require Import Ctypes Clightdefs.

Global Opaque equiv_prov.
Global Opaque has_offset.
Global Opaque points_to.
Global Opaque ccallU.
Global Opaque get_sk.
Global Opaque build_composite_env'.
Global Opaque build_composite_env.

Global Arguments alist_add /.
Global Arguments ClightPlusgen._sassign_c /.
Global Arguments ClightPlusgen._scall_c /.
Global Arguments ClightPlusgen._site_c /.
Global Arguments ClightPlusExprgen.sem_xor_c /.
Global Arguments ClightPlusExprgen.sem_binarith_c /.
Global Arguments ClightPlusExprgen.sem_cast_c /.

Ltac init_hide :=
    repeat (match goal with
    | [ |- context[hide ?p]] =>
        let H := fresh "HIDDEN" in set (H := hide p) at 1
    end).

Ltac unhide H :=
    unfold H in *;
    unfold hide at 1;
    init_hide;
    clear H.

Tactic Notation "unhide" constr(H) :=
  unhide H.

Tactic Notation "unhide" :=
    repeat (match goal with 
            | |- context[ITree.bind (?H _ _) _] => unhide H
            | |- context[{| _observe := TauF (ITree.bind (?H _ _) _) |}] => unhide H 
            end).

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
  ss; clear e; clear comp_env; unfold Maps.PTree.elements in ce; ss;
  match goal with
  | ce := ?cel |- _ => alist_composites ce cel
  end; clearbody ce.
