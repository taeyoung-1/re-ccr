Require Import Coqlib.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import Any.
Require Import ModSem.
Require Import ModSemE.
Require Import ClightDmMem1.
From compcert Require Export Ctypes Values AST Memdata Integers.

Set Implicit Arguments.

Section PROP.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition vlist_add (x: val) (l : list val) (at_tail: val) : list val :=
    if Val.eq at_tail Vzero then x :: l else snoc l x.

  Definition vlist_delete (l: list val) (from_tail: val) (default: val) : val * list val :=
    if Val.eq from_tail Vzero then (hd default l, tl l)
    else (last l default, removelast l).

  Definition check_inbound (l: list val) (from_tail: val) (index: val) : option nat :=
    match index with
    | Vint i =>
      if negb (Coqlib.zle 0 (Int.unsigned i) && Coqlib.zlt (Int.unsigned i) (Z.of_nat (List.length l)))
      then None
      else if Val.eq Vzero from_tail then Some (Z.to_nat (Int.unsigned i))
           else Some (List.length l - Z.to_nat (Int.unsigned i))
    | Vlong i => 
      if negb (Coqlib.zle 0 (Int64.unsigned i) && Coqlib.zlt (Int64.unsigned i) (Z.of_nat (List.length l)))
      then None
      else if Val.eq Vzero from_tail then Some (Z.to_nat (Int64.unsigned i))
           else Some (List.length l - Z.to_nat (Int64.unsigned i))
    | _ => None
    end.

    Definition ptr_equiv (p q: val) : iProp :=
    (⌜p = q⌝ ∨ (∃ i m1 m2, p (≃_m1) i ** q (≃_m2) i))%I.

    Definition xor_live (p: val) (q: Qp) : iProp :=
    (⌜p = Vnullptr⌝ ∨ ∃ m, p (⊨_m,Dynamic,q) Ptrofs.zero)%I.

     (* is_xorlist represents the figure below    *)
     (*    ll_h                              ll_t *)
     (*     |                                 |   *)
     (*     v                                 v   *)
     (* xs  - - - - - - - - - - - - - - - - - -   *)

  Fixpoint frag_xorlist (q: Qp) (hd_prev hd tl tl_next: val) (xs : list val) {struct xs} : iProp :=
    match xs with
    | [] => (ptr_equiv hd_prev tl ** ptr_equiv hd tl_next)
    | Vlong a :: xs' =>
        ∃ i_prev i_next m_prev m_hd,
          ⌜m_hd.(sz) = (size_chunk Mint64 + size_chunk Mptr)%Z⌝
          ** hd_prev (≃_m_prev) i_prev
          ** hd (⊨_m_hd,Dynamic,q) Ptrofs.zero
          ** hd (↦_m_hd,q) (encode_val Mint64 (Vlong a) ++ encode_val Mptr (Vptrofs (Ptrofs.xor i_prev i_next)))
          ** frag_xorlist q hd (Vptrofs i_next) tl tl_next xs'
    | _ => False
    end%I.

  Lemma unfold_frag_xorlist (q: Qp) (hd_prev hd tl tl_next: val) (xs : list val) :
  frag_xorlist q hd_prev hd tl tl_next xs =
    match xs with
    | [] => (ptr_equiv hd_prev tl ** ptr_equiv hd tl_next)
    | Vlong a :: xs' =>
        ∃ i_prev i_next m_prev m_hd,
          ⌜m_hd.(sz) = (size_chunk Mint64 + size_chunk Mptr)%Z⌝
          ** hd_prev (≃_m_prev) i_prev
          ** hd (⊨_m_hd,Dynamic,q) Ptrofs.zero
          ** hd (↦_m_hd,q) (encode_val Mint64 (Vlong a) ++ encode_val Mptr (Vptrofs (Ptrofs.xor i_prev i_next)))
          ** frag_xorlist q hd (Vptrofs i_next) tl tl_next xs'
    | _ => False
    end%I.
  Proof. des_ifs. Qed.

  Definition full_xorlist q hd_hdl tl_hdl xs : iProp :=
    (∃ m_hd_hdl m_tl_hdl hd tl ofs_hd_hdl ofs_tl_hdl tg_hd_hdl tg_tl_hdl,
    hd_hdl (↦_m_hd_hdl,q) (encode_val Mptr hd)
    ** hd_hdl (⊨_m_hd_hdl,tg_hd_hdl,q) ofs_hd_hdl
    ** ⌜((size_chunk Mptr) | Ptrofs.unsigned ofs_hd_hdl)%Z⌝
    ** tl_hdl (↦_m_tl_hdl,q) (encode_val Mptr tl)
    ** tl_hdl (⊨_m_tl_hdl,tg_tl_hdl,q) ofs_tl_hdl
    ** ⌜((size_chunk Mptr) | Ptrofs.unsigned ofs_tl_hdl)%Z⌝
    ** frag_xorlist q Vnullptr hd tl Vnullptr xs)%I.

  (* Example xorlist_example1 q p1 p2 p3 m1 m2 m3 i1 i2 i3:
  (p1 ↦m1#q≻ (encode_val Mint64 (Vlong Int64.one) ++ encode_val Mint64 (Vptrofs (Ptrofs.repr i2)))
  ** p1 (≃_ m1) i1
  ** live_ q# (m1, Dynamic)
  ** p1 ⊨m1# 0
  ** ⌜m1.(sz) = (size_chunk Mint64 + size_chunk Mptr)%Z⌝)

  ** (p2 ↦m2#q≻ (encode_val Mint64 (Vlong Int64.one) ++ encode_val Mint64 (Vptrofs (Ptrofs.repr (Z.lxor i1 i3))))
     ** p2 (≃_ m2) i2
     ** live_ q# (m2, Dynamic)
     ** p2 ⊨m2# 0
     ** ⌜m2.(sz) = (size_chunk Mint64 + size_chunk Mptr)%Z⌝)

  ** (p3 ↦m3#q≻ (encode_val Mint64 (Vlong Int64.one) ++ encode_val Mint64 (Vptrofs (Ptrofs.repr i2)))
     ** p3 (≃_ m3) i3
     ** live_ q# (m3, Dynamic)
     ** p3 ⊨m3# 0
     ** ⌜m3.(sz) = (size_chunk Mint64 + size_chunk Mptr)%Z⌝)

  ⊢ full_xorlist q p1 p3 [Vlong Int64.one;Vlong Int64.one;Vlong Int64.one].
  Proof.
    iIntros "[[N1 N2] N3]".
    iDestruct "N1" as "[[[[n1_point n1_addr] n1_live] n1_ofs] %]".
    iDestruct "N2" as "[[[[n2_point n2_addr] n2_live] n2_ofs] %]".
    iDestruct "N3" as "[[[[n3_point n3_addr] n3_live] n3_ofs] %]".
    unfold full_xorlist. simpl.
    destruct (Val.eq Vnullptr Vnullptr) eqn:?; clarify.
    iPoseProof (capture_dup with "n2_addr") as "[n2_addr_b n2_addr_f]".
    iPoseProof (points_to_notnull with "n1_point") as "%".
    iPoseProof (points_to_notnull with "n2_point") as "%".
    iPoseProof (points_to_notnull with "n3_point") as "%".
    iExists _,_,_.
    iSplitL "n1_point n1_live n1_ofs n2_addr_f".
    { iSplitR "n2_addr_f". iSplit; try rewrite H3. iSplitR "n1_live". iSplitR "n1_ofs".
      { iApply "n1_point". }
      { iApply "n1_ofs". }
      { iApply "n1_live". }
      { simpl. iPureIntro. reflexivity. }
      { iPoseProof (captured_address_not_zero with "n2_addr_f") as "%".
        destruct (i2 =? 0)%Z eqn: ?.
        { exfalso. apply Z.eqb_eq in Heqb. clarify. }
        { iExists _. iApply "n2_addr_f". } } }
    destruct (Val.eq Vnullptr p1) eqn: ?; clarify.
    iExists _,_,_,_,_.
    iSplitL "n2_point n2_live n2_ofs n1_addr n3_addr".
    { iSplitR "n3_addr". iSplitR "n1_addr".
      iSplit; try rewrite H4.
      iSplitR "n2_live". iSplitR "n2_ofs".
      { iApply "n2_point". }
      { iApply "n2_ofs". }
      { iApply "n2_live". }
      { simpl. iPureIntro. reflexivity. }
      { iApply "n1_addr". }
      { rewrite <- Z.lxor_assoc. rewrite Z.lxor_nilpotent.
        rewrite Z.lxor_0_l.
        iPoseProof (captured_address_not_zero with "n3_addr") as "%".
        destruct (i3 =? 0)%Z eqn: ?.
        { exfalso. apply Z.eqb_eq in Heqb. clarify. }
        { iExists _. iApply "n3_addr". } } }
    destruct (Val.eq Vnullptr p2) eqn: ?; clarify.
    iExists _,_,_,_,_.
    iSplitR "".
    iSplitR "". iSplitR "n2_addr_b".
    iSplit; try rewrite H5.
    iSplitR "n3_live". iSplitR "n3_ofs".
    { iApply "n3_point". }
    { iApply "n3_ofs". }
    { iApply "n3_live". }
    { simpl. iPureIntro. reflexivity. }
    { iApply "n2_addr_b". }
    { rewrite Z.lxor_nilpotent. simpl. ss. }
    { iPureIntro. et. }
  Qed. *)

  (* Example xorlist_example2 q p2 m2:
  p2 ↦m2#q≻ (encode_val Mint64 (Vlong Int64.one) ++ encode_val Mint64 (Vptrofs Ptrofs.zero))
  ** live_ q# (m2, Dynamic)
  ** p2 ⊨m2# 0
  ** ⌜m2.(sz) = (size_chunk Mint64 + size_chunk Mptr)%Z⌝
  ⊢ full_xorlist q p2 p2 [Vlong Int64.one].
  Proof.
    iIntros "[[[d e] f] %]".
    unfold full_xorlist. simpl.
    destruct (Val.eq Vnullptr Vnullptr); clarify.
    iExists _,_,_. 
    iPoseProof (offset_dup with "f") as "[f f']".
    iSplitR "f'". iSplitR "".
    iSplitR "". iSplitR "e". iSplitR "f".
    { iApply "d". }
    { iApply "f". }
    { iApply "e". }
    { simpl. iPureIntro. ss. }
    { simpl. iPureIntro. ss. }
    { simpl. iPureIntro. ss. }
  Qed. *)
    
  Lemma capture_unique'
      vaddr m1 m2 i j
    :
      vaddr (≃_m1) i ** vaddr (≃_m2) j ⊢ ⌜i = j⌝.
  Proof.
    iIntros "[A B]".
    unfold captured_to.
    des_ifs.
    - iDestruct "A" as "%".
      iDestruct "B" as "%".
      clarify.
    - iDestruct "A" as "[A A']".
      iDestruct "A'" as (a) "[A' %]".
      iDestruct "B" as "[B B']".
      iDestruct "B'" as (c) "[B' %]".
      des. clarify. rewrite H4.
      iCombine "A' B'" as "C".
      iOwnWf "C" as wfc.
      iPureIntro. ur in wfc. specialize (wfc (blk m2)).
      ur in wfc.
      Transparent _has_base.
      unfold _has_base in *.
      des_ifs.
      admit.
  Admitted.

  Lemma equiv_refl p
    : ⊢ ptr_equiv p p.
  Proof. iIntros. iLeft. clarify. Qed.

  Lemma equiv_sym p q
    : ptr_equiv p q ⊢ ptr_equiv q p.
  Proof.
    iIntros "[%|A]"; [iLeft; clarify|].
    iDestruct "A" as (i m1 m2) "[A A']". iRight. iExists _,_,_. iFrame.
  Qed.

  Lemma equiv_trans p q r
    : ptr_equiv p q ** ptr_equiv q r 
    ⊢ ptr_equiv p r.
  Proof.
    iIntros "[[%|A] [%|B]]".
    - clarify. iLeft. ss.
    - iDestruct "B" as (i m1 m2) "[A B]". iRight. clarify.
      iExists _,_,_. iFrame.
    - iDestruct "A" as (i m1 m2) "[A B]". iRight. clarify.
      iExists _,_,_. iFrame.
    - iDestruct "A" as (i m1 m2) "[A A']". 
      iDestruct "B" as (i' m1' m2') "[B B']". 
      iCombine "A' B" as "A'".
      iPoseProof (capture_unique' with "A'") as "%".
      clarify. iRight. iExists _,_,_. iFrame.
  Qed.

  Lemma equiv_dup p q
    : ptr_equiv p q
    ⊢ ptr_equiv p q ** ptr_equiv p q.
  Proof.
    iIntros "[%|A]".
    - clarify. iSplitL.
      + iLeft. clarify.
      + iLeft. clarify.
    - iDestruct "A" as (i m1 m2) "[A B]".
      iPoseProof (capture_dup with "A") as "[A A']".
      iPoseProof (capture_dup with "B") as "[B B']".
      iSplitL "A B"; iRight; iExists _,_,_; iFrame.
  Qed.

  Lemma equiv_capture p q i m
    : 
      ptr_equiv p q ** q (≃_m) i
      ⊢ ∃ m, p (≃_m) i.
  Proof.
    iIntros "[[%|a] cap]".
    - iExists _. clarify.
    - iDestruct "a" as (i0 m1 m2) "[p q]".
      iCombine "cap q" as "c".
      iPoseProof (capture_unique' with "c") as "%".
      clarify. 
      iExists _. et.
  Qed.

  (* Lemma equiv_comm' p f q :
    xor_live p f ** ptr_equiv p q ⊢ xor_live q f.
  Proof.
    iIntros "[[%|A] [%|B]]".
    - clarify. iLeft. ss.
    - iDestruct "B" as (i m1 m2) "[B B']".
      clarify. replace i with Ptrofs.zero by admit. *)

  (* TODO: have to impove lemma *)
  Lemma alive_door p m tg f:
      p (⊨_m,tg,f) Ptrofs.zero 
      ⊢ p (⊨_m,tg,f) Ptrofs.zero ** (∀q m' tg' f', (q (⊨_m',tg',f') Ptrofs.zero ** ptr_equiv p q) -* ⌜p = q⌝).
  Proof.
  Admitted.

  Lemma equiv_rel p q m i :
      p (≃_m) i ** ptr_equiv p q
      ⊢ ∃ m, q (≃_m) i.
  Proof.
    iIntros "[A [%|B]]".
    - clarify. iExists _. iFrame.
    - iDestruct "B" as (i0 m1 m2) "[B B']".
      iCombine "A B" as "C".
      iPoseProof (capture_unique' with "C") as "%".
      clarify. iExists _. iFrame.
  Qed.

  Lemma frag_xorlist_replace_prev q hd_prev hd_prev' hd tl tl_next xs:
      frag_xorlist q hd_prev hd tl tl_next xs
      ** ptr_equiv hd_prev hd_prev'
      ⊢ frag_xorlist q hd_prev' hd tl tl_next xs.
  Proof.
    ginduction xs; i.
    - ss. iIntros "[[A B] C]".
      iPoseProof (equiv_sym with "C") as "C".
      iCombine "C A" as "C".
      iPoseProof (equiv_trans with "C") as "C".
      iFrame.
    - iIntros "[A B]". ss.
      destruct a; try solve [iDestruct "A" as "%"; clarify].
      iDestruct "A" as (i_prev i_next m_prev m_hd) "[[[[% hd_addr] hd_ofs] hd_point] LIST]".
      iCombine "hd_addr B" as "hd".
      iPoseProof (equiv_rel with "hd") as "hd".
      iDestruct "hd" as (m) "hd_addr".
      iExists _,_,_,_.
      iFrame. clarify.
  Qed.

  Lemma frag_xorlist_replace_next q hd_prev hd tl tl_next tl_next' xs:
      frag_xorlist q hd_prev hd tl tl_next xs
      ** ptr_equiv tl_next tl_next'
      ⊢ frag_xorlist q hd_prev hd tl tl_next' xs.
  Proof.
    ginduction xs; i.
    - ss. iIntros "[[A B] C]".
      iFrame.
      iCombine "B C" as "C".
      iPoseProof (equiv_trans with "C") as "C".
      iFrame.
    - iIntros "[A B]". ss.
      destruct a; try solve [iDestruct "A" as "%"; clarify].
      iDestruct "A" as (i_prev i_next m_prev m_hd) "[[[[% hd_addr] hd_ofs] hd_point] LIST]".
      iCombine "LIST B" as "LIST".
      iPoseProof (IHxs with "LIST") as "LIST".
      iExists _,_,_,_.
      iFrame. clarify.
  Qed.

  (* Lemma frag_xorlist_snoc m_hd mid_next' q i i_prev i_next hd_prev hd mid xs0 m_prev:
      sz m_hd = (8 + size_chunk Mptr)%Z ->
      mid_next' (⊨_m_hd, Dynamic, q) Ptrofs.zero
      ** mid_next' (↦_m_hd,
                   q) (inj_bytes (encode_int 8 (Int64.unsigned i)) ++
                       encode_val Mptr (Vptrofs (Ptrofs.xor i_prev i_next)))
      ** frag_xorlist q hd_prev hd mid mid_next' xs0
      ** mid (≃_m_prev) i_prev
      ⊢ frag_xorlist q hd_prev hd mid_next (Vptrofs i_next) (xs0 ++ [Vlong i]). *)

  Lemma concat_xorlist q hd_prev hd tl tl_next mid mid' mid_next mid_next' xs0 xs1 :
      frag_xorlist q hd_prev hd mid mid_next xs0
      ** frag_xorlist q mid' mid_next' tl tl_next xs1
      ** ptr_equiv mid mid'
      ** ptr_equiv mid_next mid_next'
      ⊢ ∃ hd' tl',
        ptr_equiv hd hd'
        ** ptr_equiv tl tl'
        ** frag_xorlist q hd_prev hd' tl' tl_next (xs0 ++ xs1).
  Proof.
    revert q hd_prev hd tl tl_next mid mid' mid_next mid_next' xs0.
    induction xs1; i; ss.
    - iIntros "[[[A [B C]] D] E]".
      rewrite app_nil_r.
      iCombine "E C" as "E".
      iPoseProof (equiv_trans with "E") as "E".
      iCombine "A E" as "E".
      iPoseProof (frag_xorlist_replace_next with "E") as "E".
      iCombine "D B" as "D".
      iPoseProof (equiv_trans with "D") as "D".
      iPoseProof (equiv_sym with "D") as "D".
      iExists _,_. iFrame.
      iApply equiv_refl.
    - iIntros "A".
      replace (xs0 ++ a :: xs1) with ((xs0 ++ [a]) ++ xs1).
      2:{ rewrite (cons_middle a xs0 xs1). rewrite app_assoc. et. }
      destruct a; try solve [iDestruct "A" as "[[[c %] b] a]"; clarify].
      iDestruct "A" as "[[[D C] B] A]".
      iDestruct "C" as (i_prev i_next m_prev m_hd) "[[[[% prev_addr] hd_ofs] hd_point] C]".
      iApply IHxs1.
      instantiate (1:= (Vptrofs i_next)).
      iPoseProof (equiv_dup with "A") as "[A A']".
      iFrame. 
      iSplitL.
      2:{ iApply equiv_refl. }
      iCombine "D A" as "A".
      iPoseProof (frag_xorlist_replace_next with "A") as "A".
      iPoseProof (equiv_sym with "B") as "B".
      iCombine "prev_addr B" as "B".
      iPoseProof (equiv_rel with "B") as "B".
      clear m_prev.
      iDestruct "B" as (m_prev) "B".

(* 
      

      instantiate (1:= ()).
      iSplitR
      
      iCombine "A B" as "A".
      iCombine "A C" as "A".
      iCombine "A D" as "A".
      iPoseProof (IHxs0 with "A") as "A".
      iDestruct "A" as (hd_next) "[equiv A]".

      destruct xs0.
      + admit.
      + ss. destruct v; try solve [iDestruct "A" as "%"; clarify].
        iDestruct "A" as (i_prev' i_next' m_prev' m_hd') "[[[[% hd_addr] next_ofs] next_point] C]".
        iPoseProof (alive_door with "next_ofs") as "[next_ofs door]".
      destruct xs0.
      + admit.
      + ss. destruct v; try solve [iDestruct "A" as "%"; clarify].
        iDestruct "A" as (i_prev' i_next' m_prev' m_hd') "[[[[% hd_addr] next_ofs] next_point] C]".
        iPoseProof (alive_door with "next_ofs") as "[next_ofs door]".
        iAssert (frag_xorlist q hd (Vptrofs i_next) mid mid_next (Vlong i0 :: xs0))
          with "[C next_point next_ofs hd_addr]" as "LIST".
        { ss. iExists _,_,_,_. iFrame. ss. }
        iCombine "LIST B" as "C".
        iPoseProof (IHxs0 with "C") as "C".
        iDestruct "C" as (hd' hd_next' tl_next' tl') "[[[[equiv1 equiv2] equiv3] equiv4] C]".
        iDestruct "C" as (? ? ? ?) "[[[[% hd_addr] next_ofs] next_point] C]".
        iCombine "next_ofs equiv2" as "T".
        iAssert (⌜Vptrofs i_next = hd_next'⌝)%I with "[door T]" as "%".
        { iApply "door". ss. }
        iExists hd_prev,hd,tl_next',tl'. 
        iSplitL "". { admit. }
        iExists _,_,_,_. 
        iSplitL "prev_addr hd_ofs hd_point".
        { iFrame. ss. }
        iExists _,_,_,_. iSplitR "C". 2:{ rewrite H6. iFrame. } 
        rewrite H6. iFrame. iDestruct "T" as "[T T']". iFrame. *)
  Admitted.


  Lemma rev_xorlist q hd tl xs
    : frag_xorlist q Vnullptr hd tl Vnullptr xs
      ⊢ frag_xorlist q Vnullptr tl hd Vnullptr (rev xs).
  Proof.
    revert q hd tl.
    induction xs; i; ss.
  Admitted.

End PROP.

Section SPEC.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition encrypt_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(left_ptr, right_ptr, m_l, m_r, ofs_l, ofs_r, tg_l, tg_r, q_l, q_r) => (
            (ord_pure 1%nat),
            (fun varg => ⌜varg = [left_ptr; right_ptr]↑⌝
                         ** left_ptr (⊨_m_l,tg_l,q_l) ofs_l
                         ** right_ptr (⊨_m_r,tg_r,q_r) ofs_r),
            (fun vret => ∃ i_l i_r, ⌜vret = (Vptrofs (Ptrofs.xor i_l i_r))↑⌝
                         ** left_ptr (⊨_m_l,tg_l,q_l) ofs_l
                         ** right_ptr (⊨_m_r,tg_r,q_r) ofs_r
                         ** left_ptr (≃_ m_l) i_l
                         ** right_ptr (≃_ m_r) i_r))%I.

  Definition encrypt_hoare2 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(left_ptr, m_l, ofs_l, tg_l, q_l) => (
            (ord_pure 1%nat),
            (fun varg => ⌜varg = [left_ptr; Vnullptr]↑⌝
                         ** left_ptr (⊨_m_l,tg_l,q_l) ofs_l),
            (fun vret => ∃ i_l, ⌜vret = (Vptrofs i_l)↑⌝
                         ** left_ptr (≃_ m_l) i_l
                         ** left_ptr (⊨_m_l,tg_l,q_l) ofs_l))%I.

  Definition encrypt_hoare3 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(right_ptr, m_r, ofs_r, tg_r, q_r) => (
            (ord_pure 1%nat),
            (fun varg => ⌜varg = [Vnullptr; right_ptr]↑⌝
                         ** right_ptr (⊨_m_r,tg_r,q_r) ofs_r),
            (fun vret => ∃ i_r, ⌜vret = (Vptrofs i_r)↑⌝
                         ** right_ptr (≃_ m_r) i_r
                         ** right_ptr (⊨_m_r,tg_r,q_r) ofs_r))%I.

  Definition encrypt_hoare4 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '() => (
            (ord_pure 1%nat),
            (fun varg => ⌜varg = [Vnullptr; Vnullptr]↑⌝),
            (fun vret => ⌜vret = Vnullptr↑⌝))%I.
  
  Definition encrypt_spec :=
    mk_simple (
      encrypt_hoare1
      @ encrypt_hoare2
      @ encrypt_hoare3
      @ encrypt_hoare4
    ).

  Definition decrypt_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(i_key, ptr, m, ofs, q, tg) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [Vptrofs i_key; ptr]↑⌝
                     ** ptr (⊨_m,tg,q) ofs),
        (fun vret => ∃ i_ptr, ⌜vret = (Vptrofs (Ptrofs.xor i_key i_ptr))↑⌝
                     ** ptr (⊨_m,tg,q) ofs
                     ** ptr (≃_m) i_ptr))%I.
                     
  Definition decrypt_hoare2 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(i_key) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [Vptrofs i_key; Vnullptr]↑⌝),
        (fun vret => ⌜vret = (Vptrofs i_key)↑⌝))%I.
  
  Definition decrypt_spec : fspec :=
    mk_simple (
      decrypt_hoare1
      @ decrypt_hoare2
    ).

  (* {hd_handler |-> hd  /\ tl_handler |-> tl /\ is_xorlist hd tl xs}
     void add(node** hd_handler, node** tl_handler, long item, bool at_tail)
     {r. if hd = null
         then exists new_node, hd_handler |-> new_node /\ tl_handler |-> new_node /\ is_xorlist new_node new_node [item]
         else if at_tail = false
              then exists new_hd, hd_handler |-> new_hd /\ tl_handler |-> tl /\ is_xorlist new_hd tl (item :: xs)
              else exists new_tl, hd_handler |-> hd /\ tl_handler |-> new_tl /\ is_xorlist hd new_tl (xs ++ [item])
     } *)

  Definition add_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, item, at_tail, xs) => (
        (ord_pure 2%nat),
        (fun varg => ⌜varg = [hd_handler; tl_handler; Vlong item; Vint at_tail]↑⌝
                     ** full_xorlist 1 hd_handler tl_handler xs),
        (fun vret => ⌜vret = Vundef↑⌝
                     ** full_xorlist 1 hd_handler tl_handler (vlist_add (Vlong item) xs (Vint at_tail)))
    )))%I.

  (* {hd_handler |-> hd  /\ tl_handler |-> tl /\ is_xorlist hd tl xs}
     long delete(node** hd_handler, node** tl_handler, bool from_tail)
     {r. if hd = null
         then r = 0 /\ hd_handler |-> hd /\ tl_handler |-> tl /\ is_xorlist hd tl []
         else if from_tail = false
              then r = last xs /\ exists new_hd, hd_handler |-> new_hd /\ tl_handler |-> tl /\ is_xorlist new_hd tl (removelast xs)
              else r = hd xs /\ exists new_tl, hd_handler |-> hd /\ tl_handler |-> new_tl /\ is_xorlist hd new_tl (tl xs)
     } *)

  Definition delete_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, from_tail, xs) => (
        (ord_pure 2%nat),
        (fun varg => ⌜varg = [hd_handler; tl_handler; Vint from_tail]↑⌝
                     ** full_xorlist 1 hd_handler tl_handler xs),
        (fun vret => let '(item, xs') := vlist_delete xs (Vint from_tail) (Vlong Int64.zero) in
                     ⌜vret = item↑⌝ ** full_xorlist 1 hd_handler tl_handler xs')
    )))%I.

  Definition search_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, from_tail, index, xs, idx, q) => (
        (ord_pure 2%nat),
        (fun varg => ⌜varg = [hd_handler; tl_handler; Vint from_tail; Vlong index]↑
                     /\ check_inbound xs (Vint from_tail) (Vlong index) = Some idx⌝
                     ** full_xorlist q hd_handler tl_handler xs),
        (fun vret => ∃ mid mid_prev m_hd_hdl m_tl_hdl p_hd p_tl ofs_hd_hdl ofs_tl_hdl tg_hd_hdl tg_tl_hdl,
                     ⌜vret = mid↑⌝
                     ** hd_handler (↦_m_hd_hdl,q) (encode_val Mptr p_hd)
                     ** hd_handler (⊨_m_hd_hdl,tg_hd_hdl,q) ofs_hd_hdl
                     ** ⌜((size_chunk Mptr) | Ptrofs.unsigned ofs_hd_hdl)%Z⌝
                     ** tl_handler (↦_m_tl_hdl,q) (encode_val Mptr p_tl)
                     ** tl_handler (⊨_m_tl_hdl,tg_tl_hdl,q) ofs_tl_hdl
                     ** ⌜((size_chunk Mptr) | Ptrofs.unsigned ofs_tl_hdl)%Z⌝
                     ** frag_xorlist q mid_prev mid p_tl Vnullptr (drop idx xs)
                     ** frag_xorlist q Vnullptr p_hd mid_prev mid (firstn idx xs))
    )))%I.

  (* sealed *)
  Definition xorStb : list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("encrypt", encrypt_spec);
           ("decrypt", decrypt_spec);
           ("add", add_spec);
           ("delete", delete_spec);
           ("search", search_spec)
           ].
  Defined.

End SPEC.

Require Import xorlist0.

Section SMOD.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition xorSbtb: list (gname * fspecbody) :=
    [("encrypt",  mk_pure encrypt_spec);
     ("decrypt",  mk_pure decrypt_spec);
     ("add",  mk_pure add_spec);
     ("delete",  mk_pure delete_spec);
     ("search",  mk_pure search_spec)
     ].
  
  Definition SxorSem : SModSem.t := {|
    SModSem.fnsems := xorSbtb;
    SModSem.mn := "xorlist";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}.
  
  Definition Sxor : SMod.t := {|
    SMod.get_modsem := fun _ => SxorSem;
    SMod.sk := xorlist0.xor.(Mod.sk);
  |}.
  
  Definition xor stb : Mod.t := (SMod.to_tgt stb) Sxor.
  
End SMOD.