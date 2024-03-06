Require Import CoqlibCCR.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import Any.
Require Import ModSem.
Require Import ModSemE.
Require Import ClightPlusMem1.
From compcert Require Export Ctypes Values AST Memdata Integers.

Set Implicit Arguments.

Section PROP.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition vlist_delete_hd (l: list val) (default: val) : val * list val := (hd default l, tl l).

  Definition vlist_delete_tl (l: list val) (default: val) : val * list val := (last l default, removelast l).

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

    (* Definition ptr_equiv (p q: val) : iProp := *)
    (* (⌜p = q⌝ ∨ (∃ i m1 m2, p (≃_m1) i ** q (≃_m2) i))%I. *)

    (* Definition xor_live (p: val) (q: Qp) : iProp := *)
    (* (⌜p = Vnullptr⌝ ∨ ∃ m, p (⊨_m,Dynamic,q) Ptrofs.zero)%I. *)

     (* is_xorlist represents the figure below    *)
     (*    ll_h                              ll_t *)
     (*     |                                 |   *)
     (*     v                                 v   *)
     (* xs  - - - - - - - - - - - - - - - - - -   *)

  Fixpoint frag_xorlist (q: Qp) (m_prev m_next: metadata) (hd_prev hd tl tl_next: val) (xs : list val) {struct xs} : iProp :=
    match xs with
    | [] => (hd_prev (≃_ m_prev) tl ** hd (≃_ m_next) tl_next)
    | Vlong a :: xs' =>
        ∃ i_prev i_next m_hd,
          ⌜m_hd.(sz) = (size_chunk Mint64 + size_chunk Mptr)%Z⌝
          ** hd_prev (≃_ m_prev) (Vptrofs i_prev)
          ** hd (⊨_m_hd,Dynamic,q) Ptrofs.zero
          ** hd (↦_m_hd,q) (encode_val Mint64 (Vlong a) ++ encode_val Mptr (Vptrofs (Ptrofs.xor i_prev i_next)))
          ** frag_xorlist q m_hd m_next hd (Vptrofs i_next) tl tl_next xs'
    | _ => False
    end%I.

  Lemma unfold_frag_xorlist (q: Qp) (m_prev m_next: metadata) (hd_prev hd tl tl_next: val) (xs : list val) :
  frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs =
    match xs with
    | [] => (hd_prev (≃_ m_prev) tl ** hd (≃_ m_next) tl_next)
    | Vlong a :: xs' =>
        ∃ i_prev i_next m_hd,
          ⌜m_hd.(sz) = (size_chunk Mint64 + size_chunk Mptr)%Z⌝
          ** hd_prev (≃_ m_prev) (Vptrofs i_prev)
          ** hd (⊨_m_hd,Dynamic,q) Ptrofs.zero
          ** hd (↦_m_hd,q) (encode_val Mint64 (Vlong a) ++ encode_val Mptr (Vptrofs (Ptrofs.xor i_prev i_next)))
          ** frag_xorlist q m_hd m_next hd (Vptrofs i_next) tl tl_next xs'
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
    ** frag_xorlist q m_null m_null Vnullptr hd tl Vnullptr xs)%I.

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
    
  Lemma rev_xorlist q m_prev m_next hd_prev hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs
      ⊢ frag_xorlist q m_next m_prev tl_next tl hd hd_prev (rev xs).
  Proof.
    ginduction xs; i; ss.
    - iIntros "[A B]". 
      iPoseProof (equiv_sym with "A") as "A".
      iPoseProof (equiv_sym with "B") as "B". iFrame.
    - destruct a; try solve [iIntros "[]"].
      iIntros "A".
      iDestruct "A" as (i_prev i_next m_hd) "[[[[% D] C] B] A]".
      iPoseProof (IHxs with "A") as "A".
      generalize (rev xs). i.
      iStopProof. clear - H3. ginduction l; i; ss.
      + iIntros "[A [B [C [D E]]]]".
        iPoseProof (equiv_sym with "E") as "E".
        iPoseProof (equiv_dup with "E") as "[E E']".
        iCombine "E' B" as "B".
        iPoseProof (equiv_offset_comm with "B") as "B".
        iPoseProof (equiv_dup with "E") as "[E E']".
        iCombine "E' C" as "C".
        iPoseProof (equiv_point_comm with "C") as "C".
        iPoseProof (equiv_sym with "A") as "A".
        iPoseProof (equiv_sym with "E") as "E".
        rewrite Ptrofs.xor_commut.
        iExists i_next,i_prev,_. iFrame. 
        et.
      + iIntros "[A [B [C D]]]".
        destruct a; try solve [iDestruct "D" as "[]"].
        iDestruct "D" as (i_prev0 i_next0 m_hd0) "[[[[% G] D] E] F]".
        iExists _,_,_. iFrame. iSplit; ss.
        iApply IHl. { apply H3. } iFrame. 
  Qed.

  Lemma xorlist_hd_deen q m_prev m_next hd_prev hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs ⊢ ⌜decode_val Mptr (encode_val Mptr hd) = hd⌝.
  Proof.
    destruct xs.
    - ss. iIntros "[A B]". iApply decode_encode_ptr_equiv. et.
    - ss. iIntros "A". destruct v; clarify.
      iDestruct "A" as (i_prev i_next m_hd) "[[[_ A] _] _]". 
      iApply decode_encode_ptr_ofs. et.
  Qed.

  Lemma xorlist_hd_not_Vundef q m_prev m_next hd_prev hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs ⊢ ⌜hd <> Vundef⌝.
  Proof.
    destruct xs.
    - ss. iIntros "[A B]". iApply equiv_notundef. et.
    - ss. des_ifs; et. iIntros "A". 
      iDestruct "A" as (i_prev i_next m_hd) "[[[_ A] _] _]". 
      iApply offset_notundef. et.
  Qed.

  Lemma xorlist_tl_deen q m_prev m_next hd_prev hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs ⊢ ⌜decode_val Mptr (encode_val Mptr tl) = tl⌝.
  Proof.
    ginduction xs; i; ss.
    - iIntros "[A B]". iApply decode_encode_ptr_equiv. iApply equiv_sym. et.
    - ss. iIntros "A". destruct a; clarify.
      iDestruct "A" as (i_prev i_next m_hd) "[_ A]". 
      iApply IHxs. et.
  Qed.

  Lemma xorlist_tl_not_Vundef q m_prev m_next hd_prev hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs ⊢ ⌜tl <> Vundef⌝.
  Proof.
    ginduction xs; i; ss.
    - ss. iIntros "[A B]". iApply equiv_notundef. iApply equiv_sym. et.
    - ss. iIntros "A". destruct a; clarify.
      iDestruct "A" as (i_prev i_next m_hd) "[_ A]". 
      iApply IHxs. et.
  Qed.

  Lemma xorlist_hd_prev_replace q m_prev m_next hd_prev hd_prev' hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs ** hd_prev (≃_m_prev) hd_prev' ⊢ frag_xorlist q m_prev m_next hd_prev' hd tl tl_next xs.
  Proof.
    destruct xs; i; ss.
    - ss. iIntros "[[A B] C]". iFrame. iApply equiv_trans. iFrame. iApply equiv_sym. et.
    - ss. iIntros "[A B]". destruct v; clarify.
      iDestruct "A" as (i_prev i_next m_hd) "[[[[% F] D] E] A]". 
      iExists _,_,_. iFrame. iSplit; ss. iApply equiv_trans. iFrame. iApply equiv_sym. et.
  Qed.

  Lemma xorlist_tl_next_replace q m_prev m_next hd_prev tl_next' hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs ** tl_next (≃_m_next) tl_next' ⊢ frag_xorlist q m_prev m_next hd_prev hd tl tl_next' xs.
  Proof.
    iIntros "[A B]". set xs at 1. rewrite <- (rev_involutive xs). unfold l.
    iApply rev_xorlist. iApply xorlist_hd_prev_replace. iFrame.
    iApply rev_xorlist. et.
  Qed.

End PROP.

Section SPEC.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  (* Definition encrypt_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(left_ptr, right_ptr, m_l, m_r, ofs_l, ofs_r, tg_l, tg_r, q_l, q_r) => (
            (ord_pure 1%nat),
            (fun varg => ⌜varg = [left_ptr; right_ptr]↑⌝
                         ** left_ptr (⊨_m_l,tg_l,q_l) ofs_l
                         ** right_ptr (⊨_m_r,tg_r,q_r) ofs_r),
            (fun vret => ∃ i_l i_r, ⌜vret = (Vptrofs (Ptrofs.xor i_l i_r))↑⌝
                         ** left_ptr (⊨_m_l,tg_l,q_l) ofs_l
                         ** right_ptr (⊨_m_r,tg_r,q_r) ofs_r
                         ** left_ptr (≃_ m_l) (Vptrofs i_l)
                         ** right_ptr (≃_ m_r) (Vptrofs i_r)))%I.

  Definition encrypt_hoare2 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(left_ptr, m_l, ofs_l, tg_l, q_l) => (
            (ord_pure 1%nat),
            (fun varg => ⌜varg = [left_ptr; Vnullptr]↑⌝
                         ** left_ptr (⊨_m_l,tg_l,q_l) ofs_l),
            (fun vret => ∃ i_l, ⌜vret = (Vptrofs i_l)↑⌝
                         ** left_ptr (≃_ m_l) (Vptrofs i_l)
                         ** left_ptr (⊨_m_l,tg_l,q_l) ofs_l))%I.

  Definition encrypt_hoare3 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(right_ptr, m_r, ofs_r, tg_r, q_r) => (
            (ord_pure 1%nat),
            (fun varg => ⌜varg = [Vnullptr; right_ptr]↑⌝
                         ** right_ptr (⊨_m_r,tg_r,q_r) ofs_r),
            (fun vret => ∃ i_r, ⌜vret = (Vptrofs i_r)↑⌝
                         ** right_ptr (≃_ m_r) (Vptrofs i_r)
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
                     ** ptr (≃_m) (Vptrofs i_ptr)))%I.
                     
  Definition decrypt_hoare2 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(i_key) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [Vptrofs i_key; Vnullptr]↑⌝),
        (fun vret => ⌜vret = (Vptrofs i_key)↑⌝))%I.
  
  Definition decrypt_spec : fspec :=
    mk_simple (
      decrypt_hoare1
      @ decrypt_hoare2
    ). *)

  Definition add_hd_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, item, xs) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [hd_handler; tl_handler; Vlong item]↑⌝
                     ** full_xorlist 1 hd_handler tl_handler xs),
        (fun vret => ⌜vret = Vundef↑⌝
                     ** full_xorlist 1 hd_handler tl_handler (Vlong item :: xs))
    )))%I.

  Definition add_tl_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, item, xs) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [hd_handler; tl_handler; Vlong item]↑⌝
                     ** full_xorlist 1 hd_handler tl_handler xs),
        (fun vret => ⌜vret = Vundef↑⌝
                     ** full_xorlist 1 hd_handler tl_handler (xs ++ [Vlong item]))
    )))%I.

  Definition delete_hd_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, xs) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [hd_handler; tl_handler]↑⌝
                     ** full_xorlist 1 hd_handler tl_handler xs),
        (fun vret => let '(item, xs') := vlist_delete_hd xs (Vlong Int64.zero) in
                     ⌜vret = item↑⌝ ** full_xorlist 1 hd_handler tl_handler xs')
    )))%I.

  Definition delete_tl_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, xs) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [hd_handler; tl_handler]↑⌝
                     ** full_xorlist 1 hd_handler tl_handler xs),
        (fun vret => let '(item, xs') := vlist_delete_tl xs (Vlong Int64.zero) in
                     ⌜vret = item↑⌝ ** full_xorlist 1 hd_handler tl_handler xs')
    )))%I.

  (* Definition search_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, from_tail, index, xs, idx, q) => (
        (ord_pure 2%nat),
        (fun varg => ⌜varg = [hd_handler; tl_handler; Vint from_tail; Vlong index]↑
                     /\ check_inbound xs (Vint from_tail) (Vlong index) = Some idx⌝
                     ** full_xorlist q hd_handler tl_handler xs),
        (fun vret => ∃ mid mid_prev m_mid m_mid_prev m_hd_hdl m_tl_hdl p_hd p_tl ofs_hd_hdl ofs_tl_hdl tg_hd_hdl tg_tl_hdl,
                     ⌜vret = mid↑⌝
                     ** hd_handler (↦_m_hd_hdl,q) (encode_val Mptr p_hd)
                     ** hd_handler (⊨_m_hd_hdl,tg_hd_hdl,q) ofs_hd_hdl
                     ** ⌜((size_chunk Mptr) | Ptrofs.unsigned ofs_hd_hdl)%Z⌝
                     ** tl_handler (↦_m_tl_hdl,q) (encode_val Mptr p_tl)
                     ** tl_handler (⊨_m_tl_hdl,tg_tl_hdl,q) ofs_tl_hdl
                     ** ⌜((size_chunk Mptr) | Ptrofs.unsigned ofs_tl_hdl)%Z⌝
                     ** frag_xorlist q m_null m_mid Vnullptr p_hd mid_prev mid (firstn idx xs)
                     ** frag_xorlist q m_mid_prev m_null mid_prev mid p_tl Vnullptr (drop idx xs))
    )))%I. *)

  (* sealed *)
  Definition xorStb : list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [
           (* ("encrypt", encrypt_spec);
           ("decrypt", decrypt_spec); *)
           ("add_hd", add_hd_spec);
           ("add_tl", add_tl_spec);
           ("delete_hd", delete_hd_spec);
           ("delete_tl", delete_tl_spec)
           (* ("search", search_spec) *)
           ].
  Defined.

End SPEC.

Section SMOD.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition xorSbtb: list (gname * fspecbody) :=
    [
     ("add_hd", mk_pure add_hd_spec);
     ("add_tl", mk_pure add_tl_spec);
     ("delete_hd", mk_pure delete_hd_spec);
     ("delete_tl", mk_pure delete_tl_spec)
     ].
  
  Definition SxorSem : SModSem.t := {|
    SModSem.fnsems := xorSbtb;
    SModSem.mn := "xorlist";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}.

  Variable xor0: Mod.t.

  Definition Sxor : SMod.t := {|
    SMod.get_modsem := fun _ => SxorSem;
    SMod.sk := xor0.(Mod.sk);
  |}.

  Definition xor stb : Mod.t := (SMod.to_tgt stb) Sxor.

End SMOD.
