Require Import Coqlib.
Require Import Any.
Require Import ModSem.
Require Import PCM IPM.
Require Import HoareDef STB.
Require Export HSim IProofMode.
Require Import ClightDmMem1.
From compcertip Require Import AST Values Integers Memdata.

Section MEM.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memphyRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.
  Context `{@GRA.inG memidRA Σ}.
  Variable world: Type.
  Variable le: relation world.
  Variable I: world -> Any.t -> Any.t -> iProp.

  Variable mn: mname.

  Lemma isim_ccallU_salloc
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        sz itr_src (ktr_tgt: block -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  **
                  (∀ st_src st_tgt vaddr b,
                      ((inv_with le I w0 st_src st_tgt) ** (vaddr ⊢1#> List.repeat Undef (Z.to_nat sz) ** vaddr ⊸ (b, 0) ** b ↱1# (sz, Local, None))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt b)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "salloc" sz >>= ktr_tgt)).
  Proof.
    iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. }
      { ss. } }
    instantiate (1:=sz).
    ss.
    iSplitL "H0".
    { iSplit; ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [RES %]]".
    iDestruct "RES" as (b vaddr) "[[[% STR] LIV] PTR]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "H1". iFrame. 
  Qed.

  Lemma isim_ccallU_sfree
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        mvl vaddr b sz opti itr_src (ktr_tgt: unit -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (vaddr ⊢1#> mvl ** vaddr ⊸ (b, 0) ** b ↱1# (sz, Local, opti) ** ⌜Z.of_nat (List.length mvl) = sz⌝)
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt)) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt tt)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "sfree" (b, sz) >>= ktr_tgt)).
  Proof.
    iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. des_ifs. }
      { ss. des_ifs. } }
    instantiate (1:=()).
    ss.
    iSplitL "H0".
    { iDestruct "H0" as "[INV PRE]". iFrame. iSplit; ss.
      iDestruct "PRE" as "[[[STR PTR] LIV] %]". iExists _, _, _, _, _.
      iFrame. ss. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [% %]]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "H1". iFrame. 
  Qed.

  Lemma isim_ccallU_load
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        chunk vaddr q mvs itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (vaddr ⊢q#> mvs)
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (vaddr ⊢q#> mvs)) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (decode_val chunk mvs))))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "load" (chunk, vaddr) >>= ktr_tgt)).
  Proof.
    iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. des_ifs_safe. destruct p0. ss. }
      { ss. des_ifs_safe. destruct p0. ss. } }
    instantiate (1:=(chunk, vaddr, q, mvs)).
    ss.
    iSplitL "H0".
    { iDestruct "H0" as "[INV PRE]". iSplitL "INV"; et. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [RES %]]".
    iDestruct "RES" as (v) "[% POST]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "H1". iFrame. 
  Qed.

  Lemma isim_ccallU_store
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        chunk vaddr v_new itr_src (ktr_tgt: unit -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (∃ mvs_old, ⌜length mvs_old = size_chunk_nat chunk⌝ ** vaddr ⊢1#> mvs_old)
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (vaddr ⊢1#> (encode_val chunk v_new))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt tt)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "store" (chunk, vaddr, v_new) >>= ktr_tgt)).
  Proof.
    iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. des_ifs_safe. destruct p. ss. }
      { ss. des_ifs_safe. destruct p. ss. } }
    instantiate (1:=(chunk, vaddr, v_new)).
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
  Qed.

  
  Lemma isim_ccallU_capture1
        o stb w0 fuel1
        R_src R_tgt
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        i itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  **
                  (∀ st_src st_tgt,
                      ((inv_with le I w0 st_src st_tgt)) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt (Vptrofs i))))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "capture" [Vptrofs i] >>= ktr_tgt)).
  Proof.
    iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { instantiate (1:= inl _). ss. }
      { ss. } }
    instantiate (1:=(i)).
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
        b ofs q sz tg opti itr_src (ktr_tgt: val -> _)
        fuel0
        (STBINCL: stb_incl (to_stb MemStb) stb)
        (DEPTH: ord_lt (ord_pure 0%nat) o)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** b ↱q# (sz, tg, opti)
                  **
                  (∀ st_src st_tgt ret,
                      ((inv_with le I w0 st_src st_tgt) ** (∃ i, ⌜ret = (Vptrofs (Ptrofs.add i ofs))⌝ ** b ↱q# (sz, tg, Some (Ptrofs.unsigned i)))) -* isim le I mn stb o (g, g, true, true) Q (Some fuel1) (st_src, itr_src) (st_tgt, ktr_tgt ret)))
        (isim le I mn stb o (r, g, f_src, f_tgt) Q (Some fuel0) (st_src, itr_src) (st_tgt, ccallU "capture" [Vptr b ofs] >>= ktr_tgt)).
  Proof.
    iIntros "[H0 H1]". iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. ss. }
      { ss. instantiate (1:= inr _).
        ss. unfold capture_hoare2. des_ifs_safe. destruct p0. ss. }
      { ss. unfold capture_hoare2. des_ifs_safe. destruct p0. ss. } }
    instantiate (1:=(b, q, sz, tg)).
    ss.
    iSplitL "H0".
    { iDestruct "H0" as "[INV PRE]". iSplitL "INV"; et. }
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iDestruct "H0" as "[INV [RES %]]".
    iDestruct "RES" as (v) "[% POST]".
    des. clarify.
    iExists _. iSplit; ss.
    iApply "H1". iSplitL "INV"; iFrame.
    iExists _. iSplit; ss.
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