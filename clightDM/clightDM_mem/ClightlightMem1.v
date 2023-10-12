Require Import Coqlib.
Require Import ITreelib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
Require Import ProofMode.
Require Import Any.
From compcert Require Import Floats Integers Values Memory AST Ctypes Clight Clightdefs.

Set Implicit Arguments.

Inductive block_kind :=
| Dynamic
| Local
| Unfreeable.

Let _memcntRA: URA.t := (block ==> Z ==> (Consent.t memval))%ra.
Let _memhdRA: URA.t := (block ==> (Excl.t (Z * block_kind)))%ra.

Compute (URA.car (t:=_memcntRA)).
Compute (URA.car (t:=_memhdRA)).
Instance memcntRA: URA.t := Auth.t _memcntRA.
Instance memhdRA: URA.t := Auth.t _memhdRA.

Section RA.

Section POINTSTO.

  Local Open Scope Z.

  Definition __points_to (b: block) (ofs: Z) (mvs: list memval) (q: Qp): _memcntRA :=
    (fun _b _ofs => if (dec _b b) && ((Coqlib.zle ofs _ofs) && (Coqlib.zlt _ofs (ofs + Z.of_nat (List.length mvs))))
                    then 
                      match List.nth_error mvs (Z.to_nat (_ofs - ofs)) with
                      | Some mv => Consent.just q mv
                      | None => ε
                      end
                    else ε)
  .

  Definition _points_to (b: block) (ofs: Z) (mvs: list memval) (q: Qp): memcntRA := Auth.white (__points_to b ofs mvs q).

  Lemma _points_to_split_aux
        blk ofs hd tl q
    :
      (_points_to blk ofs (hd :: tl) q) = (_points_to blk ofs [hd] q) ⋅ (_points_to blk (ofs + 1)%Z tl q)
  .
  Proof.
    ss. unfold _points_to, Auth.white. repeat (rewrite URA.unfold_add; ss).
    f_equal. unfold __points_to. ss.
    repeat (apply func_ext; i).
    des_ifs; bsimpl; des; des_sumbool; subst; ss;
      try rewrite Z.leb_gt in *; try rewrite Z.leb_le in *; try rewrite Z.ltb_ge in *; try rewrite Z.ltb_lt in *; try lia; clarify.
    - clear_tac. subst. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss. clarify. 
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq4; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss. clarify.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq4; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss. clarify.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq4; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss. clarify.
  Qed.

  Lemma __points_to_nil : forall blk ofs q _b _ofs, __points_to blk ofs [] _b _ofs q = ε.
  Proof.
    intros. unfold __points_to. ss. des_ifs. destruct (Z.to_nat _) in Heq0; ss. 
  Qed.

  Lemma points_to_nil : forall blk ofs q, _points_to blk ofs [] q = ε.
  Proof.
    intros. ss. unfold _points_to, Auth.white.
    change (memcntRA.(URA.unit)) with (Auth.frag (_memcntRA.(URA.unit))). f_equal. ss.
    repeat (apply func_ext; i). apply __points_to_nil.
  Qed.

  Lemma _points_to_app l l' q blk ofs:
    (_points_to blk ofs (l++l') q) = (_points_to blk ofs l q) ⋅ (_points_to blk (ofs + length l) l' q).
  Proof.
    revert l' blk ofs. induction l;i;ss.
    - rewrite points_to_nil. rewrite URA.unit_idl. rewrite Z.add_0_r. auto.
    - rewrite _points_to_split_aux. rewrite (_points_to_split_aux blk ofs a l).
      replace (ofs + Z.pos (Pos.of_succ_nat (strings.length l)))
        with ((ofs + 1) + length l) by nia.
      rewrite <- URA.add_assoc. rewrite <- IHl. auto.
  Qed.

  Lemma _points_to_split :
    forall (blk : Values.block) (ofs : Z) (q: Qp) (n : nat) (l : list memval),
      _points_to blk ofs l q =
        _points_to blk ofs (firstn n l) q ⋅ _points_to blk (ofs + (length (firstn n l))) (skipn n l) q.
  Proof.
    intros. set l as k at 2 3 4. rewrite <- (firstn_skipn n l). unfold k. clear k.
    rewrite _points_to_app. auto.
  Qed.

End POINTSTO.

Section ALLOCEDWITH.

  Definition __alloced_with (b: block) (sz: Z) (bk: block_kind) : _memhdRA :=
    (fun _b => if dec _b b
               then Excl.just (sz, bk)
               else ε)
  .

  Definition _alloced_with (b: block) (sz: Z) (bk: block_kind) : memhdRA := Auth.white (__alloced_with b sz bk).

End ALLOCEDWITH.

End RA.

Section PROP.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.

  (* Definition updblk [A: Type] (i f: nat) (l l': list A) : list A := firstn i l ++ l' ++ skipn f l.
  Definition getblk [A: Type] (i delta: nat) (l: list A) : list A := firstn delta (skipn i l).

  (* how to use getblk, updblk *)
  Lemma getblk_updblk A (i delta: nat) (l: list A) : updblk i (i + delta) l (getblk i delta l) = l.
  Proof.
    unfold updblk, getblk. rewrite <- drop_drop. do 2 rewrite firstn_skipn. refl.
  Qed. *)

  Definition size_rule (sz: nat) : Z :=
    if sz <? 2 then 1
    else if sz <? 4 then 2
    else if sz <? 8 then 4
    else 8
  .

  Definition points_to addr mvs q : iProp :=
    match addr with
    | Vptr b ofs =>
          let ofs' := Ptrofs.unsigned ofs in
          let align := size_rule (Z.to_nat (length mvs)) in
          OwnM (_points_to b ofs' mvs q)
          ** ⌜(align | ofs')⌝
    | _ => ⌜False⌝%I 
    end.
  
  Definition alloced_with b sz bk : iProp :=
    OwnM (_alloced_with b sz bk).

  Definition has_ofs v b ofs : iProp :=
    match v with
    | Vptr b' ofs' => ⌜b' = b /\ Ptrofs.unsigned ofs' = ofs⌝%I
    | _ => ⌜False⌝%I 
    end.

  (* Lemma detach_size addr vs sz : (addr #↦ vs ⋯ sz) -∗ (addr ↦ vs).
  Proof. 
    iIntros "A". unfold mpoints_to, points_to. des_ifs.
    iDestruct "A" as "[B C]". iApply "B".
  Qed.

  Lemma asdf b ofs b' ofs' vs vs': Vptr b ofs ↦ vs ** Vptr b' ofs' ↦ vs' -∗ (Vptr b ofs ↦ vs ∧ Vptr b' ofs' ↦ vs').
  Proof.
    iIntros "A". iDestruct "A" as "[B C]".
    iSplit.
    - iApply "B".
    - iApply "C".
  Qed.
  Lemma _points_to_split :
    forall (blk: block) (ofs delta: ptrofs) (n: nat) (l: list memval)
    (IN_RANGE: 0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned delta < Ptrofs.modulus),
    n = Z.to_nat (Ptrofs.unsigned delta) ->
      Vptr blk ofs ↦ l -∗
        Vptr blk ofs ↦ (firstn n l) ** Vptr blk (Ptrofs.add ofs delta) (skipn (Z.to_nat (Ptrofs.unsigned delta)) l).
  Proof.
    intros. set l as k at 2 3 4. rewrite <- (firstn_skipn n l). unfold k. clear k.
    rewrite _points_to_app. auto.
  Qed.

  Lemma points_to_load :
    forall addr addr' (i delta : nat) l,
      0 <= i <= length l ->
      addr ↦ l -∗
       (addr' ↦ getblk i delta l **
         ((addr' ↦ getblk i delta l) -* (addr ↦ l))).
  Proof.
    intros. iIntros "A". unfold getblk, points_to. destruct H0 as [S1 S2].
    assert (S3 : Z.to_nat m ≤ strings.length l) by nia.
    pose proof (_points_to_split' blk ofs (Z.to_nat m) l S3) as Hr. set l as k at 4.
    rewrite Hr. unfold k. clear k.
    pose proof (_points_to_split blk (ofs + m) n (drop (Z.to_nat m) l)) as Ht.
    replace (ofs + Z.to_nat m) with (ofs + m) by nia.
    rewrite Ht. iDestruct "A" as "[A [B C]]".
    iSplitL "B";auto. iIntros "B". iCombine "B C" as "B". rewrite <- _points_to_split.
    iCombine "A B" as "A". replace (ofs + m) with (ofs + Z.to_nat m) by nia.
    rewrite <- _points_to_split';auto.
  Qed. *)

End PROP.

Notation "addr |_ q #> mvs" := (points_to addr mvs q) (at level 20).
Notation "b #≔ ( sz , bk )" := (alloced_with b sz bk) (at level 10).

Section AUX.

  Context `{@GRA.inG memRA Σ}.

  (* Lemma points_to_disj
        ptr x0 x1
    :
      (ptr |-> [x0] -∗ ptr |-> [x1] -* ⌜False⌝)
  .
  Proof.
    destruct ptr as [blk ofs].
    iIntros "A B". iCombine "A B" as "A". iOwnWf "A" as WF0.
    unfold _points_to in WF0. rewrite ! unfold__points_to in *. repeat (ur in WF0); ss.
    specialize (WF0 blk ofs). des_ifs; bsimpl; des; SimComp.Coqlib.des_sumbool; zsimpl; ss; try lia.
  Qed. *)

  (** TODO-is_list **)
  (* Fixpoint is_list (ll: val) (xs: list val): iProp := *)
  (*   match xs with *)
  (*   | [] => (⌜ll = Vnullptr⌝: iProp)%I *)
  (*   | xhd :: xtl => *)
  (*     (∃ lhd ltl, ⌜ll = Vptr lhd (Ptrofs.repr 0)⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                            ** is_list ltl xtl: iProp)%I *)
  (*   end *)
  (* . *)

  (* Lemma unfold_is_list: forall ll xs, *)
  (*     is_list ll xs = *)
  (*     match xs with *)
  (*     | [] => (⌜ll = Vnullptr⌝: iProp)%I *)
  (*     | xhd :: xtl => *)
  (*       (∃ lhd ltl, ⌜ll = Vptr lhd (Ptrofs.repr 0)⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                              ** is_list ltl xtl: iProp)%I *)
  (*     end *)
  (* . *)
  (* Proof. *)
  (*   i. destruct xs; auto. *)
  (* Qed. *)

  (* Lemma unfold_is_list_cons: forall ll xhd xtl, *)
  (*     is_list ll (xhd :: xtl) = *)
  (*     (∃ lhd ltl, ⌜ll = Vptr lhd (Ptrofs.repr 0)⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                            ** is_list ltl xtl: iProp)%I. *)
  (* Proof. *)
  (*   i. eapply unfold_is_list. *)
  (* Qed. *)

  (* Lemma is_list_wf *)
  (*       ll xs *)
  (*   : *)
  (*     (is_list ll xs) -∗ (⌜(ll = Vnullptr) \/ (match ll with | Vptr _ ofs => Ptrofs.eq ofs (Ptrofs.repr 0) | _ => False end)⌝) *)
  (* . *)
  (* Proof. *)
  (*   iIntros "H0". destruct xs; ss; et. *)
  (*   { iPure "H0" as H0. iPureIntro. left. et. } *)
  (*   iDestruct "H0" as (lhd ltl) "[[H0 H1] H2]". *)
  (*   iPure "H0" as H0. iPureIntro. right. subst. et. *)
  (* Qed. *)

  (* Global Opaque is_list. *)
  (* Definition encode_list chunk vlist : list memval := flat_map (encode_val chunk) vlist. 
  
  Definition is_arr (chunk : memory_chunk) (ll : val) (xs : list val) :=
    (∃ (b :block) (ofs : ptrofs),
        ⌜ll = Vptr b ofs⌝ ** (b, Ptrofs.intval ofs) |-> (encode_list chunk xs))%I. *)
End AUX.

Section SMODSEM.

  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.

  Variable sk: Sk.t.
  Let skenv: SkEnv.t := Sk.load_skenv sk.

Section SPECBODY.

Section SPEC.

  
  Definition salloc_spec: fspec :=
    (mk_simple (fun sz => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = sz↑⌝),
                    (fun vret => ∃ b vaddr, ⌜vret = b↑⌝
                                 ** vaddr |_1#> List.repeat Undef (Z.to_nat sz)
                                 ** b #≔ (sz, Local)
                                 ** has_ofs vaddr b 0)
    )))%I.

  Definition sfree_spec: fspec :=
    (mk_simple (fun '() => (
                   (ord_pure 0%nat),
                   (fun varg => ∃ mvl vaddr b sz,
                                ⌜varg = (b, sz)↑ /\ Z.of_nat (List.length mvl) = sz⌝
                                ** vaddr |_1#> mvl
                                ** b #≔ (sz, Local)
                                ** has_ofs vaddr b 0),
                   (fun vret => ⌜vret = tt↑⌝)
    )))%I.

  Definition load_spec: fspec :=
    (mk_simple (fun '(chunk, vaddr, q, mvs) => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (chunk, vaddr)↑⌝
                                 ** vaddr |_q#> mvs),
                    (fun vret => ∃ v, ⌜vret = v↑ /\ decode_val chunk mvs = v⌝
                                 ** vaddr |_q#> mvs)
    )))%I.

  Definition loadbytes_spec: fspec :=
    (mk_simple (fun '(vaddr, sz, q, mvs) => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (vaddr, sz)↑ /\ Z.of_nat (List.length mvs) = sz⌝ 
                                 ** vaddr |_q#> mvs),
                    (fun vret => ⌜vret = mvs↑⌝ ** vaddr |_q#> mvs)
    ))).

  Definition store_spec: fspec :=
    (mk_simple
       (fun '(chunk, vaddr, v_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ mvs_old, ⌜varg = (chunk, vaddr, v_new)↑
                                    /\ List.length mvs_old = size_chunk_nat chunk⌝
                                    ** vaddr |_1#> mvs_old),
            (fun vret => ∃ mvs_new, ⌜vret = tt↑ /\ encode_val chunk v_new = mvs_new⌝
                                    ** vaddr |_1#> mvs_new)
    )))%I.

  Definition storebytes_spec: fspec :=
    (mk_simple
       (fun '(vaddr, mvs_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ mvs_old, ⌜varg = (vaddr, mvs_new)↑
                                    /\ List.length mvs_old = List.length mvs_new⌝
                                    ** vaddr |_1#> mvs_old),
            (fun vret => ⌜vret = tt↑⌝ ** vaddr |_1#> mvs_new)
    )))%I.

  Definition cmp_ptr_spec: fspec :=
    (mk_simple
       (fun '(b, ofs, resource, sz) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr blk, ⌜varg = vaddr↑ /\ resource b = Excl.just (sz, blk)⌝
                         ** has_ofs vaddr b ofs
                         ** OwnM (Auth.white resource)),
            (fun vret => ⌜vret = (is_valid sz ofs)↑⌝ 
                         ** OwnM (Auth.white resource))%I
    )))%I.
  
  Definition sub_ptr_spec: fspec :=
    (mk_simple
       (fun '(ofs0, ofs1, sz) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr0 vaddr1 b,
                         ⌜varg = (sz, vaddr0, vaddr1)↑ /\ 0 < sz ≤ Ptrofs.max_signed⌝
                         ** has_ofs vaddr0 b ofs0
                         ** has_ofs vaddr1 b ofs1),
            (fun vret => ⌜vret = (Z.div (ofs0 - ofs1) sz)↑⌝)
    )))%I.
  
  Definition is_weak_valid (sz: Z) (ofs: Z) : bool :=
    Coqlib.zle 0 ofs && Coqlib.zle ofs sz.

  Definition weak_valid_pointer_spec: fspec :=
    (mk_simple
       (fun '(b, ofs, resource, sz) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr blk, ⌜varg = vaddr↑ /\ resource b = Excl.just (sz, blk)⌝
                         ** has_ofs vaddr b ofs
                         ** OwnM (Auth.white resource)),
            (fun vret => ⌜vret = (is_valid sz ofs)↑⌝ 
                         ** OwnM (Auth.white resource))%I
    )))%I.

  (* heap malloc free *)
  Definition malloc_spec: fspec :=
    (mk_simple (fun sz => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (Vptrofs sz)↑⌝),
                    (fun vret => ∃ vaddr b, ⌜vret = vaddr↑⌝
                                 ** vaddr |_1#> List.repeat Undef (Z.to_nat (Ptrofs.unsigned sz))
                                 ** b #≔ (Ptrofs.unsigned sz, Dynamic)
                                 ** has_ofs vaddr b 0) 
    )))%I.

  Definition mfree_spec: fspec :=
    (mk_simple (fun '() => (
                    (ord_pure 0%nat),
                    (fun varg => ∃ mvs vaddr b sz,
                                 ⌜varg = vaddr↑ /\ Z.of_nat (List.length mvs) = sz⌝
                                 ** vaddr |_1#> mvs
                                 ** b #≔ (sz, Dynamic)
                                 ** has_ofs vaddr b 0),
                    (fun vret => ⌜vret = tt↑⌝)
    )))%I.

  (* sealed *)
  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("salloc", salloc_spec); ("sfree", sfree_spec); 
           ("load", load_spec); ("loadbytes", loadbytes_spec); 
           ("store", store_spec); ("storebytes", storebytes_spec);
           ("sub_ptr", cfunU sub_ptr_spec); ("cmp_ptr", cfunU cmp_ptr_spec);
           ("valid_pointer", weak_valid_pointer_spec);
           ("malloc", malloc_spec); ("mfree", mfree_spec)
           ].
    Defined.

End SPEC.

Section BODY.
End BODY.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("salloc", mk_specbody salloc_spec (fun _ => trigger (Choose _)));
    ("sfree",   mk_specbody sfree_spec (fun _ => trigger (Choose _)));
    ("load",   mk_specbody load_spec (fun _ => trigger (Choose _)));
    ("loadbytes",   mk_specbody loadbytes_spec (fun _ => trigger (Choose _)));
    ("store",  mk_specbody store_spec (fun _ => trigger (Choose _)));
    ("storebytes",   mk_specbody storebytes_spec (fun _ => trigger (Choose _)));
    ("sub_ptr", mk_specbody sub_ptr_spec (fun _ => trigger (Choose _)));
    ("cmp_ptr", mk_specbody cmp_ptr_spec (fun _ => trigger (Choose _)));
    ("valid_pointer",   mk_specbody weak_valid_pointer_spec (fun _ => trigger (Choose _)));
    ("malloc",   mk_specbody malloc_spec (fun _ => trigger (Choose _)));
    ("mfree",   mk_specbody mfree_spec (fun _ => trigger (Choose _)))
    ]
  .

End SPECBODY.

Section MRS.

  Definition store_init_data (res : _memcntRA) (b : block) (p : Z) (optq : option Qp) (id : init_data) : option _memcntRA :=
    match id with
    | Init_int8 n => 
      if Zdivide_dec (align_chunk Mint8unsigned) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint8unsigned (Vint n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_int16 n =>
      if Zdivide_dec (align_chunk Mint16unsigned) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint16unsigned (Vint n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_int32 n =>
      if Zdivide_dec (align_chunk Mint32) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint32 (Vint n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_int64 n =>
      if Zdivide_dec (align_chunk Mint64) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint64 (Vlong n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_float32 n =>
      if Zdivide_dec (align_chunk Mfloat32) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mfloat32 (Vsingle n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_float64 n =>
      if Zdivide_dec (align_chunk Mfloat64) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mfloat64 (Vfloat n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_space z => 
      match optq with
      | Some q => Some (__points_to b p (repeat (Byte Byte.zero) (Z.to_nat z)) q ⋅ res)
      | None => Some res
      end
    | Init_addrof symb ofs =>
      match SkEnv.id2blk skenv (string_of_ident symb) with
      | Some b' =>
        if Zdivide_dec (align_chunk Mptr) p
        then
          match optq with
          | Some q => Some (__points_to b p (encode_val Mptr (Vptr (Pos.of_succ_nat b') ofs)) q ⋅ res)
          | None => Some res
          end
        else None
      | None => None
      end
    end.

  Fixpoint store_init_data_list (res : _memcntRA) (b : block) (p : Z) (optq: option Qp) (idl : list init_data) {struct idl} : option _memcntRA :=
    match idl with
    | [] => Some res
    | id :: idl' =>
        match store_init_data res b p optq id with
        | Some res' => store_init_data_list res' b (p + init_data_size id)%Z optq idl'
        | None => None
        end
    end.

  Definition alloc_global (res : Σ) (b: block) (entry : string * Any.t) : option Σ :=
    let (_, agd) := entry in
    match Any.downcast agd : option (globdef Clight.fundef type) with
    | Some g => 
      match g with
      | Gfun _ => Some (GRA.embed (Auth.black (__alloced_with b 1 Unfreeable)) ⋅ res)
      | Gvar v =>
        let optq := match Globalenvs.Genv.perm_globvar v with
                    | Freeable | Writable => Some 1%Qp
                    | Readable => Some (1/2)%Qp
                    | Nonempty => None
                    end
        in
        match store_init_data_list ε b 0 optq (gvar_init v) with
        | Some res' => Some (GRA.embed (Auth.black (__alloced_with b (init_data_list_size (gvar_init v)) Unfreeable))
                             ⋅ GRA.embed (Auth.black res') ⋅ res)
        | None => None
        end
      end
    | None => None
    end.

  Fixpoint alloc_globals (res: Σ) (b: block) (sk: list (string * Any.t)) : Σ :=
  match sk with
  | nil => res
  | g :: gl' => 
    match alloc_global res b g with
    | Some res' => alloc_globals res' (Pos.succ b) gl'
    | None => ε
    end
  end.

  Definition load_resource : Σ := alloc_globals ε xH sk.

  End MRS.

  Definition SMemSem : SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.mn := "Mem";
    SModSem.initial_mr := load_resource;
    SModSem.initial_st := tt↑;
  |}
  .

  End SMODSEM.

Section MOD.
  Context `{@GRA.inG memcntRA Σ}.
  Context `{@GRA.inG memhdRA Σ}.

  Definition SMem: SMod.t := {|
    SMod.get_modsem := SMemSem;
    SMod.sk := [("malloc", (@Gfun Clight.fundef type (External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default))↑);
               ("free", (@Gfun Clight.fundef type (External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default))↑)]
  |}
  .

  Definition Mem: Mod.t := (SMod.to_tgt (fun _ => to_stb [])) SMem.

End MOD.

Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
Global Opaque _alloced_with.