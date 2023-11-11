Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM IPM.
Require Import HoareDef STB.
Require Import ClightDmExprgen.
Require Import ClightDmgen.
From compcertip Require Import Floats Integers Values Memory AST Ctypes Clight Clightdefs.

Set Implicit Arguments.

Inductive tag :=
| Dynamic
| Local
| Unfreeable.

Record metadata := { blk : block; sz : Z }.

Let _pointstoRA: URA.t := (block ==> Z ==> (Consent.t memval))%ra.
Let _allocatedRA: URA.t := (block ==> (Consent.t tag))%ra.

Compute (URA.car (t:=_pointstoRA)).
Compute (URA.car (t:=_allocatedRA)).
Instance pointstoRA: URA.t := Auth.t _pointstoRA.
Instance allocatedRA: URA.t := Auth.t _allocatedRA.
Instance blocksizeRA: URA.t := (block ==> (OneShot.t Z))%ra.
Instance blockaddressRA: URA.t := (block ==> (OneShot.t Z))%ra.

Local Open Scope Z.
Local Open Scope bi_scope.

Section POINTSTO.


  Definition __points_to (b: block) (ofs: Z) (mvs: list memval) (q: Qp): _pointstoRA :=
    (fun _b _ofs => if (dec _b b) && ((Coqlib.zle ofs _ofs) && (Coqlib.zlt _ofs (ofs + Z.of_nat (List.length mvs))))
                    then 
                      match List.nth_error mvs (Z.to_nat (_ofs - ofs)) with
                      | Some mv => Consent.just q mv
                      | None => ε
                      end
                    else ε)
  .

  Definition _points_to (b: block) (ofs: Z) (mvs: list memval) (q: Qp): pointstoRA := Auth.white (__points_to b ofs mvs q).

End POINTSTO.

Section ALLOCATEDWITH.

  Definition __allocated_with (b: block) (tg: tag) (q: Qp) : _allocatedRA :=
    (fun _b => if dec _b b
              then Consent.just q tg
              else ε)
  .

  Definition _allocated_with (b: block) (tg: tag) (q: Qp) : allocatedRA := Auth.white (__allocated_with b tg q).

End ALLOCATEDWITH.

Section BLOCKSIZE.

  Definition _has_size (b: block) (sz: Z) : blocksizeRA :=
    (fun _b => if dec _b b
              then OneShot.white sz
              else ε).

End BLOCKSIZE.

Section BLOCKADDR.

  Definition _has_base (b: block) (base: Z) : blockaddressRA :=
    (fun _b => if dec _b b
              then OneShot.white base
              else ε).

End BLOCKADDR.

Section PROP.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition get_align (sz: nat) : Z :=
    if lt_dec sz 2 then 1
    else if le_dec sz 4 then 2
    else if lt_dec sz 8 then 4
    else 8
  .

  Definition captured_to vaddr m i : iProp :=
    OwnM (_has_size m.(blk) m.(sz))
    ** ∃ a, OwnM (_has_base m.(blk) a)
       ** match vaddr with
          | Vptr b ofs => ⌜b = m.(blk) /\ Ptrofs.unsigned ofs = i - a⌝
          | Vint i' => ⌜i = Int.unsigned i'⌝
          | Vlong i' => ⌜i = Int64.unsigned i'⌝
          | _ => ⌜False⌝
          end%I.

  Definition has_offset vaddr m ofs : iProp :=
    OwnM (_has_size m.(blk) m.(sz))
    ** match vaddr with
       | Vptr b ofs' => 
          let ofs' := Ptrofs.unsigned ofs' in
          ⌜b = m.(blk) /\ ofs = ofs'⌝
       | Vint i =>
          if Archi.ptr64 then ⌜False⌝
          else  
            ∃ i', ⌜i' = Int.unsigned i⌝
            ** captured_to (Vptr m.(blk) (Ptrofs.repr ofs)) m i'
       | Vlong i =>
          if negb Archi.ptr64 then ⌜False⌝
          else 
            ∃ i', ⌜i' = Int64.unsigned i⌝
            ** captured_to (Vptr m.(blk) (Ptrofs.repr ofs)) m i'
       | _ => ⌜False⌝
       end.

  Definition metadata_alive m tg q : iProp :=
    OwnM (_allocated_with m.(blk) tg q)
    ** OwnM (_has_size m.(blk) m.(sz)).

  Definition points_to vaddr m mvs q : iProp :=
    OwnM (_has_size m.(blk) m.(sz))
    ** ∃ ofs, OwnM (_points_to m.(blk) ofs mvs q)
       ** has_offset vaddr m ofs.

  Definition disjoint (m m0: metadata) : Prop :=
    m.(blk) <> m.(blk).
  
  Definition valid (m: metadata) (vaddr: val) (ofs: Z) : iProp :=
    has_offset vaddr m ofs ** ⌜0 ≤ ofs < m.(sz)⌝.

  Definition weak_valid (m: metadata) (vaddr: val) (ofs: Z) : iProp :=
    has_offset vaddr m ofs ** ⌜0 ≤ ofs ≤ m.(sz)⌝.

End PROP.

Notation "vaddr '(≃_' m ) i " := (captured_to vaddr m i) (at level 10).
Notation "vaddr ⊨ m # ofs" := (has_offset vaddr m ofs) (at level 10).
Notation "'live_' q # ( m , tg )" := (metadata_alive m tg q) (at level 10).
Notation "vaddr ↦ m # q ≻ mvs" := (points_to vaddr m mvs q) (at level 20).
Notation "m #^ m0" := (disjoint m m0) (at level 20).

Section RULES.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Lemma points_to_split
      vaddr mvs0 mvs1 m q
    : 
      (vaddr ↦m#q≻ (mvs0 ++ mvs1)
      ⊢ vaddr ↦m#q≻ mvs0 ** (Val.addl vaddr (Vptrofs (Ptrofs.repr (Z.of_nat (List.length mvs0)))) ↦m#q≻ mvs1)).
  Proof.
  Admitted.

  Lemma points_to_collect
      vaddr mvs0 mvs1 m q
    : 
      
      vaddr ↦m#q≻ mvs0 ** (Val.addl vaddr (Vptrofs (Ptrofs.repr (Z.of_nat (List.length mvs0)))) ↦m#q≻ mvs1)
      ⊢ vaddr ↦m#q≻ (mvs0 ++ mvs1).
  Proof.
  Admitted.

  Lemma points_to_ownership
      vaddr mvs m q q0 q1
      (Qadd: q = (q0 + q1)%Qp)
    : 
      
      ⊢ vaddr ↦m# (q0 + q1)%Qp≻ mvs ∗-∗ vaddr ↦m#q≻ mvs.
  Proof.
  Admitted.

  Lemma allocated_disjoint
      m0 m1 tg0 tg1 q
    : 
      live_ q# (m0, tg0) ** live_ q# (m1, tg1)
      ⊢ ⌜m0 #^ m1⌝%I. 
  Proof.
  Admitted.

  Lemma allocated_ownership
      m tg q q0 q1
      (Qadd: q = (q0 + q1)%Qp)
    : 
      
      ⊢ live_ q# (m, tg) ∗-∗ live_ q0# (m, tg) ** live_ q1# (m, tg).
  Proof.
  Admitted.

  Lemma capture_offset_comm
      vaddr i m ofs
    : 
      vaddr (≃_m) i ⊢ vaddr ⊨m# ofs ∗-∗ (Vptrofs (Ptrofs.repr i)) ⊨m# ofs.
  Proof.
  Admitted.

  Lemma capture_pointto_comm
      vaddr i m q mvs
    : 
      vaddr (≃_m) i ⊢ vaddr ↦m#q≻ mvs ∗-∗ (Vptrofs (Ptrofs.repr i)) ↦m#q≻ mvs.
  Proof.
  Admitted.

  Lemma capture_neq
      vaddr0 vaddr1 i0 i1 m0 m1 q0 q1 ofs0 ofs1 tg0 tg1
    : 
      ⌜m0 #^ m1 ⌝ ** valid m0 vaddr0 ofs0 ** valid m1 vaddr1 ofs1 ** live_ q0# (m0, tg0) ** live_ q1# (m1, tg1)
      ** vaddr0 (≃_m0) i0 ** vaddr1 (≃_m1) i1 ⊢ ⌜i0 <> i1⌝.
  Proof.
  Admitted.


  Lemma capture_slide
      vaddr m i k
    :
      vaddr (≃_m) i ⊢ (Val.addl vaddr (Vptrofs (Ptrofs.repr k))) (≃_m) (i + k).
  Proof.
  Admitted.

  Lemma capture_unique
      vaddr m i j
    :
      vaddr (≃_m) i ** vaddr (≃_m) j ⊢ ⌜i = j⌝.
  Proof.
  Admitted.

  Lemma capture_dup
      vaddr m i
    :
      vaddr (≃_m) i ⊢ vaddr (≃_m) i ** vaddr (≃_m) i.
  Proof.
  Admitted.

  Lemma offset_slide
      vaddr m ofs k
      (INBOUND: ofs + k ≤ m.(sz))
    :
      vaddr ⊨m# ofs ⊢ (Val.addl vaddr (Vptrofs (Ptrofs.repr k))) ⊨m# (ofs + k).
  Proof.
  Admitted.

  Lemma offset_unique
      vaddr m ofs0 ofs1
    :
      vaddr ⊨m# ofs0 ** vaddr ⊨m# ofs1 ⊢ ⌜ofs0 = ofs1⌝.
  Proof.
  Admitted.

  Lemma offset_unique_meta
      vaddr m0 m1 ofs
    :
      vaddr ⊨m0# ofs ** vaddr ⊨m1# ofs ⊢ ⌜m0 = m1⌝.
  Proof.
  Admitted.

  Lemma offset_dup
      vaddr m ofs
    :
      vaddr ⊨m# ofs ⊢ vaddr ⊨m# ofs ** vaddr ⊨m# ofs.
  Proof.
  Admitted.

  Lemma captured_address_not_zero
      vaddr m i
    :
      vaddr (≃_m) i ⊢ ⌜Vptrofs (Ptrofs.repr i) <> Vnullptr⌝.
  Proof.
  Admitted.

  Lemma captured_pointer_notnull
      vaddr m i
    :
      vaddr (≃_m) i ⊢ ⌜Vnullptr <> vaddr⌝.
  Proof.
  Admitted.

  Lemma has_offset_notnull
      vaddr m ofs
    :
      vaddr ⊨m# ofs ⊢ ⌜Vnullptr <> vaddr⌝.
  Proof.
  Admitted.

  Lemma points_to_notnull
      vaddr m q mvs
    :
      vaddr ↦m#q≻ mvs ⊢ ⌜Vnullptr <> vaddr⌝.
  Proof.
  Admitted.

  Lemma replace_meta_to_alive
      vaddr m0 m1 q mvs i
    :
      vaddr ↦m0#q≻ mvs ** vaddr (≃_m1) i ⊢ vaddr ↦m0#q≻ mvs ** vaddr (≃_m0) i.
  Proof.
  Admitted.



  Definition cast_to_ptr (v: val) : itree Es val :=
    match v with
    | Vptr _ _ => Ret v
    | Vint _ => if Archi.ptr64 then triggerUB else Ret v
    | Vlong _ => if Archi.ptr64 then Ret v else triggerUB
    | _ => triggerUB
    end.

  Lemma liveness_ptr v m ofs
    : 
      v ⊨m# ofs ⊢ ⌜cast_to_ptr v = Ret v⌝.
  Proof.
    iIntros "A". unfold has_offset.
    destruct v; ss; des_ifs_safe;
    iDestruct "A" as "[A %]"; clarify.
  Qed.

  Lemma points_to_is_ptr v m q mvs
    : 
      v ↦m#q≻ mvs ⊢ ⌜is_ptr_val v = true⌝.
  Proof.
    iIntros "A". unfold points_to, has_offset.
    destruct v; ss; des_ifs_safe;
    iDestruct "A" as "[A B]"; clarify;
    iDestruct "B" as (ofs) "[B [C %]]"; clarify.
  Qed.

  Lemma decode_encode_ptr v m ofs 
    : 
      v ⊨m# ofs ⊢ ⌜decode_val Mptr (encode_val Mptr v) = v⌝.
  Proof.
    unfold Mptr. des_ifs.
    pose proof (decode_encode_val_general v Mint64 Mint64).
    unfold decode_encode_val in H3.
    iIntros "A". unfold has_offset.
    destruct v; try solve [iDestruct "A" as "[A %]"; clarify].
    rewrite H3. et.
  Qed.

End RULES.

Section SPEC.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition salloc_spec: fspec :=
    (mk_simple (fun n => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = n↑⌝),
                    (fun vret => ∃ m vaddr, ⌜vret = (m.(blk))↑ /\ m.(sz) = Z.of_nat n /\ n ≤ Ptrofs.max_unsigned⌝
                                 ** vaddr ↦m#1≻ List.repeat Undef n
                                 ** vaddr ⊨m# 0
                                 ** live_ 1# (m, Local))
    )))%I.

  Definition sfree_spec: fspec :=
    (mk_simple (fun '() => (
                  (ord_pure 0%nat),
                  (fun varg => ∃ m mvs vaddr,
                                ⌜varg = (m.(blk), m.(sz))↑
                                /\ Z.of_nat (List.length mvs) = m.(sz)⌝
                                ** vaddr ↦m#1≻ mvs
                                ** vaddr ⊨m# 0
                                ** live_ 1# (m, Local)),
                  (fun vret => ⌜vret = tt↑⌝)
    )))%I.

  Definition load_spec: fspec :=
    (mk_simple (fun '(chunk, vaddr, m, q, mvs) => (
                    (ord_pure 0%nat),
                    (fun varg => ∃ ofs, ⌜varg = (chunk, vaddr)↑
                                 /\ List.length mvs = size_chunk_nat chunk
                                 /\ ((size_chunk chunk) | ofs)⌝
                                 ** vaddr ⊨m# ofs
                                 ** vaddr ↦m#q≻ mvs),
                    (fun vret => ∃ v, ⌜vret = v↑ /\ decode_val chunk mvs = v⌝
                                 ** vaddr ↦m#q≻ mvs)
    )))%I.

  (* Definition loadbytes_spec: fspec :=
    (mk_simple (fun '(vaddr, sz, q, mvs) => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = (vaddr, sz)↑ /\ Z.of_nat (List.length mvs) = sz⌝ 
                                ** vaddr ⊢q#> mvs),
                    (fun vret => ⌜vret = mvs↑⌝ ** vaddr ⊢q#> mvs)
    ))). *)

  Definition store_spec: fspec :=
    (mk_simple
      (fun '(chunk, vaddr, m, v_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ mvs_old ofs, ⌜varg = (chunk, vaddr, v_new)↑
                         /\ List.length mvs_old = size_chunk_nat chunk
                         /\ ((size_chunk chunk) | ofs)⌝
                         ** vaddr ⊨m# ofs
                         ** vaddr ↦m#1≻ mvs_old),
            (fun vret => ∃ mvs_new, ⌜vret = tt↑
                         /\ encode_val chunk v_new = mvs_new⌝
                         ** vaddr ↦m#1≻ mvs_new)
    )))%I.

  (* Definition storebytes_spec: fspec :=
    (mk_simple
      (fun '(vaddr, mvs_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ mvs_old, ⌜varg = (vaddr, mvs_new)↑
                                    /\ List.length mvs_old = List.length mvs_new⌝
                                    ** vaddr ⊢1#> mvs_old),
            (fun vret => ⌜vret = tt↑⌝ ** vaddr ⊢1#> mvs_new)
    )))%I. *)

  Definition cmp_ofs (c: comparison) (ofs0 ofs1: Z) :=
    match c with
    | Ceq => ofs0 =? ofs1
    | Cne => negb (ofs0 =? ofs1)
    | Clt => ofs0 <? ofs1
    | Cle => ofs0 <=? ofs1
    | Cgt => ofs0 >? ofs1
    | Cge => ofs0 >=? ofs1
    end.

  Definition cmp_ptr_hoare0 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(c) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (c, Vnullptr, Vnullptr)↑⌝),
            (fun vret => ⌜vret = match c with
                                 | Ceq | Cle | Cge => true↑
                                 | _ => false↑
                                 end⌝)
          )%I.

  Definition cmp_ptr_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(m, q, tg) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr ofs, ⌜varg = (Ceq, Vnullptr, vaddr)↑⌝
                         ** weak_valid m vaddr ofs
                         ** live_ q# (m, tg)),
            (fun vret => ⌜vret = false↑⌝ 
                         ** live_ q# (m, tg))
          )%I.

  Definition cmp_ptr_hoare2 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(m, q, tg) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr ofs, ⌜varg = (Cne, Vnullptr, vaddr)↑⌝
                         ** weak_valid m vaddr ofs
                         ** live_ q# (m, tg)),
            (fun vret => ⌜vret = true↑⌝ 
                         ** live_ q# (m, tg))
          )%I.

  Definition cmp_ptr_hoare3 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(m, q, tg) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr ofs, ⌜varg = (Ceq, vaddr, Vnullptr)↑⌝
                         ** weak_valid m vaddr ofs
                         ** live_ q# (m, tg)),
            (fun vret => ⌜vret = false↑⌝ 
                         ** live_ q# (m, tg))
          )%I.

  Definition cmp_ptr_hoare4 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(m, q, tg) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr ofs, ⌜varg = (Cne, vaddr, Vnullptr)↑⌝
                         ** weak_valid m vaddr ofs
                         ** live_ q# (m, tg)),
            (fun vret => ⌜vret = true↑⌝ 
                         ** live_ q# (m, tg))
          )%I.

  Definition cmp_ptr_hoare5 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(c, m, ofs0, ofs1, q, tg) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr0 vaddr1, ⌜varg = (c, vaddr0, vaddr1)↑⌝
                         ** weak_valid m vaddr0 ofs0
                         ** weak_valid m vaddr1 ofs1
                         ** live_ q# (m, tg)),
            (fun vret => ⌜vret = (cmp_ofs c ofs0 ofs1)↑⌝
                         ** live_ q# (m, tg))
          )%I.

  Definition cmp_ptr_hoare6 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(m0, q0, tg0, m1, q1, tg1) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr0 vaddr1 ofs0 ofs1, ⌜varg = (Ceq, vaddr0, vaddr1)↑
                         /\ m0 #^ m1⌝
                         ** valid m0 vaddr0 ofs0
                         ** valid m1 vaddr1 ofs1
                         ** live_ q0# (m0, tg0)
                         ** live_ q1# (m1, tg1)),
            (fun vret => ⌜vret = false↑⌝ 
                         ** live_ q0# (m0, tg0)
                         ** live_ q1# (m1, tg1))
          )%I.

  Definition cmp_ptr_hoare7 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(m0, q0, tg0, m1, q1, tg1) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr0 vaddr1 ofs0 ofs1, ⌜varg = (Cne, vaddr0, vaddr1)↑
                         /\ m0 #^ m1⌝
                         ** valid m0 vaddr0 ofs0
                         ** valid m1 vaddr1 ofs1
                         ** live_ q0# (m0, tg0)
                         ** live_ q1# (m1, tg1)),
            (fun vret => ⌜vret = true↑⌝ 
                         ** live_ q0# (m0, tg0)
                         ** live_ q1# (m1, tg1))
          )%I.

  Definition cmp_ptr_spec: fspec :=
    mk_simple (
      cmp_ptr_hoare0
      @ cmp_ptr_hoare1
      @ cmp_ptr_hoare2
      @ cmp_ptr_hoare3
      @ cmp_ptr_hoare4
      @ cmp_ptr_hoare5
      @ cmp_ptr_hoare6
      @ cmp_ptr_hoare7
    ).

  Definition sub_ptr_spec : fspec :=
    (mk_simple
      (fun '(size, m, ofs0, ofs1, q, tg) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr0 vaddr1, ⌜varg = (size, vaddr0, vaddr1)↑
                         /\ 0 < size ≤ Ptrofs.max_signed⌝
                         ** weak_valid m vaddr0 ofs0
                         ** weak_valid m vaddr1 ofs1
                         ** live_ q# (m, tg)),
            (fun vret => ⌜vret = (Vptrofs (Ptrofs.repr (Z.div (ofs0 - ofs1) size)))↑⌝
                         ** live_ q# (m, tg))
    )))%I.

  Definition non_null_spec: fspec :=
    (mk_simple
      (fun '(m, q, tg) => (
            (ord_pure 0%nat),
            (fun varg => ∃ vaddr ofs, ⌜varg = vaddr↑⌝
                         ** weak_valid m vaddr ofs
                         ** live_ q# (m, tg)),
            (fun vret => ⌜vret = true↑⌝ 
                         ** live_ q# (m, tg))
    )))%I.

  (* heap malloc free *)
  Definition malloc_spec: fspec :=
    (mk_simple (fun n => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = [Vptrofs n]↑ /\ Ptrofs.unsigned n > 0⌝),
                    (fun vret => ∃ m vaddr, ⌜vret = vaddr↑ /\ m.(sz) = Ptrofs.unsigned n⌝
                                 ** vaddr ↦m#1≻ List.repeat Undef (Z.to_nat (Ptrofs.unsigned n))
                                 ** vaddr ⊨m# 0
                                 ** live_ 1# (m, Dynamic))
    )))%I.

  Definition mfree_spec: fspec :=
    (mk_simple (fun '() => (
                    (ord_pure 0%nat),
                    (fun varg => ∃ m mvs vaddr,
                                 ⌜varg = [vaddr]↑ /\ Z.of_nat (List.length mvs) = m.(sz)⌝
                                 ** vaddr ↦m#1≻ mvs
                                 ** vaddr ⊨m# 0
                                 ** live_ 1# (m, Dynamic)),
                    (fun vret => ⌜vret = Vundef↑⌝)
    )))%I.

  Definition memcpy_resource (vaddr vaddr': val) (m_src m_dst: metadata) (mvs_src mvs_dst: list memval) : iProp :=
    if Val.eq vaddr' vaddr then vaddr ↦m_dst#1≻ mvs_dst
    else vaddr' ↦m_src#1≻ mvs_src ** vaddr ↦m_dst#1≻ mvs_dst.

  Definition memcpy_spec: fspec :=
    (mk_simple
       (fun '(vaddr, vaddr', m_src, m_dst, mvs_dst) => (
            (ord_pure 0%nat),
            (fun varg => ∃ al sz mvs_src,
                         ⌜varg = (al, sz, [vaddr; vaddr'])↑
                         /\ List.length mvs_src = List.length mvs_dst
                         /\ List.length mvs_dst = sz
                         /\ (al | sz)⌝
                         ** memcpy_resource vaddr vaddr' m_src m_dst mvs_src mvs_dst),
            (fun vret => ⌜vret = Vundef↑⌝ ** memcpy_resource vaddr vaddr' m_src m_dst mvs_dst mvs_dst)
    )))%I.

  Definition capture_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '() => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = [Vnullptr]↑⌝),
            (fun vret => ⌜vret = (Vnullptr)↑⌝ )
          )%I.

  Definition capture_hoare2 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, q, ofs, tg) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = [vaddr]↑⌝
                         ** vaddr ⊨m# ofs
                         ** live_ q# (m, tg)),
            (fun vret => ∃ i, ⌜vret = (Vptrofs i)↑⌝
                         ** live_ q# (m, tg)
                         ** vaddr (≃_m) (Ptrofs.unsigned i))
          )%I.

  Definition capture_spec: fspec :=
    mk_simple (capture_hoare1 @ capture_hoare2).

  (* sealed *)
  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("salloc", salloc_spec); ("sfree", sfree_spec); 
           ("load", load_spec);
           (* ("loadbytes", loadbytes_spec);  *)
           ("store", store_spec);
           (* ("storebytes", storebytes_spec); *)
           ("sub_ptr", sub_ptr_spec); ("cmp_ptr", cmp_ptr_spec);
           ("non_null?", non_null_spec);
           ("malloc", malloc_spec); ("free", mfree_spec);
           ("memcpy", memcpy_spec);
           ("capture", capture_spec)
           ].
    Defined.

End SPEC.

Section MRS.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Variable sk: Sk.sem.
  Let skenv: SkEnv.t := Sk.load_skenv sk.

  Definition store_init_data (res : _pointstoRA) (b : block) (p : Z) (optq : option Qp) (id : init_data) : option _pointstoRA :=
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

  Fixpoint store_init_data_list (res : _pointstoRA) (b : block) (p : Z) (optq: option Qp) (idl : list init_data) {struct idl} : option _pointstoRA :=
    match idl with
    | [] => Some res
    | id :: idl' =>
        match store_init_data res b p optq id with
        | Some res' => store_init_data_list res' b (p + init_data_size id)%Z optq idl'
        | None => None
        end
    end.

  Definition alloc_global (res : Σ) (b: block) (gd : globdef clightdm_fundef type) : option Σ :=
    match gd with
    | Gfun _ => Some (GRA.embed (Auth.black (__allocated_with b Unfreeable (1/2)%Qp))
                      ⋅ GRA.embed (_has_size b 1) ⋅ res)
    | Gvar v =>
      let optq := match Globalenvs.Genv.perm_globvar v with
                  | Freeable | Writable => Some 1%Qp
                  | Readable => Some (1/2)%Qp
                  | Nonempty => None
                  end
      in
      match store_init_data_list ε b 0 optq (gvar_init v) with
      | Some res' => Some (GRA.embed (Auth.black (__allocated_with b  Unfreeable (1/2)%Qp))
                           ⋅ GRA.embed (_has_size b (init_data_list_size (gvar_init v)))
                           ⋅ GRA.embed (Auth.black res') ⋅ res)
      | None => None
      end
    end.

  Fixpoint alloc_globals (res: Σ) (b: block) (sk: list (ident * _)) : Σ :=
    match sk with
    | nil => res
    | g :: gl' => 
      let (_, gd) := g in
      match gd with
      | inl false => alloc_globals res (Pos.succ b) gl'
      | inl true => ε
      | inr gd =>
        match alloc_global res b gd with
        | Some res' => alloc_globals res' (Pos.succ b) gl'
        | None => ε
        end
      end
    end.

  Definition res_init : Σ := alloc_globals ε xH sk.

End MRS.

Section SMOD.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("salloc", mk_pure salloc_spec);
    ("sfree",   mk_pure sfree_spec);
    ("load",   mk_pure load_spec);
    (* ("loadbytes",   mk_pure loadbytes_spec); *)
    ("store",  mk_pure store_spec);
    (* ("storebytes",   mk_pure storebytes_spec); *)
    ("sub_ptr", mk_pure sub_ptr_spec);
    ("cmp_ptr", mk_pure cmp_ptr_spec);
    ("non_null?",   mk_pure non_null_spec);
    ("malloc",   mk_pure malloc_spec);
    ("free",   mk_pure mfree_spec);
    ("memcpy", mk_pure memcpy_spec);
    ("capture", mk_pure capture_spec)
    ]
  .

  Definition SMemSem sk : SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.mn := "Mem";
    SModSem.initial_mr := res_init sk ⋅ GRA.embed ((fun _ => OneShot.black) : blockaddressRA)
                          ⋅ GRA.embed ((fun b => if Coqlib.plt (Pos.of_succ_nat (List.length sk)) b then OneShot.black else OneShot.unit) : blocksizeRA);
    SModSem.initial_st := tt↑;
  |}
  .

  Import Clightdefs.ClightNotations.
  Local Open Scope clight_scope.

  Definition SMem: SMod.t := {|
    SMod.get_modsem := SMemSem;
    SMod.sk := Maps.PTree.set ($"malloc") (inr (Gfun (CExternal CEF_malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))))
                (Maps.PTree.set ($"free") (inr (Gfun (CExternal CEF_free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))))
                  (Maps.PTree.set ($"memcpy") (inr (Gfun (CExternal (CEF_memcpy 1 1) (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) (tptr tvoid) cc_default))))
                    (Maps.PTree.set ($"capture") (inr (Gfun (CExternal CEF_capture (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) (tptr tvoid) cc_default))))
                      (Maps.PTree.empty _))))
  |}
  .

  Definition Mem: Mod.t := (SMod.to_tgt (fun _ => to_stb [])) SMem.

End SMOD.

Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
Global Opaque _allocated_with.
Global Opaque _has_size.
Global Opaque _has_base.