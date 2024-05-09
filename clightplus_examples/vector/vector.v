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

  (* Variable (item : Type) (item_size : item -> nat). *)

  Definition VECTOR_INIT_CAPACITY := 4.
  Definition vector_struct_size := (size_chunk Mptr + 3 * (size_chunk Mint64))%Z.

  Definition is_vector_handler q (handler items size capacity total: val) : iProp :=
    (∃ m tag offset,
      handler (↦_m,q) (encode_val Mptr items ++ flat_map (encode_val Mint64) [size; capacity; total])
      ** handler (⊨_m,tag,q) offset
      ** ⌜(vector_struct_size | Ptrofs.unsigned offset)%Z⌝)%I.

  (* block m is allocated with qb fractional resource which is distributed over the list *)
  Definition valid_entry m qb ptr ofs vl qv size : iProp :=
    ptr (↦_m,qv) vl
    ** ptr (⊨_m,Dynamic,qb) ofs
    ** ⌜bytes_not_pure vl = false⌝
    ** ⌜(Z.of_nat size | Ptrofs.unsigned ofs)%Z⌝
    ** ⌜Datatypes.length vl = size⌝.

  Fixpoint list_points_to qb ptr m ofs memlist size : iProp :=
    match memlist with
    | [] => ptr (⊨_m,Dynamic,qb) ofs
    | [(ml, qv)] => valid_entry m qb ptr ofs ml qv size
    | (ml, qv) :: tl =>
        valid_entry m (qb/2) ptr ofs ml qv size
        ** list_points_to (qb/2)%Qp
            (Val.addl ptr (Vptrofs (Ptrofs.repr size))) m (Ptrofs.add ofs (Ptrofs.repr size)) tl size
    end.

  (* total <= capacity <= size * capacity <= Ptrofs.max_unsigned *)
  Definition is_vector vm q qb handler (size capacity total : nat) (memlist : list ((list memval) * Qp)) : iProp :=
    (∃ items unused,
      ⌜size >= 1
      /\ size * capacity <= Z.to_nat Ptrofs.max_unsigned
      /\ total <= capacity
      /\ Datatypes.length memlist = total
      /\ (total + (Datatypes.length unused))%nat = capacity
      /\ Forall (fun a => a.2 = 1%Qp) unused⌝
      ** is_vector_handler q handler items
          (Vlong (Int64.repr size)) (Vlong (Int64.repr capacity)) (Vlong (Int64.repr total))
      ** list_points_to qb items vm Ptrofs.zero (memlist ++ unused) size)%I.

End PROP.

Section SPEC.

  Fixpoint set_n {A} (l : list A) (n : nat) (a : A) :=
    match n, l with
    | O, hd :: tl => a :: tl
    | S n', hd :: tl => hd :: set_n tl n' a
    | _, [] => []
    end.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition vector_init_spec : fspec :=
    mk_simple
      (fun '(vec_ptr, size, items, usize, capacity, total) => (
        (ord_pure 1%nat),
        (fun varg =>
          ⌜varg = [vec_ptr; Vlong (Int64.repr (size : nat))]↑
          /\ (0 < size * VECTOR_INIT_CAPACITY <= Z.to_nat Ptrofs.max_unsigned)%Z⌝
          ** is_vector_handler 1 vec_ptr items usize capacity total)%I,
        (fun vret =>
          ⌜vret = Vundef↑⌝
          ** ∃ m, is_vector m 1 1 vec_ptr size 0 VECTOR_INIT_CAPACITY [])
      )).

  Definition vector_total_spec : fspec :=
    mk_simple
      (fun '(vec_ptr, vec_m, size, total, capacity, memlist, q, qb) => (
        (ord_pure 1%nat),
        (fun varg =>
          ⌜varg = [vec_ptr]↑⌝
          ** is_vector vec_m q qb vec_ptr size total capacity memlist)%I,
        (fun vret =>
          ⌜vret = (Vlong (Int64.repr total))↑⌝
          ** is_vector vec_m q qb vec_ptr size total capacity memlist)
      )).

  Definition vector_resize_spec : fspec :=
    mk_simple
      (fun '(vec_ptr, newcap, vec_m, vec_m', size, total, oldcap, memlist) => (
        (ord_pure 1%nat),
        (fun varg =>
          ⌜varg = [vec_ptr; (Vlong (Int64.repr (newcap : nat)))]↑
          /\ 0 < newcap * size < (Z.to_nat Ptrofs.max_unsigned)
          /\ total < newcap⌝
          ** is_vector vec_m 1 1 vec_ptr size total oldcap memlist)%I,
        (fun vret =>
          ⌜vret = Vundef↑⌝
          ** is_vector vec_m' 1 1 vec_ptr size total newcap memlist))
      ).

  Definition vector_add_spec : fspec :=
    mk_simple
      (fun '(vec_ptr, item_ptr, vec_m, vec_m', item, m, size, total, capacity, memlist, qitem, qbitem, tagitem, ofs) => (
        (ord_pure 1%nat),
        (fun varg =>
          ⌜varg = [vec_ptr; item_ptr]↑
          /\ Datatypes.length item = size⌝
          ** is_vector vec_m 1 1 vec_ptr size total capacity memlist
          ** item_ptr (↦_m,qitem) item
          ** item_ptr (⊨_m,tagitem,qbitem) ofs),
        (fun vret =>
          ⌜vret = Vundef↑⌝
          ** (if total <? capacity
              then is_vector vec_m 1 1 vec_ptr size (total + 1) capacity (memlist ++ [(item, 1%Qp)])
              else if capacity <? Z.to_nat Ptrofs.half_modulus
                then is_vector vec_m' 1 1 vec_ptr size (total + 1) (2 * capacity) (memlist ++ [(item, 1%Qp)])
                else True%I)
          ** item_ptr (↦_m,qitem) item
          ** item_ptr (⊨_m,tagitem,qbitem) ofs)
      )).

  Definition vector_set_spec : fspec :=
    mk_simple
      (fun '(vec_ptr, idx, item_ptr, vec_m, item, m, size, total, capacity, l1, old, l2, qb, qh, qitem, qbitem, tagitem, ofs) => (
        (ord_pure 1%nat),
        (fun varg =>
          ⌜varg = [vec_ptr; (Vlong (Int64.repr (idx : nat))); item_ptr]↑
          /\ Datatypes.length item = size
          /\ Datatypes.length l1 = idx⌝
          ** is_vector vec_m qh qb vec_ptr size total capacity (l1 ++ (old, 1%Qp) :: l2)
          ** item_ptr (↦_m,qitem) item
          ** item_ptr (⊨_m,tagitem,qbitem) ofs),
        (fun vret =>
          ⌜vret = Vundef↑⌝
          ** is_vector vec_m qh qb vec_ptr size total capacity (l1 ++ (item, 1%Qp) :: l2)
          ** item_ptr (↦_m,qitem) item
          ** item_ptr (⊨_m,tagitem,qbitem) ofs)
      )).

  Definition vector_get_spec : fspec :=
    mk_simple
      (fun '(vec_ptr, idx, vec_m, qh, item_ptr, item, qi, size, total, capacity, qb, l1, l2) => (
        (ord_pure 1%nat),
        (fun varg =>
          ⌜varg = [vec_ptr; (Vlong (Int64.repr (idx : nat)))]↑
          /\ Datatypes.length l1 = idx⌝
          ** is_vector vec_m qh qb vec_ptr size total capacity (l1 ++ (item, qi) :: l2)),
        (fun vret =>
          ⌜vret = item_ptr↑⌝
          ** is_vector vec_m qh (qb/2) vec_ptr size total capacity (l1 ++ (item, qi/2) :: l2)%Qp
          ** item_ptr (↦_vec_m,qi/2) item
          ** item_ptr (⊨_vec_m,Dynamic,qb/2) (Ptrofs.add Ptrofs.zero (Ptrofs.repr (idx * size))))
      )).

  Definition vector_delete_spec : fspec :=
    (mk_simple
      (fun '(vec_ptr, idx, vec_m, vec_m', size, total, capacity, hd, tl) => (
        (ord_pure 1%nat),
        (fun varg =>
          ⌜varg = [vec_ptr; (Vlong (Int64.repr (idx : nat)))]↑
          /\ idx < S total
          /\ Forall (fun a => a.2 = 1%Qp) tl⌝
          ** is_vector vec_m 1 1 vec_ptr size (S total) capacity ((hd, 1%Qp) :: tl)),
        (fun vret => ⌜vret = Vundef↑⌝
          ** (if (0 <? total) && (total =? (capacity / 4))%nat
              then is_vector vec_m' 1 1 vec_ptr size total (capacity / 2) tl
              else is_vector vec_m 1 1 vec_ptr size total capacity tl))
    )))%I.

  Definition vector_free_spec : fspec :=
    (mk_simple
      (fun '(vec_ptr, vec_m, size, total, capacity, memlist, items) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [vec_ptr]↑⌝
          ** is_vector vec_m 1 1 vec_ptr size total capacity memlist),
        (fun vret => ⌜vret = Vundef↑⌝
          ** is_vector_handler 1 vec_ptr items
            (Vlong (Int64.repr size)) (Vlong (Int64.repr capacity)) (Vlong (Int64.repr total)))
    )))%I.
    
  (* sealed *)
  Definition vectorStb : list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [
           ("vector_init", vector_init_spec);
           ("vector_total", vector_total_spec);
           ("vector_resize", vector_resize_spec);
           ("vector_add", vector_add_spec);
           ("vector_set", vector_set_spec);
           ("vector_get", vector_get_spec);
           ("vector_delete", vector_delete_spec);
           ("vector_free", vector_free_spec)
           ].
  Defined.

End SPEC.

Section SMOD.

  Context `{@GRA.inG pointstoRA Σ}.
  Context `{@GRA.inG allocatedRA Σ}.
  Context `{@GRA.inG blocksizeRA Σ}.
  Context `{@GRA.inG blockaddressRA Σ}.

  Definition vectorSbtb: list (gname * fspecbody) :=
    [
      ("vector_init", mk_pure vector_init_spec);
      ("vector_total", mk_pure vector_total_spec);
      ("vector_resize", mk_pure vector_resize_spec);
      ("vector_add", mk_pure vector_add_spec);
      ("vector_set", mk_pure vector_set_spec);
      ("vector_get", mk_pure vector_get_spec);
      ("vector_delete", mk_pure vector_delete_spec);
      ("vector_free", mk_pure vector_free_spec)
    ].
  
  Definition SvectorSem : SModSem.t := {|
    SModSem.fnsems := vectorSbtb;
    SModSem.mn := "vector";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}.

  Variable vector0: Mod.t.

  Definition Svector : SMod.t := {|
    SMod.get_modsem := fun _ => SvectorSem;
    SMod.sk := vector0.(Mod.sk);
  |}.

  Definition vector stb : Mod.t := (SMod.to_tgt stb) Svector.

End SMOD.