Require Import Coqlib.
Require Import ProofMode.
From Coq Require Import Program.
From compcert Require Import Values Integers Clightdefs.

  Lemma ptrofs_max : Archi.ptr64 = true -> Int64.max_unsigned = Ptrofs.max_unsigned.
  Proof. des_ifs_safe. Qed.
  
  Lemma mkint64_eq' x y : Int64.unsigned x = Int64.unsigned y -> x = y.
  Proof. i. destruct x. destruct y. apply Int64.mkint_eq. et. Qed.

  Local Open Scope Z_scope.

  Lemma lxor_size a b
    :
      0 ≤ a ≤ Ptrofs.max_unsigned
      -> 0 ≤ b ≤ Ptrofs.max_unsigned
      -> 0 ≤ Z.lxor a b ≤ Ptrofs.max_unsigned.
  Proof.
    i. change Ptrofs.max_unsigned with (2 ^ 64 - 1) in *.
    assert (I1: 0 ≤ a < 2 ^ 64) by nia.
    assert (I2: 0 ≤ b < 2 ^ 64) by nia. 
    assert (0 ≤ Z.lxor a b < 2 ^ 64); try nia.
    destruct (Coqlib.zeq a 0);
    destruct (Coqlib.zeq b 0); clarify.
    2: split.
    - rewrite Z.lxor_0_r. nia.
    - rewrite Z.lxor_nonneg. nia.
    - des.
      rewrite Z.log2_lt_pow2 in I3; try nia.
      rewrite Z.log2_lt_pow2 in I0; try nia.
      destruct (Coqlib.zeq (Z.lxor a b) 0); try nia.
      rewrite Z.log2_lt_pow2; cycle 1.
      + assert (0 ≤ Z.lxor a b); try nia. rewrite Z.lxor_nonneg. nia.
      + eapply Z.le_lt_trans; try apply Z.log2_lxor; try nia. 
  Qed.

  Lemma int64_ptrofs_xor_comm p1 p2 : Int64.xor (Ptrofs.to_int64 p1) (Ptrofs.to_int64 p2) = Ptrofs.to_int64 (Ptrofs.xor p1 p2).
  Proof.
    i. unfold Ptrofs.to_int64, Ptrofs.xor, Int64.xor.
    do 2 try rewrite Int64.unsigned_repr.
    2,3: change Int64.max_unsigned with Ptrofs.max_unsigned; apply Ptrofs.unsigned_range_2.
    rewrite Ptrofs.unsigned_repr; et.
    apply lxor_size; apply Ptrofs.unsigned_range_2.
  Qed.

Create HintDb ptrArith.

Hint Unfold Vptrofs Int64.xor Ptrofs.to_int64 : ptrArith.
Hint Rewrite ptrofs_max Ptrofs.unsigned_repr Int64.unsigned_repr : ptrArith.
Hint Resolve Ptrofs.unsigned_range_2 : ptrArith.

(* #[global] Transparent Ptrofs.repr.

Lemma modulus_non_zero: Ptrofs.modulus <> 0%Z.
Proof.
  unfold Ptrofs.modulus.
  unfold Ptrofs.wordsize.
  unfold Wordsize_Ptrofs.wordsize.
  destruct (Archi.ptr64); intro; inversion H.
Qed.

Lemma mul_modulus: forall x y,
Ptrofs.Z_mod_modulus
  (Ptrofs.Z_mod_modulus x * Ptrofs.Z_mod_modulus y)
= Ptrofs.Z_mod_modulus (x * y).
Proof.
  intros.
  repeat (rewrite Ptrofs.Z_mod_modulus_eq).
  symmetry.
  apply Z.mul_mod.
  apply modulus_non_zero.
Qed.

Lemma mul_modulus_l: forall x y,
Ptrofs.Z_mod_modulus
  (Ptrofs.Z_mod_modulus x * y)
= Ptrofs.Z_mod_modulus (x * y).
Proof.
  intros.
  repeat (rewrite Ptrofs.Z_mod_modulus_eq).
  apply Z.mul_mod_idemp_l.
  apply modulus_non_zero.
Qed.

Lemma mul_modulus_r: forall x y,
Ptrofs.Z_mod_modulus
  (x * Ptrofs.Z_mod_modulus y)
= Ptrofs.Z_mod_modulus (x * y).
Proof.
  intros.
  repeat (rewrite Ptrofs.Z_mod_modulus_eq).
  apply Z.mul_mod_idemp_r.
  apply modulus_non_zero.
Qed.

Lemma add_modulus: forall x y,
Ptrofs.Z_mod_modulus
  (Ptrofs.Z_mod_modulus x + Ptrofs.Z_mod_modulus y)
= Ptrofs.Z_mod_modulus (x + y).
Proof.
  intros.
  repeat (rewrite Ptrofs.Z_mod_modulus_eq).
  symmetry.
  apply Zplus_mod.
Qed.

Lemma add_modulus_l: forall x y,
Ptrofs.Z_mod_modulus
  (Ptrofs.Z_mod_modulus x + y)
= Ptrofs.Z_mod_modulus (x + y).
Proof.
  intros.
  repeat (rewrite Ptrofs.Z_mod_modulus_eq).
  apply Z.add_mod_idemp_l.
  apply modulus_non_zero.
Qed.

Lemma add_modulus_r: forall x y,
Ptrofs.Z_mod_modulus
  (x + Ptrofs.Z_mod_modulus y)
= Ptrofs.Z_mod_modulus (x + y).
Proof.
  intros.
  repeat (rewrite Ptrofs.Z_mod_modulus_eq).
  apply Z.add_mod_idemp_r.
  apply modulus_non_zero.
Qed.

Lemma Zbits_p_mod_two_p_trivial: forall (x: positive),
  (Zpos x < two_power_nat 32)%Z ->
  Zbits.P_mod_two_p x (if Archi.ptr64 then 64%nat else 32%nat) = Zpos x.
Proof.
  intros.
  rewrite Zbits.P_mod_two_p_eq.
  destruct Archi.ptr64.
  - apply Z.mod_small.
    split.
    + lia.
    + assert (two_power_nat 32 < two_power_nat 64)%Z by reflexivity.
      lia.
  - apply Z.mod_small.
    lia.
Qed.

Lemma mod_modulus_idempotent: forall x, Ptrofs.Z_mod_modulus (Ptrofs.Z_mod_modulus x) = Ptrofs.Z_mod_modulus x.
 intro.
 repeat (rewrite Ptrofs.Z_mod_modulus_eq).
 apply (Z.mod_mod).
 apply modulus_non_zero.
Qed.

Create HintDb Ptrofs_arith.

#[export] Hint Unfold
  Ptrofs.repr
  Ptrofs.add
  Ptrofs.mul
  align_attr
  bitalignof
  Coqlib.align
  bitsizeof
  align_attr
  sizeof_struct
  bytes_of_bits
  Ptrofs.modulus
  Ptrofs.wordsize
  Wordsize_Ptrofs.wordsize
: Ptrofs_arith.

#[export] Hint Rewrite
  Ptrofs.Z_mod_modulus_eq
  Zbits_p_mod_two_p_trivial
: Ptrofs_arith.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Ltac solve_ptr_eq :=
  repeat match goal with
  | H:= hide |- _ => try clear H end;
  apply Ptrofs.mkint_eq;
  repeat (autounfold with Ptrofs_arith; autorewrite with Ptrofs_arith;
  simpl);
  destruct (Archi.ptr64);
  simpl;
  unfold two_power_nat;
  simpl;
  zify;
  lia. *)
(*
Ltac rewrite_ptrofs ptr1 ptr2 :=
  let H1 := fresh in
  let H2 := fresh in
  let H2eq := fresh in
  assert (H1: ptr1 = ptr2);
  [apply Ptrofs.mkint_eq;
  repeat (autounfold with Ptrofs_arith;
  simpl);
  repeat rewrite Ptrofs.Z_mod_modulus_eq;
  unfold Ptrofs.modulus;
  unfold Ptrofs.wordsize;
  unfold Wordsize_Ptrofs.wordsize;
  destruct (Archi.ptr64);
  simpl;
  [remember (two_power_nat 64) as H2 eqn: H2eq;
  vm_compute in H2eq; rewrite H2eq|
  remember (two_power_nat 32) as H2 eqn: H2eq;
  vm_compute in H2eq; rewrite H2eq];
  simpl;
  zify;
  lia
  | rewrite H1; clear H1].

Ltac simpl_ptrofs ptr :=
  match goal with
  | [|- gpaco8 _ _ _ _ _ _ _ _ _ _ _ ?x] =>
    let H := fresh in
    pose (H := x);
    match goal with
    | [_ := context[Ptrofs.repr ?t] |- _] => rewrite_ptrofs (Ptrofs.repr t) ptr
    | [_ := context[Ptrofs.add ?t1 ?t2] |- _] => rewrite_ptrofs (Ptrofs.add t1 t2) ptr
    | [_ := context[Ptrofs.mul ?t1 ?t2] |- _] => rewrite_ptrofs (Ptrofs.mul t1 t2) ptr
    end;
    clear H
  end.

#[export] Hint Rewrite
  mul_modulus
  mul_modulus_l
  mul_modulus_r
  add_modulus
  add_modulus_l
  add_modulus_r
  Z.add_0_r
  Z.add_0_l
  Zbits_p_mod_two_p_trivial
  mod_modulus_idempotent
  using reflexivity
: Ptrofs_arith.

Ltac red_ptrofs H :=
  repeat (autounfold with Ptrofs_arith; simpl; autorewrite with Ptrofs_arith).
*)