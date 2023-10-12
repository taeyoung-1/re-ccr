Require Import Coqlib.
From compcert Require Import Integers Ctypes.
Require Import ConvC2ITree.

#[global] Transparent Ptrofs.repr.

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
  lia.
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