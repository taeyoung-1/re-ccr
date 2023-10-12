Require Import Coqlib.
Require Import ProofMode.

From compcert Require Import Integers Ctypes.

Open Scope Z.

Lemma Int_ltu_ltb: forall x y,
    0 ≤ x ≤ Int.max_unsigned
    -> 0 ≤ y ≤ Int.max_unsigned
    -> Int.ltu (Int.repr x) (Int.repr y) = (x <? y).
Proof.
    intros.
    destruct (Z.ltb_lt x y) as [? ?].
    unfold Int.ltu.
    repeat rewrite Int.unsigned_repr; et.
    destruct (x <? y) eqn: HH.
    - pose (H1 eq_refl).
    rewrite Coqlib.zlt_true; et.
    - rewrite Coqlib.zlt_false; et.
    apply Znot_lt_ge.
    intro.
    apply H2 in H3.
    inversion H3.
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

Create HintDb Int_arith.

(* #[global] Transparent Int.repr.*)
#[global] Opaque Zbits.Zzero_ext.

#[export] Hint Unfold
  Int.add
  Int.sub
  Int.mul
  Int.eq
  Int.max_unsigned
  Int.max_signed
  Int.min_signed
  Int.zero_ext
  align_attr
  bitalignof
  Coqlib.align
  bitsizeof
  align_attr
  sizeof_struct
  bytes_of_bits
  Int.half_modulus
  Int.modulus
  Int.wordsize
  Wordsize_32.wordsize
  two_p
  two_power_pos
  two_power_nat
  Archi.align_int64
  Int64.add
  Int64.sub
  Int64.mul
  Int64.eq
  Int64.max_unsigned
  Int64.max_signed
  Int64.min_signed
  Int64.zero_ext
  Int64.half_modulus
  Int64.modulus
  Int64.wordsize
  Wordsize_64.wordsize
: Int_arith.

#[export] Hint Rewrite
  Int.Z_mod_modulus_eq
  Zbits.Zzero_ext_mod
  Zbits_p_mod_two_p_trivial
  Int_ltu_ltb
  Int.repr_unsigned
  Int.unsigned_repr
  Int.repr_signed
  Int.signed_repr
  Int64.repr_unsigned
  Int64.unsigned_repr
  Int64.repr_signed
  Int64.signed_repr
: Int_arith.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Ltac simpl_int :=
  try apply Int.mkint_eq;
  repeat (repeat (autounfold with Int_arith;
    autorewrite with Int_arith; simpl);
  try match goal with
    | |- context[Archi.ptr64] => destruct Archi.ptr64; simpl
  end);
  try reflexivity;
  try lia.

Ltac solve_int :=
  simpl_int;
  try zify;
  try lia.
