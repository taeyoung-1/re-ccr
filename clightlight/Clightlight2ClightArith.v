From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.

Require Import Clightlight2ClightMatch.
Require Import Clightlight2ClightGenv.

From compcert Require Import Csharpminor.

Set Implicit Arguments.

Ltac unfold_Int64_modulus := unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize in *.
Ltac unfold_Int64_max_signed := unfold Int64.max_signed, Int64.half_modulus in *; unfold_Int64_modulus.
Ltac unfold_Int64_min_signed := unfold Int64.min_signed, Int64.half_modulus in *; unfold_Int64_modulus.
Ltac unfold_Ptrofs_modulus := unfold Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize in *.
Ltac unfold_Ptrofs_half_modulus := unfold Ptrofs.half_modulus in *; unfold_Ptrofs_modulus.
Ltac unfold_Int_modulus := unfold Int.modulus, Int.wordsize, Wordsize_32.wordsize in *.
Ltac unfold_Int_max_signed := unfold Int.max_signed, Int.half_modulus in *; unfold_Int_modulus.
Ltac unfold_Int_min_signed := unfold Int.min_signed, Int.half_modulus in *; unfold_Int_modulus.

Section ARITH.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Lemma int64_ptrofs :
    Ptrofs.modulus = Int64.modulus.
  Proof. unfold_Int64_modulus. unfold_Ptrofs_modulus. des_ifs. Qed.

  Lemma int64_ext
        i0 i1
        (INTVAL: (Int64.intval i0) = (Int64.intval i1))
    :
      i0 = i1.
  Proof.
    destruct i0, i1. ss. clarify. f_equal. apply proof_irrelevance.
  Qed.

  Lemma int64_mod_ext
        i0 i1
        (INTVAL: ((Int64.intval i0) mod Int64.modulus)%Z = ((Int64.intval i1) mod Int64.modulus)%Z)
    :
      i0 = i1.
  Proof.
    destruct i0, i1. ss. rewrite Z.mod_small in INTVAL; try lia. rewrite Z.mod_small in INTVAL; try lia.
    eapply int64_ext; eauto.
  Qed.

  Lemma ptrofs_ext
        i0 i1
        (INTVAL: (Ptrofs.intval i0) = (Ptrofs.intval i1))
    :
      i0 = i1.
  Proof.
    destruct i0, i1. ss. clarify. f_equal. apply proof_irrelevance.
  Qed.

  Lemma ptrofs_mod_ext
        i0 i1
        (INTVAL: ((Ptrofs.intval i0) mod Ptrofs.modulus)%Z = ((Ptrofs.intval i1) mod Ptrofs.modulus)%Z)
    :
      i0 = i1.
  Proof.
    destruct i0, i1. ss. rewrite Z.mod_small in INTVAL; try lia. rewrite Z.mod_small in INTVAL; try lia.
    eapply ptrofs_ext; eauto.
  Qed.

  Lemma map_val_addl_comm
        defs a b v
        (VADD: Values.Val.addl a b = v)
    :
      Values.Val.addl (map_val defs a) (map_val defs b) = (map_val defs v).
  Proof.
  Admitted.

  Lemma map_val_add_comm
        defs a b v
        (VADD: Values.Val.add a b = v)
    :
      Values.Val.add (map_val defs a) (map_val defs b) = (map_val defs v).
  Proof.
  Admitted.

  Lemma map_val_sub_comm
        defs a b v
        (VADD: Values.Val.sub a b = v)
    :
      Values.Val.sub (map_val defs a) (map_val defs b) = (map_val defs v).
  Proof.
  Admitted.

  Lemma map_val_subl_comm
        defs a b v
        (VADD: Values.Val.subl a b = v)
    :
      Values.Val.subl (map_val defs a) (map_val defs b) = (map_val defs v).
  Proof.
  Admitted.

  Lemma map_val_mul_comm
        defs a b v
        (VADD: Values.Val.mul a b = v)
    :
      Values.Val.mul (map_val defs a) (map_val defs b) = (map_val defs v).
  Proof.
  Admitted.

  Lemma map_val_mull_comm
        defs a b v
        (VADD: Values.Val.mull a b = v)
    :
      Values.Val.mull (map_val defs a) (map_val defs b) = (map_val defs v).
  Proof.
  Admitted.

(*   Lemma map_val_div_comm
        defs a b v
        (VADD: Values.Val.div a b = v)
    :
      Values.Val.div (map_val defs a) (map_val defs b) = (map_val defs v).
  Proof.
  Admitted. *)

End ARITH.

