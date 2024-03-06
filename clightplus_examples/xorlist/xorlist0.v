Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import Any.
Require Import ClightPlusgen.
Require Import xorlist.

Definition _xor : option Mod.t := compile prog "xorlist".

Theorem valid_xor: exists xor, _xor = Some xor.
Proof. eauto. Qed.
