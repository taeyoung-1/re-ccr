Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import Any.
Require Import ClightPlusgen.
Require Import xorlist.

Definition _xor : Errors.res Mod.t := compile prog "xorlist".

Theorem valid_xor: exists xor, _xor = Errors.OK xor.
Proof. eauto. Qed.
