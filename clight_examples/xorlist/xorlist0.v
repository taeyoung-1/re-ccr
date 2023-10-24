Require Import ITreelib.
Require Import ModSem.
Require Import Skeleton.
Require Import Any.
Require Import ClightDmgen.
Require Import xorlist.

Definition xor : Mod.t := get_mod composites global_definitions Logic.I "xorlist".