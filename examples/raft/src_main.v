Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import ImpPrelude.

Require Import src.

Set Implicit Arguments.

Definition srcModules : list Mod.t := [src.H; src.CC; src.F; src.G; src.Main].

Definition test_itr := ModSemL.initial_itr (ModL.enclose (Mod.add_list srcModules)) None.

