Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import ImpPrelude.

Require Import lm.
Require Import Mem0.

Set Implicit Arguments.

Definition lmModules : list Mod.t := [ListI0.List; MemI0.cMem; lm.lmMain; Mem0.Mem (fun _ => false)].

Definition test_itr := ModSem.initial_itr (Mod.enclose (Mod.add_list lmModules)) None.

