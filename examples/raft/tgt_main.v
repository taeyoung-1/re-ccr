Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import ImpPrelude.

Require Import tgt.

Set Implicit Arguments.

Definition tgtModules : list Mod.t := [tgt.H; tgt.CC; tgt.F; tgt.G; tgt.Main; TH1; TH2; TH3].

Definition test_itr := ModSemL.initial_itr (ModL.enclose (Mod.add_list tgtModules)) None.

