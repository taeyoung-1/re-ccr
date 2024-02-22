Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Imp.

Set Implicit Arguments.

Require Import ListI0 MemI0.

(* TODO: Try to use list module while testing memory module *)
Definition main : Any.t-> itree Es Any.t :=
  fun varg =>
  _ <- trigger (Call "init" [(Vint 568)]↑);;
  node1 <- trigger (Call "c_malloc" [(Vint 64)]↑);;
  node2 <- trigger (Call "c_malloc" [(Vint 80)]↑);;
  node3 <- trigger (Call "c_malloc" [(Vint 80)]↑);;
  `node1:val <- node1↓?;;
  `node2:val <- node2↓?;;
  `node3:val <- node3↓?;;
  _ <- trigger (Call "c_free" [node1]↑);;
  _ <- trigger (Call "c_free" [node2]↑);;
  _ <- trigger (Call "c_free" [node3]↑);;
  n1 <- trigger (Call "c_malloc" [(Vint 80)]↑);;
  n2 <- trigger (Call "c_malloc" [(Vint 80)]↑);;
  n3 <- trigger (Call "c_malloc" [(Vint 48)]↑);;
  n4 <- trigger (Call "c_malloc" [(Vint 64)]↑);;
  n5 <- trigger (Call "c_malloc" [(Vint 48)]↑);;
  _ <- trigger (Call "mem_clear" (@nil val)↑);;
  
   Ret Vundef↑
  .

Definition lmMainSem: ModSem.t := {|
  ModSem.fnsems := [("main", main)];
  ModSem.init_st := tt↑;
|}
.

Definition lmMain: Mod.t := {|
  Mod.get_modsem := fun _ => lmMainSem;
  Mod.sk := Sk.unit;
|}
.