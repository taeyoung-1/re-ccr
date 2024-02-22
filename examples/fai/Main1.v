Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Set Implicit Arguments.



Section PROOF.

  Definition mainF: Any.t -> itree Es Any.t :=
    fun _ =>
      assume True;;;
      trigger Yield;;;
      trigger (Syscall "print_num" [1%Z]↑ top1);;;
      r <- trigger Yield;;
      Ret r↑
    .

  Definition MainSem: ModSem.t := {|
    ModSem.fnsems := [("main", mainF)];
    ModSem.init_st := tt↑;
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.