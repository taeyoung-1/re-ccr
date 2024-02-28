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
      trigger Yield;;;
      v <- ccallU "alloc" [Vint 1];;
      `_ : val <- ccallU "store" [v; Vint 0];;
      trigger Yield;;;
      `_ : val <- ccallU "FAI" [v];;
      trigger Yield;;;
      vint <- ccallU "load" [v];;
      z <- (pargs [Tint] [vint])?;;
      trigger (Syscall "print_num" [z]↑ top1);;;
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