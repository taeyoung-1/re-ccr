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

  Definition FAIF: Any.t -> itree Es Any.t :=
    fun varg =>
      varg <- varg↓?;;
      ` _ : () <- ccallU "_yield" ();;
      (if negb (val_dec varg (Vint 0))
      then
        ` _ : () <- ccallU "_yield" ();;
        trigger (Call "fai" [varg]↑);;;
        ccallU "_yield" ()
      else Ret ());;;
      ` r : () <- ccallU "_yield" ();;
      Ret r↑
    .

  Definition FAISem: ModSem.t := {|
    ModSem.fnsems := [("FAI", FAIF)];
    ModSem.init_st := tt↑;
  |}
  .

  Definition FAI: Mod.t := {|
    Mod.get_modsem := fun _ => FAISem;
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.