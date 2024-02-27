Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef OpenDef.

Set Implicit Arguments.






Section PROOF.

  Context `{Σ: GRA.t}.

  Definition main_body: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;;
      `_:val <- (ccallN "echo" ([]: list val));;;
      Ret (Vint 0)
  .

  Definition MainSem: SModSem.t := {|
    SModSem.fnsems := [("main", mk_specbody fspec_trivial (cfunN main_body))];
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition Main: SMod.t := {|
    SMod.get_modsem := fun _ => MainSem;
    SMod.sk := Sk.unit;
  |}
  .
End PROOF.
