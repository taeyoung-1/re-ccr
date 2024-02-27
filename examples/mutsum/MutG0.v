Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.

Set Implicit Arguments.



Section PROOF.

  (***
    g(n) := if (n == 0) then 0 else (n + f(n-1))
  ***)
  Definition gF: list val -> itree Es val :=
    fun varg =>
      `n: Z <- (pargs [Tint] varg)?;;
      assume (intrange_64 n);;;
      if dec n 0%Z
      then Ret (Vint 0)
      else (
        m <- ccallU "f" [Vint (n - 1)];;
        r <- (vadd (Vint n) m)?;;
        Ret r).

  Definition GSem: ModSem.t := {|
    ModSem.fnsems := [("g", cfunU gF)];
    ModSem.init_st := tt↑;
  |}
  .

  Definition G: Mod.t := {|
    Mod.get_modsem := fun _ => GSem;
    Mod.sk := [("g", Gfun↑)];
  |}
  .
End PROOF.
