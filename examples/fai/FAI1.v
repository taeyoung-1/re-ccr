Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
Require Import ProofMode.
Require Import Mem1.

Set Implicit Arguments.



Section PROOF.

  Context {Σ : GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition has_n varg n : iProp := (∃ b ofs, ⌜varg = Vptr b ofs⌝ ** OwnM((b, ofs) |-> [Vint n]))%I.

  Definition FAIF: Any.t -> itree Es Any.t :=
    fun varg =>
      `varg : val <- varg↓?;;
      trigger Yield;;;
      σ <- trigger (Take Σ);;
      n <- trigger (Take Z);;
      assume (has_n varg n σ);;;
      trigger (Call "fai" [varg]↑);;;
      guarantee (has_n varg (n + 1) σ);;;
      r <- trigger Yield;;
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