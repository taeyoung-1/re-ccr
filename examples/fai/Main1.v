Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
Require Import ProofMode.

Set Implicit Arguments.



Section PROOF.

  Context {Σ : GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition mainF: Any.t -> itree (hEs) Any.t :=
    fun _ =>
      trigger Yield;;;
      trigger (Syscall "print_num" [1%Z]↑ top1);;;
      r <- trigger Yield;;
      Ret r↑
    .

  Definition main_spec: fspec :=
    (mk_simple (fun _ : () => (
                    ord_top,
                    fun varg => True%I,
                    fun vret => True%I
    )))
    .

  Definition MainStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("main", main_spec)].
  Defined.

  Definition MainSbtb: list (gname * fspecbody) :=
    [("main", mk_specbody main_spec mainF)].

  Definition SMainSem (sk: Sk.t): SModSem.t := {|
    SModSem.fnsems := MainSbtb;
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SMain: SMod.t := {|
    SMod.get_modsem := SMainSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition Main stb: Mod.t := SMod.to_tgt stb SMain.

End PROOF.