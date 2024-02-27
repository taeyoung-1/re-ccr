Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef OpenDef.
Require Import ProofMode.
Require Import STB.
Require Import Add0.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Section SKENV.
    Definition succ_spec:    fspec :=
      mk_simple (X:=Z)
                (fun n => (
                     (ord_pure 0),
                     (fun varg =>
                        (⌜varg = [Vint n]↑⌝)%I
                     ),
                     (fun vret =>
                        (⌜vret = (Vint (n + 1))↑⌝)%I
                     )
                )).

    Definition add_body: list val -> itree hEs val :=
      fun args =>
        '(n, m) <- (pargs [Tint; Tint] args)?;;
        _ <- assume(intrange_64 m /\ m >= 0)%Z;;;
        Ret (Vint (n + m)%Z)
    .

    Definition AddSbtb: list (gname * fspecbody) :=
      [("succ", mk_specbody succ_spec (cfunU succF));
      ("add", mk_specbody fspec_trivial (cfunU add_body))].

    Definition SAddSem: SModSem.t := {|
      SModSem.fnsems := AddSbtb;
      SModSem.initial_mr := ε;
      SModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition SAdd: SMod.t := {|
    SMod.get_modsem := fun _ => SAddSem;
    SMod.sk := [("succ", Gfun↑); ("add", Gfun↑)];
  |}
  .

  Definition Add: Mod.t := (SMod.to_tgt GlobalStb) SAdd.

End PROOF.
