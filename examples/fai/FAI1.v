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
Require Import Mem1.

Set Implicit Arguments.



Section PROOF.

  Context {Σ : GRA.t}.
  Context `{@GRA.inG memRA Σ}.
  Variable GlobalStb: gname -> option fspec.

  Definition fai_pre b ofs v : Any.t -> Any.t -> iProp :=
    fun larg harg => 
      (⌜larg = ([Vptr b ofs])↑ /\ larg = harg⌝ ** OwnM((b, ofs) |-> [v]))%I.

  Definition fai_post b ofs v : Any.t -> Any.t -> iProp :=
    fun lret hret => 
      (∃ v', OwnM((b, ofs) |-> [v']) ** ⌜vadd v (Vint 1) = Some v' /\ lret = (Vint 0)↑ /\ hret = lret⌝)%I.

  Definition FAI_pre : () -> Any.t -> Any.t -> iProp :=
    fun _ larg harg => ⌜exists v, larg = v↑ /\ v <> Vint 0 /\ larg = harg⌝%I.

  Definition FAI_post : () -> Any.t -> Any.t -> iProp :=
    fun _ larg harg => ⌜larg = harg⌝%I.

  Definition FAIF: Any.t -> itree Es Any.t :=
    fun varg =>
      '(ctx, (t, varg)) <- HoareFunArg FAI_pre varg;;
      (* '(ctx, varg) <- ASSUME FAI_pre varg ε;; *)
      ` _ : () <- ccallU "_yield" ();;
      '(b, ofs, v) <- trigger (Take (nat * Z * val));;
      '(ctx, varg) <- ASSUME (fai_pre b ofs v) varg ctx;;
      '(ctx, vret) <- interp_hCallE_tgt GlobalStb ord_top (interp_hEs_tgt (trigger hAPC;;; trigger (Choose _))) ctx;;
      '(ctx, vret) <- ASSERT (fai_post b ofs v) vret ctx;;
      ` _ : () <- ccallU "_yield" ();;
      (* '(_, vret) <- ASSERT FAI_post vret ctx;; *)
      HoareFunRet FAI_post t (ctx, vret).

  Definition FAISem: ModSem.t := {|
    ModSem.fnsems := [("FAI", FAIF)];
    ModSem.init_st := Any.pair tt↑ (ε : Σ)↑;
  |}
  .

  Definition FAI: Mod.t := {|
    Mod.get_modsem := fun _ => FAISem;
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.