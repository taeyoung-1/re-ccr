Require Import HoareDef STB CannonRA CannonMain0 CannonMain1 Cannon0 Cannon1.
Require Import Cannon01proof CannonMain01proof.
Require Import ModSemFacts SimModSemFacts.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Hoare ProofMode.

Set Implicit Arguments.


Section PROOF.

  Let Σ: GRA.t := GRA.of_list [CannonRA].
  Local Existing Instance Σ.

  Let CannonRA_inG: @GRA.inG CannonRA Σ.
  Proof. exists 0. ss. Defined.
  Local Existing Instance CannonRA_inG.

  Section ERASE.
    Variable num_fire: nat.

    (* Let smd0 := Cannon1.SCannon.
    Let stb0 := fun sk => to_closed_stb (SMod.get_stb smd0 sk).
    Let src0 := SMod.to_src smd0.
    Let tgt0 := (SMod.to_tgt stb0) smd0.

    Let smd1 := CannonMain1.SMain num_fire.
    Let stb1 := fun sk => to_closed_stb (SMod.get_stb smd1 sk).
    Let src1 := SMod.to_src smd1.
    Let tgt1 := (SMod.to_tgt stb1) smd1. *)


    Let smd2 := SMod.add Cannon1.SCannon (CannonMain1.SMain num_fire).
    Let stb2 := fun sk => to_closed_stb (SMod.get_stb smd2 sk).
    Let src2 := SMod.to_src smd2.
    Let tgt2 := (SMod.to_tgt stb2) smd2.

    Theorem cannon_erase_spec:
      refines_closed tgt2 src2. 
    Proof.
      eapply adequacy_type_closed with (entry_r := GRA.embed Ball).
      { g_wf_tac. des_ifs. eapply BallReady_wf. }
      { unfold to_closed_stb. cbn. i. ss. clarify.
        exists tt. split; ss.
        { iIntros "H". iSplits; ss. }
        { split; ss. ii. iPureIntro. i. des. auto. }
      }
    Qed.


    
  (* Definition get_stb_list (mds: list SMod.t): Sk.t -> alist gname fspec :=
    fun sk => map (map_snd fsb_fspec) (flat_map (SModSem.fnsems ∘ (flip SMod.get_modsem sk)) mds).

    Let smd := [Cannon1.SCannon; CannonMain1.SMain num_fire].
    Let stb := fun sk => to_closed_stb (get_stb_list smd sk).
    (* Let stb := fun sk => to_closed_stb (concat (List.map (fun f => f sk) (List.map SMod.get_stb smd))). *)
    Let prog_src := List.map SMod.to_src smd.
    Let prog_tgt := List.map (SMod.to_tgt stb) smd.

    Theorem cannon_erase_spec:
      refines_closed
        (Mod.add_list prog_tgt)
        (Mod.add_list prog_src).
    Proof.
      eapply adequacy_type_closed with (entry_r := GRA.embed Ball).
      { g_wf_tac. eapply BallReady_wf. }
      { unfold to_closed_stb. cbn. i. ss. clarify.
        exists tt. split; ss.
        { iIntros "H". iSplits; ss. }
        { split; ss. ii. iPureIntro. i. des. auto. }
      }
    Qed.

    Theorem cannon_erase_spec:
      refines_closed
        (Mod.add_list prog_tgt)
        (Mod.add_list prog_src).
    Proof.
      eapply adequacy_type_closed with (entry_r := GRA.embed Ball).
      { g_wf_tac. eapply BallReady_wf. }
      { unfold to_closed_stb. cbn. i. ss. clarify.
        exists tt. split; ss.
        { iIntros "H". iSplits; ss. }
        { split; ss. ii. iPureIntro. i. des. auto. }
      }
    Qed. *)
  End ERASE.

  Lemma add_to_src
    (m1 m2 : SMod.t)
  :
    SMod.to_src (SMod.add m1 m2) = Mod.add (SMod.to_src m1) (SMod.to_src m2)
  .
  Proof. Admitted.

  Lemma add_to_tgt
  (m1 m2 : SMod.t)
  stb
:
  SMod.to_tgt stb (SMod.add m1 m2) = Mod.add (SMod.to_tgt stb m1) (SMod.to_tgt stb m2)
.
Proof. Admitted.

  Theorem cannon_1_correct:
    refines_closed
      (Mod.add_list ([Cannon0.Cannon; CannonMain0.Main 1]))
      (* (SMod.to_src (SMod.add SCannon (SMain 1))). *)
      (Mod.add_list (List.map SMod.to_src [SCannon; SMain 1])).
  Proof.
    s.
    etrans.
    2: {
      etrans. 
      { eapply cannon_erase_spec. }
      { rewrite add_to_src. unfold refines_closed. ii. apply PR. }
      }
    (* etrans; [|eapply cannon_erase_spec]. *)
    { eapply refines_close.
      rewrite add_to_tgt.
      eapply refines_add.
      { eapply Cannon01proof.correct. }
      { eapply CannonMain01proof.correct. i. ss. }
    }
  Qed.

End PROOF.
