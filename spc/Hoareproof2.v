Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
(* Import ModSemL. *)
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import SimSTS.
Require Import HoareDef.
Require Import SimModSem.
Require Import HTactics.
From Ordinal Require Import Ordinal Arithmetic.

Set Implicit Arguments.


Module TAC.
  Ltac my_steps := repeat (_steps; des_ifs_safe).
  Ltac my_force_l := _force_l.
  Ltac my_force_r := _force_r.
End TAC.
Import TAC.

Section CANCEL.

  (*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
  Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)



  Context `{Σ: GRA.t}.

  (* Variable mds: list SMod.t. *)
  Variable md: SMod.t.

  (* Let sk: Sk.t := Sk.sort (fold_right Sk.add Sk.unit (List.map SMod.sk mds)). *)
  Let sk: Sk.t := Sk.add Sk.unit (SMod.sk md).
  (* Let skenv: SkEnv.t := Sk.load_skenv sk. *)
  (* Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) sk) mds). *)
  Let ms: SModSem.t := (SMod.get_modsem md) sk.
  (* Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss). *)
  Let sbtb := SModSem.fnsems ms.
  (* Let _stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb. *)
  Let _stb := fun fn => match (sbtb fn) with
                      | None => None 
                      | Some fsb => Some (fsb_fspec fsb)
                      end
  .

  Variable stb: gname -> option fspec.
  (* Hypothesis STBCOMPLETE:
    forall fn fsp (FIND: alist_find fn _stb = Some fsp), stb fn = Some fsp. *)
  Hypothesis STBCOMPLETE:
    forall fn fsp (FIND: _stb fn = Some fsp), stb fn = Some fsp.

  (* Hypothesis STBSOUND:
    forall fn (FIND: alist_find fn _stb = None),
      (<<NONE: stb fn = None>>) \/ (exists fsp, <<FIND: stb fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>). *)

  Hypothesis STBSOUND:
    forall fn (FIND: _stb fn = None),
      (<<NONE: stb fn = None>>) \/ (exists fsp, <<FIND: stb fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>).


  (* Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_mid2: list Mod.t := List.map (SMod.to_mid2 stb) mds. *)

  Let md_src: Mod.t := SMod.to_src md.
  Let md_mid2: Mod.t := SMod.to_mid2 stb md.

  Let W: Type := p_state.

  Opaque interp_Es.

  (* Let ms_src: ModSemL.t := ModL.enclose (Mod.add_list mds_src).
  Let ms_mid2: ModSemL.t := ModL.enclose (Mod.add_list mds_mid2). *)

  Let ms_src: ModSem.t := Mod.enclose md_src.
  Let ms_mid2: ModSem.t := Mod.enclose md_mid2.

  (* Let p_src := ModSemL.prog ms_src.
  Let p_mid2 := ModSemL.prog ms_mid2. *)

  Let p_src := ModSem.prog ms_src.
  Let p_mid2 := ModSem.prog ms_mid2.

  Require Import IRed.


  (* Lemma my_lemma__APC o (w: unit) st
    :
      paco8 (_sim_itree (fun (_: unit) '(st_src, st_tgt) => st_src = st_tgt) top2) bot8 unit unit
            (fun st_src st_tgt _ _ => st_src = st_tgt)
            false false w
            (st, Ret tt)
            (st, interp_hCallE_mid2 (_APC o)).
  Proof.
    ginit. revert w st.
    induction (Ord.lt_well_founded o); i. clear H. rename x into o. rename H0 into IH.
    rewrite unfold_APC. my_steps.
    destruct x.
    { my_steps. }
    my_steps. deflag.
    eapply IH; auto.
  Qed. *)

  Lemma my_lemma__APC o (w: unit) st (st0: st)
    :
      paco11 (_sim_itree top2) bot11 _ _ unit unit (fun (_: unit) '(st_src0, st_tgt0) => st_src0 = st_tgt0)
            (fun st_src0 st_tgt0 _ _ => st_src0 = st_tgt0)
            false false w
            (st0, Ret tt)
            (st0, interp_hCallE_mid2 (_APC _ o)).
  Proof.
    ginit. revert w st0.
    induction (Ord.lt_well_founded o); i. clear H. rename x into o. rename H0 into IH.
    rewrite unfold_APC. my_steps.
    destruct x.
    { my_steps. }
    my_steps. deflag. eapply IH; auto. 
    (* rewrite interp_mid2_bind. rewrite interp_mid2_triggere. rewrite bind_bind. 
    apply sim_itreeC_spec. eapply sim_itreeC_choose_tgt. i. rewrite bind_tau.
    apply sim_itreeC_spec. eapply sim_itreeC_tau_tgt. rewrite bind_ret_l.
    rewrite interp_mid2_bind. rewrite interp_mid2_guarantee. rewrite bind_bind.
    unfold guarantee. rewrite bind_bind. 
    apply sim_itreeC_spec. eapply sim_itreeC_choose_tgt. rewrite bind_ret_l. rewrite bind_tau. i.
    apply sim_itreeC_spec. eapply sim_itreeC_tau_tgt. rewrite bind_ret_l.
    rewrite interp_mid2_bind. rewrite interp_mid2_triggere. rewrite bind_bind.
    apply sim_itreeC_spec. eapply sim_itreeC_choose_tgt. i. rewrite bind_tau. 
    apply sim_itreeC_spec. eapply sim_itreeC_tau_tgt. rewrite bind_ret_l. 
    destruct x1. rewrite interp_mid2_bind. ired_r.
    apply sim_itreeC_spec. eapply sim_itreeC_tau_tgt. 
    apply sim_itreeC_spec. eapply sim_itreeC_choose_tgt. i. rewrite bind_tau.
    apply sim_itreeC_spec. eapply sim_itreeC_tau_tgt. rewrite bind_ret_l.
    eapply IH; auto. *)
  Qed.

  Lemma idK_spec2: forall E A B (a: A) (itr: itree E B), itr = Ret a >>= fun _ => itr. Proof. { i. ired. ss. } Qed.

  Context {CONF: EMSConfig}.
  Theorem adequacy_type_m2s:
    Beh.of_program (Mod.compile md_mid2) <1=
    Beh.of_program (Mod.compile md_src).
  Proof.
    eapply ModSem.refines_close.
    eapply (@adequacy_local_strong md_src md_mid2).
    (* eapply (@adequacy_local_list_strong mds_src mds_mid2). *)
    unfold md_src, md_mid2.
    
    (* eapply Forall2_apply_Forall2. *)
    (* { refl. } *)
    econs; ss. econs; ss.
    { instantiate (1:=fun (_ _: unit) => True). ss. }
    { instantiate (1:=fun _ '(st_src, st_tgt) => st_src = st_tgt). ii. des_ifs.
    
  


      (* eapply Forall2_apply_Forall2. *)
      (* { refl. } *)
      (* destruct b0.  *)
      (* econs; ss. *)
       ii. subst.
      unfold fun_to_src, fun_to_mid2, body_to_src, body_to_mid2. ss.
      generalize (fsb_body f y).
      revert mrs_tgt w. ginit. gcofix CIH. i. ides i.
      (* { rewrite interp_hEs_tgt_ret, interp_mid2_ret, interp_src_ret. steps. } *)
      { steps. }
      { steps. deflag. gbase. eapply CIH. }
      rewrite <- bind_trigger.
      destruct e.
      { resub. destruct h. ired_both.
        Local Transparent APC. unfold APC. Local Opaque APC.
        force_r. i. ired_both.
        steps. deflag. rewrite (idK_spec2 tt (interp_hEs_src (k ()))).
        guclo lbindC_spec. econs.
        { deflag. gfinal. right. eapply paco11_mon.
          { eapply my_lemma__APC. }
          { i. ss. }
        }
        { i. ss. subst. destruct vret_tgt. steps.
          deflag. gbase. et.
        }
      }
      destruct e.
      { resub. destruct c. steps.
        deflag. gbase. et.
      }
      destruct s0.
      { resub. destruct s0.
        { ired_both. force_r. force_l. steps.
          deflag. gbase. et.
        }
        (* { ired_both. force_r. force_l. steps.
          deflag. gbase. et.
        } *)
      }
      { resub. destruct e.
        { ired_both. force_r. i. force_l. exists x. steps.
          deflag. gbase. et.
        }
        { ired_both. force_l. i. force_r. exists x. steps.
          deflag. gbase. et.
        }
        { ired_both. steps.
          deflag. gbase. et.
        }
      }
    }
    { exists tt. ss. }
    Unshelve. all: ss.
  Qed.

End CANCEL.
