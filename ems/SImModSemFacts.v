Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import ModSem.
Require Import Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Any.

Require Import SimGlobal.
Require Import Red IRed.
Require Import SimModSem.
Require Import ModSemFacts.
Import TAC.

Section ADEQUACY.

  Definition embl_st (stp: Any.t * Any.t) : Prop :=
    exists a b c, (fst stp = Any.pair a b /\ 
    snd stp = Any.pair a c).

  Lemma sim_emb_l 
    x x' (wf: unit -> Any.t * Any.t -> Prop) wf' (w:unit) it
    (WF: wf tt (x, x'))
    (WF': wf' = (fun _ '(stl, str) => match (Any.split stl), (Any.split str) with
                                      | Some (xl, _), Some (xr, _) => wf tt (xl, xr)
                                      | _, _ => False
                                      end
    ) )
    (* (SIM: sim_itree wf top2 false false w (x, it) (x', it)) *)
    (SIM: sim_fsem wf top2 (fun _ => it) (fun _ => it))
  :
    forall x1 x2, sim_itree wf' top2 false false w (Any.pair x x1, translate ModSem.emb_l it)
    (Any.pair x' x2, translate ModSem.emb_l it)
  .
  Proof.
    ginit. 
    generalize it as itr.
    revert WF. 
    generalize x as a.
    generalize x' as b.
    gcofix CIH. i.
    rewrite (itree_eta_ itr).
    destruct (observe itr).
    - (* Ret *)
    erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    gstep. apply sim_itree_ret.
    unfold lift_rel. 
    exists w. splits; et. rewrite WF'. rewrite ! Any.pair_split. et.
  - (* Tau *)
    erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    gstep. 
    apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
    eapply sim_itree_progress; et.
    gfinal. left. eapply CIH; et.
  - (* Vis *)
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    rewrite <- ! bind_trigger.
    destruct e as [c|[s|e']].
    + (* callE *)
      gstep. destruct c.
      eapply sim_itree_call; clarify.
      -- rewrite ! Any.pair_split. apply WF.
      -- i. des_ifs. 
         gfinal. left. apply Any.split_pair in Heq. apply Any.split_pair in Heq0.
         des. clarify. eapply CIH. apply WF0.
    + (* sE *)
      gstep. destruct s.
      apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
      eapply sim_itree_progress; et.
      unfold ModSem.run_l. rewrite ! Any.pair_split.
      gfinal. left. destruct (run a), (run b). ss. eapply CIH.
      
    + (* eventE *)
      gstep. destruct e, EMB.
      (* Choose *)
      * apply sim_itree_choose_tgt. i. apply sim_itree_choose_src. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH.
      (* Take *)
        * apply sim_itree_take_src. i. apply sim_itree_take_tgt. exists x0.
        eapply sim_itree_progress; et.
        gfinal. left. eapply CIH. 
      (* Syscall *)
        * apply sim_itree_syscall. i.
        eapply sim_itree_flag_down.
        gfinal. left. eapply CIH. 
  Admitted.

  Theorem adequacy_local_strong md_src md_tgt
          (SIM: ModPair.sim md_src md_tgt)
    :
    <<CR: (refines_strong md_tgt md_src)>>
  .
  Proof. 
  (* Admitted. *)
    ii. 
    unfold Mod.compile, Mod.enclose in *.
    destruct (classic (Mod.wf (Mod.add ctx md_src))).
    2:{ eapply ModSem.compile_not_wf. ss. }
    pose (sk_tgt := (Mod.sk (Mod.add ctx md_tgt))).
    pose (sk_src := (Mod.sk (Mod.add ctx md_src))).
    assert (SKEQ: sk_tgt = sk_src).
    { unfold sk_src, sk_tgt. ss. f_equal.
      inv SIM. auto. }
    rr in H.
    unfold Mod.enclose in *. fold sk_src in H. des. inv WF.
    rename SK into SKWF.
    rename wf_fnsems into FNWF.
    inv SIM. hexploit (sim_modsem (Sk.canon sk_tgt)).
    { etrans; [|eapply Sk.sort_incl]. ss. ii. eapply in_or_app. auto. }
    { ss. 
      fold sk_src in SKWF. 
      rewrite SKEQ. 
      clear - SKWF.
      unfold Sk.wf in *. ss. eapply Permutation.Permutation_NoDup; [|et].
      eapply Permutation.Permutation_map. eapply Sk.SkSort.sort_permutation. }
    i. inv H. des.
    assert (WFTGT: Mod.wf (Mod.add ctx md_tgt)).
    { rr. unfold Mod.enclose. fold sk_src sk_tgt. 
      rewrite SKEQ in *. split; auto. econs.
      match goal with
        | H: NoDup ?l0 |- NoDup ?l1 => replace l1 with l0
      end; auto. ss. unfold ModSem.add_fnsems.
      rewrite ! List.map_app. f_equal. rewrite ! List.map_map.
      eapply Forall2_eq. eapply Forall2_apply_Forall2; et.
      i. destruct a, b. inv H. ss.
    }

    eapply adequacy_local_aux in PR; et.

    { ss. ii. fold sk_src sk_tgt. rewrite <- SKEQ.
      unfold ModSem.add_fnsems. rewrite ! alist_find_app_o. des_ifs.
      { eapply alist_find_some in Heq.
        eapply in_map_iff in Heq. des. destruct x. ss. clarify.
        right. left.
        exists i0, (Mod.get_modsem ctx (Sk.sort sk_tgt)), (Mod.get_modsem md_src (Sk.sort sk_tgt)), (Mod.get_modsem md_tgt (Sk.sort sk_tgt)).
        esplits; et.
        - apply alist_find_some_iff; et.
          unfold ModSem.add_fnsems in FNWF. rewrite List.map_app in FNWF.
          apply nodup_app_l in FNWF. rewrite List.map_map in FNWF.
          revert FNWF.
          replace (fun x : string * (Any.t -> itree Es Any.t) => fst (ModSem.trans_l x)) with (fun x : string * (Any.t -> itree Es Any.t) => fst x).
          2: { extensionality x. rewrite ModSemFacts.fst_trans_l. refl. }
          rewrite SKEQ. i. et.
        - unfold sim_fsem, "==>". i. clarify.
          instantiate (1:= top2). instantiate (1:= unit). instantiate (1:= (fun _ => embl_st)). 
          ss. unfold embl_st in SIMMRS. ss. inv SIMMRS. inv H. inv H0. inv H.
          eapply sim_emb_l. destruct w. eapply self_sim_itree.
          unfold ModSem.emb_l, ModSem.run_l. ss.
          
          2: { et.  }
        
        et. des. inv sim_fnsems0.
        destruct b. esplits; ss; et. erewrite alist_find_some_iff; et.


        admit.

      }
      {
        
      }


      destruct (ModSem.fnsems (Mod.get_modsem CTX (Sk.sort sk_tgt)) fn) eqn:Hctx.
      - right. admit.
      -  
      (* revert_until SKEQ. *)
      (* pattern (Sk.sort sk_tgt) at 1. *)
      (* rewrite <- SKEQ. rewrite ! alist_find_app_o. des_ifs. *)

      esplits. instantiate (1:= le).
      instantiate (1:= wf_lift wf).
      unfold sim_fnsem in *.
      (* revert fn. *)

      hexploit (sim_fnsems fn). i.
      
      revert_until SKEQ.
      generalize (Mod.get_modsem md_src (Sk.sort sk_tgt)) as ms_src. 
      generalize (Mod.get_modsem md_tgt (Sk.sort sk_tgt)) as ms_tgt.
      unfold ModSemAdd.add_fnsems.
      i. des_ifs; et; right.
      - exists (fun _ : Any.t => triggerUB), (fun _ : Any.t => triggerUB). 
        esplits; et. 
        unfold sim_fsem, "==>". i.
        ginit. gstep. econs. ss.
      - exists (fun args : Any.t => translate ModSemAdd.emb_l (i args)), (fun args : Any.t => translate ModSemAdd.emb_l (i args)).
        esplits; et.
        unfold sim_fsem, "==>". i. rewrite H1.
        unfold wf_lift in SIMMRS. des_ifs.
        +  
        ginit. gstep. econs.

      generalize (ModSemAdd.add_fnsems (Mod.get_modsem ctx (Sk.sort sk_tgt)) ms_src) as o_src. 
      generalize (ModSemAdd.add_fnsems (Mod.get_modsem ctx (Sk.sort sk_tgt)) ms_tgt) as o_tgt.
      i.
      destruct o_src, o_tgt; et; right.
      - exists i, i0. esplits; et. apply sim_fnsems. 
      destruct (ModSem.fnsems ms_src fn); cycle 1.
      - left. et.
      - right. exists i.
    
      
      
      exists i. destruct o_tgt; cycle 1. 
        + eexists. splits; et. instantiate (1:= le). instantiate (1:=wf).
          splits.
          *     
        + exists i0. splits; et.
          unfold sim_fsem, respectful'. ii.

      (* - right. destruct (ModSem.add_fnsems (Mod.get_modsem ctx (Sk.sort sk_tgt))
        (Mod.get_modsem md_tgt (Sk.sort sk_tgt)) fn).
        + exists i. exists i0. splits; et.
          unfold sim_fsem, respectful'. i. inv H0.
     *)
    
    rewrite <- SKEQ. rewrite ! alist_find_app_o. des_ifs.
      { eapply alist_find_some in Heq.
        rewrite Mod.add_list_fnsems in Heq.
        rewrite <- fold_right_app_flat_map in Heq. ss.
        eapply in_flat_map in Heq. des.
        eapply in_map_iff in Heq0. des. destruct x1. ss. clarify.
        right. left. esplits; ss; et.
        instantiate (1:=ModSem.mn (Mod.get_modsem md_src (Sk.sort sk_tgt))).
        ii. eapply NoDup_app_disjoint.
        { rewrite List.map_app in MNWF. eapply MNWF. }
        { rewrite Mod.add_list_initial_mrs.
          rewrite <- fold_right_app_flat_map. eapply in_map.
          eapply in_flat_map. ss. esplits; et. }
        { ss. rewrite <- SKEQ. rewrite H. auto. }
      }
      { rewrite ! alist_find_map_snd. uo. des_ifs_safe ltac:(auto).
        eapply alist_find_some in Heq0. right. right.
        eapply Forall2_In_l in sim_fnsems; et. des. inv sim_fnsems0.
        destruct b. esplits; ss; et. erewrite alist_find_some_iff; et.
        { rewrite sim_mn. ss; et. }
        { inv WFTGT. inv H1. ss. rewrite List.map_app in wf_fnsems.
          apply nodup_app_r in wf_fnsems.
          rewrite List.map_map in wf_fnsems. ss. fold sk_tgt in wf_fnsems.
          erewrite List.map_ext; et. i. destruct a. ss.
        }
        { ss. inv H. ss. clarify. }
      }
    }
    { exists w_init. econs.
      { refl. }
      { ss. 
        instantiate (1:=wf).
        
        unfold ModSem.initial_p_state.
        erewrite ! alist_find_some_iff; et.
        { clear FNWF.
          match goal with
          | H: NoDup ?l0 |- NoDup ?l1 => replace l1 with l0
          end; auto. ss.
          fold sk_src. fold sk_tgt. rewrite <- SKEQ.
          rewrite ! List.map_app. f_equal. ss. f_equal. auto.
        }
        { ss. eapply in_or_app. right. ss. left. fold sk_tgt. f_equal. auto. }
        { ss. eapply in_or_app. right. ss. left. fold sk_src. rewrite SKEQ. auto. }
      }
      { ii. ss. fold sk_src sk_tgt. rewrite SKEQ. unfold ModSem.initial_p_state.
        ss. rewrite ! alist_find_app_o. des_ifs_safe.
        rewrite <- SKEQ. ss. rewrite ! eq_rel_dec_correct. des_ifs. }
    }
  Qed.

  Context {CONF: EMSConfig}.

  Theorem adequacy_local md_src md_tgt
          (SIM: ModPair.sim md_src md_tgt)
    :
      <<CR: (refines md_tgt md_src)>>
  .
  Proof.
    eapply refines_strong_refines.
    eapply adequacy_local_strong; et.
  Qed.

  (* Corollary adequacy_local_list_strong
            mds_src mds_tgt
            (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt)
    :
      <<CR: refines_strong (Mod.add_list mds_tgt) (Mod.add_list mds_src)>>
  .
  Proof. Admitted. *)


    (* r. induction FORALL; ss.
    { ii. auto. }
    (* rewrite ! Mod.add_list_cons. *)
    etrans.
    { rewrite <- Mod.add_list_single. eapply refines_strong_proper_r.
      rewrite ! Mod.add_list_single. eapply adequacy_local_strong; et. }
    replace (Mod.lift x) with (Mod.add_list [x]); cycle 1.
    { cbn. rewrite Mod.add_empty_r. refl. }
    eapply refines_strong_proper_l; et.
  Qed. *)

  (* Theorem adequacy_local2 md_src md_tgt
          (SIM: ModPair.sim md_src md_tgt)
    :
      <<CR: (refines2 [md_tgt] [md_src])>>
  .
  Proof.
    eapply ModSem.refines_strong_refines.
    eapply adequacy_local_list_strong. econs; ss.
  Qed. *)

  (* Corollary adequacy_local_list
            mds_src mds_tgt
            (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt)
    :
      <<CR: refines (Mod.add_list mds_tgt) (Mod.add_list mds_src)>>
  .
  Proof.
    eapply ModSem.refines_strong_refines.
    eapply adequacy_local_list_strong; et.
  Qed. *)

End ADEQUACY.