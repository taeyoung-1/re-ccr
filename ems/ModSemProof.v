Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Import STS Behavior.
Require Import ModSem.
Require Import SimGlobal.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Optics.

Set Implicit Arguments.

Module ModSemAdd.
Import ModSem.

Section ADD.
  Variable M1 M2 : t.

  Definition emb_l : forall T, Es T -> Es T :=
    lmap fstl.

  Definition emb_r : forall T, Es T -> Es T :=
    lmap sndl.


  Definition add_fnsems : gname -> option (Any.t -> itree _ Any.t) :=
    fun fn =>
      match M1.(fnsems) fn, M2.(fnsems) fn with
      | Some fn_body, None => Some (fun args => translate emb_l (fn_body args))
      | None, Some fn_body => Some (fun args => translate emb_r (fn_body args))
      | Some _, Some _ => Some (fun args => triggerUB)
      | _, _ => None
      end.

  Definition add : t :=
  {|
    init_st := Any.pair (init_st M1) (init_st M2);
    fnsems := add_fnsems;
    (* idea: maintain linked-status? (boolean) *)
  |}.

End ADD.

Section PROOF.

Definition swap ab: Any.t :=
  match Any.split ab with
  | Some (a, b) => Any.pair b a
  | None => ab (* or UB? *)
  end.

Definition swap_state {X} (f: Any.t -> Any.t * X)  :=
  (fun ba => let '(ab', t) := f (swap ba) in ((swap ab'), t)).

Definition swap_Es T (es: Es T) : Es T :=
  match es with
  | inr1 (inl1 (SUpdate f)) => inr1 (inl1 (SUpdate (swap_state f)))
  | inr1 (inr1 x) => inr1 (inr1 x)
  | inl1 y => inl1 y
  end.  
  
Definition swap_ems {R} (itl: itree Es R) (itr: itree Es R) :=
  itr = translate swap_Es itl.

(* Definition assoc oa'bc: Any.t :=
  match oa'bc with
  | Some a'bc => 
    match Any.split a'bc with
    | Some (a, bc) => 
      match Any.split bc with
      | Some (b, c) => Some (Any.pair (Any.pair a b) c)
      | None => Some (a'bc)
      end
    | None => Some (a'bc)
    end
  | None => None
  end. *)


(* 
Definition assoc a'bc: Any.t :=
  match Any.split a'bc with
  | Some (a, bc) => 
      match Any.split bc with
      | Some (b, c) => (Any.pair (Any.pair a b) c)
      | None => (a'bc) (* or UB? *)
      end
    |None => (a'bc) (* or UB? *)
  end
  . 
  
Definition assoc' ab'c: Any.t :=
  match Any.split ab'c with
  | Some (ab, c) => 
      match Any.split ab with
      | Some (a, b) => (Any.pair a (Any.pair b c))
      | None => (ab'c) (* or UB? *)
      end
    |None => (ab'c) (* or UB? *)
  end
  . 

Definition assoc_state {X} (f: Any.t -> Any.t * X) :=
  (fun ab'c => let '(a'bc, t) := f (assoc' ab'c) in (assoc a'bc, t)).

Definition assoc_Es T (es: Es T) : Es T :=
  match es with
  | inr1 (inl1 (SUpdate f)) => inr1 (inl1 (SUpdate (assoc_state f)))
  | inr1 (inr1 x) => inr1 (inr1 x)
  | inl1 y => inl1 y
  end.
  
Definition assoc_ems {R} (itl: itree Es R) (itr: itree Es R) :=
  itr = translate assoc_Es itl.  *)



Lemma translate_triggerUB T (f: forall T, Es T -> Es T) (g: forall T, (Any.t -> Any.t * T) -> (Any.t -> Any.t * T))
      (F: f = (fun _ es => match es with
                        | inr1 (inl1 (SUpdate run)) => inr1 (inl1 (SUpdate (g _ run)))
                        | inr1 (inr1 x) => inr1 (inr1 x)
                        | inl1 y => inl1 y
                 end))
  :
      @triggerUB _ T _ = translate f (@triggerUB _ T _)
.
Proof.
  unfold triggerUB.
  erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
  f_equal.
  - unfold trigger. rewrite F.
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    repeat f_equal.
    extensionality v. destruct v.
  - extensionality v. destruct v.
Qed. 


Lemma swap_swap a : swap (swap a) = a.
Proof.
  i. unfold swap.
  destruct (Any.split a) eqn:A.
  - destruct p. rewrite Any.pair_split. 
    rewrite <- Any.split_pair with (a:=a); et.
  - rewrite A. et.  
Qed.


Lemma swap_ems_prog X ms0 ms1 (e: callE X)
:
      swap_ems (prog (add ms1 ms0) e) (prog (add ms0 ms1) e)
.
Proof. 
  destruct e. s. unfold unwrapU, add_fnsems. 
  des_ifs; grind; unfold swap_ems.
  - eapply translate_triggerUB; ss.
  - erewrite <- ! (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
    f_equal.
    unfold ">>>", Cat_IFun, emb_l, emb_r, lmap. 
    extensionalities T es.
    unfold swap_Es.
    destruct es as [c|[s|e]]; et.
    destruct s.
    unfold map_lens. 
    repeat (f_equal).
    unfold swap_state. 
    extensionality x. ss.
    (* destruct x; ss. *)
    destruct (Any.split x) eqn:Xspl.
    + destruct p. unfold lens_state.
        unfold swap, Lens.set, Lens.view. s.
        unfold fstl, sndl.
        rewrite ! Xspl.
        rewrite ! Any.pair_split. ss. f_equal.
        rewrite Any.pair_split. ss.
      + unfold lens_state, swap, Lens.set, Lens.view.
        unfold fstl, sndl. rewrite ! Xspl. ss.
        rewrite Any.upcast_split. et.

  - erewrite <- ! (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
    f_equal.
    unfold ">>>", Cat_IFun, emb_l, emb_r, lmap. 
    extensionalities T es. des_ifs.
    destruct s0. s. 
    repeat (f_equal).
    unfold swap_state. 
    extensionality x. ss.
    unfold lens_state, swap, Lens.set, Lens.view. s.
    unfold fstl, sndl.
    destruct (Any.split x) eqn:Xspl.
      + destruct p. s. 
        rewrite ! Any.pair_split. ss. f_equal.
        rewrite ! Any.pair_split. et.

      + ss. rewrite ! Xspl. ss.
        rewrite Any.upcast_split. et.  
  - unfold triggerUB. grind.
    erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
    f_equal.
    + unfold trigger.
      erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
      repeat f_equal.
      extensionality v. destruct v.
    + extensionality v. destruct v.
Qed.


(* Lemma assoc_ems_prog X ms0 ms1 ms2 (e: callE X)

:
  assoc_ems (prog (add ms0 (add ms1 ms2)) e) (prog (add (add ms0 ms1) ms2) e)
.
Proof.
  destruct e. s. 
  unfold unwrapU.
  repeat (unfold add_fnsems; grind).
  des_ifs; grind; unfold assoc_ems.
  - eapply translate_triggerUB. ss. 
  - eapply translate_triggerUB. ss.
  - erewrite <- ! (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
    eapply translate_triggerUB.
    unfold ">>>".
    unfold Cat_IFun.
    extensionalities T es. des_ifs.
    (* destruct es as [c|[s|e]]; unfold emb_r, lmap; et.
    destruct s. s.
    repeat f_equal.
    unfold assoc_state. s. 
    (* destruct SUpdate.  *)
    extensionality x. destruct x, p. 
    instantiate (1 := (fun _ run '(s0, s1, s2) => (s0, fst (fst (run (s1, s2) )), snd (fst (run (s1, s2))), snd (run (s1, s2))))).
     s. unfold Lens.view. des_ifs. ss.
    rewrite Heq. et. *)
  - erewrite <- translate_triggerUB with (f:=assoc_Es); ss.
    symmetry.
    eapply translate_triggerUB.
    unfold emb_l, lmap.
    extensionalities T es. des_ifs.
  - erewrite <- ! (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).

    f_equal.
    unfold ">>>", Cat_IFun.
    unfold emb_l, lmap.
    extensionalities T es. des_ifs. s.
    destruct s1. s.

    repeat f_equal. 
    unfold assoc_state. s.
    extensionality ab'c.
    unfold lens_state. s.
    unfold Lens.set, Lens.view.
    (* unfold fstl, sndl. *)
    (* unfold assoc, assoc'. *)
    f_equal.
    + unfold fstl. 
      destruct (Any.split ab'c) eqn:AB'C. 
      * destruct p as [ab c]. s.
        unfold assoc. 
        destruct (Any.split ab) eqn:AB.
        -- destruct p as [a b]. s.
           unfold assoc'. des_ifs; ss; clarify.
           4: { rewrite Any.upcast_split in Heq. inv Heq. }
           5: { admit. }
           all: admit.
        -- s. unfold assoc'. des_ifs; ss; clarify.
          ++ rewrite Any.pair_split in Heq.
        destruct (Any.split (assoc' ab'c)) eqn:A'BC. 
        -- destruct p.
          (* At this point, split t0, split t3 shouldn't be None. *)
           s. rewrite Any.pair_split.
           unfold assoc' in *. rewrite AB'C in A'BC.
           destruct (Any.split t0) eqn:T0. destruct p.
           rewrite Any.pair_split in A'BC. inv A'BC.
           ++ s. rewrite Any.pair_split. et. 
           ++ s. destruct (Any.split t3) eqn:T3. destruct p.
            ** destruct p
            --- destruct p. s. rewrite Any.pair_split in X'.
                inv X'. rewrite Any.pair_split in T3. inv T3. et.
            --- s. rewrite X' in X. inv X.

    s. destruct (Any.split x) eqn:X.
    + destruct p. s.
      destruct (Any.split t0) eqn:T0.
      * destruct p. s.
      unfold assoc_state, assoc. des_ifs.
        f_equal.
        -- s. f_equal.
           ++ f_equal.
      
      destruct (Any.split t2) eqn:T2.
        -- destruct p. s. rewrite Any.pair_split. s.
           destruct (Any.split t1) eqn:T1.
           ++ destruct p. s.
           f_equal.
           ++ 
     
    
    destruct (run (fst (fstl (fst (fstl (Some t0)))))) eqn: T0.
      (* destruct (run (fst (fstl (assoc (Some t0))))) eqn: Assoc0. *)
      s. destruct (Any.split t0) eqn:T1.
      * destruct p. s.
        destruct (Any.split t2) eqn:T2.
        -- destruct (Any.split t3) eqn: T3.
          ++ destruct p, p0. s. rewrite Any.pair_split. s.   
             f_equal.
      f_equal.
      * s. destruct (Any.split t0) eqn:T1.
        -- destruct p. f_equal. s. 
      * destruct p. s. destruct (Any.split t1) eqn: T1.
        -- destruct p. ss. destruct (Any.split t2) eqn: T2.
          ++ destruct p. ss. rewrite ! Any.pair_split. ss.
    unfold lens_state. s. 
    f_equal.
    (* Set Printing All.  *)
  - erewrite <- ! (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
    f_equal.
    unfold ">>>", Cat_IFun, emb_l, emb_r, lmap.
    extensionalities T es. des_ifs.
    destruct s2. s.
    repeat f_equal.
    extensionality x. destruct x, p. 
    s. des_ifs.
  - erewrite <- ! (bisimulation_is_eq _ _ (translate_cmpE _ _ _ _ _ _ _)).
    f_equal.
    unfold ">>>", Cat_IFun, emb_r, lmap.
    extensionalities T es. des_ifs. 
    destruct s0. s.
    repeat f_equal. 
    unfold assoc_state, lens_state.
    extensionality x. destruct x, p. s.
    f_equal.
  - unfold triggerUB. grind.
    erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
    f_equal.
    + unfold trigger.
      erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
      repeat f_equal.
      extensionality v. destruct v.
    + extensionality v. destruct v.
Qed. *)

(* Move to SimGlobal? *)
Lemma simg_map R0 R1 RR R0' R1' RR' f_src f_tgt itl itr (f0: R0 -> R0') (f1: R1 -> R1')
      (SIM: @simg R0 R1 RR f_src f_tgt itl itr)
      (IMPL: forall r0 r1, RR r0 r1 -> RR' (f0 r0) (f1 r1): Prop)
:
      @simg R0' R1' RR' f_src f_tgt (f0 <$> itl) (f1 <$> itr)
.
Proof.
  revert_until RR'.
  pcofix CIH. i.
  (* punfold SIM.  *)
  induction SIM using simg_ind; s.
  - erewrite ! (bisimulation_is_eq _ _ (map_ret _ _)). eauto with paco.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_syscall. i. right. eapply CIH; et.
    (* specialize (SIM _ _ EQ). pclearbot. et. *)
    (* edestruct SIM; et. inv H. *)
  - erewrite ! (bisimulation_is_eq _ _ (map_tau _ _)).
    pfold. apply simg_tauL; et. punfold IHSIM.
  - erewrite ! (bisimulation_is_eq _ _ (map_tau _ _)). 
    pfold. apply simg_tauR; et. punfold IHSIM.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_chooseL; et. 
    des. exists x. punfold IH.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_chooseR; et.
    i. exploit SIM. esplits. des. punfold IH.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_takeL; et.
    i. exploit SIM. esplits. des. punfold IH.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_takeR; et.
    des. exists x. punfold IH.
  - pfold. apply simg_progress; et. right. eapply CIH; et.
Qed.

Context {CONF: EMSConfig}.



Theorem add_comm
        ms0 ms1
        (P0 P1: Prop) (IMPL: P1 -> P0)
        (* (WF: wf (add ms1 ms0)) *)
  :
    <<COMM: Beh.of_program (compile (add ms0 ms1) (Some P0)) <1= Beh.of_program (compile (add ms1 ms0) (Some P1))>>
.
Proof.

  destruct (classic (P1)); cycle 1.
  { ii. eapply initial_itr_not_wf;et. }
  replace P0 with P1.
  2: { eapply prop_ext. split; auto. }
  


  unfold compile. red. apply adequacy_global_itree; et.

  unfold initial_itr, assume. i.
  rewrite ! bind_bind.
  pfold. apply simg_takeL; et. i. apply simg_takeR; et. exists x.
  apply simg_progress; et.
  rewrite ! bind_ret_l.
  left. 

  generalize (Call "main" initial_arg) as e.
  assert (REL: swap (init_st (add ms1 ms0)) = init_st (add ms0 ms1)).
  { unfold init_st, swap. ss. rewrite Any.pair_split. et. }

  revert REL.
  (* generalize (option Any.t) as X. *)
  generalize (init_st (add ms1 ms0)) as stl0.
  generalize (init_st (add ms0 ms1)) as str0.

  i. eapply simg_map.
  2: { instantiate (1 := (fun r0 r1 => snd r0 = snd r1 /\ swap (fst r0) = fst r1)).
       i. apply H0.   }
  revert_until x.
  ginit. { i. apply cpn7_wcompat. apply simg_mon. }  
  (* gcofix CIH. i. *)
  i.

  pose proof (swap_ems_prog ms0 ms1 e) as REL'.

  revert REL'.
  generalize (prog (add ms1 ms0) e) as itl.
  generalize (prog (add ms0 ms1) e) as itr.
  rewrite <- REL. (* generalize states with swap relation *)
  generalize stl0 as stl. 
  gcofix CIH'. i.
  inv REL'.
  rewrite (itree_eta_ itl).
  destruct (observe itl).
  - (* Ret *)
    erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    rewrite ! interp_Es_ret.
    gstep. apply simg_ret. et.   
  - (* Tau *)
    erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    rewrite ! interp_Es_tau.
    gstep. apply simg_tauL; et. apply simg_tauR; et. 
    apply simg_progress; et.
    gfinal. left. eapply CIH'. ss.
  - (* Vis *)
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    destruct e0 as [c|[s|e0]].
    + (* callE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es X (@prog (add ms1 ms0)) (@ITree.trigger Es X (@inl1 callE (sum1 sE eventE) X c)) stl). 
      pattern (@interp_Es X (@prog (add ms0 ms1)) (@ITree.trigger Es X (@swap_Es X (@inl1 callE (sum1 sE eventE) X c)))
      (swap stl)).
      setoid_rewrite interp_Es_callE.
      setoid_rewrite interp_Es_callE.
      rewrite ! bind_tau.
      gstep. apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      rewrite <- ! interp_Es_bind.
    
      gfinal. left. eapply CIH'.
      unfold swap_ems. erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
      f_equal. apply swap_ems_prog.

    + (* sE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es X (@prog (add ms1 ms0))
      (@ITree.trigger Es X (@inr1 callE (sum1 sE eventE) X (@inl1 sE eventE X s))) stl).
      pattern (@interp_Es X (@prog (add ms0 ms1))
      (@ITree.trigger Es X (@swap_Es X (@inr1 callE (sum1 sE eventE) X (@inl1 sE eventE X s)))) 
      (swap stl)).
      setoid_rewrite interp_Es_sE.
      grind.
      setoid_rewrite interp_Es_sE.
      grind.
      gstep. 
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      unfold swap_state in *. rewrite swap_swap in Heq0. 
      rewrite Heq in Heq0. inv Heq0.
      gfinal. left. eapply CIH'. unfold swap_ems. et.

    + (* eventE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es X (@prog (add ms1 ms0))
      (@ITree.trigger Es X (@inr1 callE (sum1 sE eventE) X (@inr1 sE eventE X e0))) stl).
      pattern (@interp_Es X (@prog (add ms0 ms1))
      (@ITree.trigger Es X (@swap_Es X (@inr1 callE (sum1 sE eventE) X (@inr1 sE eventE X e0)))) 
      (swap stl)).
      setoid_rewrite interp_Es_eventE.
      setoid_rewrite interp_Es_eventE.
      grind. 
      gstep.
      destruct e0.
      * (* Choose *)
        apply simg_chooseR; et. i. apply simg_chooseL; et. exists x0.
        grind.
        apply simg_tauL; et. apply simg_tauR; et.
        apply simg_tauL; et. apply simg_tauR; et.
        apply simg_progress; et.
        gfinal. left. apply CIH'. unfold swap_ems. et.
      * (* Take *)
        apply simg_takeL; et. i. apply simg_takeR; et. exists x0.
        grind.
        apply simg_tauL; et. apply simg_tauR; et.
        apply simg_tauL; et. apply simg_tauR; et.
        apply simg_progress; et.
        gfinal. left. apply CIH'. unfold swap_ems. et.
      * (* Syscall *)
        apply simg_syscall. i. inv EQ.
        grind. 
        gstep.
        apply simg_tauL; et. apply simg_tauR; et.
        apply simg_tauL; et. apply simg_tauR; et.
        apply simg_progress; et.
        gfinal. left. apply CIH'. unfold swap_ems. et.

Qed.



(* Lemma add_assoc' ms0 ms1 ms2:
  add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
Proof. Admitted.
  (* induction ms2; ss. unfold add. f_equal; ss.
  { eapply app_assoc. }
  { eapply app_assoc. }
Qed. *)

Lemma add_assoc_eq ms0 ms1 ms2
  :
    add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
Proof. Admitted.
  (* unfold add. ss. f_equal.
  { apply List.app_assoc. }
  { apply List.app_assoc. }
Qed. *) *)


(* TODO: Define aux for both comm / assoc. *)
Lemma add_assoc_aux
        ms0 ms1 ms2
  :
        paco7 _simg bot7 Any.t Any.t eq false false
        (snd <$> interp_Es (prog (add (add ms0 ms1) ms2)) (prog (add (add ms0 ms1) ms2) (Call "main" initial_arg)) (init_st (add (add ms0 ms1) ms2)))
        (snd <$> interp_Es (prog (add ms0 (add ms1 ms2))) (prog (add ms0 (add ms1 ms2)) (Call "main" initial_arg)) (init_st (add ms0 (add ms1 ms2))))
.
Proof. Admitted.
  (* generalize (Call "main" initial_arg) as e.
  assert (REL: assoc (init_st (add ms0 (add ms1 ms2))) = init_st (add (add ms0 ms1) ms2)).
  { unfold init_st, assoc. ss. rewrite ! Any.pair_split. et. }
  revert REL.

  generalize (init_st (add (add ms0 ms1) ms2)) as stl0.
  generalize (init_st (add ms0 (add ms1 ms2))) as str0.

  i. eapply simg_map.
  2: { instantiate (1 := (fun r0 r1 => snd r0 = snd r1 /\ fst r0 = (assoc (fst r1)))).
       i. apply H. }
    
  revert_until ms2.
  ginit. { i. apply cpn7_wcompat. apply simg_mon. }
  gcofix CIH. i.

  pose proof (assoc_ems_prog ms0 ms1 ms2 e) as REL'.
  revert REL'.

  generalize (prog (add (add ms0 ms1) ms2) e) as itl.
  generalize (prog (add ms0 (add ms1 ms2)) e) as itr.
  rewrite <- REL.
  generalize str0 as str.

  gcofix CIH'. i.
  inv REL'.
    
  rewrite (itree_eta_ itr).
  destruct (observe itr).

  - (* Ret *)
    erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    rewrite ! interp_Es_ret.
    gstep. apply simg_ret. et.
  - (* Tau *)
    erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    rewrite ! interp_Es_tau.
    gstep. apply simg_tauL; et. apply simg_tauR; et. 
    apply simg_progress; et.
    gfinal. left. eapply CIH'. ss.
  - (* Vis *)
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    destruct e0 as [c|[s|e0]].
    + (* call E *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es X (@prog (add (add ms0 ms1) ms2)) (@ITree.trigger Es X (@assoc_Es X (@inl1 callE (sum1 sE eventE) X c))) (assoc str)).
      pattern (@interp_Es X (@prog (add ms0 (add ms1 ms2))) (@ITree.trigger Es X (@inl1 callE (sum1 sE eventE) X c)) str).
      setoid_rewrite interp_Es_callE.
      setoid_rewrite interp_Es_callE.
      rewrite ! bind_tau.
      gstep. apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      rewrite <- ! interp_Es_bind.
    
      gfinal. left. eapply CIH'.
      unfold assoc_ems. erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
      f_equal. apply assoc_ems_prog.
    + (* sE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es X (@prog (add (add ms0 ms1) ms2)) (@ITree.trigger Es X (@assoc_Es X (@inr1 callE (sum1 sE eventE) X (@inl1 sE eventE X s)))) (assoc str)).
      pattern (@interp_Es X (@prog (add ms0 (add ms1 ms2))) (@ITree.trigger Es X (@inr1 callE (sum1 sE eventE) X (@inl1 sE eventE X s))) str).
      setoid_rewrite interp_Es_sE.
      grind.
      (* Set Printing All. *)
      pattern (@interp_Es X (@prog (add (add ms0 ms1) ms2))
      (@ITree.trigger Es X (@inr1 callE (sum1 sE eventE) X (@inl1 sE eventE X (@SUpdate X (@assoc_state X run))))) (assoc str)).
      setoid_rewrite interp_Es_sE.
      grind.
      gstep. 
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      unfold assoc_state in *. 
      (* make lemma of assoc_assoc *)
      assert (assoc_assoc: forall x, assoc' (assoc x) = x). 
      { i. unfold assoc, assoc'. des_ifs.
        - rewrite Any.pair_split in Heq1.
          inv Heq1. inv Heq4. 
          rewrite Any.pair_split in Heq2.
          inv Heq2. rewrite <- Any.split_pair with (a:=x1); et.
          rewrite Heq3. f_equal. f_equal.
          rewrite <- Any.split_pair with (a:=t7); et.
        all: admit.
      }
      admit.
      (* rewrite assoc_assoc in Heq0.
      destruct str. destruct s4. inv Heq1.
      (* rewrite H0 in Heq. *)
      assert (SSS: (s, x) = (s1, (s0, s3), x0)). { rewrite <- H0, <- Heq. et. }
      inv SSS.
      gfinal. left.
      replace (s1, s0, s3) with (assoc (s1, (s0, s3))); et.
      eapply CIH'. unfold assoc_ems. et. *)
  + (* eventE *)
    rewrite <- ! bind_trigger, ! interp_Es_bind. admit.
    (* Set Printing All. *)
    pattern (@interp_Es (prod (prod (state ms0) (state ms1)) (state ms2)) X0 (@prog (add (add ms0 ms1) ms2))
    (@ITree.trigger (Es (prod (prod (state ms0) (state ms1)) (state ms2))) X0
       (@assoc_Es (state ms0) (state ms1) (state ms2) X0
          (@inr1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 (@inr1 (sE (state (add ms0 (add ms1 ms2)))) eventE X0 e0))))
    (@assoc (state ms0) (state ms1) (state ms2) str)).
    pattern (@interp_Es (state (add ms0 (add ms1 ms2))) X0 (@prog (add ms0 (add ms1 ms2)))
    (@ITree.trigger (Es (state (add ms0 (add ms1 ms2)))) X0
       (@inr1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 (@inr1 (sE (state (add ms0 (add ms1 ms2)))) eventE X0 e0))) str).
    setoid_rewrite interp_Es_eventE.
    setoid_rewrite interp_Es_eventE.
    grind.
    gstep.
    destruct e0.
    * (* Choose *)
      apply simg_chooseR; et. i. apply simg_chooseL; et. exists x.
      grind.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      gfinal. left. apply CIH'. unfold assoc_ems. et.
    * (* Take *)
      apply simg_takeL; et. i. apply simg_takeR; et. exists x.
      grind.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      gfinal. left. apply CIH'. unfold assoc_ems. et.
    * (* Syscall *)
      apply simg_syscall. i. inv EQ.
      grind. 
      gstep.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      gfinal. left. apply CIH'. unfold assoc_ems. et.
Qed.  *)

Lemma add_assoc_rev_aux
        ms0 ms1 ms2
  :
        paco7 _simg bot7 Any.t Any.t eq false false
        (snd <$> interp_Es (prog (add ms0 (add ms1 ms2))) (prog (add ms0 (add ms1 ms2)) (Call "main" initial_arg)) (init_st (add ms0 (add ms1 ms2))))
        (snd <$> interp_Es (prog (add (add ms0 ms1) ms2)) (prog (add (add ms0 ms1) ms2) (Call "main" initial_arg)) (init_st (add (add ms0 ms1) ms2)))
.
Proof. Admitted.
  (* generalize (Call "main" initial_arg) as e.
  assert (REL: assoc (init_st (add ms0 (add ms1 ms2))) = init_st (add (add ms0 ms1) ms2)).
  { unfold init_st. et. }
  revert REL.

  generalize (Any.t) as X.
  generalize (init_st (add ms0 (add ms1 ms2))) as stl0.
  generalize (init_st (add (add ms0 ms1) ms2)) as str0.

  i. eapply simg_map.
  2: { instantiate (1 := (fun r0 r1 => snd r0 = snd r1 /\ assoc (fst r0) = fst r1)).
       i. apply H. }
    
  revert_until ms2.
  ginit. { i. apply cpn7_wcompat. apply simg_mon. }
  gcofix CIH. i.

  pose proof (assoc_ems_prog ms0 ms1 ms2 e) as REL'.
  revert REL'.

  generalize (prog (add ms0 (add ms1 ms2)) e) as itl.
  generalize (prog (add (add ms0 ms1) ms2) e) as itr.
  rewrite <- REL.
  generalize stl0 as stl.

  gcofix CIH'. i.
  inv REL'.
    
  rewrite (itree_eta_ itl).
  destruct (observe itl).

  - (* Ret *)
    erewrite ! (bisimulation_is_eq _ _ (translate_ret _ _)).
    rewrite ! interp_Es_ret.
    gstep. apply simg_ret. et.
  - (* Tau *)
    erewrite ! (bisimulation_is_eq _ _ (translate_tau _ _)).
    rewrite ! interp_Es_tau.
    gstep. apply simg_tauL; et. apply simg_tauR; et. 
    apply simg_progress; et.
    gfinal. left. eapply CIH'. ss.
  - (* Vis *)
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    destruct e0 as [c|[s|e0]].
    + (* callE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es (state (add ms0 (add ms1 ms2))) X0 (@prog (add ms0 (add ms1 ms2)))
      (@ITree.trigger (Es (state (add ms0 (add ms1 ms2)))) X0 (@inl1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 c)) stl).
      pattern (@interp_Es (prod (prod (state ms0) (state ms1)) (state ms2)) X0 (@prog (add (add ms0 ms1) ms2))
      (@ITree.trigger (Es (prod (prod (state ms0) (state ms1)) (state ms2))) X0
         (@assoc_Es (state ms0) (state ms1) (state ms2) X0 (@inl1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 c)))
      (@assoc (state ms0) (state ms1) (state ms2) stl)).
      setoid_rewrite interp_Es_callE.
      setoid_rewrite interp_Es_callE.
      rewrite ! bind_tau.
      gstep. apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      rewrite <- ! interp_Es_bind.
    
      gfinal. left. eapply CIH'.
      unfold assoc_ems. erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
      f_equal. apply assoc_ems_prog.
    + (* sE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es (state (add ms0 (add ms1 ms2))) X0 (@prog (add ms0 (add ms1 ms2)))
      (@ITree.trigger (Es (state (add ms0 (add ms1 ms2)))) X0
         (@inr1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 (@inl1 (sE (state (add ms0 (add ms1 ms2)))) eventE X0 s))) stl).
      pattern (@interp_Es (prod (prod (state ms0) (state ms1)) (state ms2)) X0 (@prog (add (add ms0 ms1) ms2))
      (@ITree.trigger (Es (prod (prod (state ms0) (state ms1)) (state ms2))) X0
         (@assoc_Es (state ms0) (state ms1) (state ms2) X0
            (@inr1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 (@inl1 (sE (state (add ms0 (add ms1 ms2)))) eventE X0 s))))
      (@assoc (state ms0) (state ms1) (state ms2) stl)).

      setoid_rewrite interp_Es_sE.
      grind.
      setoid_rewrite interp_Es_sE.
      grind.
      gstep. 
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      destruct stl. destruct s4. inv Heq1.
      (* rewrite H0 in Heq. *)
      assert (SSS: (s, x) = (s1, (s0, s3), x0)). { rewrite <- H0, <- Heq. et. }
      inv SSS.
      gfinal. left.
      replace (s1, s0, s3) with (assoc (s1, (s0, s3))); et.
      eapply CIH'. unfold assoc_ems. et.
  + (* eventE *)
    rewrite <- ! bind_trigger, ! interp_Es_bind.
    Set Printing All.

    pattern  (@interp_Es (state (add ms0 (add ms1 ms2))) X0 (@prog (add ms0 (add ms1 ms2)))
    (@ITree.trigger (Es (state (add ms0 (add ms1 ms2)))) X0
       (@inr1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 (@inr1 (sE (state (add ms0 (add ms1 ms2)))) eventE X0 e0))) stl).
    pattern  (@interp_Es (prod (prod (state ms0) (state ms1)) (state ms2)) X0 (@prog (add (add ms0 ms1) ms2))
    (@ITree.trigger (Es (prod (prod (state ms0) (state ms1)) (state ms2))) X0
       (@assoc_Es (state ms0) (state ms1) (state ms2) X0
          (@inr1 callE (sum1 (sE (state (add ms0 (add ms1 ms2)))) eventE) X0 (@inr1 (sE (state (add ms0 (add ms1 ms2)))) eventE X0 e0))))
    (@assoc (state ms0) (state ms1) (state ms2) stl)).

    setoid_rewrite interp_Es_eventE.
    setoid_rewrite interp_Es_eventE.
    grind.
    gstep.
    destruct e0.
    * (* Choose *)
      apply simg_chooseR; et. i. apply simg_chooseL; et. exists x.
      grind.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      gfinal. left. apply CIH'. unfold assoc_ems. et.
    * (* Take *)
      apply simg_takeL; et. i. apply simg_takeR; et. exists x.
      grind.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      gfinal. left. apply CIH'. unfold assoc_ems. et.
    * (* Syscall *)
      apply simg_syscall. i. inv EQ.
      grind. 
      gstep.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      gfinal. left. apply CIH'. unfold assoc_ems. et.
Qed. *)


Theorem add_assoc
        ms0 ms1 ms2 P
  :
    <<COMM: Beh.of_program (compile (add ms0 (add ms1 ms2)) P) <1=
            Beh.of_program (compile (add (add ms0 ms1) ms2) P)>>
.
Proof. 

  unfold compile. red. apply adequacy_global_itree; et.
  unfold initial_itr, assume. 
  destruct P.
  - rewrite ! bind_bind. pfold.
    apply simg_takeL; et. i. apply simg_takeR; et. exists x.
    apply simg_progress; et.
    rewrite ! bind_ret_l.
    left. apply add_assoc_aux.
  - rewrite ! bind_ret_l. apply add_assoc_aux.
Qed.




Theorem add_assoc_rev
        ms0 ms1 ms2 P
  :
    <<COMM: Beh.of_program (compile (add (add ms0 ms1) ms2) P) <1=
            Beh.of_program (compile (add ms0 (add ms1 ms2)) P)>>
.
Proof.
  unfold compile. red. apply adequacy_global_itree; et.
  unfold initial_itr, assume. 
  destruct P.
  - rewrite ! bind_bind. pfold.
    apply simg_takeL; et. i. apply simg_takeR; et. exists x.
    apply simg_progress; et.
    rewrite ! bind_ret_l.
    left. apply add_assoc_rev_aux.
  - rewrite ! bind_ret_l. apply add_assoc_rev_aux.
Qed.

End PROOF.
End ModSemAdd.

Module ModAdd.
Import Mod.
Section BEH.

Context `{Sk.ld}.
Context {CONF: EMSConfig}.

(* Definition compile (md: t): semantics :=
  ModSem.compile_itree (ModSem.initial_itr md.(enclose) (Some (wf md))). *)


Definition compile (md: t): semantics :=
  ModSem.compile_itree (ModSem.initial_itr md.(enclose) (Some (wf md))).


(*** wf about modsem is enforced in the semantics ***)

Definition add (md0 md1: t): t := {|
  get_modsem := fun sk =>
                  ModSemAdd.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
  sk := Sk.add md0.(sk) md1.(sk);
|}
.


(* Definition add (md0 md1: t): t := {|
  get_modsem := fun sk =>
                  ModSem.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
  sk := Sk.add md0.(sk) md1.(sk);
|}
. *)
(* 
Lemma enclose_eq md0 md1 ms0 ms1
    (ENCL0: enclose md0 = ms0)
    (ENCL1: enclose md1 = ms1)
  :
    enclose (add md0 md1) = (ModSem.add ms0 ms1)
.
Proof.
  unfold enclose, get_modsem. simpl in *. f_equal.
  - unfold enclose in *.   *)



Theorem add_comm
        md0 md1
  :
    <<COMM: Beh.of_program (compile (add md0 md1)) <1= Beh.of_program (compile (add md1 md0))>>
.
Proof.
Admitted.
  (* unfold compile. red. apply adequacy_global_itree; et.
  unfold ModSem.initial_itr, assume.
  
  rewrite ! bind_bind.
  pfold. apply simg_takeL; et. i.
   apply simg_takeR; et.
  assert (SK: Sk.wf (Sk.add (sk md0) (sk md1))). { apply Sk.wf_comm. et. }
  exists SK.
  apply simg_progress; et.
  rewrite ! bind_ret_l.
  left.
  (* May need a lemma about enclose: 
      enclose (add md0 md1) = add ms0 ms1
  *)
  unfold enclose.



ii. unfold compile in *.
  destruct (classic (Sk.wf (sk (add md1 md0)))).
  (* 2: { eapply ModSem.initial_itr_not_wf. ss. } *)
  ss. des. assert (SK: Sk.wf (Sk.add (sk md0) (sk md1))).
  { apply Sk.wf_comm. auto. }
  rewrite Sk.add_comm; et.
  eapply ModSemAdd.add_comm; [|et].
  { i. auto. }
  {  }
Qed. *)



(* Lemma add_assoc' ms0 ms1 ms2:
  add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
Proof.
  unfold add. f_equal.
  { extensionality skenv_link. ss. apply ModSem.add_assoc'. }
  { ss. rewrite Sk.add_assoc. auto. }
Qed. *)

Theorem add_assoc
        md0 md1 md2
  :
    <<COMM: Beh.of_program (compile (add md0 (add md1 md2))) =
            Beh.of_program (compile (add (add md0 md1) md2))>>
.
Proof. Admitted.
  (* rewrite add_assoc'. ss.
Qed. *)

Theorem add_assoc_rev
        md0 md1 md2
  :
    <<COMM: Beh.of_program (compile (add (add md0 md1) md2)) =
            Beh.of_program (compile (add md0 (add md1 md2)))>>
.
Proof. Admitted.
  (* rewrite add_assoc'. ss.
Qed. *)

Lemma add_empty_r 
      md
  : 
    << EMPTY: Beh.of_program (compile (add md empty)) =
              Beh.of_program (compile md)>>
.
Proof. Admitted.

Lemma add_empty_l 
      md
  : 
    << EMPTY: Beh.of_program (compile (add empty md)) =
              Beh.of_program (compile md)>>
.
Proof. Admitted.


(* Lemma add_empty_r md: add md empty = md.
Proof.
  destruct md; ss.
  unfold add, ModSem.add. f_equal; ss.
  - extensionality skenv. destruct (get_modsem0 skenv); ss.
    repeat rewrite app_nil_r. auto.
  - eapply Sk.add_unit_r.
Qed.

Lemma add_empty_l md: add empty md = md.
Proof.
  destruct md; ss.
  unfold add, ModSem.add. f_equal; ss.
  { extensionality skenv. destruct (get_modsem0 skenv); ss. }
  { apply Sk.add_unit_l. }
Qed. *)


Definition add_list (xs: list t): t :=
  fold_right add empty xs
.

(* Lemma add_list_single: forall (x: t), add_list [x] = x.
Proof. ii; cbn. rewrite add_empty_r. refl. Qed. *)

Definition add_list_cons
          x xs
        :
          (add_list (x::xs) = (add x (add_list xs)))
.
Proof. ss. Qed.
(* 
Definition add_list_snoc
          x xs
        :
          add_list (snoc xs x) = add (add_list xs) x
.
Proof. ginduction xs; ii; ss. Admitted. *)

Definition add_list_snoc
          x xs
        :
          << SNOC: Beh.of_program (compile (add_list (snoc xs x))) = 
                   Beh.of_program (compile (add (add_list xs) x)) >>
.
Proof. Admitted.
  (* ginduction xs; ii; ss.
  { cbn. rewrite add_empty_l, add_empty_r. et. }
  { cbn. rewrite <- add_assoc'.  r in IHxs. r. f_equal.}  *)

End BEH.
End ModAdd.

Section REFINE.
  Context `{Sk.ld}.

   Definition refines {CONF: EMSConfig} (md_tgt md_src: Mod.t): Prop :=
     (* forall (ctx: list Mod.t), Beh.of_program (ModL.compile (add_list (md_tgt :: ctx))) <1= *)
     (*                           Beh.of_program (ModL.compile (add_list (md_src :: ctx))) *)
     forall (ctx: list Mod.t), Beh.of_program (ModAdd.compile (ModAdd.add (ModAdd.add_list ctx) md_tgt)) <1=
                               Beh.of_program (ModAdd.compile (ModAdd.add (ModAdd.add_list ctx) md_src))
   .

   Definition refines_strong (md_tgt md_src: Mod.t): Prop :=
     forall {CONF: EMSConfig}, refines md_tgt md_src.


   Section CONF.
   Context {CONF: EMSConfig}.

   Definition refines2 (md_tgt md_src: list Mod.t): Prop :=
     forall (ctx: list Mod.t), Beh.of_program (ModAdd.compile (ModAdd.add (ModAdd.add_list ctx) (ModAdd.add_list md_tgt))) <1=
                               Beh.of_program (ModAdd.compile (ModAdd.add (ModAdd.add_list ctx) (ModAdd.add_list md_src)))
   .

   
   (* Global Program Instance refines2_PreOrder: PreOrder refines2.
   Next Obligation.
     ii. ss.
   Qed.
   Next Obligation.
     ii. eapply H0 in PR. eapply H1 in PR. eapply PR.
   Qed. *)

   (*** vertical composition ***)
   Global Program Instance refines_PreOrder: PreOrder refines.

   Next Obligation. ii. ss. Qed.
   Next Obligation. ii. eapply H1. eapply H0. ss. Qed.


   Global Program Instance refines_strong_PreOrder: PreOrder refines_strong.
   Next Obligation. ii. ss. Qed.
   Next Obligation. ii. eapply H1. eapply H0. ss. Qed.



   (*** horizontal composition ***)
   Theorem refines_add
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines md0_tgt md0_src)
         (SIM1: refines md1_tgt md1_src)
     :
       <<SIM: refines (ModAdd.add md0_tgt md1_tgt) (ModAdd.add md0_src md1_src)>>
   .
   Proof. Admitted.
(*    
     ii. r in SIM0. r in SIM1.
     (***
ctx (a0 b0)
(ctx a0) b0
(ctx a0) b1
      ***)
     rewrite ModAdd.add_assoc in PR.
     specialize (SIM1 (snoc ctx md0_tgt)). spc SIM1. rewrite ModAdd.add_list_snoc in SIM1.  eapply SIM1 in PR.
     (***
ctx (a0 b1)
(a0 b1) ctx
a0 (b1 ctx)
(b1 ctx) a0
      ***)
     rewrite <- ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     rewrite <- ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     (***
(b1 ctx) a1
a1 (b1 ctx)
(a1 b1) ctx
ctx (a1 b1)
      ***)
     specialize (SIM0 (cons md1_src ctx)). spc SIM0. rewrite ModAdd.add_list_cons in SIM0. eapply SIM0 in PR.
     eapply ModAdd.add_comm in PR.
     rewrite ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     ss.
   Qed. *)

   Theorem refines_proper_r
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines (ModAdd.add_list mds0_tgt) (ModAdd.add_list mds0_src))
     :
       <<SIM: refines (ModAdd.add (ModAdd.add_list mds0_tgt) (ModAdd.add_list ctx)) (ModAdd.add (ModAdd.add_list mds0_src) (ModAdd.add_list ctx))>>
   .
   Proof. Admitted.
(*    
     ii. r in SIM0. rename ctx into xs. rename ctx0 into ys.
     (***
ys + (tgt + xs)
(tgt + xs) + ys
tgt + (xs + ys)
(xs + ys) + tgt
      ***)
     eapply ModAdd.add_comm in PR.
     rewrite <- ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     (***
(xs + ys) + src
src + (xs + ys)
(src + xs) + ys
ys + (src + xs)
      ***)
     specialize (SIM0 (xs ++ ys)). spc SIM0. rewrite ModAdd.add_list_app in SIM0. eapply SIM0 in PR.
     eapply ModAdd.add_comm in PR.
     rewrite ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     ss.
   Qed. *)

   Theorem refines_proper_l
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines (ModAdd.add_list mds0_tgt) (ModAdd.add_list mds0_src))
     :
       <<SIM: refines (ModAdd.add (ModAdd.add_list ctx) (ModAdd.add_list mds0_tgt)) (ModAdd.add (ModAdd.add_list ctx) (ModAdd.add_list mds0_src))>>
   .
   Proof. Admitted.
     (* ii. r in SIM0. rename ctx into xs. rename ctx0 into ys.
     (***
ys + (xs + tgt)
(ys + xs) + tgt
(ys + xs) + src
ys + (xs + src)
      ***)
     rewrite ModAdd.add_assoc' in PR.
     specialize (SIM0 (ys ++ xs)). spc SIM0. rewrite ModAdd.add_list_app in SIM0. eapply SIM0 in PR.
     rewrite <- ModAdd.add_assoc' in PR.
     ss.
   Qed.  *)

   Definition refines_closed (md_tgt md_src: Mod.t): Prop :=
     Beh.of_program (ModAdd.compile md_tgt) <1= Beh.of_program (ModAdd.compile md_src)
   .

   Global Program Instance refines_closed_PreOrder: PreOrder refines_closed.
   Next Obligation. ii; ss. Qed.
   Next Obligation. ii; ss. eapply H1. eapply H0. eauto. Qed.

   Lemma refines_close: refines <2= refines_closed.
   Proof. ii. specialize (PR nil). ss. unfold ModAdd.add_list in *. ss. rewrite ! ModAdd.add_empty_l in PR. eauto. Qed.

   (*** horizontal composition ***)
   Theorem refines2_add
         (s0 s1 t0 t1: list Mod.t)
         (SIM0: refines2 t0 s0)
         (SIM1: refines2 t1 s1)
     :
       <<SIM: refines2 (t0 ++ t1) (s0 ++ s1)>>
   .
   Proof. Admitted.
(*    
     ii. r in SIM0. r in SIM1.
     (***
ctx (a0 b0)
(ctx a0) b0
(ctx a0) b1
      ***)
     rewrite ModAdd.add_list_app in PR.
     rewrite ModAdd.add_assoc in PR.
     specialize (SIM1 (ctx ++ t0)). spc SIM1. rewrite ModAdd.add_list_app in SIM1. eapply SIM1 in PR.
     (***
ctx (a0 b1)
(a0 b1) ctx
a0 (b1 ctx)
(b1 ctx) a0
      ***)
     rewrite <- ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     rewrite <- ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     (***
(b1 ctx) a1
a1 (b1 ctx)
(a1 b1) ctx
ctx (a1 b1)
      ***)
     specialize (SIM0 (s1 ++ ctx)). spc SIM0. rewrite ModAdd.add_list_app in SIM0. eapply SIM0 in PR.
     eapply ModAdd.add_comm in PR.
     rewrite ModAdd.add_assoc' in PR.
     eapply ModAdd.add_comm in PR.
     rewrite ! ModAdd.add_list_app in *.
     assumption.
   Qed.  *)


   Corollary refines2_pairwise
             (mds0_src mds0_tgt: list Mod.t)
             (FORALL: List.Forall2 (fun md_src md_tgt => refines2 [md_src] [md_tgt]) mds0_src mds0_tgt)
     :
       refines2 mds0_src mds0_tgt.
   Proof.
     induction FORALL; ss.
     hexploit refines2_add.
     { eapply H0. }
     { eapply IHFORALL. }
     i. ss.
   Qed.

   Lemma refines2_eq (mds0 mds1: list Mod.t)
     :
       refines2 mds0 mds1 <-> refines (ModAdd.add_list mds0) (ModAdd.add_list mds1).
   Proof.
     split.
     { ii. eapply H0. auto. }
     { ii. eapply H0. auto. }
   Qed.

   Lemma refines2_app mhd0 mhd1 mtl0 mtl1
         (HD: refines2 mhd0 mhd1)
         (TL: refines2 mtl0 mtl1)
     :
       refines2 (mhd0++mtl0) (mhd1++mtl1).
   Proof. Admitted.
(*    
     eapply refines2_eq. rewrite ! ModAdd.add_list_app. etrans.
     { eapply refines_proper_l. eapply refines2_eq. et. }
     { eapply refines_proper_r. eapply refines2_eq. et. }
   Qed. *)

   Lemma refines2_cons mhd0 mhd1 mtl0 mtl1
         (HD: refines2 [mhd0] [mhd1])
         (TL: refines2 mtl0 mtl1)
     :
       refines2 (mhd0::mtl0) (mhd1::mtl1).
   Proof.
     eapply (refines2_app HD TL).
   Qed.

   End CONF.



   (*** horizontal composition ***)
   Theorem refines_strong_add
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines_strong md0_tgt md0_src)
         (SIM1: refines_strong md1_tgt md1_src)
     :
       <<SIM: refines_strong (ModAdd.add md0_tgt md1_tgt) (ModAdd.add md0_src md1_src)>>
   .
   Proof.
     intros CONF. eapply (@refines_add CONF); et.
   Qed.

   Theorem refines_strong_proper_r
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines_strong (ModAdd.add_list mds0_tgt) (ModAdd.add_list mds0_src))
     :
       <<SIM: refines_strong (ModAdd.add (ModAdd.add_list mds0_tgt) (ModAdd.add_list ctx)) (ModAdd.add (ModAdd.add_list mds0_src) (ModAdd.add_list ctx))>>
   .
   Proof.
     intros CONF. eapply (@refines_proper_r CONF); et.
   Qed.

   Theorem refines_strong_proper_l
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines_strong (ModAdd.add_list mds0_tgt) (ModAdd.add_list mds0_src))
     :
       <<SIM: refines_strong (ModAdd.add (ModAdd.add_list ctx) (ModAdd.add_list mds0_tgt)) (ModAdd.add (ModAdd.add_list ctx) (ModAdd.add_list mds0_src))>>
   .
   Proof.
     intros CONF. eapply (@refines_proper_l CONF); et.
   Qed.

   Lemma refines_strong_refines {CONF: EMSConfig}: refines_strong <2= refines.
   Proof. ii. eapply PR; et. Qed.
End REFINE.
