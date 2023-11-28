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

  Definition emb_l : forall X, Es (state M1) X -> Es (state M1 * state M2) X  :=
    lmap fstl.

  Definition emb_r : forall X, Es (state M2) X -> Es (state M1 * state M2) X :=
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
    state := state M1 * state M2;
    init_st := (init_st M1, init_st M2);
    fnsems := add_fnsems;
  |}.

End ADD.

Section PROOF.


Definition swap {A B} (p : A * B) : B * A :=
  (snd p, fst p).  
  
Definition swap_Es {A B} T (es: Es (A*B) T) : Es (B*A) T :=
  match es with
  | inr1 (inl1 (SUpdate f)) => inr1 (inl1 (SUpdate (fun '(b,a) => let '((a',b'), t) := f (a,b) in ((b',a'), t))))
  | inr1 (inr1 x) => inr1 (inr1 x)
  | inl1 y => inl1 y
  end.

Definition swap_ems {R A B} (itl: itree (Es (A*B)) R) (itr: itree (Es (B*A)) R) :=
  itr = translate swap_Es itl.

Lemma swap_ems_prog X ms0 ms1 (e: callE X)
:
      swap_ems (prog (add ms1 ms0) e) (prog (add ms0 ms1) e)
.
Proof.
  destruct e. s. unfold unwrapU, add_fnsems. des_ifs.
  - grind. unfold swap_ems. Set Printing All. unfold triggerUB.
    erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
    Search eq_itree.
    unfold trigger.

    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    admit.
  - grind. unfold swap_ems. Search translate. 
Admitted.


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
  { unfold init_st. et. }
  revert REL.
  generalize (Any.t) as X.
  generalize (init_st (add ms1 ms0)) as stl0.
  generalize (init_st (add ms0 ms1)) as str0.

  i. eapply simg_map.
  2: { instantiate (1 := (fun r0 r1 => snd r0 = snd r1 /\ swap (fst r0) = fst r1)).
       i. apply H0.   }
  revert_until x.
  ginit. { i. apply cpn7_wcompat. apply simg_mon. }  
  gcofix CIH. i.

  pose proof (swap_ems_prog ms0 ms1 e) as REL'.

  (* assert (REL': swap_ems (prog (add ms1 ms0) e) (prog (add ms0 ms1) e)). { apply swap_ems_prog. } *)

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
      pattern (@interp_Es (state (add ms1 ms0)) X0 (@prog (add ms1 ms0))
      (@ITree.trigger (Es (state (add ms1 ms0))) X0 (@inl1 callE (sum1 (sE (state (add ms1 ms0))) eventE) X0 c)) stl).
      pattern (@interp_Es (prod (state ms0) (state ms1)) X0 (@prog (add ms0 ms1))
      (@ITree.trigger (Es (prod (state ms0) (state ms1))) X0
         (@swap_Es (state ms1) (state ms0) X0 (@inl1 callE (sum1 (sE (state (add ms1 ms0))) eventE) X0 c)))
      (@swap (state ms1) (state ms0) stl)).
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
      pattern (@interp_Es (state (add ms1 ms0)) X0 (@prog (add ms1 ms0))
      (@ITree.trigger (Es (state (add ms1 ms0))) X0
         (@inr1 callE (sum1 (sE (state (add ms1 ms0))) eventE) X0 (@inl1 (sE (state (add ms1 ms0))) eventE X0 s))) stl).
      pattern (@interp_Es (prod (state ms0) (state ms1)) X0 (@prog (add ms0 ms1))
      (@ITree.trigger (Es (prod (state ms0) (state ms1))) X0
         (@swap_Es (state ms1) (state ms0) X0
            (@inr1 callE (sum1 (sE (state (add ms1 ms0))) eventE) X0 (@inl1 (sE (state (add ms1 ms0))) eventE X0 s))))
      (@swap (state ms1) (state ms0) stl)).
      setoid_rewrite interp_Es_sE.
      grind.
      setoid_rewrite interp_Es_sE.
      grind.
      gstep. 
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_tauL; et. apply simg_tauR; et.
      apply simg_progress; et.
      destruct stl. inv Heq1. rewrite H1 in Heq. inv Heq.
      gfinal. left. eapply CIH'. unfold swap_ems. et.

    + (* eventE *)
      rewrite <- ! bind_trigger, ! interp_Es_bind.
      (* Set Printing All. *)
      pattern (@interp_Es (state (add ms1 ms0)) X0 (@prog (add ms1 ms0))
      (@ITree.trigger (Es (state (add ms1 ms0))) X0 (@inr1 callE (sum1 (sE (state (add ms1 ms0))) eventE) X0 (@inr1 (sE (state (add ms1 ms0))) eventE X0 e0)))
      stl).
      pattern (@interp_Es (prod (state ms0) (state ms1)) X0 (@prog (add ms0 ms1))
      (@ITree.trigger (Es (prod (state ms0) (state ms1))) X0
         (@swap_Es (state ms1) (state ms0) X0 (@inr1 callE (sum1 (sE (state (add ms1 ms0))) eventE) X0 (@inr1 (sE (state (add ms1 ms0))) eventE X0 e0))))
      (@swap (state ms1) (state ms0) stl)).
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


Lemma add_assoc' ms0 ms1 ms2:
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
Qed. *)

Theorem add_assoc
        ms0 ms1 ms2 P
  :
    <<COMM: Beh.of_program (compile (add ms0 (add ms1 ms2)) P) <1=
            Beh.of_program (compile (add (add ms0 ms1) ms2) P)>>
.
Proof. 
  rewrite add_assoc_eq. ss.
Qed.

Theorem add_assoc_rev
        ms0 ms1 ms2 P
  :
    <<COMM: Beh.of_program (compile (add ms0 (add ms1 ms2)) P) <1=
            Beh.of_program (compile (add (add ms0 ms1) ms2) P)>>
.
Proof.
  rewrite add_assoc_eq. ss.
Qed.

End PROOF.
End ModSemAdd.

Module ModAdd.
Import Mod.
Section BEH.

Context `{Sk.ld}.
Context {CONF: EMSConfig}.

(* Definition compile (md: t): semantics :=
  ModSemL.compile_itree (ModSemL.initial_itr md.(enclose) (Some (wf md))). *)


Definition compile (md: t): semantics :=
  ModSem.compile_itree (ModSem.initial_itr md.(enclose) (Some (wf md))).


(*** wf about modsem is enforced in the semantics ***)

Definition add (md0 md1: t): t := {|
  get_modsem := fun sk =>
                  ModSem.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
  sk := Sk.add md0.(sk) md1.(sk);
|}
.


(* Definition add (md0 md1: t): t := {|
  get_modsem := fun sk =>
                  ModSemL.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
  sk := Sk.add md0.(sk) md1.(sk);
|}
. *)

Theorem add_comm
        md0 md1
  :
    <<COMM: Beh.of_program (compile (add md0 md1)) <1= Beh.of_program (compile (add md1 md0))>>
.
Proof. Admitted.
  (* ii. unfold compile in *.
  destruct (classic (Sk.wf (sk (add md1 md0)))).
  (* 2: { eapply ModSemL.initial_itr_not_wf. ss. } *)
  ss. des. assert (SK: Sk.wf (Sk.add (sk md0) (sk md1))).
  { apply Sk.wf_comm. auto. }
  rewrite Sk.add_comm; et.
  eapply ModSem.add_comm. [| |et].
  { i. split; auto. unfold enclose. ss. rewrite Sk.add_comm; et.
    inv H2. inv H3. econs; ss.
    { rewrite List.map_app in *. eapply nodup_comm; et. }
    { rewrite List.map_app in *. eapply nodup_comm; et. }
  }
  { rewrite Sk.add_comm; et. }
Qed. *)



Lemma add_assoc' ms0 ms1 ms2:
  add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
Proof.
  unfold add. f_equal.
  { extensionality skenv_link. ss. apply ModSem.add_assoc'. }
  { ss. rewrite Sk.add_assoc. auto. }
Qed.

Theorem add_assoc
        md0 md1 md2
  :
    <<COMM: Beh.of_program (compile (add md0 (add md1 md2))) =
            Beh.of_program (compile (add (add md0 md1) md2))>>
.
Proof.
  rewrite add_assoc'. ss.
Qed.

Theorem add_assoc_rev
        md0 md1 md2
  :
    <<COMM: Beh.of_program (compile (add (add md0 md1) md2)) =
            Beh.of_program (compile (add md0 (add md1 md2)))>>
.
Proof.
  rewrite add_assoc'. ss.
Qed.

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
  unfold add, ModSemL.add. f_equal; ss.
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
