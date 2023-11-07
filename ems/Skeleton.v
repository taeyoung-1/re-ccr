Require Import Coqlib.
Require Export ZArith.
Require Import String.
Require Import PCM.
Require Export AList.

Set Implicit Arguments.

Local Open Scope nat_scope.

Notation gname := string (only parsing). (*** convention: not capitalized ***)
Notation mname := string (only parsing). (*** convention: capitalized ***)


Fixpoint _find_idx {A} (f: A -> bool) (l: list A) (acc: nat): option (nat * A) :=
  match l with
  | [] => None
  | hd :: tl => if (f hd) then Some (acc, hd) else _find_idx f tl (S acc)
  end
.

Definition find_idx {A} (f: A -> bool) (l: list A): option (nat * A) := _find_idx f l 0.

Notation "'do' ' X <- A ; B" := (o_bind A (fun _x => match _x with | X => B end))
                                  (at level 200, X pattern, A at level 100, B at level 200)
                                : o_monad_scope.

Lemma find_idx_red {A} (f: A -> bool) (l: list A):
  find_idx f l =
  match l with
  | [] => None
  | hd :: tl =>
    if (f hd)
    then Some (0%nat, hd)
    else
      do (n, a) <- find_idx f tl;
      Some (S n, a)
  end.
Proof.
  unfold find_idx. generalize 0. induction l; ss.
  i. des_ifs; ss.
  - rewrite Heq0. ss.
  - rewrite Heq0. specialize (IHl (S n)). rewrite Heq0 in IHl. ss.
Qed.


Lemma NoDup_map A B (f: A -> B) l
  :
    NoDup l -> ((forall a b, a<>b -> In a l -> In b l -> f a <> f b) <-> NoDup (map f l)).
Proof.
  i. split; i.
  - revert H0. induction H; i; ss.
    + econs.
    + econs.
      * red. i. apply H.
        assert (forall a, In a l -> f x <> f a).
        { i. apply H1; et. red. i. clarify. }
        clear - H2 H3. 
        revert_until l. induction l; i; ss.
        hexploit (H3 a); et. i. des; clarify.
        { rewrite H2 in H. clarify. }
        right. apply IHl; et.
      * apply IHNoDup. i. apply H1; et. 
  - revert_until l. induction l; i; ss.
    des; clarify.
    + apply in_map with (f := f) in H2. inv H0. clear - H2 H5.
      red. i. apply H5. rewrite <- H. et.
    + apply in_map with (f := f) in H3. inv H0. clear - H3 H5.
      red. i. apply H5. rewrite H. et.
    + inv H. inv H0. apply IHl; et. 
Qed.

Module SkEnv.

  Notation mblock := nat (only parsing).
  Notation ptrofs := Z (only parsing).

  Record t: Type := mk {
    blk2id: mblock -> option gname;
    id2blk: gname -> option mblock;
  }
  .

  Definition wf (ske: t): Prop :=
    forall id blk, ske.(id2blk) id = Some blk <-> ske.(blk2id) blk = Some id.

End SkEnv.


Require Import Orders.
Require Import PCM.
From compcertip Require Import Maps Clightdefs.

Module Sk.
  Class ld: Type := mk {
    t:> Type;
    sem: Type;
    unit: t;
    add: t -> t -> t;
    canon: t -> sem;
    wf: sem -> Prop;
    add_comm: forall a b,
      canon (add a b) = canon (add b a);
    add_assoc: forall a b c,
      canon (add a (add b c)) = canon (add (add a b) c);
    add_unit_l: forall a, canon (add unit a) = canon a;
    add_unit_r: forall a, canon (add a unit) = canon a;
    (* wf_comm: forall a b, wf (add a b) -> wf (add b a);
    wf_assoc: forall a b c, wf (add a (add b c)) <-> wf (add (add a b) c); *)
    add_canon: forall a b a' b',
      canon a = canon a' ->
        canon b = canon b' ->
          canon (add a b) = canon (add a' b');
    unit_wf: wf (canon unit);
    wf_mon: forall a b, wf (canon (add a b)) -> wf (canon a);
    extends := fun a b => exists ctx, canon (add a ctx) = canon b;
  }
  .

  Section SK.
  Context {M: RA.t}.

  Definition _add : option RA.car -> option RA.car -> option RA.car :=
    fun optx opty =>
      match optx, opty with
      | Some x, Some y => Some (RA.add x y)
      | Some x, None => Some x
      | None, Some y => Some y
      | None, None => None
      end.

  Program Instance globalenv : ld := {
    t := PTree.t RA.car;
    sem := alist positive RA.car;
    unit := PTree.empty RA.car;
    add := PTree.combine _add;
    canon:= @PTree.elements RA.car;
    wf := fun m => (forall s x, alist_find s m = Some x -> RA.wf x)
                   /\ NoDup (map (string_of_ident ∘ fst) m);
  }.
  Next Obligation.
  Proof.
    unfold add. erewrite PTree.combine_commut; et.
    i. unfold _add. des_ifs. f_equal. apply RA.add_comm. 
  Qed.
  Next Obligation.
  Proof.
    apply PTree.elements_extensional.
    i. repeat (rewrite PTree.gcombine; et).
    unfold _add. des_ifs. f_equal. apply RA.add_assoc.
  Qed.
  Next Obligation.
  Proof.
    apply PTree.elements_extensional.
    i. rewrite PTree.xgcombine_r; et.
    unfold _add. des_ifs.
  Qed.
  Next Obligation.
  Proof.
    apply PTree.elements_extensional.
    i. repeat (rewrite PTree.gcombine; et).
    unfold _add. des_ifs.
    all: rewrite PTree.gempty in Heq0; clarify.
  Qed.
  Next Obligation.
  Proof.
    apply PTree.elements_extensional.
    i. repeat (rewrite PTree.gcombine; et).
    replace (a ! i) with (a' ! i); cycle 1.
    2: f_equal.
    - destruct (a ! i) eqn: E; destruct (a' ! i) eqn: E1; et.
      + f_equal. apply PTree.elements_correct in E.
        apply PTree.elements_correct in E1.
        rewrite H in E. pose proof (PTree.elements_keys_norepet a).
        rewrite H in H1.
        set (PTree.elements a') in *. clearbody l. clear - E E1 H1.
        revert_until l. induction l; i; ss. des; clarify; ss.
        * inv H1. eapply in_map with (f:=fst) in E. clarify.
        * inv H1. eapply in_map with (f:=fst) in E1. clarify.
        * eapply IHl; et. inv H1. et.
      + apply PTree.elements_correct in E.
        rewrite H in E.
        apply PTree.elements_complete in E.
        clarify.
      + apply PTree.elements_correct in E1.
        rewrite <- H in E1.
        apply PTree.elements_complete in E1.
        clarify.
    - destruct (b ! i) eqn: E; destruct (b' ! i) eqn: E1; et.
      + f_equal. apply PTree.elements_correct in E.
        apply PTree.elements_correct in E1.
        rewrite H0 in E. pose proof (PTree.elements_keys_norepet b).
        rewrite H0 in H1.
        set (PTree.elements b') in *. clearbody l. clear - E E1 H1.
        revert_until l. induction l; i; ss. des; clarify; ss.
        * inv H1. eapply in_map with (f:=fst) in E. clarify.
        * inv H1. eapply in_map with (f:=fst) in E1. clarify.
        * eapply IHl; et. inv H1. et.
      + apply PTree.elements_correct in E.
        rewrite H0 in E.
        apply PTree.elements_complete in E.
        clarify.
      + apply PTree.elements_correct in E1.
        rewrite <- H0 in E1.
        apply PTree.elements_complete in E1.
        clarify.
  Qed.
  Next Obligation.
  Proof.
    split; clarify. econs.
  Qed.
  Next Obligation.
  Proof.
    split.
    - i.
      assert (alist_find s (PTree.elements (PTree.combine _add a b)) = _add (Some x) (b ! s)).
      { i. apply alist_find_some in H1.
        apply PTree.elements_complete in H1.
        destruct (b ! s) eqn: E; eapply alist_find_some_iff.
        1,3: rewrite CoqlibC.NoDup_norepet; apply PTree.elements_keys_norepet.
        all: apply PTree.elements_correct; rewrite PTree.gcombine; et; rewrite H1, E; ss. }
      destruct (b ! s); ss; hexploit H; et. apply RA.wf_mon.
    - rewrite <- map_map. 
      rewrite <- NoDup_map.
      2: rewrite CoqlibC.NoDup_norepet; apply PTree.elements_keys_norepet.
      i. rewrite <- map_map in H0.
      rewrite <- NoDup_map in H0.
      2: rewrite CoqlibC.NoDup_norepet; apply PTree.elements_keys_norepet.
      apply H0; et.
      + rewrite in_map_iff in H2. des. destruct x. clarify.
        apply PTree.elements_complete in H4. 
        rewrite in_map_iff; ss.
        destruct (b ! p) eqn: E.
        * eexists (p, _). split; et.
          apply PTree.elements_correct.
          rewrite PTree.gcombine; et. rewrite H4, E. et.
        * eexists (p, _). split; et.
          apply PTree.elements_correct.
          rewrite PTree.gcombine; et. rewrite H4, E. et.
      + rewrite in_map_iff in H3. des. destruct x. clarify.
        apply PTree.elements_complete in H4. 
        rewrite in_map_iff; ss.
        destruct (b ! p) eqn: E.
        * eexists (p, _). split; et.
          apply PTree.elements_correct.
          rewrite PTree.gcombine; et. rewrite H4, E. et.
        * eexists (p, _). split; et.
          apply PTree.elements_correct.
          rewrite PTree.gcombine; et. rewrite H4, E. et.
  Qed.

  Local Existing Instance globalenv.

  (*** TODO: It might be nice if Sk.t also constitutes a resource algebra ***)
  (*** At the moment, List.app is not assoc/commutative. We need to equip RA with custom equiv. ***)

  Definition load_skenv (sks: sem): (SkEnv.t) :=
    {|
      SkEnv.blk2id := fun blk => do '(id, _) <- (List.nth_error sks blk); Some (string_of_ident id);
      SkEnv.id2blk := fun gn => do '(blk, _) <- find_idx (fun '(id', _) => dec gn (string_of_ident id')) sks; Some blk
    |}
  .

  Lemma load_skenv_wf
        sks
        (WF: wf sks)
    :
      <<WF: SkEnv.wf (load_skenv sks)>>
  .
  Proof.
    red. ss. des. split; i; ss.
    - uo. des_ifs.
      + assert (id = string_of_ident (fst p1)).
        { clear - Heq1. revert_until sks. induction sks; ss; i.
          rewrite find_idx_red in Heq1. uo. des_ifs.
          - destruct dec; clarify.
          - destruct p. ss. eapply IHsks; et. } 
        assert (p1 = (p0, c)).
        { clear -Heq1 Heq0. revert_until sks. induction sks; ss; i.
          rewrite find_idx_red in Heq1. uo. des_ifs.
          - destruct dec; ss; clarify.
          - destruct p. ss. eapply IHsks; et. }
        clarify.
      + exfalso. clear -Heq2 Heq0.
        revert_until sks. induction sks; i; ss.
        rewrite find_idx_red in Heq2. uo. des_ifs.
        destruct p. ss. eapply IHsks; et.
    - uo. des_ifs.
      + clear - WF0 Heq1 Heq0. revert_until sks. induction sks; i; ss.
        rewrite find_idx_red in Heq0. uo. des_ifs.
        * destruct dec; clarify. ss.
          inv WF0. destruct blk; et.
          ss. apply Coqlib.nth_error_in in Heq1.
          apply in_map with (f:=fst) in Heq1.
          ss. apply in_map with (f:=string_of_ident) in Heq1.
          rewrite map_map in Heq1. rewrite e in Heq1. clarify.
        * destruct blk; ss; clarify.
          { destruct dec; clarify. }
          assert (Some (fst p) = Some blk); clarify.
          inv WF0. destruct p.
          eapply IHsks; et. 
      + exfalso. clear -Heq2 Heq0.
        revert_until sks. induction sks; i; ss.
        * destruct blk; clarify.
        * rewrite find_idx_red in Heq0. uo. des_ifs.
          destruct blk; ss; clarify.
          { destruct dec; clarify. }
          eapply IHsks; et.
  Qed.

  Program Instance incl_PreOrder: PreOrder extends.
  Next Obligation.
  Proof.
    ii. unfold extends. eexists unit. apply add_unit_r.
  Qed.
  Next Obligation.
  Proof.
    ii. unfold extends in *. des. 
    exists (add ctx0 ctx). rewrite add_assoc.
    rewrite <- H0.
    apply add_canon; et.
  Qed.

  (* Lemma sort_incl sk
    :
      incl sk (sort sk).
  Proof.
    ii. eapply Permutation.Permutation_in; [|apply IN].
    eapply SkSort.sort_permutation.
  Qed.

  Lemma sort_incl_rev sk
    :
      incl (sort sk) sk.
  Proof.
    ii. eapply Permutation.Permutation_in; [|apply IN].
    symmetry. eapply SkSort.sort_permutation.
  Qed. *)

  Definition incl_env (sk0: Sk.t) (skenv: SkEnv.t): Prop :=
    forall gn gd (IN: sk0 ! (ident_of_string gn) = Some gd),
    exists blk, <<FIND: skenv.(SkEnv.id2blk) gn = Some blk>>.

  Lemma incl_incl_env sk0 sk1
        (INCL: extends sk0 sk1)
    :
      incl_env sk0 (load_skenv (canon sk1)).
  Proof.
    ii. unfold extends in *. des. rewrite <- INCL.
    ss. uo. des_ifs; et.
    exfalso. clear - IN Heq0.
    apply PTree.elements_correct in IN.
    apply in_map with (f:=fst) in IN. ss.
    assert (~ In (ident_of_string gn) (map fst (PTree.elements (PTree.combine _add sk0 ctx)))).
    { clear IN. set (PTree.elements _) in *. clearbody l.
      move l at top. revert_until l. induction l; i; ss.
      red. i. des.
      - rewrite find_idx_red in Heq0. uo. des_ifs.
        ss. clarify. rewrite string_of_ident_of_string in Heq.
        destruct dec; clarify.
      - rewrite find_idx_red in Heq0. uo. des_ifs.
        eapply IHl; et. }
    clear Heq0. apply H. clear H.
    apply in_map_iff. apply in_map_iff in IN.
    des. destruct x. ss. clarify. apply PTree.elements_complete in IN0.
    destruct (ctx ! (ident_of_string gn)) eqn: E.
    - eexists (_, _). split; et. apply PTree.elements_correct.
      rewrite PTree.gcombine; et. rewrite IN0, E. ss.
    - eexists (_, _). split; et. apply PTree.elements_correct.
      rewrite PTree.gcombine; et. rewrite IN0, E. ss.
  Qed.

  Lemma in_env_in_sk :
    forall sk blk symb
      (FIND: SkEnv.blk2id (load_skenv (canon sk)) blk = Some symb),
    exists id def, string_of_ident id = symb /\ sk ! id = Some def.
  Proof.
    i. ss. uo. des_ifs. apply Coqlib.nth_error_in in Heq0.
    apply PTree.elements_complete in Heq0. et.
  Qed.

  Lemma in_sk_in_env :
    forall sk def gn
           (IN: sk ! (ident_of_string gn) = Some def),
    exists blk, SkEnv.blk2id (load_skenv (canon sk)) blk = Some gn.
  Proof.
    i. ss. apply PTree.elements_correct in IN.
    apply In_nth_error in IN. des. exists n. rewrite IN.
    uo. rewrite string_of_ident_of_string. et.
  Qed.

  Lemma env_range_some :
    forall sks blk
      (BLKRANGE : blk < Datatypes.length sks),
      <<FOUND : exists symb, SkEnv.blk2id (load_skenv sks) blk = Some symb>>.
  Proof.
    ss. i. red. uo. des_ifs; et.
    apply nth_error_None in Heq0. nia.
  Qed.

  Lemma env_found_range :
    forall sks symb blk
      (FOUND : SkEnv.id2blk (load_skenv sks) symb = Some blk),
      <<BLKRANGE : blk < Datatypes.length sks>>.
  Proof.
    i. ss. uo. des_ifs. red. revert_until sks.
    induction sks; i; ss; clarify.
    rewrite find_idx_red in Heq0. uo. des_ifs; try nia.
    assert (fst p < List.length sks); try nia.
    destruct p. eapply IHsks; et.
  Qed.

End SK.

End Sk.
