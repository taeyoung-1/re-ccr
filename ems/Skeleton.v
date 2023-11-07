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
    wf := fun m => forall s x, alist_find s m = Some x -> RA.wf x
                   /\ NoDup (map (map_fst string_of_ident) m);
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
  (* Next Obligation.
  Proof.
    split.
    - erewrite PTree.combine_commut in H0; try eapply H; et.
      i. unfold _add. des_ifs. f_equal. apply RA.add_comm.
    - admit.
  Admitted.
  Next Obligation.
  Proof.
  Admitted. *)
  Next Obligation.
  Proof.
  Admitted.
  Next Obligation.
  Proof.
    split. 2:{ admit. }
    (* apply PTree.elements_extensional.
    i. repeat (rewrite PTree.gcombine; et).
    f_equal.
    - destruct (a ! i) eqn: E; destruct (a' ! i) eqn: E'; et.
      + apply PTree.elements_correct in E. rewrite H in E.
        apply PTree.elements_complete in E. clarify.
      + apply PTree.elements_correct in E. rewrite H in E.
        apply PTree.elements_complete in E. clarify.
      + apply PTree.elements_correct in E'. rewrite <- H in E'.
        apply PTree.elements_complete in E'. clarify.
    - destruct (b ! i) eqn: E; destruct (b' ! i) eqn: E'; et.
      + apply PTree.elements_correct in E. rewrite H0 in E.
        apply PTree.elements_complete in E. clarify.
      + apply PTree.elements_correct in E. rewrite H0 in E.
        apply PTree.elements_complete in E. clarify.
      + apply PTree.elements_correct in E'. rewrite <- H0 in E'.
        apply PTree.elements_complete in E'. clarify. *)
  Admitted.

  Local Existing Instance globalenv.

  (*** TODO: It might be nice if Sk.t also constitutes a resource algebra ***)
  (*** At the moment, List.app is not assoc/commutative. We need to equip RA with custom equiv. ***)

  Definition load_skenv (sks: sem): (SkEnv.t) :=
    {|
      SkEnv.blk2id := fun blk => do '(id, _) <- (List.nth_error sks blk); Some (string_of_ident id);
      SkEnv.id2blk := fun gn => do '(blk, _) <- find_idx (fun '(id', _) => dec (ident_of_string gn) id') sks; Some blk
    |}
  .

  Lemma load_skenv_wf
        sks
        (WF: wf sks)
    :
      <<WF: SkEnv.wf (load_skenv sks)>>
  .
  Proof.
    red. split; i; ss.
    - uo. des_ifs.
      + admit.
      + admit.
    - uo. des_ifs.
      + admit.
      + admit.
  Admitted.

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
  Admitted.

  Lemma in_env_in_sk :
    forall sk blk symb
      (FIND: SkEnv.blk2id (load_skenv (canon sk)) blk = Some symb),
    exists def, sk ! (ident_of_string symb) = Some def.
  Proof.
  Admitted.


  Lemma in_sk_in_env :
    forall sk def gn
           (IN: sk ! (ident_of_string gn) = Some def),
    exists blk, SkEnv.blk2id (load_skenv (canon sk)) blk = Some gn.
  Proof.
  Admitted.

  Lemma env_range_some :
    forall sks blk
      (BLKRANGE : blk < Datatypes.length sks),
      <<FOUND : exists symb, SkEnv.blk2id (load_skenv sks) blk = Some symb>>.
  Proof.
  Admitted.

  Lemma env_found_range :
    forall sks symb blk
      (FOUND : SkEnv.id2blk (load_skenv sks) symb = Some blk),
      <<BLKRANGE : blk < Datatypes.length sks>>.
  Proof.
  Admitted.

End SK.

End Sk.
