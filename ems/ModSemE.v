Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.

Set Implicit Arguments.


Notation gname := string (only parsing). (*** convention: not capitalized ***)

Section EVENTSCOMMON.

  Variant eventE: Type -> Type :=
  | Choose (X: Type): eventE X
  | Take X: eventE X
  | Syscall (fn: gname) (args: Any.t) (rvs: Any.t -> Prop): eventE Any.t
  .

  (* Notation "'Choose' X" := (trigger (Choose X)) (at level 50, only parsing). *)
  (* Notation "'Take' X" := (trigger (Take X)) (at level 50, only parsing). *)

  Definition triggerUB {E A} `{eventE -< E}: itree E A :=
    v <- trigger (Take void);; match v: void with end
  .

  Definition triggerNB {E A} `{eventE -< E}: itree E A :=
    v <- trigger (Choose void);; match v: void with end
  .

  Definition unwrapN {E X} `{eventE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerNB
    end.

  Definition unwrapU {E X} `{eventE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerUB
    end.

  Definition assume {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Take P) ;;; Ret tt.
  Definition guarantee {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Choose P) ;;; Ret tt.

  (* Notation "'unint?'" := (unwrapA <*> unint) (at level 57, only parsing). *)
  (* Notation "'unint﹗'" := (unwrapG <*> unint) (at level 57, only parsing). *)
  (* Notation "'Ret!' f" := (RetG f) (at level 57, only parsing). *)
  (* Notation "'Ret?' f" := (RetA f) (at level 57, only parsing). *)

  Definition unleftU {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerUB
    end.

  Definition unleftN {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerNB
    end.

  Definition unrightU {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
    match xy with
    | inl x => triggerUB
    | inr y => Ret y
    end.

  Definition unrightN {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
    match xy with
    | inl x => triggerNB
    | inr y => Ret y
    end.

End EVENTSCOMMON.

Notation "f '?'" := (unwrapU f) (at level 9, only parsing).
Notation "f 'ǃ'" := (unwrapN f) (at level 9, only parsing).
Notation "(?)" := (unwrapU) (only parsing).
Notation "(ǃ)" := (unwrapN) (only parsing).
Goal (tt ↑↓?) = Ret tt. rewrite Any.upcast_downcast. ss. Qed.
Goal (tt ↑↓ǃ) = Ret tt. rewrite Any.upcast_downcast. ss. Qed.







(* Not used? *)
Section EVENTSCOMMON.

  Definition p_state : Type := Any.t.

  (*** Same as State.pure_state, but does not use "Vis" directly ***)
  Definition pure_state {S E}: E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).

  Lemma unfold_interp_state: forall {E F} {S R} (h: E ~> stateT S (itree F)) (t: itree E R) (s: S),
      interp_state h t s = _interp_state h (observe t) s.
  Proof. i. f. apply unfold_interp_state. Qed.

End EVENTSCOMMON.









Section EVENTS.

Section DEFINES.

  Inductive callE: Type -> Type :=
  | Call (fn: gname) (args: Any.t) : callE Any.t
  .
  

  Variant sE (V: Type): Type :=
  | SUpdate (run : Any.t -> Any.t * V) : sE V
  .

  Definition Es: Type -> Type := (callE +' sE +' eventE).

  Definition rGet : Any.t -> Any.t * Any.t := fun x => (x, x).

  Definition rPut x : Any.t -> Any.t * unit := fun _ => (x, tt).

  Definition sGet : sE (Any.t) := 
    SUpdate (rGet).

  Definition sPut x : sE unit :=
    SUpdate (rPut x).

  (* Definition sGet : sE (Any.t) := 
    SUpdate (fun x => (x, x)).

  Definition sPut x : sE unit :=
    SUpdate (fun _ => (x, tt)). *)

  Definition handle_sE {E}: sE ~> stateT Any.t (itree E) := 
    fun _ e glob =>
      match e with
      | SUpdate run => Ret (run glob)
      end.
      
 Definition interp_sE {E}: itree (sE +' E) ~> stateT Any.t (itree E) :=
    (* State.interp_state (case_ ((fun _ e s0 => resum_itr (handle_pE e s0)): _ ~> stateT _ _) State.pure_state). *)
    State.interp_state (case_ handle_sE pure_state).

  Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: Any.t): itree eventE (Any.t * _)%type :=
    '(st1, v) <- interp_sE (interp_mrec prog itr0) st0;;
    Ret (st1, v)
  .
End DEFINES.

  Lemma interp_Es_bind
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
        (prog: callE ~> itree Es)
        st0
    :
      interp_Es prog (v <- itr ;; ktr v) st0 =
      '(st1, v) <- interp_Es prog (itr) st0 ;; interp_Es prog (ktr v) st1
  .
  Proof. unfold interp_Es, interp_sE. des_ifs. grind. Qed.

  Lemma interp_Es_tau
        (prog: callE ~> itree Es)
        A
        (itr: itree Es A)
        st0
    :
      interp_Es prog (tau;; itr) st0 = tau;; interp_Es prog itr st0
  .
  Proof. unfold interp_Es, interp_sE. des_ifs. grind. Qed.

  Lemma interp_Es_ret
        T
        prog st0 (v: T)
    :
      interp_Es prog (Ret v: itree Es _) st0 = Ret (st0, v)
  .
  Proof. unfold interp_Es, interp_sE. des_ifs. grind. Qed.

  Lemma interp_Es_callE
        p st0 T
        (* (e: Es Σ) *)
        (e: callE T)
    :
      interp_Es p (trigger e) st0 = tau;; (interp_Es p (p _ e) st0)
  .
  Proof. unfold interp_Es, interp_sE. des_ifs. grind. Qed.

  Lemma interp_Es_sE
        p st0
        (* (e: Es Σ) *)
        T
        (e: sE T)
    :
      interp_Es p (trigger e) st0 =
      '(st1, r) <- handle_sE e st0;;
      tau;; tau;;
      Ret (st1, r)
  .
  Proof.
    unfold interp_Es, interp_sE. grind.
  Qed.

  Lemma interp_Es_eventE
        p st0
        (* (e: Es Σ) *)
        T
        (e: eventE T)
    :
      interp_Es p (trigger e) st0 = r <- trigger e;; tau;; tau;; Ret (st0, r)
  .
  Proof.
    unfold interp_Es, interp_sE. grind.
    unfold pure_state. grind.
  Qed.

  Lemma interp_Es_triggerUB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (interp_Es prog (triggerUB) st0: itree eventE (_ * A)) = triggerUB
  .
  Proof.
    unfold interp_Es, interp_sE, pure_state, triggerUB. grind.
  Qed.

  Lemma interp_Es_triggerNB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (interp_Es prog (triggerNB) st0: itree eventE (_ * A)) = triggerNB
  .
  Proof.
    unfold interp_Es, interp_sE, pure_state, triggerNB. grind.
  Qed.
  (* Opaque interp_Es. *)
End EVENTS.
Opaque interp_Es.


(* Lemma translate_triggerUB T (f: forall T, Es T -> Es T) (g: forall T, (Any.t -> Any.t * T) -> (Any.t -> Any.t * T))
    (COND: f _ (subevent _ (Take void)) = (subevent _ (Take void)))
  :
      translate f (@triggerUB _ T _) = @triggerUB _ T _ 
.

Proof.
  unfold triggerUB.
  erewrite ! (bisimulation_is_eq _ _ (translate_bind _ _ _)).
  f_equal.
  - unfold trigger. 
    erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
    repeat f_equal; et. 
    extensionality v. destruct v.
  - extensionality v. destruct v.
Qed.  *)