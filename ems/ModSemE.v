Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.
Require Import Optics.

Set Implicit Arguments.


Notation gname := string (only parsing). (*** convention: not capitalized ***)
Notation mname := string (only parsing). (*** convention: capitalized ***)

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







Section EVENTSCOMMON.

  Definition p_state: Type := (mname -> Any.t).
  (* Definition p_state : Type := Any.t. *)

  (*** Same as State.pure_state, but does not use "Vis" directly ***)
  Definition pure_state {S E}: E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).

  Lemma unfold_interp_state: forall {E F} {S R} (h: E ~> stateT S (itree F)) (t: itree E R) (s: S),
      interp_state h t s = _interp_state h (observe t) s.
  Proof. i. f. apply unfold_interp_state. Qed.

End EVENTSCOMMON.









Section EVENTS.

  Variable S: Type.
  (* Variable st: Type.*)

  Inductive callE: Type -> Type :=
  | Call (fn: gname) (args: Any.t) : callE Any.t
  .
  
  (* Variant sE: Type -> Type :=
  | SUpdate (run : Any.t -> Any.t * Any.t) : sE Any.t
  . *)

  Variant sE  (X : Type) : Type :=
  | SUpdate (run : S -> S * X) : sE X
  .
  
  (* Variant sE (S: Type)  (X : Type) : Type :=
  | SUpdate (run : S -> S * X) : sE X
  . 
  If implemented in this way with another variable st, universe inconsistency occurs.
  *)

  Definition Es: Type -> Type := (callE +' sE +' eventE).
  
  Definition sGet {X} (p: S -> X) : sE X := SUpdate (fun x => (x, p x)).
  Definition sModify (f: S -> S) : sE () := SUpdate (fun x => (f x, tt)).
  Definition sPut x := (sModify (fun _:S => x)).
  
  (* Double-check Types*)
  (* Definition Get (p: Any.t -> Any.t) : sE Any.t Any.t := SUpdate (fun x => (x, p x)).
  Definition Modify (f: Any.t -> Any.t) : sE Any.t () := SUpdate (fun x => (f x, tt)).
  Definition Put x := (Modify (fun _ => x)). *)

  (* Definition sGet (p: Any.t -> Any.t) : sE Any.t := SUpdate (fun x => (x, p x)).
  Definition sModify (f: Any.t -> Any.t) : sE Any.t := SUpdate (fun x => (f x, tt↑)).
  Definition sPut x := (sModify (fun _ => x)). *)


  (* Definition Es: Type -> Type := (callE +' (sE Any.t) +' eventE). *)

  (********************************************************************)
  (*************************** Interpretation *************************)
  (********************************************************************)

  (* Definition handle_pE {E}: pE ~> stateT p_state (itree E) :=
    fun _ e mps =>
      match e with
      | PPut mn p => Ret (update mps mn p, tt)
      | PGet mn => Ret (mps, mps mn)
      end. 
      
      Definition handle_pE {E} : forall X, pE X -> (p_state -> itree E (p_state * X)) :=
      


      *)
 (* Definition interp_sE {E}: itree (pE +' E) ~> stateT p_state (itree E) :=
    (* SUpdate.interp_state (case_ ((fun _ e s0 => resum_itr (handle_pE e s0)): _ ~> stateT _ _) SUpdate.pure_state). *)
    SUpdate.interp_state (case_ handle_pE pure_state).


  Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: p_state): itree eventE (p_state * _)%type :=
    '(st1, v) <- interp_sE (interp_mrec prog itr0) st0;;
    Ret (st1, v)
  . *)

  (* Definition handle_sE {E} : forall S X, sE S X -> (S -> itree E (S * X)) :=
    fun _ _ e glob =>
      match e with
      | SUpdate run => Ret (run glob)
      end. *)

  (* Definition interp_sE {E}: forall S X, itree ((sE S) +' E) (S * X) -> (S -> itree E (S * X)) :=
    (* SUpdate.interp_state (case_ ((fun _ e s0 => resum_itr (handle_pE e s0)): _ ~> stateT _ _) SUpdate.pure_state). *)
    SUpdate.interp_state (case_ handle_sE pure_state). *)

  (* Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: p_state): itree eventE (p_state * _)%type :=
    '(st1, v) <- interp_sE (interp_mrec prog itr0) st0;;
    Ret (st1, v)
  . *)

  (* Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: p_state): itree eventE (p_state * _)%type :=
    '(st1, v) <- interp_sE (interp_mrec prog itr0) st0;;
    Ret (st1, v)
  . *)

  (* Definition handle_sE {E}: sE ~> stateT Any.t (itree E) := 
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
  . *)

  Definition handle_sE {E}: sE ~> stateT S (itree E) := 
    fun _ e glob =>
      match e with
      | SUpdate run => Ret (run glob)  
      end. 
      
 Definition interp_sE {E}: itree (sE +' E) ~> stateT S (itree E) :=
    (* State.interp_state (case_ ((fun _ e s0 => resum_itr (handle_pE e s0)): _ ~> stateT _ _) State.pure_state). *)
    State.interp_state (case_ handle_sE pure_state).

  Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: S): itree eventE (S * _)%type :=
    '(st1, v) <- interp_sE (interp_mrec prog itr0) st0;;
    Ret (st1, v)
  .

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
      interp_Es prog (Ret v) st0 = Ret (st0, v)
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
(* Notation sPut x := (sModify (fun _ => x)). *)



Section LENS.
  Variable S: Type.
  Variable V: Type.

  Variable l: Lens.t S V.

  Definition lens_state X : (V -> V * X) -> (S -> S * X) :=
    fun run s =>
      (Lens.set l (fst (run (Lens.view l s))) s, snd (run (Lens.view l s))).

  Definition map_lens X (se: sE V X) : sE S X := 
    match se with
    | SUpdate run => SUpdate (lens_state run)
    end.
    
    
    (* Definition lens_state : (Any.t -> Any.t * Any.t) -> (Any.t -> Any.t * Any.t) :=
    fun run s =>
    (Lens.set l (fst (run (Lens.view l s))) s, snd (run (Lens.view l s)))
    .
    
    Definition map_lens (se: sE Any.t ) : sE Any.t :=
      match se with
      | SUpdate run => SUpdate (lens_state run)
      end
      . *)

  (* Variable l: Lens.t Any.t Any.t.

  Definition lens_state X: (Any.t -> Any.t * X) -> (Any.t -> Any.t * X) :=
    fun run s =>
      (Lens.set l (fst (run (Lens.view l s))) s, snd (run (Lens.view l s)))
  .

  Definition map_lens X (se: sE X ) : sE X :=
    match se with
    | SUpdate run => SUpdate (lens_state run)
    end
  . *)

End LENS.

Section PROGRAM_EVENT.
  Variable st st' : Type.

  Variable l : Lens.t st' st.

  (* Variable l : Lens.t Any.t Any.t. *)
  
  Definition lmap X :  Es st X -> Es st' X .
  Proof.
    intro e. destruct e as [e|[e|e]].
    - exact (e|)%sum.
    - exact (|((map_lens l e))|)%sum.
    - exact (||e)%sum.
  Defined.

End PROGRAM_EVENT.

Section MAP_EVENT.
  CoFixpoint map_event {E1 E2} (embed: forall X, E1 X -> E2 X) {R} : itree E1 R -> itree E2 R :=
    fun itr =>
      match observe itr with
      | RetF r => Ret r
      | TauF itr => Tau (map_event embed itr)
      | VisF e ktr => Vis (embed _ e) (fun x => map_event embed (ktr x))
      end.

  (* CoFixpoint map_event (embed: forall X, Es X -> Es X) : itree Es Any.t -> itree Es Any.t :=
    fun itr =>
      match observe itr with
      | RetF r => Ret r
      | TauF itr => Tau (map_event embed itr)
      | VisF e ktr => Vis (embed _ e) (fun x => map_event embed (ktr x))
      end. *)
      
End MAP_EVENT.