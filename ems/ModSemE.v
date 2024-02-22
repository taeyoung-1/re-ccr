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

  Variant schE: Type -> Type :=
  | Yield: schE unit
  | Spawn (fn: gname) (args: Any.t): schE nat
  .

  Definition Es: Type -> Type := (callE +' sE +' schE +' eventE).
  
Section STATES.
  Definition sGet : sE (Any.t) := 
    SUpdate (fun x => (x, x)).

  Definition sPut x : sE unit :=
    SUpdate (fun _ => (x, tt)).

  Definition handle_sE {E}: sE ~> stateT Any.t (itree E) := 
    fun _ e glob =>
      match e with
      | SUpdate run => Ret (run glob)
      end.
      
 Definition interp_sE {E}: itree (sE +' E) ~> stateT Any.t (itree E) :=
    (* State.interp_state (case_ ((fun _ e s0 => resum_itr (handle_pE e s0)): _ ~> stateT _ _) State.pure_state). *)
    State.interp_state (case_ handle_sE pure_state).

End STATES.

Section SCHEDULER.
  Definition interp_schE {E} :
    nat * (string * itree (sE +' schE +' eventE) E) ->
    itree (sE +' eventE) (E + (string * Any.t * (nat -> itree (sE +' schE +' eventE) E))
                        + (itree (sE +' schE +' eventE) E)).
  Proof.
    eapply ITree.iter.
    intros [tid [sname itr]].
    apply observe in itr; destruct itr as [r | itr | X e k].
    - (* Ret *)
      exact (Ret (inr (inl (inl r)))).
    - (* Tau *)
      exact (Ret (inl (tid, (sname, itr)))).
    - (* Vis *)
      destruct e as [|[|]].
      + (* sE *)
      exact (Vis (inl1 s) (fun x => Ret (inl (tid, (sname, k x))))).
      + (* schE *)
        destruct s.
        * (* Yield *)
        exact (Ret (inr (inr (k tt)))).
        * (* Spawn *)
          exact (Ret (inr (inl (inr (fn, args, fun x => k x))))).
      + (* eventE *)
        exact (Vis (inr1 e) (fun x => Ret (inl (tid, (sname, k x))))).
  Defined.

  Notation threads E := (alist nat (string * (itree (sE +' schE +' eventE) E))).

  Inductive executeE {E} : Type -> Type :=
  | Execute : nat -> executeE ((list nat) * (E + nat + unit)).

  Definition get_site (fn: string) :=
    match index 0 "." fn with
    | Some idx => substring 0 idx fn
    | None => "control"
    end.


  Definition dummy_return {E}: itree Es E := trigger (inr1 (Choose E)).

  Definition interp_executeE {E}:
  (callE ~> itree Es) * (threads E) * nat * (itree ((@executeE E) +' eventE) E) ->
  itree (sE +' eventE) E.
Proof.
  eapply ITree.iter. intros [[[prog ts] next_tid] sch].
  destruct (observe sch) as [r | sch' | X [e|e] ktr].
  - exact (Ret (inr r)).
  - exact (Ret (inl (prog, ts, next_tid, sch'))).
  - destruct e. rename n into tid.
    destruct (alist_find tid ts) as [[sname itr]|].
    * exact (r <- interp_schE (tid, (sname, itr));;
             match r with
             | inl (inl r) => (* finished *)
                 let ts' := alist_remove tid ts in
                 Ret (inl (prog, ts', next_tid, ktr (List.map fst ts', (inl (inl r)))))
             | inl (inr (fn, args, k)) => (* spawn what is root?*)
                 let new_itr := interp_mrec prog (_ <- (prog _ (Call fn args));;
                                                  v <- dummy_return;; Ret v) in
                 let ts' := alist_add next_tid (get_site fn, new_itr) (alist_replace tid (sname, k next_tid) ts) in
                 Ret (inl (prog, ts', next_tid + 1, ktr (List.map fst ts', (inl (inr tid)))))
             | inr t' => (* yield *)
                 let ts' := alist_replace tid (sname, t') ts in
                 Ret (inl (prog, ts', next_tid, ktr (List.map fst ts', (inr tt))))
             end).
    * exact triggerNB.
  - exact (Vis (inr1 e) (fun x => Ret (inl (prog, ts, next_tid, ktr x)))).
Defined.    

Definition choose_from {E} (l: list nat): itree (@executeE E +' eventE) nat :=
  tid <- ITree.trigger (inr1 (Choose nat));;
  guarantee(In tid l);;;
  Ret tid.

Definition sched_nondet {E} : nat -> itree (executeE +' eventE) E :=
  ITree.iter (fun tid => 
                '(ts, retv) <- ITree.trigger (inl1 (Execute tid));;
                match retv with
                | inl (inl r) =>
                    match ts with
                    | [] => Ret (inr r)
                    | _ => tid' <- choose_from(ts);;
                          Ret (inl tid')
                    end
                | inl (inr tid') =>
                    Ret (inl tid')
                | inr tt =>
                    tid' <- choose_from(ts);;
                    Ret (inl tid')
                end).

Definition interp_scheduler {E}
  (prog: callE ~> itree Es) (ts: threads E) (start_tid: nat) : itree (sE +' eventE) E :=
  interp_executeE (prog, ts, List.length ts, sched_nondet start_tid).


End SCHEDULER.

Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: Any.t): itree eventE (Any.t * _)%type :=
  let itr1 := interp_mrec prog itr0 in
  let itr2 := interp_scheduler prog [(0, ("init", itr1))] 0 in
  '(st1, v) <- interp_sE itr2 st0;;
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
  Proof. Admitted. 
  
  Lemma interp_Es_tau
        (prog: callE ~> itree Es)
        A
        (itr: itree Es A)
        st0
    :
      interp_Es prog (tau;; itr) st0 = tau;; interp_Es prog itr st0
  .
  Proof. Admitted. 

  Lemma interp_Es_ret
        T
        prog st0 (v: T)
    :
      interp_Es prog (Ret v: itree Es _) st0 = Ret (st0, v)
  .
  Proof. Admitted. 


  Lemma interp_Es_callE
        p st0 T
        (* (e: Es Σ) *)
        (e: callE T)
    :
      interp_Es p (trigger e) st0 = tau;; (interp_Es p (p _ e) st0)
  .
  Proof. Admitted. 


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
  Proof. Admitted.

  Lemma interp_Es_eventE
        p st0
        (* (e: Es Σ) *)
        T
        (e: eventE T)
    :
      interp_Es p (trigger e) st0 = r <- trigger e;; tau;; tau;; Ret (st0, r)
  .
  Proof. Admitted.
 
  Lemma interp_Es_triggerUB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (interp_Es prog (triggerUB) st0: itree eventE (_ * A)) = triggerUB
  .
  Proof. Admitted.

  Lemma interp_Es_triggerNB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (interp_Es prog (triggerNB) st0: itree eventE (_ * A)) = triggerNB
  .
  Proof. Admitted. 
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