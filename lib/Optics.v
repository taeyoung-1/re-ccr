From sflib Require Import sflib.
From Coq Require Import Program.
Require Import Any.

Set Implicit Arguments.

Tactic Notation "hspecialize" hyp(H) "with" uconstr(x) :=
  apply (fun H => equal_f H x) in H.

Tactic Notation "cong" uconstr(f) "in" hyp(H) :=
  eapply (f_equal f) in H.

Module Store.

  Definition t S A := (S * (S -> A))%type.

  Definition map {S A B} : (A -> B) -> t S A -> t S B :=
    fun ϕ x => (fst x, ϕ ∘ snd x).

  Definition counit {S A} : t S A -> A :=
    fun x => snd x (fst x).

  Definition cojoin {S A} : t S A -> t S (t S A) :=
    fun x => (fst x, fun a' => (a', snd x)).

End Store.

Module Lens.

  (* Lens is just a coalgebra of the Store comonad *)

  (* Record isLens {S V} (l : S -> Store.t V S) : Prop :=
    { counit : Store.counit ∘ l = id
    ; coaction : Store.map l ∘ l = Store.cojoin ∘ l
    }. *)

  Definition t S V := S -> Store.t V S.
  (* Definition t S V := {l : S -> Store.t V S | isLens l}. *)

  Definition view {S V} : t S V -> S -> V := fun l s => fst (l s).
  Definition set {S V} : t S V -> V -> S -> S := fun l a s => snd (l s) a.
  Definition modify {S V} : t S V -> (V -> V) -> (S -> S) := fun l f s => Lens.set l (f (Lens.view l s)) s.

  (* Lemma view_set {S V} (l : t S V) : forall v s, view l (set l v s) = v.
  Proof.
    destruct l as [l [H1 H2]]. 
    unfold view, set; ss.
    i. hspecialize H2 with s. cong snd in H2. hspecialize H2 with v. ss.
    unfold compose in H2. rewrite H2. ss.
  Qed.

  Lemma set_view {S V} (l : t S V) : forall s, set l (view l s) s = s.
  Proof.
    destruct l as [l [H1 H2]]. unfold view, set; ss.
    i. hspecialize H1 with s. ss.
  Qed.

  Lemma set_set {S V} (l : t S V) : forall v v' s, set l v' (set l v s) = set l v' s.
  Proof.
    destruct l as [l [H1 H2]]. unfold view, set; ss.
    i. hspecialize H2 with s. cong snd in H2. hspecialize H2 with v. ss.
    unfold compose in H2. rewrite H2. ss.
  Qed.

  Definition compose {A B C} : t A B -> t B C -> t A C.
  Proof.
    intros l1 l2.
    exists (fun a => (view l2 (view l1 a), fun c => set l1 (set l2 c (view l1 a)) a)).
    constructor.
    - extensionalities s. cbn. rewrite ! set_view. ss.
    - extensionalities s. unfold Store.map, Store.cojoin, compose; ss. f_equal.
      extensionalities c. f_equal.
      + rewrite ! view_set. ss.
      + extensionalities c'. rewrite view_set, ! set_set. ss.
  Defined.

  Lemma compose_assoc A B C D (l1 : t A B) (l2 : t B C) (l3 : t C D) :
    (compose (compose l1 l2) l3) = compose l1 (compose l2 l3).
  Proof.
    eapply eq_sig_hprop.
    - i. eapply proof_irrelevance.
    - ss.
  Qed. *)

End Lens.

Section PRODUCT_LENS.

  (* Context {A B : Type}. *)

  Definition anypair (oa ob: option Any.t) : option Any.t :=
    match oa, ob with
    | Some a, Some b => Some (Any.pair a b)
    | _, _ => None
    end.

  Definition fstl : Lens.t (option Any.t) (option Any.t) :=
    (fun oab => 
    match oab with
    | Some ab => match Any.split ab with
                | Some (a, b) => (Some a, (fun oa => anypair oa (Some b))) 
                | None => (None, (fun _ => None))
                end       
    | None => (None, (fun _ => None))
    end).

  Definition sndl : Lens.t (option Any.t) (option Any.t) :=
    (fun oab => 
    match oab with
    | Some ab => match Any.split ab with
                | Some (a, b) => (Some b, (fun ob => anypair (Some a) ob)) 
                | None => (None, (fun _ => None))
                end       
    | None => (None, (fun _ => None))
    end).

End PRODUCT_LENS.
