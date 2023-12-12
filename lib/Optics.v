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

  Definition t S V := S -> Store.t V S.

  Definition view {S V} : t S V -> S -> V := fun l s => fst (l s).
  Definition set {S V} : t S V -> V -> S -> S := fun l a s => snd (l s) a.
  Definition modify {S V} : t S V -> (V -> V) -> (S -> S) := fun l f s => Lens.set l (f (Lens.view l s)) s.

End Lens.

Section PRODUCT_LENS.

  (* Context {A B : Type}. *)

  Definition fstl : Lens.t Any.t Any.t :=
    (fun ab => 
      match Any.split ab with
      | Some (a, b) => (a, (fun a' => Any.pair a' b)) 
      | None => (tt↑, (fun _ => tt↑))
      end).

  Definition sndl : Lens.t Any.t Any.t :=
    (fun ab => 
      match Any.split ab with
      | Some (a, b) => (b, (fun b' => Any.pair a b')) 
      | None => (tt↑, (fun _ => tt↑))
      end).

End PRODUCT_LENS.
