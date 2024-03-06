Require Import sflibCCR.

Ltac eadmit :=
  exfalso; clear; admit.

Definition admit (excuse: String.string) {T: Type} : T. Admitted.

Tactic Notation "admit" constr(excuse) := idtac excuse; exact (admit excuse).