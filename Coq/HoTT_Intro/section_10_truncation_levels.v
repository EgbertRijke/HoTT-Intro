Require Export section_09_fundamental_theorem.

Definition is_prop (A : Type) : Type := forall x y : A, is_contr (Id x y).

Definition is_prop' (A : Type) : Type := forall x y : A, Id x y.

Definition is_prop_coh {A : Type} (H : is_prop' A) : is_prop' A.
Proof.
  intros x y.
  refine (concat _ _).
  exact (inv (H x x)).
  exact (H x y).
Defined.
