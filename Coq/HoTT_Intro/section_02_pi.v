Definition idmap {A} : A -> A.
Proof.
  intro a.
  exact a.
Defined.

Definition comp {A B C : Type} (g : B -> C) (f : A -> B) : A -> C.
Proof.
  intro a.
  exact (g (f a)).
Defined.

Definition const {A B} (b : B) : A -> B := fun x => b.

Definition comp_Pi {A} {B : A -> Type} {C : forall x, B x -> Type} :
  forall (f : forall x, B x), (forall x y, C x y) -> (forall x, C x (f x)).
Proof.
  intros f g x.
  exact (g x (f x)).
Defined.

Definition swap_Pi {A B} {C : A -> (B -> Type)} :
  (forall x y, C x y) -> (forall y x, C x y).
Proof.
  intros h b a.
  exact (h a b).
Defined.
