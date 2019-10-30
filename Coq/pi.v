Definition comp {A B C : Type} (g : B -> C) (f : A -> B) : A -> C.
Proof.
  intros a.
  exact (g (f a)).
Defined.
