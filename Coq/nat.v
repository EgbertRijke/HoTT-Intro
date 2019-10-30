Inductive NN : Type :=
| zero : NN
| succ : NN -> NN.

Fixpoint add_NN (m n : NN) :=
  match n with
  | zero => m
  | succ n => succ (add_NN m n)
  end.

Fixpoint mul_NN (m n : NN) : NN :=
  match n with
  | zero => zero
  | succ n => add_NN m (mul_NN m n)
  end.

Fixpoint fibonacci (n : NN) : NN :=
  match n with 
  | zero => zero
  | succ Sn =>
    match Sn with
    | zero => succ zero
    | succ m => add_NN (fibonacci Sn) (fibonacci m) 
    end
  end.

Fixpoint factorial (n : NN) : NN :=
  match n with
  | zero => succ zero
  | succ n => mul_NN (factorial n) (succ n)
  end.

Eval compute in fibonacci (succ (succ (succ (succ (succ (succ zero)))))).
                                

Eval compute in mul_NN (succ (succ zero)) (succ (succ zero)).

Inductive Id {A} (a : A) : A -> Type :=
| refl : Id a a.

Lemma ap {A B} (f : A -> B) {x y : A} (p : Id x y) : Id (f x) (f y).
Proof.
  destruct p.
  apply refl.
Defined.

Definition left_unit_law_add_NN (n : NN) : Id (add_NN zero n) n.
Proof.
  induction n.
  - apply refl.
  - cbn. now apply ap.
Defined.
