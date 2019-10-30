Require Export pi.

Inductive NN : Type :=
| zero : NN
| succ : NN -> NN.

Fixpoint add_NN (m n : NN) :=
  match n with
  | zero => m
  | succ n => succ (add_NN m n)
  end.

Definition add_NN' (m n : NN) : NN :=
  add_NN n m.

Notation "x '+' y" := (add_NN x y).

Fixpoint mul_NN (m n : NN) : NN :=
  match n with
  | zero => zero
  | succ n => add_NN m (mul_NN m n)
  end.

Notation "x '*' y" := (mul_NN x y).

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

Fixpoint power (m n : NN) : NN :=
  match m with
  | zero => succ zero
  | succ m => mul_NN n (power m n)
  end.
