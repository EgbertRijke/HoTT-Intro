Require Export section_02_pi.

Inductive N : Type :=
| zero_N : N
| succ_N : N -> N.

Definition one_N : N := succ_N zero_N.

Definition two_N : N := succ_N one_N.

Definition three_N : N := succ_N two_N.

Definition four_N : N := succ_N three_N.

Definition five_N : N := succ_N four_N.

Definition six_N : N := succ_N five_N.

Definition seven_N : N := succ_N six_N.

Definition eight_N : N := succ_N seven_N.

Definition nine_N : N := succ_N eight_N.

Definition ten_N : N := succ_N nine_N.

Definition add_N (m n : N) : N.
Proof.
  induction n as [|n s].
  - exact m.
  - exact (succ_N s).
Defined.

Definition add_N' (m n : N) : N :=
  add_N n m.

Notation "x '+' y" := (add_N x y).

(*
Fixpoint min_N (m n : N) : N :=
  match n with
  | zero_N => zero_N
  | succ_N n =>
    match m with
    | zero_N => zero_N
    | succ_N m => succ_N (min_N m n)
    end
  end.
 *)

Definition min_N : N -> N -> N.
Proof.
  intro m.
  induction m as [|m f].
  - exact (const zero_N).
  - intro n; destruct n.
    * exact zero_N.
    * exact (succ_N (f n)).
Defined.

Fixpoint max_N (m n : N) :=
  match n with
  | zero_N => m
  | succ_N n =>
    match m with
    | zero_N => succ_N n
    | succ_N m => succ_N (max_N m n)
    end
  end.

Definition mul_N (m n : N) : N.
Proof.
  induction n as [|n v].
  - exact zero_N.
  - exact (add_N m v).
Defined.

Notation "x '*' y" := (mul_N x y).

Fixpoint power_N (m n : N) : N :=
  match m with
  | zero_N => one_N
  | succ_N m => n * (power_N m n)
  end.

Fixpoint factorial (n : N) : N :=
  match n with
  | zero_N => one_N
  | succ_N n => (factorial n) * (succ_N n)
  end.

Fixpoint binomial_coefficient (n k : N) : N :=
  match n with
  | zero_N =>
    match k with
    | zero_N => one_N
    | succ_N k => zero_N
    end
  | succ_N n =>
    match k with
    | zero_N => one_N
    | succ_N k =>
      (binomial_coefficient n (succ_N k)) + (binomial_coefficient n k)
    end
  end.

Notation "n 'choose' k" := (binomial_coefficient n k) (at level 70).

Fixpoint Fibonacci (n : N) : N :=
  match n with 
  | zero_N => zero_N
  | succ_N n' =>
    match n' with
    | zero_N => one_N
    | succ_N m => (Fibonacci n') + (Fibonacci m) 
    end
  end.
