Require Export section_02_pi.

Inductive ℕ : Type :=
| zero_ℕ : ℕ
| succ_ℕ : ℕ -> ℕ.

Definition one_ℕ : ℕ := succ_ℕ zero_ℕ.

Definition two_ℕ : ℕ := succ_ℕ one_ℕ.

Definition three_ℕ : ℕ := succ_ℕ two_ℕ.

Definition four_ℕ : ℕ := succ_ℕ three_ℕ.

Definition five_ℕ : ℕ := succ_ℕ four_ℕ.

Definition six_ℕ : ℕ := succ_ℕ five_ℕ.

Definition seven_ℕ : ℕ := succ_ℕ six_ℕ.

Definition eight_ℕ : ℕ := succ_ℕ seven_ℕ.

Definition nine_ℕ : ℕ := succ_ℕ eight_ℕ.

Definition ten_ℕ : ℕ := succ_ℕ nine_ℕ.

Definition add_ℕ (m n : ℕ) : ℕ.
Proof.
  induction n as [|n s].
  - exact m.
  - exact (succ_ℕ s).
Defined.

Definition add_ℕ' (m n : ℕ) : ℕ :=
  add_ℕ n m.

Notation "x '+' y" := (add_ℕ x y).

(*
Fixpoint min_ℕ (m n : ℕ) : ℕ :=
  match n with
  | zero_ℕ => zero_ℕ
  | succ_ℕ n =>
    match m with
    | zero_ℕ => zero_ℕ
    | succ_ℕ m => succ_ℕ (min_ℕ m n)
    end
  end.
 *)

Definition min_ℕ : ℕ -> ℕ -> ℕ.
Proof.
  intro m.
  induction m as [|m f].
  - exact (const zero_ℕ).
  - intro n; destruct n.
    * exact zero_ℕ.
    * exact (succ_ℕ (f n)).
Defined.

Fixpoint max_ℕ (m n : ℕ) :=
  match n with
  | zero_ℕ => m
  | succ_ℕ n =>
    match m with
    | zero_ℕ => succ_ℕ n
    | succ_ℕ m => succ_ℕ (max_ℕ m n)
    end
  end.

Definition mul_ℕ (m n : ℕ) : ℕ.
Proof.
  induction n as [|n v].
  - exact zero_ℕ.
  - exact (add_ℕ m v).
Defined.

Notation "x '*' y" := (mul_ℕ x y).

Fixpoint power_ℕ (m n : ℕ) : ℕ :=
  match m with
  | zero_ℕ => one_ℕ
  | succ_ℕ m => n * (power_ℕ m n)
  end.

Fixpoint factorial (n : ℕ) : ℕ :=
  match n with
  | zero_ℕ => one_ℕ
  | succ_ℕ n => (factorial n) * (succ_ℕ n)
  end.

Fixpoint binomial_coefficient (n k : ℕ) : ℕ :=
  match n with
  | zero_ℕ =>
    match k with
    | zero_ℕ => one_ℕ
    | succ_ℕ k => zero_ℕ
    end
  | succ_ℕ n =>
    match k with
    | zero_ℕ => one_ℕ
    | succ_ℕ k =>
      (binomial_coefficient n (succ_ℕ k)) + (binomial_coefficient n k)
    end
  end.

Notation "n 'choose' k" := (binomial_coefficient n k) (at level 70).

Fixpoint Fibonacci (n : ℕ) : ℕ :=
  match n with 
  | zero_ℕ => zero_ℕ
  | succ_ℕ n' =>
    match n' with
    | zero_ℕ => one_ℕ
    | succ_ℕ m => (Fibonacci n') + (Fibonacci m) 
    end
  end.
