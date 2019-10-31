Require Export nat.

Inductive unit : Type :=
| star : unit.

Inductive empty : Type := .

Definition neg (A : Type) : Type := A -> empty.

Definition ex_falso {B : empty -> Type} : forall x, B x.
Proof.
  intro x.
  induction x.
Defined.

Definition ex_falso_map {A} : empty -> A := ex_falso.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b : bool) : bool.
Proof.
  induction b.
  - exact false.
  - exact true.
Defined.

Definition andb (b b' : bool) : bool.
Proof.
  induction b.
  - induction b'.
    * exact true.
    * exact false.
  - induction b'.
    * exact false.
    * exact false.
Defined.

Definition orb (b b' : bool) : bool.
Proof.
  induction b.
  - induction b'.
    * exact true.
    * exact true.
  - induction b'.
    * exact true.
    * exact false.
Defined.

Inductive coprod (A B : Type) : Type :=
| inl' : A -> coprod A B
| inr' : B -> coprod A B.

Definition inl {A B} : A -> coprod A B := inl' A B.

Definition inr {A B} : B -> coprod A B := inr' A B.

Definition Z : Type := coprod N (coprod unit N).

Definition zero_Z : Z := inr (inl star).

Definition one_Z : Z := inr (inr zero_N).

Definition two_Z : Z := inr (inr one_N).

Definition neg_one_Z : Z := inl zero_N.

Fixpoint succ_Z (k : Z) : Z :=
  match k with
  | inl' _ _ n =>
    match n with
    | zero_N => zero_Z
    | succ_N m => inl m
    end
  | inr' _ _ x =>
    match x with
    | inl' _ _ x =>
      match x with
      | star => one_Z
      end
    | inr' _ _ n =>
      match n with
      | zero_N => two_Z
      | succ_N n => inr (inr (succ_N (succ_N n)))
      end
    end
  end.
