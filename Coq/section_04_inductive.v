Require Export section_03_nat.

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

Definition neg_two_Z : Z := inl one_N.

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

Inductive Sigma (A : Type) (B : A -> Type) : Type :=
| pair' : forall x, B x -> Sigma A B.

Definition pair {A : Type} {B : A -> Type} : forall x, B x -> Sigma A B :=
  pair' A B.

Definition pr1 {A : Type} {B : A -> Type} (x : Sigma A B) : A.
Proof.
  induction x.
  assumption.
Defined.

Definition pr2 {A : Type} {B : A -> Type} (x : Sigma A B) : B (pr1 x).
Proof.
  induction x.
  assumption.
Defined.

Definition prod (A B : Type) : Type := Sigma A (fun x => B).

(* Exercises *)

Lemma double_neg_elim_decidable (A : Type) :
  coprod A (neg A) -> (neg (neg A) -> A).
Proof.
  intro x.
  induction x.
  - now apply const.
  - intro y. now apply ex_falso_map.
Defined.

Lemma triple_neg_elim (A : Type) :
  neg (neg (neg A)) -> neg A.
Proof.
  intros f a.
  apply ex_falso_map.
  now apply f.
Defined.

Fixpoint pred_Z (k : Z) : Z :=
  match k with
  | inl' _ _ n =>
    match n with
    | zero_N => neg_two_Z
    | succ_N m => inl (succ_N (succ_N m))
    end
  | inr' _ _ x =>
    match x with
    | inl' _ _ x =>
      match x with
      | star => neg_one_Z
      end
    | inr' _ _ n =>
      match n with
      | zero_N => zero_Z
      | succ_N m => inr (inr m)
      end
    end
  end.

Definition add_Z (k l : Z) : Z.
Proof.
  induction l as [n | x].
  - induction n as [|n s].
    * exact (pred_Z k).
    * exact (pred_Z s).
  - induction x as [x | n].
    * exact k.
    * induction n as [|n s].
      ** exact (succ_Z k).
      ** exact (succ_Z s).
Defined.
