prelude

inductive nat.{u} : Type.{u} :=
  | zero : nat
  | succ : nat → nat

print nat.rec
print nat.rec_on

namespace nat

definition add : nat → nat → nat :=
  λ n, nat.rec (λ m, m) (λ m (add_m : nat → nat) k, succ (add_m k)) n

end nat

inductive unit.{u} : Type.{u} :=
  | tt : unit

namespace unit

definition terminating (A : Type) : A → unit :=
  λ a, unit.tt

end unit

inductive empty.{u} : Type.{u} 

print empty.rec
print empty.rec_on

namespace empty

definition initiating (A : Type) : empty → A :=
  λ t, @empty.rec (λ x, A) t

end empty

inductive bool.{u} : Type.{u} :=
  | false : bool
  | true : bool

namespace bool

definition taut : bool → Type :=
  λ t, bool.rec empty unit t

definition or : bool → bool → bool :=
  λ t, bool.rec (λ s, bool.rec false true s) (λ s, true) t

definition and : bool → bool → bool :=
  λ t, bool.rec (λ s, false) (λ s, bool.rec false true s) t

definition implies : bool → bool → bool :=
  λ t, bool.rec (λ s, true) (λ s, bool.rec false true s) t

definition neg : bool → bool :=
  λ t, bool.rec true false t

definition mul : bool → bool → bool :=
  λ t, bool.rec (λ s, bool.rec false false s) (λ s, bool.rec false true s) t

definition mul_unit : bool := true

definition add : bool → bool → bool :=
  λ t, bool.rec (λ s, s) (λ s, neg s) t

definition add_unit : bool := false

definition add_inv : bool → bool :=
  λ t, t

end bool

inductive coprod.{u v} (A : Type.{u}) (B : Type.{v}) : Type.{max u v} :=
  | inl : A → coprod A B
  | inr : B → coprod A B

print coprod.inl

definition int : Type :=
  coprod nat (coprod unit nat)

namespace int

definition neg : nat → int :=
  λ n, @coprod.inl nat (coprod unit nat) n

definition zero : int :=
  @coprod.inr nat (coprod unit nat) (@coprod.inl unit nat unit.tt)

definition one : int :=
  @coprod.inr nat (coprod unit nat) (@coprod.inr unit nat nat.zero)

definition neg_one : int :=
  @coprod.inl nat (coprod unit nat) nat.zero

definition pos : nat → int :=
  λ n, @coprod.inr nat (coprod unit nat) (@coprod.inr unit nat n)

definition ind {P : int → Type} (pneg : Π (n : nat), P (neg n)) 
  (pzero : P zero) (ppos : Π (n : nat), P (pos n)) (k : int)
  : P k :=
  coprod.rec (λ n, pneg n) (λ l, coprod.rec (λ t, unit.rec pzero t) (λ n, ppos n) l) k

definition succ : int → int :=
  λ k, ind 
    (λ n, nat.rec zero (λ m k, neg m) n)
    one
    (λ n, pos (nat.succ n))
    k

definition pred : int → int :=
  λ k, ind
    (λ n, neg (nat.succ n))
    neg_one
    (λ n, nat.rec zero (λ m k, pos m) n)
    k

definition minus : int → int :=
  λ k, ind (λ n, pos n) zero (λ n, neg n) k

print int.ind

definition add : int → int → int :=
  λ k, ind
    (λ n, nat.rec 
            pred 
            (λ m (add_neg_m : int → int) (l : int), pred (add_neg_m l)) 
            n
    )
    (λ l, l)
    (λ n, nat.rec
            succ
            (λ m (add_pos_m : int → int) (l : int), succ (add_pos_m l))
            n
    )
    k

definition add_inv : int → int := minus

definition add_unit : int := zero

definition mul : int → int → int :=
  λ k, ind
    (λ n, nat.rec
            minus
            (λ m (mul_neg_m : int → int) (l : int), add (neg m) (mul_neg_m l))
            n
    )
    (λ l, zero)
    (λ n, nat.rec
            (λ l, l)
            (λ m (mul_pos_m : int → int) (l : int), add (pos m) (mul_pos_m l))
            n
    )
    k

definition mul_unit : int := one

end int

inductive Sigma.{u v} (A : Type.{u}) (B : A → Type.{v}) : Type.{max u v} :=
  dpair : Π (x : A), B x → Sigma A B

namespace sigma

definition pr1 {A : Type} {B : A → Type} (x : Sigma A B) : A :=
  Sigma.rec (λ a b, a) x

definition pr2 {A : Type} {B : A → Type} (x : Sigma A B) : B (pr1 x) :=
  Sigma.rec (λ a b, b) x

end sigma
