/-------------------------------------------------------------------------------
  LECTURE 2. Inductive types

-------------------------------------------------------------------------------/

prelude

inductive hnat.{u} : Type.{u} :=
  | zero : hnat
  | succ : hnat → hnat

print hnat.rec
print hnat.rec_on

notation `ℕ` := hnat

namespace hnat

definition add : hnat → hnat → hnat :=
  hnat.rec (λ m, m) (λ m (add_m : hnat → hnat) k, hnat.succ (add_m k))

definition mul : hnat → hnat → hnat :=
  hnat.rec (λ m, hnat.zero) (λ m (mul_m : hnat → hnat) k, add m (mul_m k))

end hnat

inductive hunit.{u} : Type.{u} :=
  | tt : hunit

notation `𝟙` := hunit

namespace hunit

definition terminating (A : Type) : A → hunit :=
  λ a, hunit.tt

end hunit

inductive hempty.{u} : Type.{u} 

print hempty.rec
print hempty.rec_on

notation `∅` := hempty
notation `𝟘` := hempty

definition not (A : Type) := A → ∅

namespace hempty

definition initiating (A : Type) : ∅ → A :=
  @hempty.rec (λ x, A)

end hempty

inductive hbool.{u} : Type.{u} :=
  | false : hbool
  | true : hbool

notation `ℤ₂` := hbool
notation `𝟚` := hbool

namespace hbool

definition taut : hbool → Type :=
  hbool.rec hempty hunit

definition or : hbool → hbool → hbool :=
  hbool.rec (hbool.rec false true) (λ s, true)

definition and : hbool → hbool → hbool :=
  hbool.rec (λ b, false) (hbool.rec false true)

definition implies : hbool → hbool → hbool :=
  hbool.rec (λ b, true) (hbool.rec false true)

definition neg : hbool → hbool :=
  hbool.rec true false

definition mul : hbool → hbool → hbool :=
  hbool.rec (hbool.rec false false) (hbool.rec false true)

definition mul_unit : hbool := true

definition add : hbool → hbool → hbool :=
  hbool.rec (λ b, b) (λ b, neg b)

definition add_unit : hbool := false

definition add_inv : hbool → hbool :=
  λ b, b

end hbool

inductive coprod.{u v} (A : Type.{u}) (B : Type.{v}) : Type.{max u v} :=
  | inl : A → coprod A B
  | inr : B → coprod A B

print coprod.inl

definition hint : Type :=
  coprod hnat (coprod hunit hnat)

notation `ℤ` := hint

namespace hint

definition neg : hnat → hint :=
  @coprod.inl hnat (coprod hunit hnat)

definition zero : hint :=
  @coprod.inr hnat (coprod hunit hnat) (@coprod.inl hunit hnat hunit.tt)

definition one : hint :=
  @coprod.inr hnat (coprod hunit hnat) (@coprod.inr hunit hnat hnat.zero)

definition neg_one : hint :=
  @coprod.inl hnat (coprod hunit hnat) hnat.zero

definition pos : hnat → hint :=
  λ n, @coprod.inr hnat (coprod hunit hnat) (@coprod.inr hunit hnat n)

definition destruct {P : hint → Type} (pneg : Π (n : hnat), P (neg n)) 
  (pzero : P zero) (ppos : Π (n : hnat), P (pos n))
  : Π (k : hint), P k :=
  coprod.rec (λ n, pneg n) (λ l, coprod.rec (λ t, hunit.rec pzero t) (λ n, ppos n) l)

definition destruct_full {P : hint → Type} 
  (pneg_one : P (neg_one))
  (pneg_succ : Π (n : hnat), P (neg n) → P (neg (hnat.succ n)))
  (pzero : P zero)
  (ppos_one : P (one))
  (ppos_succ : Π (n : hnat), P (pos n) → P (pos (hnat.succ n)))
  : Π (k : hint), P k :=
  destruct (hnat.rec pneg_one pneg_succ) pzero (hnat.rec ppos_one ppos_succ)

definition succ : hint → hint :=
  destruct
    ( hnat.rec zero (λ m k, neg m))
    one 
    ( λ n, pos (hnat.succ n))

definition pred : hint → hint :=
  destruct_full
    ( neg (hnat.succ hnat.zero))
    ( λ n k, neg (hnat.succ n))
    neg_one
    zero 
    ( λ m k, pos m)

definition minus : hint → hint :=
  destruct (λ n, pos n) zero (λ n, neg n)

definition add : hint → hint → hint :=
  destruct_full
    pred
    ( λ m (add_neg_m : hint → hint) (l : hint), pred (add_neg_m l))
    (λ l, l)
    succ
    ( λ m (add_pos_m : hint → hint) (l : hint), succ (add_pos_m l))

-- The additive inverse
definition add_inv : hint → hint := minus

-- The additive unit
definition add_unit : hint := zero

definition mul : hint → hint → hint :=
  destruct_full
    minus
    ( λ m (mul_neg_m : hint → hint) (l : hint), add (neg m) (mul_neg_m l))
    ( λ l, zero)
    ( λ l, l)
    ( λ m (mul_pos_m : hint → hint) (l : hint), add (pos m) (mul_pos_m l))

definition mul_unit : hint := one

end hint

inductive hSigma.{u v} (A : Type.{u}) (B : A → Type.{v}) : Type.{max u v} :=
  pair : Π (x : A), B x → hSigma A B

definition hprod (A : Type) (B : Type) : Type :=
  hSigma A (λ x, B)

namespace hprod
  
  definition pair {A : Type} {B : Type} : A → B → hprod A B :=
    λ a b, hSigma.pair a b

end hprod

namespace hSigma

definition pr1 {A : Type} {B : A → Type} (x : hSigma A B) : A :=
  hSigma.rec (λ a b, a) x

definition pr2 {A : Type} {B : A → Type} (x : hSigma A B) : B (pr1 x) :=
  hSigma.rec (λ a b, b) x

end hSigma
