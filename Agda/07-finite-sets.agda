{-# OPTIONS --without-K --exact-split --safe #-}

module 07-finite-sets where

import 06-universes
open 06-universes public

--------------------------------------------------------------------------------

{- Section 7.1 The finite types -}

{- Definition 7.1.1 -}

{- We introduce the finite types as a family indexed by ℕ. -}

Fin : ℕ → UU lzero
Fin zero-ℕ = empty
Fin (succ-ℕ k) = coprod (Fin k) unit

inl-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
inl-Fin k = inl

neg-one-Fin : {k : ℕ} → Fin (succ-ℕ k)
neg-one-Fin {k} = inr star

{- Definition 7.1.4 -}

zero-Fin : {k : ℕ} → Fin (succ-ℕ k)
zero-Fin {zero-ℕ} = inr star
zero-Fin {succ-ℕ k} = inl zero-Fin

{- Definition 7.1.5 -}

succ-Fin : {k : ℕ} → Fin k → Fin k
succ-Fin {succ-ℕ zero-ℕ} x = x
succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inl x)) = inl (succ-Fin (inl x))
succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inr x)) = neg-one-Fin
succ-Fin {succ-ℕ (succ-ℕ k)} (inr x) = zero-Fin

{- We show that the successor of neg-one-Fin is zero-Fin. -}

succ-neg-one-Fin : {k : ℕ} → Id (succ-Fin (neg-one-Fin {k})) zero-Fin
succ-neg-one-Fin {zero-ℕ} = refl
succ-neg-one-Fin {succ-ℕ k} = refl

{- Definition 7.1.6 -}

{- The modulo function -}

mod-succ-ℕ : (k : ℕ) → ℕ → Fin (succ-ℕ k)
mod-succ-ℕ k zero-ℕ = zero-Fin
mod-succ-ℕ zero-ℕ (succ-ℕ n) = zero-Fin
mod-succ-ℕ (succ-ℕ k) (succ-ℕ n) = succ-Fin (mod-succ-ℕ (succ-ℕ k) n)

mod-two-ℕ : ℕ → Fin two-ℕ
mod-two-ℕ = mod-succ-ℕ one-ℕ

mod-three-ℕ : ℕ → Fin three-ℕ
mod-three-ℕ = mod-succ-ℕ two-ℕ

-- We show that mod-succ-ℕ is a periodic function with period succ-ℕ n --

{- Definition 7.1.7 -}

is-periodic-ℕ :
  (k : ℕ) {l : Level} {A : UU l} (f : ℕ → A) → UU l
is-periodic-ℕ k f = (x : ℕ) → Id (f x) (f (add-ℕ k x))

{- Lemma 7.1.8 -}

{- Our first goal is to show that mod-succ-ℕ is a periodic function. We will
   first prove some intermediate lemmas. -}

successor-law-mod-succ-ℕ :
  (k x : ℕ) → leq-ℕ x k →
  Id (mod-succ-ℕ (succ-ℕ k) x) (inl (mod-succ-ℕ k x))
successor-law-mod-succ-ℕ k zero-ℕ star = refl
successor-law-mod-succ-ℕ (succ-ℕ k) (succ-ℕ x) p =
  ( ( ap succ-Fin
      ( successor-law-mod-succ-ℕ (succ-ℕ k) x
        ( preserves-leq-succ-ℕ x k p))) ∙
    ( ap succ-Fin (ap inl (successor-law-mod-succ-ℕ k x p)))) ∙
  ( ap inl (ap succ-Fin (inv (successor-law-mod-succ-ℕ k x p))))

{- Corollary 7.1.9 -}

neg-one-law-mod-succ-ℕ :
  (k : ℕ) → Id (mod-succ-ℕ k k) neg-one-Fin
neg-one-law-mod-succ-ℕ zero-ℕ = refl
neg-one-law-mod-succ-ℕ (succ-ℕ k) =
  ap succ-Fin
    ( ( successor-law-mod-succ-ℕ k k (reflexive-leq-ℕ k)) ∙
      ( ap inl (neg-one-law-mod-succ-ℕ k)))

base-case-is-periodic-mod-succ-ℕ :
  (k : ℕ) → Id (mod-succ-ℕ k (succ-ℕ k)) zero-Fin
base-case-is-periodic-mod-succ-ℕ zero-ℕ = refl
base-case-is-periodic-mod-succ-ℕ (succ-ℕ k) =
  ap succ-Fin (neg-one-law-mod-succ-ℕ (succ-ℕ k))

{- Proposition 7.1.10 -}

is-periodic-mod-succ-ℕ :
  (k : ℕ) → is-periodic-ℕ (succ-ℕ k) (mod-succ-ℕ k)
is-periodic-mod-succ-ℕ k zero-ℕ =
  inv (base-case-is-periodic-mod-succ-ℕ k)
is-periodic-mod-succ-ℕ zero-ℕ (succ-ℕ x) = refl
is-periodic-mod-succ-ℕ (succ-ℕ k) (succ-ℕ x) =
  ap succ-Fin (is-periodic-mod-succ-ℕ (succ-ℕ k) x)

--------------------------------------------------------------------------------

{- Section 7.2 Decidability -}

{- Definition 7.2.1 -}

is-decidable : {l : Level} (A : UU l) → UU l
is-decidable A = coprod A (¬ A)

{- Example 7.2.2 -}

is-decidable-unit : is-decidable unit
is-decidable-unit = inl star

is-decidable-empty : is-decidable empty
is-decidable-empty = inr id

{- Definition 7.2.3 -}

{- We say that a type has decidable equality if we can decide whether 
   x = y holds for any x, y : A. -}
   
has-decidable-equality : {l : Level} (A : UU l) → UU l
has-decidable-equality A = (x y : A) → is-decidable (Id x y)

{- Lemma 7.2.5 -}

is-decidable-iff :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → (B → A) → is-decidable A → is-decidable B
is-decidable-iff f g =
  functor-coprod f (functor-neg g)

{- Proposition 7.2.6 -}

{- The type ℕ is an example of a type with decidable equality. -}

is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y =
  is-decidable-iff (eq-Eq-ℕ x y) Eq-ℕ-eq (is-decidable-Eq-ℕ x y)

{- Definition 7.2.7 -}

{- Observational equality on finite sets -}

Eq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit

{- Proposition 7.2.8 -}

refl-Eq-Fin : {k : ℕ} (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin {succ-ℕ k} (inl x) = refl-Eq-Fin x
refl-Eq-Fin {succ-ℕ k} (inr x) = star

Eq-Fin-eq : {k : ℕ} {x y : Fin k} → Id x y → Eq-Fin k x y
Eq-Fin-eq {k} refl = refl-Eq-Fin {k} _

eq-Eq-Fin :
  {k : ℕ} {x y : Fin k} → Eq-Fin k x y → Id x y
eq-Eq-Fin {succ-ℕ k} {inl x} {inl y} e = ap inl (eq-Eq-Fin e)
eq-Eq-Fin {succ-ℕ k} {inr star} {inr star} star = refl

{- Proposition 7.2.9 -}

{- We show that Fin k has decidable equality, for each n : ℕ. -}

is-decidable-Eq-Fin :
  (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = inl star

is-decidable-eq-Fin :
  (k : ℕ) (x y : Fin k) → is-decidable (Id x y)
is-decidable-eq-Fin k x y =
  functor-coprod eq-Eq-Fin (functor-neg Eq-Fin-eq) (is-decidable-Eq-Fin k x y)

{- Proposition 7.2.10 -}

{- The inclusion function Fin k → Fin (succ-ℕ k) is injective. -}

is-injective-inl-Fin :
  {k : ℕ} {x y : Fin k} → Id (inl-Fin k x) (inl-Fin k y) → Id x y
is-injective-inl-Fin p = eq-Eq-Fin (Eq-Fin-eq p)

{- Lemma 7.2.11 -}

neq-zero-succ-Fin :
  {k : ℕ} {x : Fin k} → ¬ (Id (succ-Fin (inl-Fin k x)) zero-Fin)
neq-zero-succ-Fin {succ-ℕ k} {inl x} p =
  neq-zero-succ-Fin (is-injective-inl-Fin p)
neq-zero-succ-Fin {succ-ℕ k} {inr star} p =
  Eq-Fin-eq {succ-ℕ (succ-ℕ k)} {inr star} {zero-Fin} p

{- Proposition 7.2.12 -}

{- The successor function Fin k → Fin k is injective. -}

is-injective-succ-Fin :
  {k : ℕ} {x y : Fin k} → Id (succ-Fin x) (succ-Fin y) → Id x y
is-injective-succ-Fin {succ-ℕ zero-ℕ} {inr star} {inr star} p = refl
is-injective-succ-Fin {succ-ℕ (succ-ℕ k)} {inl (inl x)} {inl (inl y)} p =
  ap inl (is-injective-succ-Fin (is-injective-inl-Fin p))
is-injective-succ-Fin {succ-ℕ (succ-ℕ k)} {inl (inr star)} {inl (inr star)} p = refl
is-injective-succ-Fin {succ-ℕ (succ-ℕ k)} {inl (inl x)} {inr star} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl x} p)
is-injective-succ-Fin {succ-ℕ (succ-ℕ k)} {inr star} {inl (inl y)} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl y} (inv p))
is-injective-succ-Fin {succ-ℕ (succ-ℕ k)} {inr star} {inr star} p = refl

--------------------------------------------------------------------------------

{- Section 7.3 Definitions by case analysis -}

{- We define the predecessor function on finite sets. -}

{- We define the predecessor function with manual with-abstraction, to give a
   bit more flexibility. -}

cases-pred-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k))
  (d : is-decidable (Eq-Fin (succ-ℕ k) x zero-Fin)) → Fin (succ-ℕ k)
cases-pred-Fin {zero-ℕ} (inr star) d = zero-Fin
cases-pred-Fin {succ-ℕ k} (inl x) (inl e) = neg-one-Fin
cases-pred-Fin {succ-ℕ k} (inl x) (inr f) =
  inl (cases-pred-Fin {k} x (inr f))
cases-pred-Fin {succ-ℕ k} (inr star) (inr f) = inl neg-one-Fin

pred-Fin : {k : ℕ} → Fin k → Fin k
pred-Fin {succ-ℕ k} x =
  cases-pred-Fin {k} x (is-decidable-Eq-Fin (succ-ℕ k) x zero-Fin)

{- Alternatively, the predecessor can be defined with with-abstraction, but it
   turns out that this definition leads to complications. -}

pred-Fin' : {k : ℕ} → Fin (succ-ℕ k) → Fin (succ-ℕ k)
pred-Fin' {zero-ℕ} x = zero-Fin
pred-Fin' {succ-ℕ k} x with is-decidable-Eq-Fin (succ-ℕ (succ-ℕ k)) x zero-Fin
pred-Fin' {succ-ℕ k} (inl x) | inl e = neg-one-Fin
pred-Fin' {succ-ℕ k} (inl x) | inr f = inl (pred-Fin' x)
pred-Fin' {succ-ℕ k} (inr x) | inr f = inl neg-one-Fin

skip-neg-two-Fin :
  {k : ℕ} → Fin (succ-ℕ k) → Fin (succ-ℕ (succ-ℕ k))
skip-neg-two-Fin {k} (inl x) = inl (inl x)
skip-neg-two-Fin {k} (inr x) = inr x

cases-pred-Fin-2 :
  {k : ℕ} (x : Fin (succ-ℕ k))
  (d : is-decidable (Eq-Fin (succ-ℕ k) x zero-Fin)) → Fin (succ-ℕ k)
cases-pred-Fin-2 {zero-ℕ} x d = neg-one-Fin
cases-pred-Fin-2 {succ-ℕ k} (inl x) = skip-neg-two-Fin ∘ cases-pred-Fin-2 x
cases-pred-Fin-2 {succ-ℕ k} (inr x) d = inl neg-one-Fin

pred-Fin-2 : {k : ℕ} → Fin k → Fin k
pred-Fin-2 {succ-ℕ zero-ℕ} x = zero-Fin
pred-Fin-2 {succ-ℕ (succ-ℕ k)} (inl x) = skip-neg-two-Fin (pred-Fin x)
pred-Fin-2 {succ-ℕ (succ-ℕ k)} (inr x) = inl neg-one-Fin

--------------------------------------------------------------------------------

{- Section 7.4 The congruence relations modulo k -}

-- We introduce the divisibility relation. --

div-ℕ : ℕ → ℕ → UU lzero
div-ℕ m n = Σ ℕ (λ k → Id (mul-ℕ k m) n)

-- We show some basic properties of the divisibility relation --

{- In the following three constructions we show that if any two of the three
   numbers x, y, and x + y, is divisible by d, then so is the third. -}

div-add-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d y → div-ℕ d (add-ℕ x y)
div-add-ℕ d x y (pair n p) (pair m q) =
  pair
    ( add-ℕ n m)
    ( ( right-distributive-mul-add-ℕ n m d) ∙
      ( ap-add-ℕ p q))

div-left-summand-ℕ :
  (d x y : ℕ) → div-ℕ d y → div-ℕ d (add-ℕ x y) → div-ℕ d x
div-left-summand-ℕ zero-ℕ x y (pair m q) (pair n p) =
  pair zero-ℕ
    ( ( inv (right-zero-law-mul-ℕ n)) ∙
      ( p ∙ (ap (add-ℕ x) ((inv q) ∙ (right-zero-law-mul-ℕ m)))))
div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p) =
  pair
    ( dist-ℕ m n)
    ( is-injective-add-ℕ (mul-ℕ m (succ-ℕ d)) (mul-ℕ (dist-ℕ m n) (succ-ℕ d)) x
      ( ( inv
          ( ( right-distributive-mul-add-ℕ m (dist-ℕ m n) (succ-ℕ d)) ∙
            ( commutative-add-ℕ
              ( mul-ℕ m (succ-ℕ d))
              ( mul-ℕ (dist-ℕ m n) (succ-ℕ d))))) ∙ 
        ( ( ap
            ( mul-ℕ' (succ-ℕ d))
            ( leq-dist-ℕ m n
              ( leq-leq-mul-ℕ' m n d
                ( concatenate-eq-leq-eq-ℕ q
                  ( leq-add-ℕ' y x)
                  ( inv p))))) ∙
          ( p ∙ (ap (add-ℕ x) (inv q))))))

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (add-ℕ x y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 =
  div-left-summand-ℕ d y x H1 (tr (div-ℕ d) (commutative-add-ℕ x y) H2)

--------------------------------------------------------------------------------

-- Some lemmas that will help us showing that cong is an equivalence relation

order-two-elements-ℕ :
  (x y : ℕ) → coprod (leq-ℕ x y) (leq-ℕ y x)
order-two-elements-ℕ zero-ℕ zero-ℕ = inl star
order-two-elements-ℕ zero-ℕ (succ-ℕ y) = inl star
order-two-elements-ℕ (succ-ℕ x) zero-ℕ = inr star
order-two-elements-ℕ (succ-ℕ x) (succ-ℕ y) = order-two-elements-ℕ x y

cases-order-three-elements-ℕ :
  (x y z : ℕ) → UU lzero
cases-order-three-elements-ℕ x y z =
  coprod
    ( coprod ((leq-ℕ x y) × (leq-ℕ y z)) ((leq-ℕ x z) × (leq-ℕ z y)))
    ( coprod
      ( coprod ((leq-ℕ y z) × (leq-ℕ z x)) ((leq-ℕ y x) × (leq-ℕ x z)))
      ( coprod ((leq-ℕ z x) × (leq-ℕ x y)) ((leq-ℕ z y) × (leq-ℕ y x))))

order-three-elements-ℕ :
  (x y z : ℕ) → cases-order-three-elements-ℕ x y z
order-three-elements-ℕ zero-ℕ zero-ℕ zero-ℕ = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ zero-ℕ (succ-ℕ z) = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) zero-ℕ = inl (inr (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) =
  inl (functor-coprod (pair star) (pair star) (order-two-elements-ℕ y z))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ zero-ℕ =
  inr (inl (inl (pair star star)))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) =
  inr (inl (functor-coprod (pair star) (pair star) (order-two-elements-ℕ z x)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ =
  inr (inr (functor-coprod (pair star) (pair star) (order-two-elements-ℕ x y)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) =
  order-three-elements-ℕ x y z

triangle-equality-dist-ℕ :
  (x y z : ℕ) → (leq-ℕ x y) → (leq-ℕ y z) →
  Id (add-ℕ (dist-ℕ x y) (dist-ℕ y z)) (dist-ℕ x z)
triangle-equality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ H1 H2 = refl
triangle-equality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ z) star star =
  ap succ-ℕ (left-unit-law-add-ℕ z)
triangle-equality-dist-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) star H2 =
  left-successor-law-add-ℕ y (dist-ℕ y z) ∙
  ap succ-ℕ (leq-dist-ℕ y z H2)
triangle-equality-dist-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) H1 H2 =
  triangle-equality-dist-ℕ x y z H1 H2

cases-dist-ℕ :
  (x y z : ℕ) → UU lzero
cases-dist-ℕ x y z = 
  coprod
    ( Id (add-ℕ (dist-ℕ x y) (dist-ℕ y z)) (dist-ℕ x z))
    ( coprod
      ( Id (add-ℕ (dist-ℕ y z) (dist-ℕ x z)) (dist-ℕ x y))
      ( Id (add-ℕ (dist-ℕ x z) (dist-ℕ x y)) (dist-ℕ y z)))

is-total-dist-ℕ :
  (x y z : ℕ) → cases-dist-ℕ x y z
is-total-dist-ℕ x y z with order-three-elements-ℕ x y z
is-total-dist-ℕ x y z | inl (inl (pair H1 H2)) =
  inl (triangle-equality-dist-ℕ x y z H1 H2)
is-total-dist-ℕ x y z | inl (inr (pair H1 H2)) = 
  inr
    ( inl
      ( ( commutative-add-ℕ (dist-ℕ y z) (dist-ℕ x z)) ∙
        ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ y z)) ∙
          ( triangle-equality-dist-ℕ x z y H1 H2))))
is-total-dist-ℕ x y z | inr (inl (inl (pair H1 H2))) =
  inr
    ( inl
      ( ( ap (add-ℕ (dist-ℕ y z)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ y z x H1 H2) ∙
          ( symmetric-dist-ℕ y x))))
is-total-dist-ℕ x y z | inr (inl (inr (pair H1 H2))) =
  inr
    ( inr
      ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ x y)) ∙
        ( ( commutative-add-ℕ (dist-ℕ x z) (dist-ℕ y x)) ∙
          ( triangle-equality-dist-ℕ y x z H1 H2)))) 
is-total-dist-ℕ x y z | inr (inr (inl (pair H1 H2))) =
  inr
    ( inr
      ( ( ap (add-ℕ' (dist-ℕ x y)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ z x y H1 H2) ∙
          ( symmetric-dist-ℕ z y))))
is-total-dist-ℕ x y z | inr (inr (inr (pair H1 H2))) =
  inl
    ( ( ap-add-ℕ (symmetric-dist-ℕ x y) (symmetric-dist-ℕ y z)) ∙
      ( ( commutative-add-ℕ (dist-ℕ y x) (dist-ℕ z y)) ∙
        ( ( triangle-equality-dist-ℕ z y x H1 H2) ∙
          ( symmetric-dist-ℕ z x))))

--------------------------------------------------------------------------------

{- We define the congruence relation on ℕ and show that it is an equivalence
   relation on ℕ. -}

cong-ℕ :
  ℕ → ℕ → ℕ → UU lzero
cong-ℕ k x y = div-ℕ k (dist-ℕ x y)

eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 → cong-ℕ k x1 x4
eq-cong-eq-ℕ k refl H refl = H

reflexive-cong-ℕ :
  (k x : ℕ) → cong-ℕ k x x
reflexive-cong-ℕ k x =
  pair zero-ℕ ((left-zero-law-mul-ℕ (succ-ℕ k)) ∙ (dist-eq-ℕ x x refl))

cong-identification-ℕ :
  (k : ℕ) {x y : ℕ} → Id x y → cong-ℕ k x y
cong-identification-ℕ k {x} refl = reflexive-cong-ℕ k x

symmetric-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k y x
symmetric-cong-ℕ k x y (pair d p) =
  pair d (p ∙ (symmetric-dist-ℕ x y))

transitive-cong-ℕ :
  (k x y z : ℕ) →
  cong-ℕ k x y → cong-ℕ k y z → cong-ℕ k x z
transitive-cong-ℕ k x y z d e with is-total-dist-ℕ x y z
transitive-cong-ℕ k x y z d e | inl α =
  tr (div-ℕ k) α (div-add-ℕ k (dist-ℕ x y) (dist-ℕ y z) d e)
transitive-cong-ℕ k x y z d e | inr (inl α) =
  div-right-summand-ℕ k (dist-ℕ y z) (dist-ℕ x z) e (tr (div-ℕ k) (inv α) d)
transitive-cong-ℕ k x y z d e | inr (inr α) =
  div-left-summand-ℕ k (dist-ℕ x z) (dist-ℕ x y) d (tr (div-ℕ k) (inv α) e)

concatenate-cong-eq-cong-ℕ :
  {k x1 x2 x3 x4 : ℕ} →
  cong-ℕ k x1 x2 → Id x2 x3 → cong-ℕ k x3 x4 → cong-ℕ k x1 x4
concatenate-cong-eq-cong-ℕ {k} {x} {y} {.y} {z} H refl K =
  transitive-cong-ℕ k x y z H K
  
eq-cong-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 x5 x6 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 →
  cong-ℕ k x4 x5 → Id x5 x6 → cong-ℕ k x1 x6
eq-cong-eq-cong-eq-ℕ k {x} {.x} {y} {.y} {z} {.z} refl H refl K refl =
  transitive-cong-ℕ k x y z H K

--------------------------------------------------------------------------------

-- We show that cong-ℕ zero-ℕ is the discrete equivalence relation --

is-discrete-cong-zero-ℕ :
  (x y : ℕ) → cong-ℕ zero-ℕ x y → Id x y
is-discrete-cong-zero-ℕ x y (pair k p) =
  eq-dist-ℕ x y ((inv (right-zero-law-mul-ℕ k)) ∙ p)

-- We show that cong-ℕ one-ℕ is the indiscrete equivalence relation --

div-one-ℕ :
  (x : ℕ) → div-ℕ one-ℕ x
div-one-ℕ x = pair x (right-unit-law-mul-ℕ x)

is-indiscrete-cong-one-ℕ :
  (x y : ℕ) → cong-ℕ one-ℕ x y
is-indiscrete-cong-one-ℕ x y = div-one-ℕ (dist-ℕ x y)

-- We show that zero-ℕ is congruent to n modulo n.

cong-zero-ℕ :
  (k : ℕ) → cong-ℕ k k zero-ℕ
cong-zero-ℕ k =
  pair one-ℕ ((left-unit-law-mul-ℕ k) ∙ (inv (right-zero-law-dist-ℕ k)))

-- We show that congruence is translation invariant --

translation-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (add-ℕ z x) (add-ℕ z y)
translation-invariant-cong-ℕ k x y z (pair d p) =
  pair d (p ∙ inv (translation-invariant-dist-ℕ z x y))

translation-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (add-ℕ x z) (add-ℕ y z)
translation-invariant-cong-ℕ' k x y z H =
  eq-cong-eq-ℕ k
    ( commutative-add-ℕ x z)
    ( translation-invariant-cong-ℕ k x y z H)
    ( commutative-add-ℕ z y)

step-invariant-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k (succ-ℕ x) (succ-ℕ y)
step-invariant-cong-ℕ k x y = translation-invariant-cong-ℕ' k x y one-ℕ

--------------------------------------------------------------------------------

-- We show that mod-succ-ℕ sends congruent elements to equal elements --

zero-class-mod-succ-ℕ :
  (k x : ℕ) (d : div-ℕ (succ-ℕ k) x) → Id (mod-succ-ℕ k x) zero-Fin
zero-class-mod-succ-ℕ k .zero-ℕ (pair zero-ℕ refl) = refl
zero-class-mod-succ-ℕ k x (pair (succ-ℕ d) p) =
  ( inv (ap (mod-succ-ℕ k) p)) ∙
  ( ( ap (mod-succ-ℕ k) (commutative-add-ℕ (mul-ℕ d (succ-ℕ k)) (succ-ℕ k))) ∙
    ( ( inv (is-periodic-mod-succ-ℕ k (mul-ℕ d (succ-ℕ k)))) ∙
      ( zero-class-mod-succ-ℕ k (mul-ℕ d (succ-ℕ k)) (pair d refl))))

eq-cong-ℕ :
  (k x y : ℕ) → cong-ℕ (succ-ℕ k) x y → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y)
eq-cong-ℕ k zero-ℕ zero-ℕ H = refl
eq-cong-ℕ k zero-ℕ (succ-ℕ y) H =
  inv (zero-class-mod-succ-ℕ k (succ-ℕ y) H)
eq-cong-ℕ k (succ-ℕ x) zero-ℕ H =
  zero-class-mod-succ-ℕ k (succ-ℕ x) H
eq-cong-ℕ zero-ℕ (succ-ℕ x) (succ-ℕ y) H = refl
eq-cong-ℕ (succ-ℕ k) (succ-ℕ x) (succ-ℕ y) H =
  ap succ-Fin (eq-cong-ℕ (succ-ℕ k) x y H)

--------------------------------------------------------------------------------

{- We define the inclusion of Fin k into ℕ. -}

nat-Fin : {k : ℕ} → Fin k → ℕ
nat-Fin {succ-ℕ k} (inl x) = nat-Fin x
nat-Fin {succ-ℕ k} (inr x) = k

zero-law-nat-Fin :
  {k : ℕ} → Id (nat-Fin (zero-Fin {k})) zero-ℕ
zero-law-nat-Fin {zero-ℕ} = refl 
zero-law-nat-Fin {succ-ℕ k} = zero-law-nat-Fin {k}

{- We show that nat-Fin x ≤ k. -}

upper-bound-nat-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → leq-ℕ (nat-Fin x) k
upper-bound-nat-Fin {zero-ℕ} (inr star) = star
upper-bound-nat-Fin {succ-ℕ k} (inl x) =
  preserves-leq-succ-ℕ (nat-Fin x) k (upper-bound-nat-Fin x)
upper-bound-nat-Fin {succ-ℕ k} (inr star) = reflexive-leq-ℕ (succ-ℕ k)

{- Now we show that Fin (succ-ℕ k) is a retract of ℕ -}

issec-nat-Fin : (k : ℕ) (x : Fin (succ-ℕ k)) → Id (mod-succ-ℕ k (nat-Fin x)) x
issec-nat-Fin zero-ℕ (inr star) = refl
issec-nat-Fin (succ-ℕ k) (inl x) =
  ( successor-law-mod-succ-ℕ k (nat-Fin x) (upper-bound-nat-Fin x)) ∙
  ( ap inl (issec-nat-Fin k x))
issec-nat-Fin (succ-ℕ k) (inr star) = neg-one-law-mod-succ-ℕ (succ-ℕ k)

-- We show that nat-Fin is an injective function --

neq-leq-ℕ : {m n : ℕ} → leq-ℕ m n → ¬ (Id m (succ-ℕ n))
neq-leq-ℕ {zero-ℕ} {n} p q = Eq-ℕ-eq q
neq-leq-ℕ {succ-ℕ m} {succ-ℕ n} p q =
  neq-leq-ℕ p (is-injective-succ-ℕ m (succ-ℕ n) q)

is-injective-nat-Fin : {k : ℕ} {x y : Fin (succ-ℕ k)} →
  Id (nat-Fin x) (nat-Fin y) → Id x y
is-injective-nat-Fin {zero-ℕ} {inr star} {inr star} p = refl
is-injective-nat-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-nat-Fin p)
is-injective-nat-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (neq-leq-ℕ (upper-bound-nat-Fin x) p)
is-injective-nat-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (neq-leq-ℕ (upper-bound-nat-Fin y) (inv p))
is-injective-nat-Fin {succ-ℕ k} {inr star} {inr star} p = refl

-- We show that nat-Fin commutes with the successor for x ≠ neg-one-Fin --

nat-succ-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) (p : ¬ (Eq-Fin (succ-ℕ k) x neg-one-Fin)) →
  Id (nat-Fin (succ-Fin x)) (succ-ℕ (nat-Fin x))
nat-succ-Fin {zero-ℕ} (inr star) p = ex-falso (p star)
nat-succ-Fin {succ-ℕ k} (inl (inl x)) p =
  nat-succ-Fin (inl x) id
nat-succ-Fin {succ-ℕ k} (inl (inr star)) p = refl
nat-succ-Fin {succ-ℕ k} (inr star) p = ex-falso (p star)

-- We show that (nat-Fin (mod-succ-ℕ n x)) is congruent to x modulo n+1. --

cong-nat-mod-succ-ℕ :
  (k x : ℕ) → cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
cong-nat-mod-succ-ℕ k x with
  is-decidable-eq-Fin (succ-ℕ k) (mod-succ-ℕ k x) zero-Fin
cong-nat-mod-succ-ℕ zero-ℕ zero-ℕ | d = pair zero-ℕ refl
cong-nat-mod-succ-ℕ zero-ℕ (succ-ℕ x) | d = div-one-ℕ (dist-ℕ zero-ℕ (succ-ℕ x))
cong-nat-mod-succ-ℕ (succ-ℕ k) zero-ℕ | d =
  eq-cong-eq-ℕ (succ-ℕ (succ-ℕ k))
    ( zero-law-nat-Fin {succ-ℕ k})
    ( reflexive-cong-ℕ (succ-ℕ (succ-ℕ k)) zero-ℕ)
    ( refl)
cong-nat-mod-succ-ℕ (succ-ℕ k) (succ-ℕ x) | inl p =
  eq-cong-eq-cong-eq-ℕ
    ( succ-ℕ (succ-ℕ k))
    ( ap nat-Fin {x = mod-succ-ℕ (succ-ℕ k) (succ-ℕ x)} p ∙
      zero-law-nat-Fin {succ-ℕ k})
    ( symmetric-cong-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( zero-ℕ)
      ( succ-ℕ (succ-ℕ k))
      ( cong-zero-ℕ (succ-ℕ (succ-ℕ k))))
    ( ap
      ( succ-ℕ ∘ nat-Fin)
      { x = neg-one-Fin}
      { y = mod-succ-ℕ (succ-ℕ k) x}
      ( is-injective-succ-Fin (inv p)))
    ( step-invariant-cong-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( nat-Fin (mod-succ-ℕ (succ-ℕ k) x))
      ( x)
      ( cong-nat-mod-succ-ℕ (succ-ℕ k) x))
    ( refl)
cong-nat-mod-succ-ℕ (succ-ℕ k) (succ-ℕ x) | inr f =
  eq-cong-eq-ℕ
    ( succ-ℕ (succ-ℕ k))
    ( nat-succ-Fin
      ( mod-succ-ℕ (succ-ℕ k) x)
      ( (f ∘ ap succ-Fin) ∘
        ( eq-Eq-Fin
          { succ-ℕ (succ-ℕ k)}
          { x = mod-succ-ℕ (succ-ℕ k) x}
          { y = neg-one-Fin})))
    ( step-invariant-cong-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( nat-Fin (mod-succ-ℕ (succ-ℕ k) x))
      ( x)
      ( cong-nat-mod-succ-ℕ (succ-ℕ k) x))
    ( refl)

--------------------------------------------------------------------------------

{- We show that if mod-succ-ℕ n = is mod-succ-ℕ n x, then x and y must be
   congruent modulo succ-ℕ n. -}

cong-eq-ℕ :
  (k x y : ℕ) → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y) → cong-ℕ (succ-ℕ k) x y
cong-eq-ℕ k x y p =
  concatenate-cong-eq-cong-ℕ {succ-ℕ k} {x}
    ( symmetric-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
      ( cong-nat-mod-succ-ℕ k x))
    ( ap nat-Fin p)
    ( cong-nat-mod-succ-ℕ k y)

--------------------------------------------------------------------------------

{- We show that if x and y are congruent modulo (succ-ℕ n), then we will have
   an identification mod-succ-ℕ n x = mod-succ-ℕ n y. -}

upper-bound-dist-ℕ :
  (b x y : ℕ) → leq-ℕ x b → leq-ℕ y b → leq-ℕ (dist-ℕ x y) b
upper-bound-dist-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
upper-bound-dist-ℕ (succ-ℕ b) zero-ℕ zero-ℕ H K = star
upper-bound-dist-ℕ (succ-ℕ b) zero-ℕ (succ-ℕ y) H K = K
upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) zero-ℕ H K = H
upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) (succ-ℕ y) H K =
  preserves-leq-succ-ℕ (dist-ℕ x y) b (upper-bound-dist-ℕ b x y H K)

contradiction-leq-ℕ :
  (x y : ℕ) → leq-ℕ x y → leq-ℕ (succ-ℕ y) x → empty
contradiction-leq-ℕ (succ-ℕ x) (succ-ℕ y) H K = contradiction-leq-ℕ x y H K

eq-zero-div-ℕ :
  (d x : ℕ) → leq-ℕ x d → div-ℕ (succ-ℕ d) x → Id x zero-ℕ
eq-zero-div-ℕ d zero-ℕ H D = refl
eq-zero-div-ℕ d (succ-ℕ x) H (pair (succ-ℕ k) p) =
  ex-falso
    ( contradiction-leq-ℕ d x
      ( concatenate-eq-leq-eq-ℕ
        { x1 = succ-ℕ d}
        { x2 = succ-ℕ d}
        { x3 = succ-ℕ (add-ℕ (mul-ℕ k (succ-ℕ d)) d)}
        { x4 = succ-ℕ x}
        ( refl)
        ( leq-add-ℕ' d (mul-ℕ k (succ-ℕ d)))
        ( p)) H)

eq-cong-nat-Fin :
  (k : ℕ) (x y : Fin k) → cong-ℕ k (nat-Fin x) (nat-Fin y) → Id x y
eq-cong-nat-Fin (succ-ℕ k) x y H =
  is-injective-nat-Fin
    ( eq-dist-ℕ
      ( nat-Fin x)
      ( nat-Fin y)
      ( inv
        ( eq-zero-div-ℕ k
          ( dist-ℕ (nat-Fin x) (nat-Fin y))
          ( upper-bound-dist-ℕ k
            ( nat-Fin x)
            ( nat-Fin y)
            ( upper-bound-nat-Fin x)
            ( upper-bound-nat-Fin y))
          ( H))))

eq-mod-succ-ℕ :
  (k x y : ℕ) → cong-ℕ (succ-ℕ k) x y → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y)
eq-mod-succ-ℕ k x y H =
  eq-cong-nat-Fin
    ( succ-ℕ k)
    ( mod-succ-ℕ k x)
    ( mod-succ-ℕ k y)
    ( transitive-cong-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k x))
      ( x)
      ( nat-Fin (mod-succ-ℕ k y))
      ( cong-nat-mod-succ-ℕ k x)
      ( transitive-cong-ℕ (succ-ℕ k) x y (nat-Fin (mod-succ-ℕ k y)) H
        ( symmetric-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k y)) y
          ( cong-nat-mod-succ-ℕ k y))))

{- This completes the proof that 

   (mod-succ-ℕ n x = mod-succ-ℕ n y) ↔ (cong-ℕ (succ-ℕ n) x y). -}

--------------------------------------------------------------------------------

{- Section 7.7 Modular arithmetic -}

-- We show that congruence is invariant under scalar multiplication --

scalar-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y →  cong-ℕ k (mul-ℕ z x) (mul-ℕ z y)
scalar-invariant-cong-ℕ k x y z (pair d p) =
  pair
    ( mul-ℕ z d)
    ( ( associative-mul-ℕ z d k) ∙
      ( ( ap (mul-ℕ z) p) ∙
        ( inv (linear-dist-ℕ x y z))))

scalar-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (mul-ℕ x z) (mul-ℕ y z)
scalar-invariant-cong-ℕ' k x y z H =
  eq-cong-eq-ℕ k
    ( commutative-mul-ℕ x z)
    ( scalar-invariant-cong-ℕ k x y z H)
    ( commutative-mul-ℕ z y)

-- We show that addition respects the congruence relation --

congruence-add-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k x x' → cong-ℕ k y y' → cong-ℕ k (add-ℕ x y) (add-ℕ x' y')
congruence-add-ℕ k {x} {y} {x'} {y'} H K =
  transitive-cong-ℕ k (add-ℕ x y) (add-ℕ x y') (add-ℕ x' y')
    ( translation-invariant-cong-ℕ k y y' x K)
    ( translation-invariant-cong-ℕ' k x x' y' H)

-- We show that multiplication respects the congruence relation --

congruence-mul-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ  k x x' → cong-ℕ k y y' → cong-ℕ k (mul-ℕ x y) (mul-ℕ x' y')
congruence-mul-ℕ k {x} {y} {x'} {y'} H K =
  transitive-cong-ℕ k (mul-ℕ x y) (mul-ℕ x y') (mul-ℕ x' y')
    ( scalar-invariant-cong-ℕ k y y' x K)
    ( scalar-invariant-cong-ℕ' k x x' y' H)

--------------------------------------------------------------------------------

-- Now we start defining the finite cyclic groups ℤ/n.

-- Addition on finite sets --

add-Fin : {k : ℕ} → Fin k → Fin k → Fin k
add-Fin {succ-ℕ k} x y = mod-succ-ℕ k (add-ℕ (nat-Fin x) (nat-Fin y))

add-Fin' : {k : ℕ} → Fin k → Fin k → Fin k
add-Fin' x y = add-Fin y x

ap-add-Fin :
  {k : ℕ} {x y x' y' : Fin k} →
  Id x x' → Id y y' → Id (add-Fin x y) (add-Fin x' y')
ap-add-Fin refl refl = refl

cong-add-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin (add-Fin x y)) (add-ℕ (nat-Fin x) (nat-Fin y))
cong-add-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (add-ℕ (nat-Fin x) (nat-Fin y))

--------------------------------------------------------------------------------

-- We show that addition is associative --

associative-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (add-Fin (add-Fin x y) z) (add-Fin x (add-Fin y z))
associative-add-Fin {succ-ℕ k} x y z =
  eq-cong-ℕ k
    ( add-ℕ (nat-Fin (add-Fin x y)) (nat-Fin z))
    ( add-ℕ (nat-Fin x) (nat-Fin (add-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = add-ℕ (nat-Fin (add-Fin x y)) (nat-Fin z)}
      { x2 = add-ℕ (add-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = add-ℕ (nat-Fin x) (add-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = add-ℕ (nat-Fin x) (nat-Fin (add-Fin y z))}
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (add-Fin x y)}
        { y = nat-Fin z}
        { x' = add-ℕ (nat-Fin x) (nat-Fin y)}
        { y' = nat-Fin z}
        ( cong-add-Fin x y)
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin z)))
      ( associative-add-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin x}
        { y = add-ℕ (nat-Fin y) (nat-Fin z)}
        { x' = nat-Fin x}
        { y' = nat-Fin (add-Fin y z)}
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin x))
        ( symmetric-cong-ℕ
          ( succ-ℕ k)
          ( nat-Fin (add-Fin y z))
          ( add-ℕ (nat-Fin y) (nat-Fin z))
          ( cong-add-Fin y z))))

--------------------------------------------------------------------------------

-- addition is commutative --

commutative-add-Fin : {k : ℕ} (x y : Fin k) → Id (add-Fin x y) (add-Fin y x)
commutative-add-Fin {succ-ℕ k} x y =
  ap (mod-succ-ℕ k) (commutative-add-ℕ (nat-Fin x) (nat-Fin y))

--------------------------------------------------------------------------------

-- We prove the unit laws for add-Fin --

nat-zero-Fin :
  {k : ℕ} → cong-ℕ (succ-ℕ k) (nat-Fin (zero-Fin {k})) zero-ℕ
nat-zero-Fin {k} = cong-nat-mod-succ-ℕ k zero-ℕ

right-unit-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin x zero-Fin) x
right-unit-law-add-Fin {k} x =
  ( eq-cong-ℕ k
    ( add-ℕ (nat-Fin x) (nat-Fin {succ-ℕ k} zero-Fin))
    ( add-ℕ (nat-Fin x) zero-ℕ)
    ( congruence-add-ℕ
      ( succ-ℕ k)
      { x = nat-Fin {succ-ℕ k} x}
      { y = nat-Fin {succ-ℕ k} zero-Fin}
      { x' = nat-Fin x}
      { y' = zero-ℕ}
      ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin {succ-ℕ k} x))
      ( nat-zero-Fin {k}))) ∙
  ( issec-nat-Fin k x)

left-unit-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin zero-Fin x) x
left-unit-law-add-Fin {k} x =
  ( commutative-add-Fin zero-Fin x) ∙
  ( right-unit-law-add-Fin x)

--------------------------------------------------------------------------------

-- We define the negative of x : Fin (succ-ℕ k) --

neg-Fin :
  {k : ℕ} → Fin k → Fin k
neg-Fin {succ-ℕ k} x =
  mod-succ-ℕ k (dist-ℕ (nat-Fin x) (succ-ℕ k))

cong-neg-Fin :
  {k : ℕ} (x : Fin k) →
  cong-ℕ k (nat-Fin (neg-Fin x)) (dist-ℕ (nat-Fin x) k)
cong-neg-Fin {succ-ℕ k} x = 
  cong-nat-mod-succ-ℕ k (dist-ℕ (nat-Fin x) (succ-ℕ k))

left-inverse-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin (neg-Fin x) x) zero-Fin
left-inverse-law-add-Fin {k} x =
  eq-cong-ℕ k (add-ℕ (nat-Fin (neg-Fin x)) (nat-Fin x)) zero-ℕ
    ( concatenate-cong-eq-cong-ℕ
      { succ-ℕ k}
      { x1 = add-ℕ (nat-Fin (neg-Fin x)) (nat-Fin x)}
      { x2 = add-ℕ (dist-ℕ (nat-Fin x) (succ-ℕ k)) (nat-Fin x)}
      { x3 = succ-ℕ k}
      { x4 = zero-ℕ}
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (neg-Fin x)}
        { y = nat-Fin x}
        ( cong-neg-Fin x)
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin x)))
      ( ( ap ( add-ℕ (dist-ℕ (nat-Fin x) (succ-ℕ k)))
             ( inv (left-zero-law-dist-ℕ (nat-Fin x)))) ∙
        ( ( commutative-add-ℕ
            ( dist-ℕ (nat-Fin x) (succ-ℕ k))
            ( dist-ℕ zero-ℕ (nat-Fin x))) ∙
          ( triangle-equality-dist-ℕ zero-ℕ (nat-Fin x) (succ-ℕ k) star
            ( preserves-leq-succ-ℕ (nat-Fin x) k (upper-bound-nat-Fin x)))))
      ( symmetric-cong-ℕ
          ( succ-ℕ k)
          ( zero-ℕ)
          ( succ-ℕ k)
          ( cong-zero-ℕ (succ-ℕ k))))

right-inverse-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin x (neg-Fin x)) zero-Fin
right-inverse-law-add-Fin x =
  ( commutative-add-Fin x (neg-Fin x)) ∙ (left-inverse-law-add-Fin x)

--------------------------------------------------------------------------------

{- Exercises -}

-- We show that the predecessor of zero is negative one --

pred-zero-Fin :
  {k : ℕ} → Id (pred-Fin {succ-ℕ k} zero-Fin) neg-one-Fin
pred-zero-Fin {k} with is-decidable-Eq-Fin (succ-ℕ k) zero-Fin zero-Fin
pred-zero-Fin {zero-ℕ} | d = refl
pred-zero-Fin {succ-ℕ k} | inl e = refl
pred-zero-Fin {succ-ℕ k} | inr f =
  ex-falso (f (refl-Eq-Fin {succ-ℕ k} zero-Fin))

-- We show that the predecessor function is a section of the successor function
  
cases-succ-pred-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k))
  (d : is-decidable (Eq-Fin (succ-ℕ k) x zero-Fin)) →
  Id (succ-Fin (cases-pred-Fin x d)) x
cases-succ-pred-Fin {zero-ℕ} (inr star) d =
  refl
cases-succ-pred-Fin {succ-ℕ k} (inl x) (inl e) =
  succ-neg-one-Fin ∙ inv (eq-Eq-Fin e)
cases-succ-pred-Fin {succ-ℕ zero-ℕ} (inl (inr x)) (inr f) =
  ex-falso (f star)
cases-succ-pred-Fin {succ-ℕ (succ-ℕ k)} (inl (inl x)) (inr f) =
  ap inl (cases-succ-pred-Fin (inl x) (inr f))
cases-succ-pred-Fin {succ-ℕ (succ-ℕ k)} (inl (inr star)) (inr f) =
  refl
cases-succ-pred-Fin {succ-ℕ k} (inr star) (inr f) =
  refl

succ-pred-Fin :
  {k : ℕ} (x : Fin k) → Id (succ-Fin (pred-Fin x)) x
succ-pred-Fin {succ-ℕ k} x =
  cases-succ-pred-Fin x (is-decidable-Eq-Fin (succ-ℕ k) x zero-Fin)

-- We compute the predecessor of an element of the form inl that is not zero --

pred-inl-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) (f : ¬ (Eq-Fin (succ-ℕ k) x zero-Fin)) →
  Id (pred-Fin (inl x)) (inl (pred-Fin x))
pred-inl-Fin {k} x f with is-decidable-Eq-Fin (succ-ℕ k) x zero-Fin
... | inl e = ex-falso (f e)
... | inr f' = refl

-- We show that the predecessor of the successor of x is x.

nEq-zero-succ-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) →
  ¬ (Eq-Fin (succ-ℕ (succ-ℕ k)) (succ-Fin (inl x)) zero-Fin)
nEq-zero-succ-Fin {succ-ℕ k} (inl (inl x)) e = nEq-zero-succ-Fin (inl x) e

pred-succ-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (pred-Fin (succ-Fin x)) x
pred-succ-Fin {zero-ℕ} (inr star) = refl
pred-succ-Fin {succ-ℕ zero-ℕ} (inl (inr star)) = refl
pred-succ-Fin {succ-ℕ zero-ℕ} (inr star) = refl
pred-succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inl (inl x))) =
  ( pred-inl-Fin (inl (succ-Fin (inl x))) (nEq-zero-succ-Fin (inl x))) ∙
  ( ( ap inl (pred-inl-Fin (succ-Fin (inl x)) (nEq-zero-succ-Fin (inl x)))) ∙
    ( ap (inl ∘ inl) (pred-succ-Fin (inl x))))
pred-succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inl (inr star))) = refl
pred-succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inr star)) = refl
pred-succ-Fin {succ-ℕ (succ-ℕ k)} (inr star) = pred-zero-Fin

--------------------------------------------------------------------------------

{- We define the multiplication on the types Fin k. -}

mul-Fin :
  {k : ℕ} → Fin k → Fin k → Fin k
mul-Fin {succ-ℕ k} x y = mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

ap-mul-Fin :
  {k : ℕ} {x y x' y' : Fin k} →
  Id x x' → Id y y' → Id (mul-Fin x y) (mul-Fin x' y')
ap-mul-Fin refl refl = refl

cong-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin (mul-Fin x y)) (mul-ℕ (nat-Fin x) (nat-Fin y))
cong-mul-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

associative-mul-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin (mul-Fin x y) z) (mul-Fin x (mul-Fin y z))
associative-mul-Fin {succ-ℕ k} x y z =
  eq-cong-ℕ k
    ( mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z))
    ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z)}
      { x2 = mul-ℕ (mul-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (mul-Fin x y)}
        { y = nat-Fin z}
        ( cong-mul-Fin x y)
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin z)))
      ( associative-mul-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( symmetric-cong-ℕ
        ( succ-ℕ k)
        ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
        ( mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z)))
        ( congruence-mul-ℕ
          ( succ-ℕ k)
          { x = nat-Fin x}
          { y = nat-Fin (mul-Fin y z)}
          ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin x))
          ( cong-mul-Fin y z))))

commutative-mul-Fin :
  {k : ℕ} (x y : Fin k) → Id (mul-Fin x y) (mul-Fin y x)
commutative-mul-Fin {succ-ℕ k} x y =
  eq-cong-ℕ k
    ( mul-ℕ (nat-Fin x) (nat-Fin y))
    ( mul-ℕ (nat-Fin y) (nat-Fin x))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( commutative-mul-ℕ (nat-Fin x) (nat-Fin y)))

one-Fin : {k : ℕ} → Fin (succ-ℕ k)
one-Fin {k} = mod-succ-ℕ k one-ℕ

nat-one-Fin : {k : ℕ} → Id (nat-Fin (one-Fin {succ-ℕ k})) one-ℕ
nat-one-Fin {zero-ℕ} = refl
nat-one-Fin {succ-ℕ k} = nat-one-Fin {k}

left-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin one-Fin x) x
left-unit-law-mul-Fin {zero-ℕ} (inr star) = refl
left-unit-law-mul-Fin {succ-ℕ k} x =
  ( eq-cong-ℕ (succ-ℕ k)
    ( mul-ℕ (nat-Fin (one-Fin {succ-ℕ k})) (nat-Fin x))
    ( nat-Fin x)
    ( cong-identification-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( ( ap ( mul-ℕ' (nat-Fin x))
             ( nat-one-Fin {k})) ∙
        ( left-unit-law-mul-ℕ (nat-Fin x))))) ∙
  ( issec-nat-Fin (succ-ℕ k) x)

right-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin x one-Fin) x
right-unit-law-mul-Fin x =
  ( commutative-mul-Fin x one-Fin) ∙
  ( left-unit-law-mul-Fin x)

--------------------------------------------------------------------------------

left-distributive-mul-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin x (add-Fin y z)) (add-Fin (mul-Fin x y) (mul-Fin x z))
left-distributive-mul-add-Fin {succ-ℕ k} x y z =
  eq-cong-ℕ k
    ( mul-ℕ (nat-Fin x) (nat-Fin (add-Fin y z)))
    ( add-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin (mul-Fin x z)))
    ( concatenate-cong-eq-cong-ℕ
      { k = succ-ℕ k}
      { x1 = mul-ℕ ( nat-Fin x) (nat-Fin (add-Fin y z))}
      { x2 = mul-ℕ ( nat-Fin x) (add-ℕ (nat-Fin y) (nat-Fin z))}
      { x3 = add-ℕ ( mul-ℕ (nat-Fin x) (nat-Fin y))
                   ( mul-ℕ (nat-Fin x) (nat-Fin z))}
      { x4 = add-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin (mul-Fin x z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin x}
        { y = nat-Fin (add-Fin y z)}
        { x' = nat-Fin x}
        { y' = add-ℕ (nat-Fin y) (nat-Fin z)}
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin x))
        ( cong-add-Fin y z))
      ( left-distributive-mul-add-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( symmetric-cong-ℕ (succ-ℕ k)
        ( add-ℕ ( nat-Fin (mul-Fin x y))
                ( nat-Fin (mul-Fin x z)))
        ( add-ℕ ( mul-ℕ (nat-Fin x) (nat-Fin y))
                ( mul-ℕ (nat-Fin x) (nat-Fin z)))
        ( congruence-add-ℕ
          ( succ-ℕ k)
          { x = nat-Fin (mul-Fin x y)}
          { y = nat-Fin (mul-Fin x z)}
          { x' = mul-ℕ (nat-Fin x) (nat-Fin y)}
          { y' = mul-ℕ (nat-Fin x) (nat-Fin z)}
          ( cong-mul-Fin x y)
          ( cong-mul-Fin x z))))

right-distributive-mul-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin (add-Fin x y) z) (add-Fin (mul-Fin x z) (mul-Fin y z))
right-distributive-mul-add-Fin {k} x y z =
  ( commutative-mul-Fin (add-Fin x y) z) ∙
  ( ( left-distributive-mul-add-Fin z x y) ∙
    ( ap-add-Fin (commutative-mul-Fin z x) (commutative-mul-Fin z y)))

--------------------------------------------------------------------------------

{-
-- We introduce the absolute value of an integer. --

abs-ℤ : ℤ → ℕ
abs-ℤ (inl x) = succ-ℕ x
abs-ℤ (inr (inl star)) = zero-ℕ
abs-ℤ (inr (inr x)) = succ-ℕ x

int-abs-ℤ : ℤ → ℤ
int-abs-ℤ = int-ℕ ∘ abs-ℤ

eq-abs-ℤ : (x : ℤ) → Id zero-ℕ (abs-ℤ x) → Id zero-ℤ x
eq-abs-ℤ (inl x) p = ex-falso (Peano-8 x p)
eq-abs-ℤ (inr (inl star)) p = refl
eq-abs-ℤ (inr (inr x)) p = ex-falso (Peano-8 x p)

abs-eq-ℤ : (x : ℤ) → Id zero-ℤ x → Id zero-ℕ (abs-ℤ x)
abs-eq-ℤ .zero-ℤ refl = refl

negatives-add-ℤ :
  (x y : ℕ) → Id (add-ℤ (in-neg x) (in-neg y)) (in-neg (succ-ℕ (add-ℕ x y)))
negatives-add-ℤ zero-ℕ y = ap (inl ∘ succ-ℕ) (inv (left-unit-law-add-ℕ y))
negatives-add-ℤ (succ-ℕ x) y =
  ( ap pred-ℤ (negatives-add-ℤ x y)) ∙
  ( ap (inl ∘ succ-ℕ) (inv (left-successor-law-add-ℕ x y)))

subadditive-abs-ℤ :
  (x y : ℤ) → leq-ℕ (abs-ℤ (add-ℤ x y)) (add-ℕ (abs-ℤ x) (abs-ℤ y))
subadditive-abs-ℤ (inl x) (inl y) =
  leq-eq-ℕ
    ( abs-ℤ (add-ℤ (inl x) (inl y)))
    ( add-ℕ (succ-ℕ x) (succ-ℕ y))
    ( ( ap abs-ℤ (negatives-add-ℤ x y)) ∙
      ( ap succ-ℕ (inv (left-successor-law-add-ℕ x y))))
subadditive-abs-ℤ (inl x) (inr (inl star)) =
  leq-eq-ℕ
    ( abs-ℤ (add-ℤ (inl x) zero-ℤ))
    ( add-ℕ (succ-ℕ x) zero-ℕ)
    ( ap abs-ℤ (right-unit-law-add-ℤ (inl x)))
subadditive-abs-ℤ (inl zero-ℕ) (inr (inr zero-ℕ)) = star
subadditive-abs-ℤ (inl zero-ℕ) (inr (inr (succ-ℕ y))) =
  concatenate-leq-eq-ℕ
    ( succ-ℕ y)
    ( preserves-leq-succ-ℕ (succ-ℕ y) (succ-ℕ (succ-ℕ y)) (succ-leq-ℕ y))
    ( inv
      ( ( left-successor-law-add-ℕ zero-ℕ (succ-ℕ (succ-ℕ y))) ∙
        ( ap succ-ℕ (left-unit-law-add-ℕ (succ-ℕ (succ-ℕ y))))))
subadditive-abs-ℤ (inl (succ-ℕ x)) (inr (inr zero-ℕ)) = {!!}
subadditive-abs-ℤ (inl (succ-ℕ x)) (inr (inr (succ-ℕ y))) = {!!}
subadditive-abs-ℤ (inr x) (inl y) = {!!}
subadditive-abs-ℤ (inr x) (inr y) = {!!}

--------------------------------------------------------------------------------

dist-ℤ : ℤ → ℤ → ℕ
dist-ℤ (inl x) (inl y) = dist-ℕ x y
dist-ℤ (inl x) (inr (inl star)) = succ-ℕ x
dist-ℤ (inl x) (inr (inr y)) = succ-ℕ (succ-ℕ (add-ℕ x y))
dist-ℤ (inr (inl star)) (inl y) = succ-ℕ y
dist-ℤ (inr (inr x)) (inl y) = succ-ℕ (succ-ℕ (add-ℕ x y))
dist-ℤ (inr (inl star)) (inr (inl star)) = zero-ℕ
dist-ℤ (inr (inl star)) (inr (inr y)) = succ-ℕ y
dist-ℤ (inr (inr x)) (inr (inl star)) = succ-ℕ x
dist-ℤ (inr (inr x)) (inr (inr y)) = dist-ℕ x y

dist-ℤ' : ℤ → ℤ → ℕ
dist-ℤ' x y = dist-ℤ y x

ap-dist-ℤ :
  {x y x' y' : ℤ} → Id x x' → Id y y' → Id (dist-ℤ x y) (dist-ℤ x' y')
ap-dist-ℤ refl refl = refl

eq-dist-ℤ :
  (x y : ℤ) → Id zero-ℕ (dist-ℤ x y) → Id x y
eq-dist-ℤ (inl x) (inl y) p = ap inl (eq-dist-ℕ x y p)
eq-dist-ℤ (inl x) (inr (inl star)) p = ex-falso (Peano-8 x p)
eq-dist-ℤ (inr (inl star)) (inl y) p = ex-falso (Peano-8 y p)
eq-dist-ℤ (inr (inl star)) (inr (inl star)) p = refl
eq-dist-ℤ (inr (inl star)) (inr (inr y)) p = ex-falso (Peano-8 y p)
eq-dist-ℤ (inr (inr x)) (inr (inl star)) p = ex-falso (Peano-8 x p)
eq-dist-ℤ (inr (inr x)) (inr (inr y)) p = ap (inr ∘ inr) (eq-dist-ℕ x y p)

dist-eq-ℤ' :
  (x : ℤ) → Id zero-ℕ (dist-ℤ x x)
dist-eq-ℤ' (inl x) = dist-eq-ℕ' x
dist-eq-ℤ' (inr (inl star)) = refl
dist-eq-ℤ' (inr (inr x)) = dist-eq-ℕ' x

dist-eq-ℤ :
  (x y : ℤ) → Id x y → Id zero-ℕ (dist-ℤ x y)
dist-eq-ℤ x .x refl = dist-eq-ℤ' x

{- The distance function on ℤ is symmetric. -}

symmetric-dist-ℤ :
  (x y : ℤ) → Id (dist-ℤ x y) (dist-ℤ y x)
symmetric-dist-ℤ (inl x) (inl y) = symmetric-dist-ℕ x y
symmetric-dist-ℤ (inl x) (inr (inl star)) = refl
symmetric-dist-ℤ (inl x) (inr (inr y)) =
  ap (succ-ℕ ∘ succ-ℕ) (commutative-add-ℕ x y)
symmetric-dist-ℤ (inr (inl star)) (inl y) = refl
symmetric-dist-ℤ (inr (inr x)) (inl y) =
  ap (succ-ℕ ∘ succ-ℕ) (commutative-add-ℕ x y)
symmetric-dist-ℤ (inr (inl star)) (inr (inl star)) = refl
symmetric-dist-ℤ (inr (inl star)) (inr (inr y)) = refl
symmetric-dist-ℤ (inr (inr x)) (inr (inl star)) = refl
symmetric-dist-ℤ (inr (inr x)) (inr (inr y)) = symmetric-dist-ℕ x y

-- We compute the distance from zero --

left-zero-law-dist-ℤ :
  (x : ℤ) → Id (dist-ℤ zero-ℤ x) (abs-ℤ x)
left-zero-law-dist-ℤ (inl x) = refl
left-zero-law-dist-ℤ (inr (inl star)) = refl
left-zero-law-dist-ℤ (inr (inr x)) = refl

right-zero-law-dist-ℤ :
  (x : ℤ) → Id (dist-ℤ x zero-ℤ) (abs-ℤ x)
right-zero-law-dist-ℤ (inl x) = refl
right-zero-law-dist-ℤ (inr (inl star)) = refl
right-zero-law-dist-ℤ (inr (inr x)) = refl

-- We prove the triangle inequality --

triangle-inequality-dist-ℤ :
  (x y z : ℤ) → leq-ℕ (dist-ℤ x y) (add-ℕ (dist-ℤ x z) (dist-ℤ z y))
triangle-inequality-dist-ℤ (inl x) (inl y) (inl z) =
  triangle-inequality-dist-ℕ x y z
triangle-inequality-dist-ℤ (inl x) (inl y) (inr (inl star)) =
  triangle-inequality-dist-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ
triangle-inequality-dist-ℤ (inl x) (inl y) (inr (inr z)) = {!!}
triangle-inequality-dist-ℤ (inl x) (inr y) (inl z) = {!!}
triangle-inequality-dist-ℤ (inl x) (inr y) (inr z) = {!!}
triangle-inequality-dist-ℤ (inr x) (inl y) (inl z) = {!!}
triangle-inequality-dist-ℤ (inr x) (inl y) (inr z) = {!!}
triangle-inequality-dist-ℤ (inr x) (inr y) (inl z) = {!!}
triangle-inequality-dist-ℤ (inr x) (inr y) (inr z) = {!!}

{-

triangle-inequality-dist-ℕ :
  (m n k : ℕ) → leq-ℕ (dist-ℕ m n) (add-ℕ (dist-ℕ m k) (dist-ℕ k n))
triangle-inequality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ = star
triangle-inequality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ k) = star
triangle-inequality-dist-ℕ zero-ℕ (succ-ℕ n) zero-ℕ =
  tr ( leq-ℕ (succ-ℕ n))
     ( inv (left-unit-law-add-ℕ (succ-ℕ n)))
     ( reflexive-leq-ℕ (succ-ℕ n))
triangle-inequality-dist-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ k) =
  concatenate-eq-leq-eq-ℕ
    ( inv (ap succ-ℕ (left-zero-law-dist-ℕ n)))
    ( triangle-inequality-dist-ℕ zero-ℕ n k)
    ( ( ap (succ-ℕ ∘ (add-ℕ' (dist-ℕ k n))) (left-zero-law-dist-ℕ k)) ∙
      ( inv (left-successor-law-add-ℕ k (dist-ℕ k n))))
triangle-inequality-dist-ℕ (succ-ℕ m) zero-ℕ zero-ℕ = reflexive-leq-ℕ (succ-ℕ m)
triangle-inequality-dist-ℕ (succ-ℕ m) zero-ℕ (succ-ℕ k) =
  concatenate-eq-leq-eq-ℕ
    ( inv (ap succ-ℕ (right-zero-law-dist-ℕ m)))
    ( triangle-inequality-dist-ℕ m zero-ℕ k)
    ( ap (succ-ℕ ∘ (add-ℕ (dist-ℕ m k))) (right-zero-law-dist-ℕ k))
triangle-inequality-dist-ℕ (succ-ℕ m) (succ-ℕ n) zero-ℕ =
  concatenate-leq-eq-ℕ
    ( dist-ℕ m n)
    ( transitive-leq-ℕ
      ( dist-ℕ m n)
      ( succ-ℕ (add-ℕ (dist-ℕ m zero-ℕ) (dist-ℕ zero-ℕ n)))
      ( succ-ℕ (succ-ℕ (add-ℕ (dist-ℕ m zero-ℕ) (dist-ℕ zero-ℕ n)))) 
      ( transitive-leq-ℕ
        ( dist-ℕ m n)
        ( add-ℕ (dist-ℕ m zero-ℕ) (dist-ℕ zero-ℕ n))
        ( succ-ℕ (add-ℕ (dist-ℕ m zero-ℕ) (dist-ℕ zero-ℕ n)))
        ( triangle-inequality-dist-ℕ m n zero-ℕ)
        ( succ-leq-ℕ (add-ℕ (dist-ℕ m zero-ℕ) (dist-ℕ zero-ℕ n))))
      ( succ-leq-ℕ (succ-ℕ (add-ℕ (dist-ℕ m zero-ℕ) (dist-ℕ zero-ℕ n)))))
    ( ( ap (succ-ℕ ∘ succ-ℕ)
           ( ap-add-ℕ (right-zero-law-dist-ℕ m) (left-zero-law-dist-ℕ n))) ∙
      ( inv (left-successor-law-add-ℕ m (succ-ℕ n))))
triangle-inequality-dist-ℕ (succ-ℕ m) (succ-ℕ n) (succ-ℕ k) =
  triangle-inequality-dist-ℕ m n k

-- We show that dist-ℕ x y is a solution to a simple equation.

leq-dist-ℕ :
  (x y : ℕ) → leq-ℕ x y → Id (add-ℕ x (dist-ℕ x y)) y
leq-dist-ℕ zero-ℕ zero-ℕ H = refl
leq-dist-ℕ zero-ℕ (succ-ℕ y) star = left-unit-law-add-ℕ (succ-ℕ y)
leq-dist-ℕ (succ-ℕ x) (succ-ℕ y) H =
  ( left-successor-law-add-ℕ x (dist-ℕ x y)) ∙
  ( ap succ-ℕ (leq-dist-ℕ x y H))

rewrite-left-add-dist-ℕ :
  (x y z : ℕ) → Id (add-ℕ x y) z → Id x (dist-ℕ y z)
rewrite-left-add-dist-ℕ zero-ℕ zero-ℕ .zero-ℕ refl = refl
rewrite-left-add-dist-ℕ zero-ℕ (succ-ℕ y) .(succ-ℕ (add-ℕ zero-ℕ y)) refl =
  ( dist-eq-ℕ' y) ∙
  ( inv (ap (dist-ℕ (succ-ℕ y)) (left-unit-law-add-ℕ (succ-ℕ y))))
rewrite-left-add-dist-ℕ (succ-ℕ x) zero-ℕ .(succ-ℕ x) refl = refl
rewrite-left-add-dist-ℕ
  (succ-ℕ x) (succ-ℕ y) .(succ-ℕ (add-ℕ (succ-ℕ x) y)) refl =
  rewrite-left-add-dist-ℕ (succ-ℕ x) y (add-ℕ (succ-ℕ x) y) refl

rewrite-left-dist-add-ℕ :
  (x y z : ℕ) → leq-ℕ y z → Id x (dist-ℕ y z) → Id (add-ℕ x y) z
rewrite-left-dist-add-ℕ .(dist-ℕ y z) y z H refl =
  ( commutative-add-ℕ (dist-ℕ y z) y) ∙
  ( leq-dist-ℕ y z H)

rewrite-right-add-dist-ℕ :
  (x y z : ℕ) → Id (add-ℕ x y) z → Id y (dist-ℕ x z)
rewrite-right-add-dist-ℕ x y z p =
  rewrite-left-add-dist-ℕ y x z (commutative-add-ℕ y x ∙ p)

rewrite-right-dist-add-ℕ :
  (x y z : ℕ) → leq-ℕ x z → Id y (dist-ℕ x z) → Id (add-ℕ x y) z
rewrite-right-dist-add-ℕ x .(dist-ℕ x z) z H refl =
  leq-dist-ℕ x z H

-- We show that dist-ℕ is translation invariant

translation-invariant-dist-ℕ :
  (k m n : ℕ) → Id (dist-ℕ (add-ℕ k m) (add-ℕ k n)) (dist-ℕ m n)
translation-invariant-dist-ℕ zero-ℕ m n =
  ap-dist-ℕ (left-unit-law-add-ℕ m) (left-unit-law-add-ℕ n)
translation-invariant-dist-ℕ (succ-ℕ k)  m n =
  ( ap-dist-ℕ (left-successor-law-add-ℕ k m) (left-successor-law-add-ℕ k n)) ∙
  ( translation-invariant-dist-ℕ k m n)

-- We show that dist-ℕ is linear with respect to scalar multiplication

linear-dist-ℕ :
  (m n k : ℕ) → Id (dist-ℕ (mul-ℕ k m) (mul-ℕ k n)) (mul-ℕ k (dist-ℕ m n))
linear-dist-ℕ zero-ℕ zero-ℕ zero-ℕ = refl
linear-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ k) = linear-dist-ℕ zero-ℕ zero-ℕ k
linear-dist-ℕ zero-ℕ (succ-ℕ n) zero-ℕ = refl
linear-dist-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ k) =
  ap (dist-ℕ' (mul-ℕ (succ-ℕ k) (succ-ℕ n))) (right-zero-law-mul-ℕ (succ-ℕ k))
linear-dist-ℕ (succ-ℕ m) zero-ℕ zero-ℕ = refl
linear-dist-ℕ (succ-ℕ m) zero-ℕ (succ-ℕ k) =
  ap (dist-ℕ (mul-ℕ (succ-ℕ k) (succ-ℕ m))) (right-zero-law-mul-ℕ (succ-ℕ k))
linear-dist-ℕ (succ-ℕ m) (succ-ℕ n) zero-ℕ = refl
linear-dist-ℕ (succ-ℕ m) (succ-ℕ n) (succ-ℕ k) =
  ( ap-dist-ℕ
    ( right-successor-law-mul-ℕ (succ-ℕ k) m)
    ( right-successor-law-mul-ℕ (succ-ℕ k) n)) ∙
  ( ( translation-invariant-dist-ℕ
      ( succ-ℕ k)
      ( mul-ℕ (succ-ℕ k) m)
      ( mul-ℕ (succ-ℕ k) n)) ∙
    ( linear-dist-ℕ m n (succ-ℕ k)))
-}
-}
