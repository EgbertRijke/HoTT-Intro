{-# OPTIONS --without-K --exact-split --safe #-}

module mwe where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

--------------------------------------------------------------------------------

data ℕ : Set lzero where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ

add-ℕ : ℕ → ℕ → ℕ
add-ℕ x zero-ℕ = x
add-ℕ x (succ-ℕ y) = succ-ℕ (add-ℕ x y)

{- The following function returns the triangular numbers. In other words,
   test-with n = (1/2) * n * (n+1) -}

test-with-1 : ℕ → ℕ
test-with-1 x with x
test-with-1 zero-ℕ | y = y
test-with-1 (succ-ℕ x) | y = add-ℕ y (test-with-1 x)

{- Now we construct a function with manual with-abstraction, of which the
   definition *looks* the same. But actually we will have
   test-with-2 n = n * (n+1). -}

cases-test-with-2 : ℕ → ℕ → ℕ
cases-test-with-2 zero-ℕ y = y
cases-test-with-2 (succ-ℕ x) y = add-ℕ y (cases-test-with-2 x y)

test-with-2 : ℕ → ℕ
test-with-2 x = cases-test-with-2 x x

{- The following function test-with-3 is again the same as test-with-1. -}

cases-test-with-3 : ℕ → ℕ → ℕ
cases-test-with-3 zero-ℕ y = y
cases-test-with-3 (succ-ℕ x) zero-ℕ = zero-ℕ
cases-test-with-3 (succ-ℕ x) (succ-ℕ y) =
  add-ℕ (succ-ℕ y) (cases-test-with-3 x y)

test-with-3 : ℕ → ℕ
test-with-3 x = cases-test-with-3 x x

-- test-with-1 (succ-ℕ (succ-ℕ (succ-ℕ (succ-ℕ zero-ℕ))))
-- test-with-2 (succ-ℕ (succ-ℕ (succ-ℕ (succ-ℕ zero-ℕ))))
-- test-with-3 (succ-ℕ (succ-ℕ (succ-ℕ (succ-ℕ zero-ℕ))))

-- We do some basic setup, introducing only what we need. All else is removed.

id : {i : Level} {A : Set i} → A → A
id a = a

data empty : Set lzero where

ex-falso : {i : Level} {A : Set i} → empty → A
ex-falso ()

¬ : {i : Level} → Set i → Set i
¬ A = A → empty

data unit : Set lzero where
  star : unit

data coprod {i j : Level} (A : Set i) (B : Set j) : Set (i ⊔ j)  where
  inl : A → coprod A B
  inr : B → coprod A B

is-decidable : {l : Level} (A : Set l) → Set l
is-decidable A = coprod A (¬ A)

data Id {i : Level} {A : Set i} (x : A) : A → Set i where
  refl : Id x x

_∙_ :
  {i : Level} {A : Set i} {x y z : A} → Id x y → Id y z → Id x z
refl ∙ q = q

inv :
  {i : Level} {A : Set i} {x y : A} → Id x y → Id y x
inv refl = refl

ap :
  {i j : Level} {A : Set i} {B : Set j} (f : A → B) {x y : A} (p : Id x y) →
  Id (f x) (f y)
ap f refl = refl

--------------------------------------------------------------------------------

-- We introduce the finite types

Fin : ℕ → Set lzero
Fin zero-ℕ = empty
Fin (succ-ℕ k) = coprod (Fin k) unit

Eq-Fin : (k : ℕ) → Fin k → Fin k → Set lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit

eq-Eq-Fin :
  {k : ℕ} {x y : Fin k} → Eq-Fin k x y → Id x y
eq-Eq-Fin {succ-ℕ k} {inl x} {inl y} e = ap inl (eq-Eq-Fin e)
eq-Eq-Fin {succ-ℕ k} {inr star} {inr star} star = refl

is-decidable-Eq-Fin :
  (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = inl star

--------------------------------------------------------------------------------

-- We now study the successor and predecessor functions on Fin k

zero-Fin : {k : ℕ} → Fin (succ-ℕ k)
zero-Fin {zero-ℕ} = inr star
zero-Fin {succ-ℕ k} = inl zero-Fin

neg-one-Fin : {k : ℕ} → Fin (succ-ℕ k)
neg-one-Fin {k} = inr star

succ-Fin : {k : ℕ} → Fin k → Fin k
succ-Fin {succ-ℕ zero-ℕ} x = x
succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inl x)) = inl (succ-Fin (inl x))
succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inr x)) = neg-one-Fin
succ-Fin {succ-ℕ (succ-ℕ k)} (inr x) = zero-Fin

succ-neg-one-Fin : {k : ℕ} → Id (succ-Fin (neg-one-Fin {k})) zero-Fin
succ-neg-one-Fin {zero-ℕ} = refl
succ-neg-one-Fin {succ-ℕ k} = refl

pred-Fin' : {k : ℕ} → Fin k → Fin k
pred-Fin' {succ-ℕ k} x with (is-decidable-Eq-Fin (succ-ℕ k) x zero-Fin)
pred-Fin' {succ-ℕ zero-ℕ} (inr star) | d = zero-Fin
pred-Fin' {succ-ℕ (succ-ℕ k)} (inl x) | inl e = neg-one-Fin
pred-Fin' {succ-ℕ (succ-ℕ k)} (inl x) | inr f = inl (pred-Fin' {succ-ℕ k} x)
pred-Fin' {succ-ℕ (succ-ℕ k)} (inr x) | inr f = inl neg-one-Fin

succ-pred-Fin' :
  {k : ℕ} (x : Fin k) → Id (succ-Fin (pred-Fin' x)) x
succ-pred-Fin' {succ-ℕ k} x with is-decidable-Eq-Fin (succ-ℕ k) x zero-Fin
succ-pred-Fin' {succ-ℕ zero-ℕ} (inr star) | d = refl
succ-pred-Fin' {succ-ℕ (succ-ℕ k)} (inl x) | inl e =
  succ-neg-one-Fin ∙ inv (eq-Eq-Fin e)
succ-pred-Fin' {succ-ℕ (succ-ℕ zero-ℕ)} (inl (inr star)) | inr f =
  ex-falso (f star)
succ-pred-Fin' {succ-ℕ (succ-ℕ (succ-ℕ k))} (inl (inl x)) | inr f =
  {!!} ∙ ap inl (succ-pred-Fin' {succ-ℕ (succ-ℕ k)} (inl x))
succ-pred-Fin' {succ-ℕ (succ-ℕ (succ-ℕ k))} (inl (inr star)) | inr f = refl
succ-pred-Fin' {succ-ℕ (succ-ℕ k)} (inr star) | inr f = refl

