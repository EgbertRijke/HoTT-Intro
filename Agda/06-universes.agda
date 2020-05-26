{-# OPTIONS --without-K --exact-split --safe #-}

module 06-universes where

import 05-identity-types
open 05-identity-types public

--------------------------------------------------------------------------------

-- Section 6.3 Observational equality on the natural numbers

-- Definition 6.3.1

Eq-ℕ : ℕ → ℕ → UU lzero
Eq-ℕ zero-ℕ zero-ℕ = 𝟙
Eq-ℕ zero-ℕ (succ-ℕ n) = 𝟘
Eq-ℕ (succ-ℕ m) zero-ℕ = 𝟘
Eq-ℕ (succ-ℕ m) (succ-ℕ n) = Eq-ℕ m n

-- Lemma 6.3.2

refl-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
refl-Eq-ℕ zero-ℕ = star
refl-Eq-ℕ (succ-ℕ n) = refl-Eq-ℕ n

-- Proposition 6.3.3

Eq-ℕ-eq : {x y : ℕ} → Id x y → Eq-ℕ x y
Eq-ℕ-eq {x} {.x} refl = refl-Eq-ℕ x

eq-Eq-ℕ : (x y : ℕ) → Eq-ℕ x y → Id x y
eq-Eq-ℕ zero-ℕ zero-ℕ e = refl
eq-Eq-ℕ (succ-ℕ x) (succ-ℕ y) e = ap succ-ℕ (eq-Eq-ℕ x y e)

--------------------------------------------------------------------------------

-- Section 6.4 Peano's seventh and eighth axioms

-- Theorem 6.4.1

is-injective-succ-ℕ : (x y : ℕ) → Id (succ-ℕ x) (succ-ℕ y) → Id x y
is-injective-succ-ℕ x y e = eq-Eq-ℕ x y (Eq-ℕ-eq e)

Peano-7 :
  (x y : ℕ) →
  ((Id x y) → (Id (succ-ℕ x) (succ-ℕ y))) ×
  ((Id (succ-ℕ x) (succ-ℕ y)) → (Id x y))
Peano-7 x y = pair (ap succ-ℕ) (is-injective-succ-ℕ x y)

-- Theorem 6.4.2

Peano-8 :
  (x : ℕ) → ¬ (Id zero-ℕ (succ-ℕ x))
Peano-8 x p = Eq-ℕ-eq p

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 6.1

-- Exercise 6.1 (a)

is-injective-add-ℕ :
  (k m n : ℕ) → Id (add-ℕ m k) (add-ℕ n k) → Id m n
is-injective-add-ℕ zero-ℕ m n = id
is-injective-add-ℕ (succ-ℕ k) m n p =
  is-injective-add-ℕ k m n (is-injective-succ-ℕ (add-ℕ m k) (add-ℕ n k) p)

-- Exercise 6.1 (b)

is-injective-mul-ℕ :
  (k m n : ℕ) → Id (mul-ℕ m (succ-ℕ k)) (mul-ℕ n (succ-ℕ k)) → Id m n
is-injective-mul-ℕ k zero-ℕ zero-ℕ p = refl
is-injective-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p =
  ap succ-ℕ
    ( is-injective-mul-ℕ k m n
      ( is-injective-add-ℕ
        ( succ-ℕ k)
        ( mul-ℕ m (succ-ℕ k))
        ( mul-ℕ n (succ-ℕ k))
        ( ( inv (left-successor-law-mul-ℕ m (succ-ℕ k))) ∙
          ( ( p) ∙
            ( left-successor-law-mul-ℕ n (succ-ℕ k))))))

-- Exercise 6.1 (c)

neq-add-ℕ :
  (m n : ℕ) → ¬ (Id m (add-ℕ m (succ-ℕ n)))
neq-add-ℕ (succ-ℕ m) n p =
  neq-add-ℕ m n
    ( ( is-injective-succ-ℕ m (add-ℕ (succ-ℕ m) n) p) ∙
      ( left-successor-law-add-ℕ m n))

-- Exercise 6.1 (d)

neq-mul-ℕ :
  (m n : ℕ) → ¬ (Id (succ-ℕ m) (mul-ℕ (succ-ℕ m) (succ-ℕ (succ-ℕ n))))
neq-mul-ℕ m n p =
  neq-add-ℕ
    ( succ-ℕ m)
    ( add-ℕ (mul-ℕ m (succ-ℕ n)) n)
    ( ( p) ∙
      ( ( right-successor-law-mul-ℕ (succ-ℕ m) (succ-ℕ n)) ∙
        ( ap (add-ℕ (succ-ℕ m)) (left-successor-law-mul-ℕ m (succ-ℕ n)))))

-- Exercise 6.2

-- Exercise 6.2 (a)

Eq-𝟚 : bool → bool → UU lzero
Eq-𝟚 true true = unit
Eq-𝟚 true false = empty
Eq-𝟚 false true = empty
Eq-𝟚 false false = unit

-- Exercise 6.2 (b)

reflexive-Eq-𝟚 : (x : bool) → Eq-𝟚 x x
reflexive-Eq-𝟚 true = star
reflexive-Eq-𝟚 false = star

Eq-eq-𝟚 :
  {x y : bool} → Id x y → Eq-𝟚 x y
Eq-eq-𝟚 {x = x} refl = reflexive-Eq-𝟚 x

eq-Eq-𝟚 :
  {x y : bool} → Eq-𝟚 x y → Id x y
eq-Eq-𝟚 {true} {true} star = refl
eq-Eq-𝟚 {false} {false} star = refl

-- Exercise 6.2 (c)

neq-neg-𝟚 : (b : bool) → ¬ (Id b (neg-𝟚 b))
neq-neg-𝟚 true = Eq-eq-𝟚
neq-neg-𝟚 false = Eq-eq-𝟚

neq-false-true-𝟚 :
  ¬ (Id false true)
neq-false-true-𝟚 = Eq-eq-𝟚

-- Exercise 6.3

-- Exercise 6.3 (a)

leq-ℕ : ℕ → ℕ → UU lzero
leq-ℕ zero-ℕ m = unit
leq-ℕ (succ-ℕ n) zero-ℕ = empty
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m

_≤_ = leq-ℕ

-- Some trivialities that will be useful later

leq-zero-ℕ :
  (n : ℕ) → leq-ℕ zero-ℕ n
leq-zero-ℕ n = star

eq-leq-zero-ℕ :
  (x : ℕ) → leq-ℕ x zero-ℕ → Id zero-ℕ x
eq-leq-zero-ℕ zero-ℕ star = refl

succ-leq-ℕ : (n : ℕ) → leq-ℕ n (succ-ℕ n)
succ-leq-ℕ zero-ℕ = star
succ-leq-ℕ (succ-ℕ n) = succ-leq-ℕ n

concatenate-eq-leq-eq-ℕ :
  {x1 x2 x3 x4 : ℕ} → Id x1 x2 → leq-ℕ x2 x3 → Id x3 x4 → leq-ℕ x1 x4
concatenate-eq-leq-eq-ℕ refl H refl = H

concatenate-leq-eq-ℕ :
  (m : ℕ) {n n' : ℕ} → leq-ℕ m n → Id n n' → leq-ℕ m n'
concatenate-leq-eq-ℕ m H refl = H

concatenate-eq-leq-ℕ :
  {m m' : ℕ} (n : ℕ) → Id m' m → leq-ℕ m n → leq-ℕ m' n
concatenate-eq-leq-ℕ n refl H = H

-- Exercise 6.3 (b)

reflexive-leq-ℕ : (n : ℕ) → n ≤ n
reflexive-leq-ℕ zero-ℕ = star
reflexive-leq-ℕ (succ-ℕ n) = reflexive-leq-ℕ n

transitive-leq-ℕ :
  (n m l : ℕ) → (n ≤ m) → (m ≤ l) → (n ≤ l)
transitive-leq-ℕ zero-ℕ m l p q = star
transitive-leq-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-leq-ℕ n m l p q

anti-symmetric-leq-ℕ : (m n : ℕ) → leq-ℕ m n → leq-ℕ n m → Id m n
anti-symmetric-leq-ℕ zero-ℕ zero-ℕ p q = refl
anti-symmetric-leq-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (anti-symmetric-leq-ℕ m n p q)

-- Exercise 6.3 (c)

decide-leq-ℕ :
  (m n : ℕ) → coprod (leq-ℕ m n) (leq-ℕ n m)
decide-leq-ℕ zero-ℕ zero-ℕ = inl star
decide-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
decide-leq-ℕ (succ-ℕ m) zero-ℕ = inr star
decide-leq-ℕ (succ-ℕ m) (succ-ℕ n) = decide-leq-ℕ m n

-- Exercise 6.3 (d)

preserves-order-add-ℕ :
  (k m n : ℕ) → leq-ℕ m n → leq-ℕ (add-ℕ m k) (add-ℕ n k)
preserves-order-add-ℕ zero-ℕ m n = id
preserves-order-add-ℕ (succ-ℕ k) m n = preserves-order-add-ℕ k m n

reflects-order-add-ℕ :
  (k m n : ℕ) → leq-ℕ (add-ℕ m k) (add-ℕ n k) → leq-ℕ m n
reflects-order-add-ℕ zero-ℕ m n = id
reflects-order-add-ℕ (succ-ℕ k) m n = reflects-order-add-ℕ k m n

-- Exercise 6.3 (e)

preserves-order-mul-ℕ :
  (k m n : ℕ) → leq-ℕ m n → leq-ℕ (mul-ℕ m k) (mul-ℕ n k)
preserves-order-mul-ℕ k zero-ℕ n p = star
preserves-order-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p =
  preserves-order-add-ℕ k
    ( mul-ℕ m k)
    ( mul-ℕ n k)
    ( preserves-order-mul-ℕ k m n p)

reflects-order-mul-ℕ :
  (k m n : ℕ) → leq-ℕ (mul-ℕ m (succ-ℕ k)) (mul-ℕ n (succ-ℕ k)) → leq-ℕ m n
reflects-order-mul-ℕ k zero-ℕ n p = star
reflects-order-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p =
  reflects-order-mul-ℕ k m n
    ( reflects-order-add-ℕ
      ( succ-ℕ k)
      ( mul-ℕ m (succ-ℕ k))
      ( mul-ℕ n (succ-ℕ k))
      ( p))

-- Exercise 6.3 (f)

leq-min-ℕ :
  (k m n : ℕ) → leq-ℕ k m → leq-ℕ k n → leq-ℕ k (min-ℕ m n)
leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H K = star
leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H K = star
leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H K = star
leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H K = leq-min-ℕ k m n H K

leq-left-leq-min-ℕ :
  (k m n : ℕ) → leq-ℕ k (min-ℕ m n) → leq-ℕ k m
leq-left-leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H = star
leq-left-leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H = star
leq-left-leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H = star
leq-left-leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H = star
leq-left-leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-left-leq-min-ℕ k m n H

leq-right-leq-min-ℕ :
  (k m n : ℕ) → leq-ℕ k (min-ℕ m n) → leq-ℕ k n
leq-right-leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H = star
leq-right-leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H = star
leq-right-leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H = star
leq-right-leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H = star
leq-right-leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-right-leq-min-ℕ k m n H

leq-max-ℕ :
  (k m n : ℕ) → leq-ℕ m k → leq-ℕ n k → leq-ℕ (max-ℕ m n) k
leq-max-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
leq-max-ℕ (succ-ℕ k) zero-ℕ zero-ℕ H K = star
leq-max-ℕ (succ-ℕ k) zero-ℕ (succ-ℕ n) H K = K
leq-max-ℕ (succ-ℕ k) (succ-ℕ m) zero-ℕ H K = H
leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H K = leq-max-ℕ k m n H K

leq-left-leq-max-ℕ :
  (k m n : ℕ) → leq-ℕ (max-ℕ m n) k → leq-ℕ m k
leq-left-leq-max-ℕ k zero-ℕ zero-ℕ H = star
leq-left-leq-max-ℕ k zero-ℕ (succ-ℕ n) H = star
leq-left-leq-max-ℕ k (succ-ℕ m) zero-ℕ H = H
leq-left-leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-left-leq-max-ℕ k m n H

leq-right-leq-max-ℕ :
  (k m n : ℕ) → leq-ℕ (max-ℕ m n) k → leq-ℕ n k
leq-right-leq-max-ℕ k zero-ℕ zero-ℕ H = star
leq-right-leq-max-ℕ k zero-ℕ (succ-ℕ n) H = H
leq-right-leq-max-ℕ k (succ-ℕ m) zero-ℕ H = star
leq-right-leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-right-leq-max-ℕ k m n H

-- Exercise 6.4

-- Exercise 6.4 (a)

-- We define a distance function on ℕ --

dist-ℕ : ℕ → ℕ → ℕ
dist-ℕ zero-ℕ zero-ℕ = zero-ℕ
dist-ℕ zero-ℕ (succ-ℕ n) = succ-ℕ n
dist-ℕ (succ-ℕ m) zero-ℕ = succ-ℕ m
dist-ℕ (succ-ℕ m) (succ-ℕ n) = dist-ℕ m n

dist-ℕ' : ℕ → ℕ → ℕ
dist-ℕ' m n = dist-ℕ n m

ap-dist-ℕ :
  {m n m' n' : ℕ} → Id m m' → Id n n' → Id (dist-ℕ m n) (dist-ℕ m' n')
ap-dist-ℕ refl refl = refl

{- We show that two natural numbers are equal if and only if their distance is
   zero. -}

eq-dist-ℕ :
  (m n : ℕ) → Id zero-ℕ (dist-ℕ m n) → Id m n
eq-dist-ℕ zero-ℕ zero-ℕ p = refl
eq-dist-ℕ (succ-ℕ m) (succ-ℕ n) p = ap succ-ℕ (eq-dist-ℕ m n p)

dist-eq-ℕ' :
  (n : ℕ) → Id zero-ℕ (dist-ℕ n n)
dist-eq-ℕ' zero-ℕ = refl
dist-eq-ℕ' (succ-ℕ n) = dist-eq-ℕ' n

dist-eq-ℕ :
  (m n : ℕ) → Id m n → Id zero-ℕ (dist-ℕ m n)
dist-eq-ℕ m .m refl = dist-eq-ℕ' m

-- The distance function is symmetric --

symmetric-dist-ℕ :
  (m n : ℕ) → Id (dist-ℕ m n) (dist-ℕ n m)
symmetric-dist-ℕ zero-ℕ zero-ℕ = refl
symmetric-dist-ℕ zero-ℕ (succ-ℕ n) = refl
symmetric-dist-ℕ (succ-ℕ m) zero-ℕ = refl
symmetric-dist-ℕ (succ-ℕ m) (succ-ℕ n) = symmetric-dist-ℕ m n

-- We compute the distance from zero --

left-zero-law-dist-ℕ :
  (n : ℕ) → Id (dist-ℕ zero-ℕ n) n
left-zero-law-dist-ℕ zero-ℕ = refl
left-zero-law-dist-ℕ (succ-ℕ n) = refl

right-zero-law-dist-ℕ :
  (n : ℕ) → Id (dist-ℕ n zero-ℕ) n
right-zero-law-dist-ℕ zero-ℕ = refl
right-zero-law-dist-ℕ (succ-ℕ n) = refl

-- We prove the triangle inequality --

ap-add-ℕ :
  {m n m' n' : ℕ} → Id m m' → Id n n' → Id (add-ℕ m n) (add-ℕ m' n')
ap-add-ℕ refl refl = refl

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

-- Exercise 6.6

{- In this exercise we were asked to define the relations ≤ and < on the 
   integers. As a criterion of correctness, we were then also asked to show 
   that the type of all integers l satisfying k ≤ l satisfy the induction 
   principle of the natural numbers. -}

diff-ℤ : ℤ → ℤ → ℤ
diff-ℤ k l = add-ℤ (neg-ℤ k) l

is-non-negative-ℤ : ℤ → UU lzero
is-non-negative-ℤ (inl x) = empty
is-non-negative-ℤ (inr k) = unit

leq-ℤ : ℤ → ℤ → UU lzero
leq-ℤ k l = is-non-negative-ℤ (diff-ℤ k l)

reflexive-leq-ℤ : (k : ℤ) → leq-ℤ k k
reflexive-leq-ℤ k =
  tr is-non-negative-ℤ (inv (left-inverse-law-add-ℤ k)) star

is-non-negative-succ-ℤ :
  (k : ℤ) → is-non-negative-ℤ k → is-non-negative-ℤ (succ-ℤ k)
is-non-negative-succ-ℤ (inr (inl star)) p = star
is-non-negative-succ-ℤ (inr (inr x)) p = star

is-non-negative-add-ℤ :
  (k l : ℤ) →
  is-non-negative-ℤ k → is-non-negative-ℤ l → is-non-negative-ℤ (add-ℤ k l)
is-non-negative-add-ℤ (inr (inl star)) (inr (inl star)) p q = star
is-non-negative-add-ℤ (inr (inl star)) (inr (inr n)) p q = star
is-non-negative-add-ℤ (inr (inr zero-ℕ)) (inr (inl star)) p q = star
is-non-negative-add-ℤ (inr (inr (succ-ℕ n))) (inr (inl star)) star star =
  is-non-negative-succ-ℤ
    ( add-ℤ (inr (inr n)) (inr (inl star)))
    ( is-non-negative-add-ℤ (inr (inr n)) (inr (inl star)) star star)
is-non-negative-add-ℤ (inr (inr zero-ℕ)) (inr (inr m)) star star = star
is-non-negative-add-ℤ (inr (inr (succ-ℕ n))) (inr (inr m)) star star =
  is-non-negative-succ-ℤ
    ( add-ℤ (inr (inr n)) (inr (inr m)))
    ( is-non-negative-add-ℤ (inr (inr n)) (inr (inr m)) star star)

triangle-diff-ℤ :
  (k l m : ℤ) → Id (add-ℤ (diff-ℤ k l) (diff-ℤ l m)) (diff-ℤ k m)
triangle-diff-ℤ k l m =
  ( associative-add-ℤ (neg-ℤ k) l (diff-ℤ l m)) ∙
  ( ap
    ( add-ℤ (neg-ℤ k))
    ( ( inv (associative-add-ℤ l (neg-ℤ l) m)) ∙
      ( ( ap (λ x → add-ℤ x m) (right-inverse-law-add-ℤ l)) ∙
        ( left-unit-law-add-ℤ m))))

transitive-leq-ℤ : (k l m : ℤ) → leq-ℤ k l → leq-ℤ l m → leq-ℤ k m
transitive-leq-ℤ k l m p q =
  tr is-non-negative-ℤ
    ( triangle-diff-ℤ k l m)
    ( is-non-negative-add-ℤ
      ( add-ℤ (neg-ℤ k) l)
      ( add-ℤ (neg-ℤ l) m)
      ( p)
      ( q))

succ-leq-ℤ : (k : ℤ) → leq-ℤ k (succ-ℤ k)
succ-leq-ℤ k =
  tr is-non-negative-ℤ
    ( inv
      ( ( right-successor-law-add-ℤ (neg-ℤ k) k) ∙
        ( ap succ-ℤ (left-inverse-law-add-ℤ k))))
    ( star)

leq-ℤ-succ-leq-ℤ : (k l : ℤ) → leq-ℤ k l → leq-ℤ k (succ-ℤ l)
leq-ℤ-succ-leq-ℤ k l p = transitive-leq-ℤ k l (succ-ℤ l) p (succ-leq-ℤ l)

is-positive-ℤ : ℤ → UU lzero
is-positive-ℤ k = is-non-negative-ℤ (pred-ℤ k)

le-ℤ : ℤ → ℤ → UU lzero
le-ℤ (inl zero-ℕ) (inl x) = empty
le-ℤ (inl zero-ℕ) (inr y) = unit
le-ℤ (inl (succ-ℕ x)) (inl zero-ℕ) = unit
le-ℤ (inl (succ-ℕ x)) (inl (succ-ℕ y)) = le-ℤ (inl x) (inl y)
le-ℤ (inl (succ-ℕ x)) (inr y) = unit
le-ℤ (inr x) (inl y) = empty
le-ℤ (inr (inl star)) (inr (inl star)) = empty
le-ℤ (inr (inl star)) (inr (inr x)) = unit
le-ℤ (inr (inr x)) (inr (inl star)) = empty
le-ℤ (inr (inr zero-ℕ)) (inr (inr zero-ℕ)) = empty
le-ℤ (inr (inr zero-ℕ)) (inr (inr (succ-ℕ y))) = unit
le-ℤ (inr (inr (succ-ℕ x))) (inr (inr zero-ℕ)) = empty
le-ℤ (inr (inr (succ-ℕ x))) (inr (inr (succ-ℕ y))) =
  le-ℤ (inr (inr x)) (inr (inr y))

-- Extra material

-- We show that ℕ is an ordered semi-ring

left-law-leq-add-ℕ : (k m n : ℕ) → leq-ℕ m n → leq-ℕ (add-ℕ m k) (add-ℕ n k)
left-law-leq-add-ℕ zero-ℕ m n = id
left-law-leq-add-ℕ (succ-ℕ k) m n H = left-law-leq-add-ℕ k m n H

right-law-leq-add-ℕ : (k m n : ℕ) → leq-ℕ m n → leq-ℕ (add-ℕ k m) (add-ℕ k n) 
right-law-leq-add-ℕ k m n H =
  concatenate-eq-leq-eq-ℕ
    ( commutative-add-ℕ k m)
    ( left-law-leq-add-ℕ k m n H)
    ( commutative-add-ℕ n k)

preserves-leq-add-ℕ :
  {m m' n n' : ℕ} → leq-ℕ m m' → leq-ℕ n n' → leq-ℕ (add-ℕ m n) (add-ℕ m' n')
preserves-leq-add-ℕ {m} {m'} {n} {n'} H K =
  transitive-leq-ℕ
    ( add-ℕ m n)
    ( add-ℕ m' n)
    ( add-ℕ m' n')
    ( left-law-leq-add-ℕ n m m' H)
    ( right-law-leq-add-ℕ m' n n' K)

{-
right-law-leq-mul-ℕ : (k m n : ℕ) → leq-ℕ m n → leq-ℕ (mul-ℕ k m) (mul-ℕ k n)
right-law-leq-mul-ℕ zero-ℕ m n H = star
right-law-leq-mul-ℕ (succ-ℕ k) m n H = {!!}
-}

{-
  preserves-leq-add-ℕ
    { m = mul-ℕ k m}
    { m' = mul-ℕ k n}
    ( right-law-leq-mul-ℕ k m n H) H

left-law-leq-mul-ℕ : (k m n : ℕ) → leq-ℕ m n → leq-ℕ (mul-ℕ m k) (mul-ℕ n k)
left-law-leq-mul-ℕ k m n H =
  concatenate-eq-leq-eq-ℕ
    ( commutative-mul-ℕ k m)
    ( commutative-mul-ℕ k n)
    ( right-law-leq-mul-ℕ k m n H)
-}

-- We show that ℤ is an ordered ring

{-
leq-add-ℤ : (m k l : ℤ) → leq-ℤ k l → leq-ℤ (add-ℤ m k) (add-ℤ m l)
leq-add-ℤ (inl zero-ℕ) k l H = {!!}
leq-add-ℤ (inl (succ-ℕ x)) k l H = {!!}
leq-add-ℤ (inr m) k l H = {!!}
-}

-- Section 5.5 Identity systems

succ-fam-Eq-ℕ :
  {i : Level} (R : (m n : ℕ) → Eq-ℕ m n → UU i) →
  (m n : ℕ) → Eq-ℕ m n → UU i
succ-fam-Eq-ℕ R m n e = R (succ-ℕ m) (succ-ℕ n) e

succ-refl-fam-Eq-ℕ :
  {i : Level} (R : (m n : ℕ) → Eq-ℕ m n → UU i)
  (ρ : (n : ℕ) → R n n (refl-Eq-ℕ n)) →
  (n : ℕ) → (succ-fam-Eq-ℕ R n n (refl-Eq-ℕ n))
succ-refl-fam-Eq-ℕ R ρ n = ρ (succ-ℕ n)

path-ind-Eq-ℕ :
  {i : Level} (R : (m n : ℕ) → Eq-ℕ m n → UU i)
  ( ρ : (n : ℕ) → R n n (refl-Eq-ℕ n)) →
  ( m n : ℕ) (e : Eq-ℕ m n) → R m n e
path-ind-Eq-ℕ R ρ zero-ℕ zero-ℕ star = ρ zero-ℕ
path-ind-Eq-ℕ R ρ zero-ℕ (succ-ℕ n) ()
path-ind-Eq-ℕ R ρ (succ-ℕ m) zero-ℕ ()
path-ind-Eq-ℕ R ρ (succ-ℕ m) (succ-ℕ n) e =
  path-ind-Eq-ℕ
    ( λ m n e → R (succ-ℕ m) (succ-ℕ n) e)
    ( λ n → ρ (succ-ℕ n)) m n e

comp-path-ind-Eq-ℕ :
  {i : Level} (R : (m n : ℕ) → Eq-ℕ m n → UU i)
  ( ρ : (n : ℕ) → R n n (refl-Eq-ℕ n)) →
  ( n : ℕ) → Id (path-ind-Eq-ℕ R ρ n n (refl-Eq-ℕ n)) (ρ n)
comp-path-ind-Eq-ℕ R ρ zero-ℕ = refl
comp-path-ind-Eq-ℕ R ρ (succ-ℕ n) =
  comp-path-ind-Eq-ℕ
    ( λ m n e → R (succ-ℕ m) (succ-ℕ n) e)
    ( λ n → ρ (succ-ℕ n)) n


{-
-- Graphs
Gph : (i : Level) → UU (lsuc i)
Gph i = Σ (UU i) (λ X → (X → X → (UU i)))

-- Reflexive graphs
rGph : (i : Level) →  UU (lsuc i)
rGph i = Σ (UU i) (λ X → Σ (X → X → (UU i)) (λ R → (x : X) → R x x))
-}

-- Exercise 3.7

{- With the construction of the divisibility relation we open the door to basic
   number theory. -}
   
divides : (d n : ℕ) → UU lzero
divides d n = Σ ℕ (λ m → Eq-ℕ (mul-ℕ d m) n)

-- We prove some lemmas about inequalities --

leq-add-ℕ :
  (m n : ℕ) → leq-ℕ m (add-ℕ m n)
leq-add-ℕ m zero-ℕ = reflexive-leq-ℕ m
leq-add-ℕ m (succ-ℕ n) =
  transitive-leq-ℕ m (add-ℕ m n) (succ-ℕ (add-ℕ m n))
    ( leq-add-ℕ m n)
    ( succ-leq-ℕ (add-ℕ m n))

leq-add-ℕ' :
  (m n : ℕ) → leq-ℕ m (add-ℕ n m)
leq-add-ℕ' m n =
  concatenate-leq-eq-ℕ m (leq-add-ℕ m n) (commutative-add-ℕ m n)

leq-leq-add-ℕ :
  (m n x : ℕ) → leq-ℕ (add-ℕ m x) (add-ℕ n x) → leq-ℕ m n
leq-leq-add-ℕ m n zero-ℕ H = H
leq-leq-add-ℕ m n (succ-ℕ x) H = leq-leq-add-ℕ m n x H

leq-leq-add-ℕ' :
  (m n x : ℕ) → leq-ℕ (add-ℕ x m) (add-ℕ x n) → leq-ℕ m n
leq-leq-add-ℕ' m n x H =
  leq-leq-add-ℕ m n x
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-add-ℕ m x)
      ( H)
      ( commutative-add-ℕ x n))

leq-leq-mul-ℕ :
  (m n x : ℕ) → leq-ℕ (mul-ℕ (succ-ℕ x) m) (mul-ℕ (succ-ℕ x) n) → leq-ℕ m n
leq-leq-mul-ℕ zero-ℕ zero-ℕ x H = star
leq-leq-mul-ℕ zero-ℕ (succ-ℕ n) x H = star
leq-leq-mul-ℕ (succ-ℕ m) zero-ℕ x H =
  ex-falso
    ( concatenate-leq-eq-ℕ
      ( mul-ℕ (succ-ℕ x) (succ-ℕ m))
      ( H)
      ( right-zero-law-mul-ℕ (succ-ℕ x)))
leq-leq-mul-ℕ (succ-ℕ m) (succ-ℕ n) x H =
  leq-leq-mul-ℕ m n x
    ( leq-leq-add-ℕ' (mul-ℕ (succ-ℕ x) m) (mul-ℕ (succ-ℕ x) n) (succ-ℕ x)
      ( concatenate-eq-leq-eq-ℕ
        ( inv (right-successor-law-mul-ℕ (succ-ℕ x) m))
        ( H)
        ( right-successor-law-mul-ℕ (succ-ℕ x) n)))

leq-leq-mul-ℕ' :
  (m n x : ℕ) → leq-ℕ (mul-ℕ m (succ-ℕ x)) (mul-ℕ n (succ-ℕ x)) → leq-ℕ m n
leq-leq-mul-ℕ' m n x H =
  leq-leq-mul-ℕ m n x
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-mul-ℕ (succ-ℕ x) m)
      ( H)
      ( commutative-mul-ℕ n (succ-ℕ x)))

{-
succ-relation-ℕ :
  {i : Level} (R : ℕ → ℕ → UU i) → ℕ → ℕ → UU i
succ-relation-ℕ R m n = R (succ-ℕ m) (succ-ℕ n)

succ-reflexivity-ℕ :
  {i : Level} (R : ℕ → ℕ → UU i) (ρ : (n : ℕ) → R n n) →
  (n : ℕ) → succ-relation-ℕ R n n
succ-reflexivity-ℕ R ρ n = ρ (succ-ℕ n)

{- In the book we suggest that first the order of the variables should be
   swapped, in order to make the inductive hypothesis stronger. Agda's pattern
   matching mechanism allows us to bypass this step and give a more direct
   construction. -}

least-reflexive-Eq-ℕ :
  {i : Level} (R : ℕ → ℕ → UU i) (ρ : (n : ℕ) → R n n) →
  (m n : ℕ) → Eq-ℕ m n → R m n
least-reflexive-Eq-ℕ R ρ zero-ℕ zero-ℕ star = ρ zero-ℕ
least-reflexive-Eq-ℕ R ρ zero-ℕ (succ-ℕ n) ()
least-reflexive-Eq-ℕ R ρ (succ-ℕ m) zero-ℕ ()
least-reflexive-Eq-ℕ R ρ (succ-ℕ m) (succ-ℕ n) e =
  least-reflexive-Eq-ℕ (succ-relation-ℕ R) (succ-reflexivity-ℕ R ρ) m n e
-}

-- The definition of <

le-ℕ : ℕ → ℕ → UU lzero
le-ℕ m zero-ℕ = empty
le-ℕ zero-ℕ (succ-ℕ m) = unit
le-ℕ (succ-ℕ n) (succ-ℕ m) = le-ℕ n m

_<_ = le-ℕ

anti-reflexive-le-ℕ : (n : ℕ) → ¬ (n < n)
anti-reflexive-le-ℕ zero-ℕ = ind-empty
anti-reflexive-le-ℕ (succ-ℕ n) = anti-reflexive-le-ℕ n

transitive-le-ℕ : (n m l : ℕ) → (le-ℕ n m) → (le-ℕ m l) → (le-ℕ n l)
transitive-le-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ l) p q = star
transitive-le-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-le-ℕ n m l p q

succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
succ-le-ℕ zero-ℕ = star
succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n

anti-symmetric-le-ℕ : (m n : ℕ) → le-ℕ m n → le-ℕ n m → Id m n
anti-symmetric-le-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (anti-symmetric-le-ℕ m n p q)

{-
--------------------------------------------------------------------------------

data Fin-Tree : UU lzero where
  constr : (n : ℕ) → (Fin n → Fin-Tree) → Fin-Tree

root-Fin-Tree : Fin-Tree
root-Fin-Tree = constr zero-ℕ ex-falso

succ-Fin-Tree : Fin-Tree → Fin-Tree
succ-Fin-Tree t = constr one-ℕ (λ i → t)

map-assoc-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  coprod (coprod A B) C → coprod A (coprod B C)
map-assoc-coprod (inl (inl x)) = inl x
map-assoc-coprod (inl (inr x)) = inr (inl x)
map-assoc-coprod (inr x) = inr (inr x)

map-coprod-Fin :
  (m n : ℕ) → Fin (add-ℕ m n) → coprod (Fin m) (Fin n)
map-coprod-Fin m zero-ℕ = inl
map-coprod-Fin m (succ-ℕ n) =
  map-assoc-coprod ∘ (functor-coprod (map-coprod-Fin m n) (id {A = unit}))

add-Fin-Tree : Fin-Tree → Fin-Tree → Fin-Tree
add-Fin-Tree (constr n x) (constr m y) =
  constr (add-ℕ n m) ((ind-coprod (λ i → Fin-Tree) x y) ∘ (map-coprod-Fin n m))

--------------------------------------------------------------------------------

data labeled-Bin-Tree {l1 : Level} (A : UU l1) : UU l1 where
  leaf : A → labeled-Bin-Tree A
  constr : (bool → labeled-Bin-Tree A) → labeled-Bin-Tree A

mul-leaves-labeled-Bin-Tree :
  {l1 : Level} {A : UU l1} (μ : A → (A → A)) →
  labeled-Bin-Tree A → A
mul-leaves-labeled-Bin-Tree μ (leaf x) = x
mul-leaves-labeled-Bin-Tree μ (constr f) =
  μ ( mul-leaves-labeled-Bin-Tree μ (f false))
    ( mul-leaves-labeled-Bin-Tree μ (f true))

pick-list : {l1 : Level} {A : UU l1} → ℕ → list A → coprod A unit
pick-list zero-ℕ nil = inr star
pick-list zero-ℕ (cons a x) = inl a
pick-list (succ-ℕ n) nil = inr star
pick-list (succ-ℕ n) (cons a x) = pick-list n x
-}
