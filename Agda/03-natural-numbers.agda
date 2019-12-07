{-# OPTIONS --without-K --exact-split #-}

module 03-natural-numbers where

import 02-pi
open 02-pi public

-- Section 3.1 The formal specification of the type of natural numbers

data ℕ : UU lzero where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ

{- We define the numbers one-ℕ to ten-ℕ -}

one-ℕ : ℕ
one-ℕ = succ-ℕ zero-ℕ

two-ℕ : ℕ
two-ℕ = succ-ℕ one-ℕ

three-ℕ : ℕ
three-ℕ = succ-ℕ two-ℕ

four-ℕ : ℕ
four-ℕ = succ-ℕ three-ℕ

five-ℕ : ℕ
five-ℕ = succ-ℕ four-ℕ

six-ℕ : ℕ
six-ℕ = succ-ℕ five-ℕ

seven-ℕ : ℕ
seven-ℕ = succ-ℕ six-ℕ

eight-ℕ : ℕ
eight-ℕ = succ-ℕ seven-ℕ

nine-ℕ : ℕ
nine-ℕ = succ-ℕ eight-ℕ

ten-ℕ : ℕ
ten-ℕ = succ-ℕ nine-ℕ

-- Remark 3.1.2

ind-ℕ : {i : Level} {P : ℕ → UU i} → P zero-ℕ → ((n : ℕ) → P n → P(succ-ℕ n)) → ((n : ℕ) → P n)
ind-ℕ p0 pS zero-ℕ = p0
ind-ℕ p0 pS (succ-ℕ n) = pS n (ind-ℕ p0 pS n)

-- Section 3.2 Addition on the natural numbers

-- Definition 3.2.1

add-ℕ : ℕ → ℕ → ℕ
add-ℕ x zero-ℕ = x
add-ℕ x (succ-ℕ y) = succ-ℕ (add-ℕ x y)

-- Exercises

-- Exercise 3.1

min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ zero-ℕ n = zero-ℕ
min-ℕ (succ-ℕ m) zero-ℕ = zero-ℕ
min-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (min-ℕ m n)

max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ zero-ℕ n = n
max-ℕ (succ-ℕ m) zero-ℕ = succ-ℕ m
max-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (max-ℕ m n)

-- Exercise 3.2

mul-ℕ : ℕ → (ℕ → ℕ)
mul-ℕ zero-ℕ n = zero-ℕ
mul-ℕ (succ-ℕ m) n = add-ℕ (mul-ℕ m n) n

-- Exercise 3.3

pow-ℕ : ℕ → (ℕ → ℕ)
pow-ℕ m zero-ℕ = one-ℕ
pow-ℕ m (succ-ℕ n) = mul-ℕ m (pow-ℕ m n)

-- Exercise 3.4

factorial : ℕ → ℕ
factorial zero-ℕ = one-ℕ
factorial (succ-ℕ m) = mul-ℕ (succ-ℕ m) (factorial m)

-- Exercise 3.5

_choose_ : ℕ → ℕ → ℕ
zero-ℕ choose zero-ℕ = one-ℕ
zero-ℕ choose succ-ℕ k = zero-ℕ
(succ-ℕ n) choose zero-ℕ = one-ℕ
(succ-ℕ n) choose (succ-ℕ k) = add-ℕ (n choose k) (n choose (succ-ℕ k))

-- Exercise 3.6

Fibonacci : ℕ → ℕ
Fibonacci zero-ℕ = zero-ℕ
Fibonacci (succ-ℕ zero-ℕ) = one-ℕ
Fibonacci (succ-ℕ (succ-ℕ n)) = add-ℕ (Fibonacci n) (Fibonacci (succ-ℕ n))
