{-# OPTIONS --without-K --exact-split #-}

module 02-natural-numbers where

import 00-preamble
open 00-preamble public

-- Definition 2.2.3
id : {i : Level} {A : UU i} → A → A
id a = a 

-- Definition 2.2.4
_∘_ :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} →
  (B → C) → ((A → B) → (A → C))
(g ∘ f) a = g (f a)

data ℕ : UU lzero where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ

one-ℕ : ℕ
one-ℕ = succ-ℕ zero-ℕ

-- induction: for any dependent type P over ℕ, define a section of P
-- built out of a term in P 0 and a section of P n → P(Nsucc n)
ind-ℕ : {i : Level} {P : ℕ → UU i} → P zero-ℕ → ((n : ℕ) → P n → P(succ-ℕ n)) → ((n : ℕ) → P n)
ind-ℕ p0 pS zero-ℕ = p0
ind-ℕ p0 pS (succ-ℕ n) = pS n (ind-ℕ p0 pS n)

-- use the general induction principle to define addition
-- in this case P is ℕ, the special non-dependent type over ℕ, and
-- so sections of P (dependent functions Π_{x:ℕ} P(x)) are functions ℕ → ℕ

add-ℕ : ℕ → ℕ → ℕ
add-ℕ zero-ℕ y = y
add-ℕ (succ-ℕ x) y = succ-ℕ (add-ℕ x y)

-- Exercise 2.2
const : {i j : Level} (A : UU i) (B : UU j) (b : B) → A → B
const A B b x = b

-- Exercise 2.3

-- In this exercise we are asked to construct some standard functions on the
-- natural numbers.

-- Exercise 2.3(a)
max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ zero-ℕ n = n
max-ℕ (succ-ℕ m) zero-ℕ = succ-ℕ m
max-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (max-ℕ m n)

min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ zero-ℕ n = zero-ℕ
min-ℕ (succ-ℕ m) zero-ℕ = zero-ℕ
min-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (min-ℕ m n)

-- Exercise 2.3(b)
mul-ℕ : ℕ → (ℕ → ℕ)
mul-ℕ zero-ℕ n = zero-ℕ
mul-ℕ (succ-ℕ m) n = add-ℕ (mul-ℕ m n) n

-- Exercise 2.3(c)
_^_ : ℕ → (ℕ → ℕ)
m ^ zero-ℕ = one-ℕ
m ^ (succ-ℕ n) = mul-ℕ m (m ^ n)

-- Exercise 2.3(d)
factorial : ℕ → ℕ
factorial zero-ℕ = one-ℕ
factorial (succ-ℕ m) = mul-ℕ (succ-ℕ m) (factorial m)

-- Exercise 2.3(e)
_choose_ : ℕ → ℕ → ℕ
zero-ℕ choose zero-ℕ = one-ℕ
zero-ℕ choose succ-ℕ k = zero-ℕ
(succ-ℕ n) choose zero-ℕ = one-ℕ
(succ-ℕ n) choose (succ-ℕ k) = add-ℕ (n choose k) (n choose (succ-ℕ k))

-- Exercise 2.3(f)
Fibonacci : ℕ → ℕ
Fibonacci zero-ℕ = zero-ℕ
Fibonacci (succ-ℕ zero-ℕ) = one-ℕ
Fibonacci (succ-ℕ (succ-ℕ n)) = add-ℕ (Fibonacci n) (Fibonacci (succ-ℕ n))

-- Exercise 2.4
_∘'_ :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : (x : A) → B x → UU k} →
  (g : (x : A) → (y : B x) → C x y) (f : (x : A) → B x) → (x : A) → C x (f x)
(g ∘' f) x = g x (f x)

-- Exercise 2.5
Π-swap : {i j k : Level} {A : UU i} {B : UU j} {C : A → (B → UU k)} →
  ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
Π-swap f y x = f x y

-- Note: apparently Agda still allows us to define a sequence of universe levels indexed by ℕ

Level-ℕ : ℕ → Level
Level-ℕ zero-ℕ = lzero
Level-ℕ (succ-ℕ n) = lsuc (Level-ℕ n)

sequence-UU : (n : ℕ) → UU (Level-ℕ (succ-ℕ n))
sequence-UU n = UU (Level-ℕ n)

-- However, the following definition is unacceptable for Agda, since it runs
-- into Setω.

{-
Π-sequence-UU : Setω
Π-sequence-UU = (n : ℕ) → sequence-UU n
-}
