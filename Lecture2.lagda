\begin{code}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture2 where

import Basics
open Basics public

-- Definition 2.2.3 define identity, and show lambda-abstraction in so doing
id : {i : Level} {A : UU i} → A → A
id = λ a → a -- can also use plain backslash \ instead of lambda (as it resembles lambda?)

-- Definition 2.2.4
comp : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} → (B → C) → ((A → B) → (A → C))
comp = λ g f a → g(f(a)) -- the lambda extends to cover g, f and a
_∘_ : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} → (B → C) → ((A → B) → (A → C))
g ∘ f = comp g f

data ℕ : U where
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

-- try some examples, hit C-c C-n (or whatever "compute normal form" is bound to)
-- and try entering "add (Nsucc Nzero) (Nsucc (Nsucc Nzero))"
-- you should get "Nsucc (Nsucc (Nsucc Nzero))"

_+_ : ℕ → ℕ → ℕ
n + m = add-ℕ n m

-- Exercise 2.3
const : {i j : Level} (A : UU i) (B : UU j) (b : B) → A → B
const A B b x = b

-- Exercise 2.4
Pi-swap : {i j k : Level} {A : UU i} {B : UU j} {C : A → (B → UU k)} →
  ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
Pi-swap f y x = f x y

-- Exercise 2.5(a)
mul-ℕ : ℕ → (ℕ → ℕ)
mul-ℕ zero-ℕ n = zero-ℕ
mul-ℕ (succ-ℕ m) n = add-ℕ (mul-ℕ m n) n

_**_ : ℕ → (ℕ → ℕ)
m ** n = mul-ℕ m n

-- Exercise 2.5(b)
_^_ : ℕ → (ℕ → ℕ)
m ^ zero-ℕ = one-ℕ
m ^ (succ-ℕ n) = mul-ℕ m (m ^ n)

-- Exercise 2.5(c)
factorial : ℕ → ℕ
factorial zero-ℕ = one-ℕ
factorial (succ-ℕ m) = (succ-ℕ m) ** (factorial m)

-- Exercise 2.6
max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ zero-ℕ n = n
max-ℕ (succ-ℕ m) zero-ℕ = succ-ℕ m
max-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (max-ℕ m n)

-- Exercise 2.6
min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ zero-ℕ n = zero-ℕ
min-ℕ (succ-ℕ m) zero-ℕ = zero-ℕ
min-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (min-ℕ m n)

\end{code}
