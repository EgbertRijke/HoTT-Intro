{-# OPTIONS --without-K --exact-split --safe #-}

module 03-natural-numbers where

import 02-pi
open 02-pi public

--------------------------------------------------------------------------------

-- Section 3.1 The formal specification of the type of natural numbers

data ℕ : UU lzero where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ

{- We define the numbers one-ℕ to twenty-ℕ -}

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

eleven-ℕ : ℕ
eleven-ℕ = succ-ℕ ten-ℕ

twelve-ℕ : ℕ
twelve-ℕ = succ-ℕ eleven-ℕ

thirteen-ℕ : ℕ
thirteen-ℕ = succ-ℕ twelve-ℕ

fourteen-ℕ : ℕ
fourteen-ℕ = succ-ℕ thirteen-ℕ

fifteen-ℕ : ℕ
fifteen-ℕ = succ-ℕ fourteen-ℕ

sixteen-ℕ : ℕ
sixteen-ℕ = succ-ℕ fifteen-ℕ

seventeen-ℕ : ℕ
seventeen-ℕ = succ-ℕ sixteen-ℕ

eighteen-ℕ : ℕ
eighteen-ℕ = succ-ℕ seventeen-ℕ

nineteen-ℕ : ℕ
nineteen-ℕ = succ-ℕ eighteen-ℕ

twenty-ℕ : ℕ
twenty-ℕ = succ-ℕ nineteen-ℕ

-- Remark 3.1.2

ind-ℕ : {i : Level} {P : ℕ → UU i} → P zero-ℕ → ((n : ℕ) → P n → P(succ-ℕ n)) → ((n : ℕ) → P n)
ind-ℕ p0 pS zero-ℕ = p0
ind-ℕ p0 pS (succ-ℕ n) = pS n (ind-ℕ p0 pS n)

--------------------------------------------------------------------------------

-- Section 3.2 Addition on the natural numbers

-- Definition 3.2.1

add-ℕ : ℕ → ℕ → ℕ
add-ℕ x zero-ℕ = x
add-ℕ x (succ-ℕ y) = succ-ℕ (add-ℕ x y)

add-ℕ' : ℕ → ℕ → ℕ
add-ℕ' m n = add-ℕ n m

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 3.1

mul-ℕ : ℕ → (ℕ → ℕ)
mul-ℕ zero-ℕ n = zero-ℕ
mul-ℕ (succ-ℕ m) n = add-ℕ (mul-ℕ m n) n

mul-ℕ' : ℕ → (ℕ → ℕ)
mul-ℕ' x y = mul-ℕ y x

pow-ℕ : ℕ → (ℕ → ℕ)
pow-ℕ m zero-ℕ = one-ℕ
pow-ℕ m (succ-ℕ n) = mul-ℕ m (pow-ℕ m n)

-- Exercise 3.2

min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ zero-ℕ n = zero-ℕ
min-ℕ (succ-ℕ m) zero-ℕ = zero-ℕ
min-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (min-ℕ m n)

max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ zero-ℕ n = n
max-ℕ (succ-ℕ m) zero-ℕ = succ-ℕ m
max-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (max-ℕ m n)

-- Exercise 3.3

triangular-number : ℕ → ℕ
triangular-number zero-ℕ = zero-ℕ
triangular-number (succ-ℕ n) = add-ℕ (triangular-number n) (succ-ℕ n)

factorial : ℕ → ℕ
factorial zero-ℕ = one-ℕ
factorial (succ-ℕ m) = mul-ℕ (factorial m) (succ-ℕ m)

-- Exercise 3.4

_choose_ : ℕ → ℕ → ℕ
zero-ℕ choose zero-ℕ = one-ℕ
zero-ℕ choose succ-ℕ k = zero-ℕ
(succ-ℕ n) choose zero-ℕ = one-ℕ
(succ-ℕ n) choose (succ-ℕ k) = add-ℕ (n choose k) (n choose (succ-ℕ k))


-- Exercise 3.5

Fibonacci : ℕ → ℕ
Fibonacci zero-ℕ = zero-ℕ
Fibonacci (succ-ℕ zero-ℕ) = one-ℕ
Fibonacci (succ-ℕ (succ-ℕ n)) = add-ℕ (Fibonacci n) (Fibonacci (succ-ℕ n))

{- The above definition of the Fibonacci sequence uses Agda's rather strong
   pattern matching definitions. Below, we will give a definition of the 
   Fibonacci sequence in terms of ind-ℕ. In particular, the following is a
   solution that can be given in terms of the material in the book. 

   The problem with defining the Fibonacci sequence using ind-ℕ, is that ind-ℕ
   doesn't give us a way to refer to both (F n) and (F (succ-ℕ n)). So, we have
   to give a workaround, where we store two values in the Fibonacci sequence
   at once.

   The basic idea is that we define a sequence of pairs of integers, which will
   be consecutive Fibonacci numbers. This would be a function of type

   ℕ → ℕ².

   Such a function is easy to give with induction, using the map ℕ² → ℕ² that
   takes a pair (m,n) to the pair (n,n+m). Starting the iteration with (0,1)
   we obtain the Fibonacci sequence by taking the first projection.

   However, we haven't defined cartesian products or booleans yet. Therefore
   we mimic the above idea, using ℕ → ℕ instead of ℕ². -}

shift-one : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-one n f = ind-ℕ n (λ x y → f x)

shift-two : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-two m n f = shift-one m (shift-one n f)

Fibo-zero-ℕ : ℕ → ℕ
Fibo-zero-ℕ = shift-two zero-ℕ one-ℕ (const ℕ ℕ zero-ℕ)

Fibo-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
Fibo-succ-ℕ f =
  shift-two (f one-ℕ) (add-ℕ (f one-ℕ) (f zero-ℕ)) (const ℕ ℕ zero-ℕ)

Fibo-function : ℕ → ℕ → ℕ
Fibo-function =
  ind-ℕ
    ( Fibo-zero-ℕ)
    ( λ n → Fibo-succ-ℕ)

Fibo : ℕ → ℕ
Fibo k = Fibo-function k zero-ℕ

-- Exercise 3.6

div-two-ℕ : ℕ → ℕ
div-two-ℕ zero-ℕ = zero-ℕ
div-two-ℕ (succ-ℕ zero-ℕ) = zero-ℕ
div-two-ℕ (succ-ℕ (succ-ℕ n)) = succ-ℕ (div-two-ℕ n)

div-two-zero-ℕ : ℕ → ℕ
div-two-zero-ℕ = const ℕ ℕ zero-ℕ

div-two-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
div-two-succ-ℕ f =
  shift-two (f one-ℕ) (succ-ℕ (f zero-ℕ)) (const ℕ ℕ zero-ℕ)

div-two-function : ℕ → ℕ → ℕ
div-two-function = ind-ℕ div-two-zero-ℕ (λ n → div-two-succ-ℕ)

div-two-ℕ' : ℕ → ℕ
div-two-ℕ' n = div-two-function n zero-ℕ
