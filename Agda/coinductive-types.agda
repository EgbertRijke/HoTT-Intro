{-# OPTIONS --cubical #-}

open import 16-number-theory public

{- streams -}

record stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : stream A

open stream public

from : ℕ → stream ℕ
hd (from n) = n
tl (from n) = from (succ-ℕ n)

map-stream : {A B : Set} → (A → B) → stream A → stream B
hd (map-stream f xs) = f (hd xs)
tl (map-stream f xs) = map-stream f (tl xs)

list-stream :
  {A : Set} → stream A → ℕ → list A
list-stream xs zero-ℕ = nil
list-stream xs (succ-ℕ n) = cons (hd xs) (list-stream xs n)

record ℕ∞ : Set where
  coinductive
  field
    pred∞ : coprod ℕ∞ unit

zero-ℕ∞ : ℕ∞
pred∞ zero-ℕ∞ = {!inr star!}
