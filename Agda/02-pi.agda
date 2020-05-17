{-# OPTIONS --without-K --exact-split --safe #-}

module 02-pi where

import 00-preamble
open 00-preamble public

--------------------------------------------------------------------------------

-- Section 2.3 The identity function, composition, and their laws

-- Definition 2.3.1
id : {i : Level} {A : UU i} → A → A
id a = a 

-- Definition 2.3.2
_∘_ :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} →
  (B → C) → ((A → B) → (A → C))
(g ∘ f) a = g (f a)

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 2.3
const : {i j : Level} (A : UU i) (B : UU j) (b : B) → A → B
const A B b x = b

-- Exercise 2.4
Π-swap : {i j k : Level} {A : UU i} {B : UU j} {C : A → (B → UU k)} →
  ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
Π-swap f y x = f x y
