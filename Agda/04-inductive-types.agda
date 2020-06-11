{-# OPTIONS --without-K --exact-split --safe #-}

module 04-inductive-types where

import 03-natural-numbers
open 03-natural-numbers public

--------------------------------------------------------------------------------

-- Section 4.2 The unit type

-- Definition 4.2.1

data unit : UU lzero where
  star : unit
  
𝟙 = unit

ind-unit : {i : Level} {P : unit → UU i} → P star → ((x : unit) → P x)
ind-unit p star = p

--------------------------------------------------------------------------------

-- Section 4.3 The empty type

-- Definition 4.3.1

data empty : UU lzero where

𝟘 = empty

ind-empty : {i : Level} {P : empty → UU i} → ((x : empty) → P x)
ind-empty ()

ex-falso : {i : Level} {A : UU i} → empty → A
ex-falso = ind-empty

-- Definition 4.3.2

¬ : {i : Level} → UU i → UU i
¬ A = A → empty

-- Proposition 4.3.3

functor-neg : {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬ Q → ¬ P)
functor-neg f nq p = nq (f p)

--------------------------------------------------------------------------------

-- Section 4.4 The booleans

-- Definition 4.4.1

data bool : UU lzero where
  true false : bool

-- Example 4.4.2

neg-𝟚 : bool → bool
neg-𝟚 true = false
neg-𝟚 false = true

conjunction-𝟚 : bool → (bool → bool)
conjunction-𝟚 true true = true
conjunction-𝟚 true false = false
conjunction-𝟚 false true = false
conjunction-𝟚 false false = false

disjunction-𝟚 : bool → (bool → bool)
disjunction-𝟚 true true = true
disjunction-𝟚 true false = true
disjunction-𝟚 false true = true
disjunction-𝟚 false false = false

--------------------------------------------------------------------------------

-- Section 4.5 Coproducts

-- Definition 4.5.1

data coprod {i j : Level} (A : UU i) (B : UU j) : UU (i ⊔ j)  where
  inl : A → coprod A B
  inr : B → coprod A B

ind-coprod : {i j k : Level} {A : UU i} {B : UU j} (C : coprod A B → UU k) →
  ((x : A) → C (inl x)) → ((y : B) → C (inr y)) →
  (t : coprod A B) → C t
ind-coprod C f g (inl x) = f x
ind-coprod C f g (inr x) = g x

-- Remark 4.5.2

functor-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'} →
  (A → A') → (B → B') → coprod A B → coprod A' B'
functor-coprod f g (inl x) = inl (f x)
functor-coprod f g (inr y) = inr (g y)

-- Proposition 4.5.3

coprod-elim-left :
  {i j : Level} (A : UU i) (B : UU j) →
  ¬ B → coprod A B → A
coprod-elim-left A B nb (inl a) = a
coprod-elim-left A B nb (inr b) = ex-falso (nb b)

coprod-elim-right :
  {i j : Level} (A : UU i) (B : UU j) →
  ¬ A → coprod A B → B
coprod-elim-right A B na (inl a) = ex-falso (na a)
coprod-elim-right A B na (inr b) = b

--------------------------------------------------------------------------------

-- Section 4.6 Dependent pair types

-- Definition 4.6.1

data Σ {i j : Level} (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
  pair : (x : A) → (B x → Σ A B)

ind-Σ : {i j k : Level} {A : UU i} {B : A → UU j} {C : Σ A B → UU k} →
  ((x : A) (y : B x) → C (pair x y)) → ((t : Σ A B) → C t)
ind-Σ f (pair x y) = f x y

-- Remark 4.6.2

ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((t : Σ A B) → C t) → (x : A) (y : B x) → C (pair x y)
ev-pair f x y = f (pair x y)

-- Definition 4.6.3

pr1 : {i j : Level} {A : UU i} {B : A → UU j} → Σ A B → A
pr1 (pair a b) = a

pr2 : {i j : Level} {A : UU i} {B : A → UU j} → (t : Σ A B) → B (pr1 t)
pr2 (pair a b) = b

-- Definition 4.6.4

prod : {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
prod A B = Σ A (λ a → B)

pair' :
  {i j : Level} {A : UU i} {B : UU j} → A → B → prod A B
pair' = pair

_×_ :  {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A × B = prod A B

--------------------------------------------------------------------------------

-- Section 4.7 The type of integers

-- Definition 4.7.1

-- The type of integers

ℤ : UU lzero
ℤ = coprod ℕ (coprod unit ℕ)

-- Inclusion of the negative integers

in-neg : ℕ → ℤ
in-neg n = inl n

-- Negative one

neg-one-ℤ : ℤ
neg-one-ℤ = in-neg zero-ℕ

-- Zero

zero-ℤ : ℤ
zero-ℤ = inr (inl star)

-- One

one-ℤ : ℤ
one-ℤ = inr (inr zero-ℕ)

-- Inclusion of the positive integers

in-pos : ℕ → ℤ
in-pos n = inr (inr n)

-- Proposition 4.7.2

ind-ℤ :
  {i : Level} (P : ℤ → UU i) →
  P neg-one-ℤ → ((n : ℕ) → P (inl n) → P (inl (succ-ℕ n))) →
  P zero-ℤ →
  P one-ℤ → ((n : ℕ) → P (inr (inr (n))) → P (inr (inr (succ-ℕ n)))) →
  (k : ℤ) → P k
ind-ℤ P p-1 p-S p0 p1 pS (inl zero-ℕ) = p-1
ind-ℤ P p-1 p-S p0 p1 pS (inl (succ-ℕ x)) =
  p-S x (ind-ℤ P p-1 p-S p0 p1 pS (inl x))
ind-ℤ P p-1 p-S p0 p1 pS (inr (inl star)) = p0
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr zero-ℕ)) = p1
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (succ-ℕ x))) =
  pS x (ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (x))))

-- Definition 4.7.3

succ-ℤ : ℤ → ℤ
succ-ℤ (inl zero-ℕ) = zero-ℤ
succ-ℤ (inl (succ-ℕ x)) = inl x
succ-ℤ (inr (inl star)) = one-ℤ
succ-ℤ (inr (inr x)) = inr (inr (succ-ℕ x))

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 4.1 (a)

pred-ℤ : ℤ → ℤ
pred-ℤ (inl x) = inl (succ-ℕ x)
pred-ℤ (inr (inl star)) = inl zero-ℕ
pred-ℤ (inr (inr zero-ℕ)) = inr (inl star)
pred-ℤ (inr (inr (succ-ℕ x))) = inr (inr x)

-- Exercise 4.1 (b)

-- Addition on ℤ

add-ℤ : ℤ → ℤ → ℤ
add-ℤ (inl zero-ℕ) l = pred-ℤ l
add-ℤ (inl (succ-ℕ x)) l = pred-ℤ (add-ℤ (inl x) l)
add-ℤ (inr (inl star)) l = l
add-ℤ (inr (inr zero-ℕ)) l = succ-ℤ l
add-ℤ (inr (inr (succ-ℕ x))) l = succ-ℤ (add-ℤ (inr (inr x)) l)

-- The negative of an integer

neg-ℤ : ℤ → ℤ
neg-ℤ (inl x) = inr (inr x)
neg-ℤ (inr (inl star)) = inr (inl star)
neg-ℤ (inr (inr x)) = inl x

-- Exercise 4.1 (c)

-- Multiplication on ℤ

mul-ℤ : ℤ → ℤ → ℤ
mul-ℤ (inl zero-ℕ) l = neg-ℤ l
mul-ℤ (inl (succ-ℕ x)) l = add-ℤ (neg-ℤ l) (mul-ℤ (inl x) l)
mul-ℤ (inr (inl star)) l = zero-ℤ
mul-ℤ (inr (inr zero-ℕ)) l = l
mul-ℤ (inr (inr (succ-ℕ x))) l = add-ℤ l (mul-ℤ (inr (inr x)) l)

-- Exercise 4.2

¬¬ : {l : Level} → UU l → UU l
¬¬ P = ¬ (¬ P)

¬¬¬ : {l : Level} → UU l → UU l
¬¬¬ P = ¬ (¬ (¬ P))

-- Exercise 4.2 (a)

no-fixed-points-neg :
  {l1 : Level} (A : UU l1) → ¬ ((A → ¬ A) × (¬ A → A))
no-fixed-points-neg A (pair f g) =
  ( λ (h : ¬ A) → h (g h)) (λ (a : A) → f a a)

-- Exercise 4.2 (b)

intro-dn : {l : Level} {P : UU l} → P → ¬¬ P
intro-dn p f = f p

-- Exercise 4.2 (c)

functor-dn : {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬¬ P → ¬¬ Q)
functor-dn f = functor-neg (functor-neg f)

-- Exercise 4.2 (d)

{- In this exercise we were asked to show that (A + ¬A) implies (¬¬A → A). In 
   other words, we get double negation elimination for the types that are 
   decidable. -}

double-negation-elim-is-decidable :
  {i : Level} (P : UU i) → coprod P (¬ P) → (¬¬ P → P)
double-negation-elim-is-decidable P (inl x) p = x
double-negation-elim-is-decidable P (inr x) p = ind-empty (p x)

-- Exercise 4.2 (e)

dn-is-decidable : {l : Level} {P : UU l} → ¬¬ (coprod P (¬ P))
dn-is-decidable {P = P} f =
  functor-neg (inr {A = P} {B = ¬ P}) f
    ( functor-neg (inl {A = P} {B = ¬ P}) f)

-- Exercise 4.2 (f)

dn-dn-elim : {l : Level} {P : UU l} → ¬¬ (¬¬ P → P)
dn-dn-elim {P = P} f =
  ( λ (np : ¬ P) → f (λ (nnp : ¬¬ P) → ind-empty {P = λ x → P} (nnp np)))
    ( λ (p : P) → f (λ (nnp : ¬¬ P) → p))

-- Exercise 4.2 (g)

tautology-4-2-f :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ (((P → Q) → P) → P)
tautology-4-2-f {P = P} {Q} f =
  ( λ (np : ¬ P) → f (λ h → h (λ p → ex-falso (np p))))
  ( λ (p : P) → f (λ h → p))

-- Exercise 4.2 (h)

dn-linearity-implication :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ (coprod (P → Q) (Q → P))
dn-linearity-implication {P = P} {Q = Q} f =
  ( λ (np : ¬ P) →
    functor-neg (inl {A = P → Q} {B = Q → P}) f (λ p → ind-empty (np p)))
    ( λ (p : P) →
      functor-neg (inr {A = P → Q} {B = Q → P}) f (λ q → p))

-- Exercise 4.2 (i)

dn-elim-neg : {l : Level} (P : UU l) → ¬¬¬ P → ¬ P
dn-elim-neg P f p = f (λ g → g p)

-- Exercise 4.2 (j)

dn-extend :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → ¬¬ Q) → (¬¬ P → ¬¬ Q)
dn-extend {P = P} {Q = Q} f = dn-elim-neg (¬ Q) ∘ (functor-dn f)

-- Exercise 4.2 (k)

dn-elim-exp :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ (P → ¬¬ Q) → (P → ¬¬ Q)
dn-elim-exp {P = P} {Q = Q} f p =
  dn-elim-neg (¬ Q) (functor-dn (λ (g : P → ¬¬ Q) → g p) f)

-- Exercise 4.2 (l)

dn-elim-prod :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ ((¬¬ P) × (¬¬ Q)) → (¬¬ P) × (¬¬ Q)
dn-elim-prod {P = P} {Q = Q} f =
  pair
    ( dn-elim-neg (¬ P) (functor-dn pr1 f))
    ( dn-elim-neg (¬ Q) (functor-dn pr2 f))

-- Exercise 4.3

-- Exercise 4.3 (a)

data list {l : Level} (A : UU l) : UU l where
  nil : list A
  cons : A → list A → list A

in-list : {l : Level} {A : UU l} → A → list A
in-list a = cons a nil

-- Exercise 4.3 (b)

fold-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) (μ : A → (B → B)) →
  list A → B
fold-list b μ nil = b
fold-list b μ (cons a l) = μ a (fold-list b μ l)

-- Exercise 4.3 (c)

length-list :
  {l : Level} {A : UU l} → list A → ℕ
length-list = fold-list zero-ℕ (λ a → succ-ℕ)

-- Exercise 4.3 (d)

sum-list-ℕ :
  list ℕ → ℕ
sum-list-ℕ = fold-list zero-ℕ add-ℕ

-- Exercise 4.3 (e)

concat-list :
  {l : Level} {A : UU l} → list A → (list A → list A)
concat-list {l} {A} = fold-list id (λ a f → (cons a) ∘ f)

-- Exercise 4.3 (f)

flatten-list :
  {l : Level} {A : UU l} → list (list A) → list A
flatten-list = fold-list nil concat-list

-- Exercise 4.3 (g)

reverse-list :
  {l : Level} {A : UU l} → list A → list A
reverse-list nil = nil
reverse-list (cons a l) = concat-list (reverse-list l) (in-list a)
