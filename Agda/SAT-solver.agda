{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module SAT-solver where

import 12-univalence
open 12-univalence public

{- The literates are atomic propositions or negations thereof. We simply use 
   the natural numbers to encode the atomic propositions, and we use the 
   booleans to tell whether it should be negated or not. -}

Literate = ℕ × bool

neg-Literate : Literate → Literate
neg-Literate (pair n b) = pair n (neg-𝟚 b)

zero-true-Literate : Literate
zero-true-Literate = pair zero-ℕ true

truth-value-Literate : (ℕ → bool) → Literate → bool
truth-value-Literate f (pair n true) = f n
truth-value-Literate f (pair n false) = neg-𝟚 (f n)

bool-Eq-ℕ : ℕ → ℕ → bool
bool-Eq-ℕ zero-ℕ zero-ℕ = true
bool-Eq-ℕ zero-ℕ (succ-ℕ n) = false
bool-Eq-ℕ (succ-ℕ m) zero-ℕ = false
bool-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = bool-Eq-ℕ m n

bool-Eq-𝟚 : bool → bool → bool
bool-Eq-𝟚 true true = true
bool-Eq-𝟚 true false = false
bool-Eq-𝟚 false true = false
bool-Eq-𝟚 false false = true

bool-Eq-Literate : Literate → Literate → bool
bool-Eq-Literate (pair m x) (pair n y) =
  conjunction-𝟚 (bool-Eq-ℕ m n) (bool-Eq-𝟚 x y)

{- Clauses are finite disjunctions of literates. We simply encode them using
   lists of literates. -}

Clause = list Literate

clause-Literate : Literate → Clause
clause-Literate l = cons l nil

is-literate-Clause : Clause → UU lzero
is-literate-Clause c = Σ Literate (λ l → Id (clause-Literate l) c)

zero-true-Clause = clause-Literate zero-true-Literate

truth-value-Clause : (ℕ → bool) → Clause → bool
truth-value-Clause f nil = false
truth-value-Clause f (cons l c) =
  disjunction-𝟚 (truth-value-Literate f l) (truth-value-Clause f c)

contains-Clause : Literate → Clause → bool
contains-Clause l nil = false
contains-Clause l (cons l' c) =
  disjunction-𝟚 (bool-Eq-Literate l l') (contains-Clause l c)

if-then-else : {l : Level} {A : UU l} → bool → A → A → A
if-then-else true x y = x
if-then-else false x y = y

if-then-else-dep :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  (b : bool) {x y : A} (u : Id b true → B x) (v : Id b false → B y) →
  B (if-then-else b x y)
if-then-else-dep B true u v = u refl
if-then-else-dep B false u v = v refl

{- We write a function that simplifies a clause in the following way:
    * simplified clauses do not contain any literate more than once.
    * if a simplified clause contains a literate and its negation, then it is
      of the form l ∨ ¬l. -}

simplify-Clause : Clause → Clause
simplify-Clause nil = nil
simplify-Clause (cons l c) =
  if-then-else
    ( contains-Clause (neg-Literate l) c)
    ( cons l (cons (neg-Literate l) nil))
    ( if-then-else
      ( contains-Clause l c)
      ( simplify-Clause c)
      ( cons l (simplify-Clause c)))

is-satisfiable-Clause : Clause → UU lzero
is-satisfiable-Clause c = Σ (ℕ → bool) (λ f → Id (truth-value-Clause f c) true)

{- We show that any non-empty disjunctive clause is satisfiable. -}

right-true-law-disjunction-𝟚 : (b : bool) → Id (disjunction-𝟚 b true) true
right-true-law-disjunction-𝟚 true = refl
right-true-law-disjunction-𝟚 false = refl

left-true-law-disjunction-𝟚 : (b : bool) → Id (disjunction-𝟚 true b) true
left-true-law-disjunction-𝟚 true = refl
left-true-law-disjunction-𝟚 false = refl

is-satisfiable-cons-Clause :
  ( l : Literate) (c : Clause) → is-satisfiable-Clause (cons l c)
is-satisfiable-cons-Clause (pair n true) c =
  pair
    ( const ℕ bool true)
    ( left-true-law-disjunction-𝟚 (truth-value-Clause (const ℕ bool true) c))
is-satisfiable-cons-Clause (pair n false) c =
  pair
    ( const ℕ bool false)
    ( left-true-law-disjunction-𝟚 (truth-value-Clause (const ℕ bool false) c))

{- Formulas in conjunctive normal form are finite conjunctions of clauses, as
   defined above. Therefore we encode them as lists of clauses. -}

CNF = list Clause

truth-value-CNF : (ℕ → bool) → CNF → bool
truth-value-CNF f nil = true
truth-value-CNF f (cons c φ) =
  conjunction-𝟚 (truth-value-Clause f c) (truth-value-CNF f φ)

{- A formula φ is in conjunctive normal form is said to be satisfiable if there
   is a map ℕ → bool which evaluates φ to true. -}

is-satisfiable-CNF : CNF → UU lzero
is-satisfiable-CNF φ = Σ (ℕ → bool) (λ f → Id (truth-value-CNF f φ) true)

contains-CNF : (l : Literate) (φ : CNF) → bool
contains-CNF l nil = false
contains-CNF l (cons c φ) =
  disjunction-𝟚 (contains-Clause l c) (contains-CNF l φ)

contains

simplify-CNF : CNF → CNF
simplify-CNF nil = nil
simplify-CNF (cons c φ) = cons (simplify-Clause c) (simplify-CNF φ)

