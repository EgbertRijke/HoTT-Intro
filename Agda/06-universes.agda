{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module 06-universes where

import 05-identity-types
open 05-identity-types public

-- Section 4.1 Type theoretic universes

{- Because of Agda's design we already had to introduce universes in the very
   first file. What is left to do here is to formalize the examples of
   structured types. -}

-- Pointed types
UU-pt : (i : Level) → UU (lsuc i)
UU-pt i = Σ (UU i) (λ X → X)
 
-- Graphs
Gph : (i : Level) → UU (lsuc i)
Gph i = Σ (UU i) (λ X → (X → X → (UU i)))

-- Reflexive graphs
rGph : (i : Level) →  UU (lsuc i)
rGph i = Σ (UU i) (λ X → Σ (X → X → (UU i)) (λ R → (x : X) → R x x))

-- Section 4.2 Defining families and relations using a universe

-- Finite sets
Fin : ℕ → UU lzero
Fin zero-ℕ = empty
Fin (succ-ℕ n) = coprod (Fin n) unit

-- Observational equality on the natural numbers
Eq-ℕ : ℕ → (ℕ → UU lzero)
Eq-ℕ zero-ℕ zero-ℕ = 𝟙
Eq-ℕ zero-ℕ (succ-ℕ n) = 𝟘
Eq-ℕ (succ-ℕ m) zero-ℕ = 𝟘
Eq-ℕ (succ-ℕ m) (succ-ℕ n) = Eq-ℕ m n

-- Exercises

-- Exercise 3.1

{- In this exercise we were asked to show that (A + ¬A) implies (¬¬A → A). In 
   other words, we get double negation elimination for the types that are 
   decidable. -}

is-decidable : {l : Level} (A : UU l) → UU l
is-decidable A = coprod A (¬ A)

double-negation-elim-is-decidable :
  {i : Level} (A : UU i) → is-decidable A → (¬ (¬ A) → A)
double-negation-elim-is-decidable A (inl x) p = x
double-negation-elim-is-decidable A (inr x) p = ind-empty (p x)

-- Exercise 3.3

{- In this exercise we were asked to show that the observational equality on ℕ 
   is an equivalence relation. -}
   
refl-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
refl-Eq-ℕ zero-ℕ = star
refl-Eq-ℕ (succ-ℕ n) = refl-Eq-ℕ n

symmetric-Eq-ℕ : (m n : ℕ) → Eq-ℕ m n → Eq-ℕ n m
symmetric-Eq-ℕ zero-ℕ zero-ℕ t = t
symmetric-Eq-ℕ zero-ℕ (succ-ℕ n) t = t
symmetric-Eq-ℕ (succ-ℕ n) zero-ℕ t = t
symmetric-Eq-ℕ (succ-ℕ m) (succ-ℕ n) t = symmetric-Eq-ℕ m n t

transitive-Eq-ℕ : (l m n : ℕ) → Eq-ℕ l m → Eq-ℕ m n → Eq-ℕ l n
transitive-Eq-ℕ zero-ℕ zero-ℕ zero-ℕ s t = star
transitive-Eq-ℕ (succ-ℕ n) zero-ℕ zero-ℕ s t = ind-empty s
transitive-Eq-ℕ zero-ℕ (succ-ℕ n) zero-ℕ s t = ind-empty s
transitive-Eq-ℕ zero-ℕ zero-ℕ (succ-ℕ n) s t = ind-empty t
transitive-Eq-ℕ (succ-ℕ l) (succ-ℕ m) zero-ℕ s t = ind-empty t
transitive-Eq-ℕ (succ-ℕ l) zero-ℕ (succ-ℕ n) s t = ind-empty s
transitive-Eq-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) s t = ind-empty s
transitive-Eq-ℕ (succ-ℕ l) (succ-ℕ m) (succ-ℕ n) s t = transitive-Eq-ℕ l m n s t

-- Exercise 3.4

{- In this exercise we were asked to show that observational equality on the 
   natural numbers is the least reflexive relation, in the sense that it 
   implies all other reflexive relation. As we will see once we introduce the 
   identity type, it follows that observationally equal natural numbers can be 
   identified. -}

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

-- Exercise 3.5

{- In this exercise we were asked to show that any function on the natural 
   numbers preserves observational equality. The quick solution uses the fact 
   that observational equality is the least reflexive relation. -}
   
preserve_Eq-ℕ : (f : ℕ → ℕ) (n m : ℕ) → (Eq-ℕ n m) → (Eq-ℕ (f n) (f m))
preserve_Eq-ℕ f =
  least-reflexive-Eq-ℕ
    ( λ x y → Eq-ℕ (f x) (f y))
    ( λ x → refl-Eq-ℕ (f x))

-- Exercise 3.6

{- In this exercise we were asked to construct the relations ≤ and < on the 
   natural numbers, and show basic properties about them. -}

-- The definition of ≤ 

leq-ℕ : ℕ → ℕ → UU lzero
leq-ℕ zero-ℕ m = unit
leq-ℕ (succ-ℕ n) zero-ℕ = empty
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m

_≤_ = leq-ℕ

leq-zero-ℕ :
  (n : ℕ) → leq-ℕ zero-ℕ n
leq-zero-ℕ zero-ℕ = star
leq-zero-ℕ (succ-ℕ n) = star

-- The definition of <

le-ℕ : ℕ → ℕ → UU lzero
le-ℕ m zero-ℕ = empty
le-ℕ zero-ℕ (succ-ℕ m) = unit
le-ℕ (succ-ℕ n) (succ-ℕ m) = le-ℕ n m

_<_ = le-ℕ

reflexive-leq-ℕ : (n : ℕ) → n ≤ n
reflexive-leq-ℕ zero-ℕ = star
reflexive-leq-ℕ (succ-ℕ n) = reflexive-leq-ℕ n

anti-reflexive-le-ℕ : (n : ℕ) → ¬ (n < n)
anti-reflexive-le-ℕ zero-ℕ = ind-empty
anti-reflexive-le-ℕ (succ-ℕ n) = anti-reflexive-le-ℕ n

transitive-leq-ℕ :
  (n m l : ℕ) → (n ≤ m) → (m ≤ l) → (n ≤ l)
transitive-leq-ℕ zero-ℕ m l p q = star
transitive-leq-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-leq-ℕ n m l p q

transitive-le-ℕ : (n m l : ℕ) → (le-ℕ n m) → (le-ℕ m l) → (le-ℕ n l)
transitive-le-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ l) p q = star
transitive-le-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-le-ℕ n m l p q

succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
succ-le-ℕ zero-ℕ = star
succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n

-- Exercise 3.7

{- With the construction of the divisibility relation we open the door to basic
   number theory. -}
   
divides : (d n : ℕ) → UU lzero
divides d n = Σ ℕ (λ m → Eq-ℕ (mul-ℕ d m) n)

-- Exercise 3.8

{- In this exercise we were asked to construct observational equality on the 
   booleans. This construction is analogous to, but simpler than, the 
   construction of observational equality on the natural numbers. -}

Eq-𝟚 : bool → bool → UU lzero
Eq-𝟚 true true = unit
Eq-𝟚 true false = empty
Eq-𝟚 false true = empty
Eq-𝟚 false false = unit

reflexive-Eq-𝟚 : (x : bool) → Eq-𝟚 x x
reflexive-Eq-𝟚 true = star
reflexive-Eq-𝟚 false = star

least-reflexive-Eq-𝟚 : {i : Level}
  (R : bool → bool → UU i) (ρ : (x : bool) → R x x)
  (x y : bool) → Eq-𝟚 x y → R x y
least-reflexive-Eq-𝟚 R ρ true true p = ρ true
least-reflexive-Eq-𝟚 R ρ true false p = ind-empty p
least-reflexive-Eq-𝟚 R ρ false true p = ind-empty p
least-reflexive-Eq-𝟚 R ρ false false p = ρ false

-- Exercise 3.10

{- In this exercise we were asked to define the relations ≤ and < on the 
   integers. As a criterion of correctness, we were then also asked to show 
   that the type of all integers l satisfying k ≤ l satisfy the induction 
   principle of the natural numbers. -}

is-non-negative-ℤ : ℤ → UU lzero
is-non-negative-ℤ (inl x) = empty
is-non-negative-ℤ (inr k) = unit

diff-ℤ : ℤ → ℤ → ℤ
diff-ℤ k l = add-ℤ (neg-ℤ k) l

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

-- We prove that the induction principle for ℕ implies strong induction.

zero-ℕ-leq-ℕ :
  (n : ℕ) → leq-ℕ zero-ℕ n
zero-ℕ-leq-ℕ n = star

fam-strong-ind-ℕ :
  { l : Level} → (ℕ → UU l) → ℕ → UU l
fam-strong-ind-ℕ P n = (m : ℕ) → (leq-ℕ m n) → P m

zero-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) → P zero-ℕ → fam-strong-ind-ℕ P zero-ℕ
zero-strong-ind-ℕ P p0 zero-ℕ t = p0
zero-strong-ind-ℕ P p0 (succ-ℕ m) ()

succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  ( k : ℕ) → (fam-strong-ind-ℕ P k) → (fam-strong-ind-ℕ P (succ-ℕ k))
succ-strong-ind-ℕ P pS k f zero-ℕ t = f zero-ℕ (zero-ℕ-leq-ℕ k)
succ-strong-ind-ℕ P pS k f (succ-ℕ m) t =
  pS m (λ m' t' → f m' (transitive-leq-ℕ m' m k t' t))

conclusion-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( ( n : ℕ) → fam-strong-ind-ℕ P n) → (n : ℕ) → P n
conclusion-strong-ind-ℕ P f n = f n n (reflexive-leq-ℕ n)

induction-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( fam-strong-ind-ℕ P zero-ℕ) →
  ( (k : ℕ) → (fam-strong-ind-ℕ P k) → (fam-strong-ind-ℕ P (succ-ℕ k))) →
  ( n : ℕ) → fam-strong-ind-ℕ P n
induction-strong-ind-ℕ P q0 qS zero-ℕ = q0
induction-strong-ind-ℕ P q0 qS (succ-ℕ n) = qS n
  ( induction-strong-ind-ℕ P q0 qS n)

strong-ind-ℕ :
  { l : Level} → (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) → P n
strong-ind-ℕ P p0 pS = 
  conclusion-strong-ind-ℕ P
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS))

-- We show that induction on ℕ implies ordinal induction.

fam-ordinal-ind-ℕ :
  { l : Level} → (ℕ → UU l) → ℕ → UU l
fam-ordinal-ind-ℕ P n = (m : ℕ) → (le-ℕ m n) → P m

le-zero-ℕ :
  (m : ℕ) → (le-ℕ m zero-ℕ) → empty
le-zero-ℕ zero-ℕ ()
le-zero-ℕ (succ-ℕ m) ()

zero-ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) → fam-ordinal-ind-ℕ P zero-ℕ
zero-ordinal-ind-ℕ P m t = ind-empty (le-zero-ℕ m t)

le-one-ℕ :
  (n : ℕ) → le-ℕ (succ-ℕ n) one-ℕ → empty
le-one-ℕ zero-ℕ ()
le-one-ℕ (succ-ℕ n) ()

transitive-le-ℕ' :
  (k l m : ℕ) → (le-ℕ k l) → (le-ℕ l (succ-ℕ m)) → le-ℕ k m
transitive-le-ℕ' zero-ℕ zero-ℕ m () s
transitive-le-ℕ' (succ-ℕ k) zero-ℕ m () s
transitive-le-ℕ' zero-ℕ (succ-ℕ l) zero-ℕ star s = ind-empty (le-one-ℕ l s)
transitive-le-ℕ' (succ-ℕ k) (succ-ℕ l) zero-ℕ t s = ind-empty (le-one-ℕ l s)
transitive-le-ℕ' zero-ℕ (succ-ℕ l) (succ-ℕ m) star s = star
transitive-le-ℕ' (succ-ℕ k) (succ-ℕ l) (succ-ℕ m) t s =
  transitive-le-ℕ' k l m t s

succ-ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( (n : ℕ) → (fam-ordinal-ind-ℕ P n) → P n) →
  ( k : ℕ) → fam-ordinal-ind-ℕ P k → fam-ordinal-ind-ℕ P (succ-ℕ k)
succ-ordinal-ind-ℕ P f k g m t =
  f m (λ m' t' → g m' (transitive-le-ℕ' m' m k t' t))

induction-ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( qS : (k : ℕ) → fam-ordinal-ind-ℕ P k → fam-ordinal-ind-ℕ P (succ-ℕ k))
  ( n : ℕ) → fam-ordinal-ind-ℕ P n
induction-ordinal-ind-ℕ P qS zero-ℕ = zero-ordinal-ind-ℕ P 
induction-ordinal-ind-ℕ P qS (succ-ℕ n) =
  qS n (induction-ordinal-ind-ℕ P qS n)

conclusion-ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  (( n : ℕ) → fam-ordinal-ind-ℕ P n) → (n : ℕ) → P n
conclusion-ordinal-ind-ℕ P f n = f (succ-ℕ n) n (succ-le-ℕ n)

ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( (n : ℕ) → (fam-ordinal-ind-ℕ P n) → P n) →
  ( n : ℕ) → P n
ordinal-ind-ℕ P f =
  conclusion-ordinal-ind-ℕ P
    ( induction-ordinal-ind-ℕ P (succ-ordinal-ind-ℕ P f))

-- Extra material

-- We show that ℕ is an ordered semi-ring

leq-eq-ℕ : {m m' n n' : ℕ} → Id m m' → Id n n' → leq-ℕ m n → leq-ℕ m' n'
leq-eq-ℕ refl refl = id

right-law-leq-add-ℕ : (k m n : ℕ) → leq-ℕ m n → leq-ℕ (add-ℕ k m) (add-ℕ k n)
right-law-leq-add-ℕ zero-ℕ m n = id
right-law-leq-add-ℕ (succ-ℕ k) m n H = right-law-leq-add-ℕ k m n H

left-law-leq-add-ℕ : (k m n : ℕ) → leq-ℕ m n → leq-ℕ (add-ℕ m k) (add-ℕ n k)
left-law-leq-add-ℕ k m n H =
  leq-eq-ℕ
    ( commutative-add-ℕ k m)
    ( commutative-add-ℕ k n)
    ( right-law-leq-add-ℕ k m n H)

preserves-leq-add-ℕ :
  {m m' n n' : ℕ} → leq-ℕ m m' → leq-ℕ n n' → leq-ℕ (add-ℕ m n) (add-ℕ m' n')
preserves-leq-add-ℕ {m} {m'} {n} {n'} H K =
  transitive-leq-ℕ
    ( add-ℕ m n)
    ( add-ℕ m' n)
    ( add-ℕ m' n')
    ( left-law-leq-add-ℕ n m m' H)
    ( right-law-leq-add-ℕ m' n n' K)

right-law-leq-mul-ℕ : (k m n : ℕ) → leq-ℕ m n → leq-ℕ (mul-ℕ k m) (mul-ℕ k n)
right-law-leq-mul-ℕ zero-ℕ m n H = star
right-law-leq-mul-ℕ (succ-ℕ k) m n H =
  preserves-leq-add-ℕ
    { m = mul-ℕ k m}
    { m' = mul-ℕ k n}
    ( right-law-leq-mul-ℕ k m n H) H

left-law-leq-mul-ℕ : (k m n : ℕ) → leq-ℕ m n → leq-ℕ (mul-ℕ m k) (mul-ℕ n k)
left-law-leq-mul-ℕ k m n H =
  leq-eq-ℕ
    ( commutative-mul-ℕ k m)
    ( commutative-mul-ℕ k n)
    ( right-law-leq-mul-ℕ k m n H)

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
  path-ind-Eq-ℕ (succ-fam-Eq-ℕ R) (succ-refl-fam-Eq-ℕ R ρ) m n e

comp-path-ind-Eq-ℕ :
  {i : Level} (R : (m n : ℕ) → Eq-ℕ m n → UU i)
  ( ρ : (n : ℕ) → R n n (refl-Eq-ℕ n)) →
  ( n : ℕ) → Id (path-ind-Eq-ℕ R ρ n n (refl-Eq-ℕ n)) (ρ n)
comp-path-ind-Eq-ℕ R ρ zero-ℕ = refl
comp-path-ind-Eq-ℕ R ρ (succ-ℕ n) =
  comp-path-ind-Eq-ℕ (succ-fam-Eq-ℕ R) (succ-refl-fam-Eq-ℕ R ρ) n
