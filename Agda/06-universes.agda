{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module 06-universes where

import 05-identity-types
open 05-identity-types public

-- Section 4.1 Type theoretic universes

{- Because of Agda's design we already had to introduce universes in the very
   first file. What is left to do here is to formalize the examples of
   structured types. -}

-- Pointed types
U-pt : (i : Level) → UU (lsuc i)
U-pt i = Σ (UU i) (λ X → X)
 
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

-- The ring axioms for ℤ

abstract
  left-inverse-pred-ℤ :
    (k : ℤ) → Id (pred-ℤ (succ-ℤ k)) k
  left-inverse-pred-ℤ (inl zero-ℕ) = refl
  left-inverse-pred-ℤ (inl (succ-ℕ x)) = refl
  left-inverse-pred-ℤ (inr (inl star)) = refl
  left-inverse-pred-ℤ (inr (inr zero-ℕ)) = refl
  left-inverse-pred-ℤ (inr (inr (succ-ℕ x))) = refl
  
  right-inverse-pred-ℤ :
    (k : ℤ) → Id (succ-ℤ (pred-ℤ k)) k
  right-inverse-pred-ℤ (inl zero-ℕ) = refl
  right-inverse-pred-ℤ (inl (succ-ℕ x)) = refl
  right-inverse-pred-ℤ (inr (inl star)) = refl
  right-inverse-pred-ℤ (inr (inr zero-ℕ)) = refl
  right-inverse-pred-ℤ (inr (inr (succ-ℕ x))) = refl

{- Exercise 6.12 (a) simply asks to prove the unit laws. The left unit law 
   holds by judgmental equality. -}

abstract
  left-unit-law-add-ℤ :
    (k : ℤ) → Id (add-ℤ zero-ℤ k) k
  left-unit-law-add-ℤ k = refl
  
  right-unit-law-add-ℤ :
    (k : ℤ) → Id (add-ℤ k zero-ℤ) k
  right-unit-law-add-ℤ (inl zero-ℕ) = refl
  right-unit-law-add-ℤ (inl (succ-ℕ x)) =
    ap pred-ℤ (right-unit-law-add-ℤ (inl x))
  right-unit-law-add-ℤ (inr (inl star)) = refl
  right-unit-law-add-ℤ (inr (inr zero-ℕ)) = refl
  right-unit-law-add-ℤ (inr (inr (succ-ℕ x))) =
    ap succ-ℤ (right-unit-law-add-ℤ (inr (inr x)))

{- Exercise 6.12 (b) asks to show the left and right predecessor and successor 
   laws. These are helpful to give proofs of associativity and commutativity. 
   -}

abstract
  left-predecessor-law-add-ℤ :
    (x y : ℤ) → Id (add-ℤ (pred-ℤ x) y) (pred-ℤ (add-ℤ x y))
  left-predecessor-law-add-ℤ (inl n) y = refl
  left-predecessor-law-add-ℤ (inr (inl star)) y = refl
  left-predecessor-law-add-ℤ (inr (inr zero-ℕ)) y =
    ( ap (λ t → add-ℤ t y) (left-inverse-pred-ℤ zero-ℤ)) ∙ 
    ( inv (left-inverse-pred-ℤ y))
  left-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) y =
    ( ap (λ t → (add-ℤ t y)) (left-inverse-pred-ℤ (inr (inr x)))) ∙
    ( inv (left-inverse-pred-ℤ (add-ℤ (inr (inr x)) y)))

  right-predecessor-law-add-ℤ :
    (x y : ℤ) → Id (add-ℤ x (pred-ℤ y)) (pred-ℤ (add-ℤ x y))
  right-predecessor-law-add-ℤ (inl zero-ℕ) n = refl
  right-predecessor-law-add-ℤ (inl (succ-ℕ m)) n =
    ap pred-ℤ (right-predecessor-law-add-ℤ (inl m) n)
  right-predecessor-law-add-ℤ (inr (inl star)) n = refl
  right-predecessor-law-add-ℤ (inr (inr zero-ℕ)) n =
    (right-inverse-pred-ℤ n) ∙ (inv (left-inverse-pred-ℤ n))
  right-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) n =
    ( ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) n)) ∙
    ( ( right-inverse-pred-ℤ (add-ℤ (inr (inr x)) n)) ∙ 
      ( inv (left-inverse-pred-ℤ (add-ℤ (inr (inr x)) n))))

abstract
  left-successor-law-add-ℤ :
    (x y : ℤ) → Id (add-ℤ (succ-ℤ x) y) (succ-ℤ (add-ℤ x y))
  left-successor-law-add-ℤ (inl zero-ℕ) y =
    ( ap (λ t → add-ℤ t y) (right-inverse-pred-ℤ zero-ℤ)) ∙
    ( inv (right-inverse-pred-ℤ y))
  left-successor-law-add-ℤ (inl (succ-ℕ x)) y =
    ( inv (right-inverse-pred-ℤ (add-ℤ (inl x) y))) ∙
    ( ap succ-ℤ (inv (left-predecessor-law-add-ℤ (inl x) y)))
  left-successor-law-add-ℤ (inr (inl star)) y = refl
  left-successor-law-add-ℤ (inr (inr x)) y = refl

  right-successor-law-add-ℤ :
    (x y : ℤ) → Id (add-ℤ x (succ-ℤ y)) (succ-ℤ (add-ℤ x y))
  right-successor-law-add-ℤ (inl zero-ℕ) y =
    (left-inverse-pred-ℤ y) ∙ (inv (right-inverse-pred-ℤ y))
  right-successor-law-add-ℤ (inl (succ-ℕ x)) y =
    ( ap pred-ℤ (right-successor-law-add-ℤ (inl x) y)) ∙
    ( ( left-inverse-pred-ℤ (add-ℤ (inl x) y)) ∙
      ( inv (right-inverse-pred-ℤ (add-ℤ (inl x) y))))
  right-successor-law-add-ℤ (inr (inl star)) y = refl
  right-successor-law-add-ℤ (inr (inr zero-ℕ)) y = refl
  right-successor-law-add-ℤ (inr (inr (succ-ℕ x))) y =
    ap succ-ℤ (right-successor-law-add-ℤ (inr (inr x)) y)

{- Exercise 6.12 (c) asks to prove associativity and commutativity. Note that 
   we avoid an unwieldy amount of cases by only using induction on the first 
   argument. The resulting proof term is fairly short, and we don't have to 
   present ℤ as a certain quotient of ℕ × ℕ. -}

abstract
  associative-add-ℤ :
    (x y z : ℤ) → Id (add-ℤ (add-ℤ x y) z) (add-ℤ x (add-ℤ y z))
  associative-add-ℤ (inl zero-ℕ) y z =
    ( ap (λ t → add-ℤ t z) (left-predecessor-law-add-ℤ zero-ℤ y)) ∙
    ( ( left-predecessor-law-add-ℤ y z) ∙
      ( inv (left-predecessor-law-add-ℤ zero-ℤ (add-ℤ y z))))
  associative-add-ℤ (inl (succ-ℕ x)) y z =
    ( ap (λ t → add-ℤ t z) (left-predecessor-law-add-ℤ (inl x) y)) ∙
    ( ( left-predecessor-law-add-ℤ (add-ℤ (inl x) y) z) ∙
      ( ( ap pred-ℤ (associative-add-ℤ (inl x) y z)) ∙ 
        ( inv (left-predecessor-law-add-ℤ (inl x) (add-ℤ y z)))))
  associative-add-ℤ (inr (inl star)) y z = refl
  associative-add-ℤ (inr (inr zero-ℕ)) y z =
    ( ap (λ t → add-ℤ t z) (left-successor-law-add-ℤ zero-ℤ y)) ∙ 
    ( ( left-successor-law-add-ℤ y z) ∙ 
      ( inv (left-successor-law-add-ℤ zero-ℤ (add-ℤ y z))))
  associative-add-ℤ (inr (inr (succ-ℕ x))) y z =
    ( ap (λ t → add-ℤ t z) (left-successor-law-add-ℤ (inr (inr x)) y)) ∙
    ( ( left-successor-law-add-ℤ (add-ℤ (inr (inr x)) y) z) ∙
      ( ( ap succ-ℤ (associative-add-ℤ (inr (inr x)) y z)) ∙
        ( inv (left-successor-law-add-ℤ (inr (inr x)) (add-ℤ y z)))))

abstract
  commutative-add-ℤ :
    (x y : ℤ) → Id (add-ℤ x y) (add-ℤ y x)
  commutative-add-ℤ (inl zero-ℕ) y =
    ( left-predecessor-law-add-ℤ zero-ℤ y) ∙
    ( inv
      ( ( right-predecessor-law-add-ℤ y zero-ℤ) ∙
        ( ap pred-ℤ (right-unit-law-add-ℤ y))))
  commutative-add-ℤ (inl (succ-ℕ x)) y =
    ( ap pred-ℤ (commutative-add-ℤ (inl x) y)) ∙ 
    ( inv (right-predecessor-law-add-ℤ y (inl x)))
  commutative-add-ℤ (inr (inl star)) y = inv (right-unit-law-add-ℤ y)
  commutative-add-ℤ (inr (inr zero-ℕ)) y =
    inv
      ( ( right-successor-law-add-ℤ y zero-ℤ) ∙
        ( ap succ-ℤ (right-unit-law-add-ℤ y)))
  commutative-add-ℤ (inr (inr (succ-ℕ x))) y =
    ( ap succ-ℤ (commutative-add-ℤ (inr (inr x)) y)) ∙ 
    ( inv (right-successor-law-add-ℤ y (inr (inr x))))

{- Exercise 6.12 (d) finally asks to show the inverse laws, completing the 
   verification of the group laws. Combined with associativity and 
   commutativity we conclude that (add-ℤ x) and (λ x → add-ℤ x y) are 
   equivalences, for every x : ℤ and y : ℤ, respectively. -}

abstract
  left-inverse-law-add-ℤ :
    (x : ℤ) → Id (add-ℤ (neg-ℤ x) x) zero-ℤ
  left-inverse-law-add-ℤ (inl zero-ℕ) = refl
  left-inverse-law-add-ℤ (inl (succ-ℕ x)) =
    ( ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) (inl x))) ∙ 
    ( ( right-inverse-pred-ℤ (add-ℤ (inr (inr x)) (inl x))) ∙
      ( left-inverse-law-add-ℤ (inl x))) 
  left-inverse-law-add-ℤ (inr (inl star)) = refl
  left-inverse-law-add-ℤ (inr (inr x)) =
    ( commutative-add-ℤ (inl x) (inr (inr x))) ∙ 
    ( left-inverse-law-add-ℤ (inl x))
  
  right-inverse-law-add-ℤ :
    (x : ℤ) → Id (add-ℤ x (neg-ℤ x)) zero-ℤ
  right-inverse-law-add-ℤ x =
    ( commutative-add-ℤ x (neg-ℤ x)) ∙ (left-inverse-law-add-ℤ x)

-- Similar for multiplication on ℤ

neg-neg-ℤ : (k : ℤ) → Id (neg-ℤ (neg-ℤ k)) k
neg-neg-ℤ (inl n) = refl
neg-neg-ℤ (inr (inl star)) = refl
neg-neg-ℤ (inr (inr n)) = refl

left-zero-law-mul-ℤ : (k : ℤ) → Id (mul-ℤ zero-ℤ k) zero-ℤ
left-zero-law-mul-ℤ k = refl

right-zero-law-mul-ℤ : (k : ℤ) → Id (mul-ℤ k zero-ℤ) zero-ℤ
right-zero-law-mul-ℤ (inl zero-ℕ) = refl
right-zero-law-mul-ℤ (inl (succ-ℕ n)) =
  right-zero-law-mul-ℤ (inl n)
right-zero-law-mul-ℤ (inr (inl star)) = refl
right-zero-law-mul-ℤ (inr (inr zero-ℕ)) = refl
right-zero-law-mul-ℤ (inr (inr (succ-ℕ n))) =
  right-zero-law-mul-ℤ (inr (inr n))

left-unit-law-mul-ℤ : (k : ℤ) → Id (mul-ℤ one-ℤ k) k
left-unit-law-mul-ℤ k = refl

right-unit-law-mul-ℤ : (k : ℤ) → Id (mul-ℤ k one-ℤ) k
right-unit-law-mul-ℤ (inl zero-ℕ) = refl
right-unit-law-mul-ℤ (inl (succ-ℕ n)) =
  ap (add-ℤ (neg-one-ℤ)) (right-unit-law-mul-ℤ (inl n))
right-unit-law-mul-ℤ (inr (inl star)) = refl
right-unit-law-mul-ℤ (inr (inr zero-ℕ)) = refl
right-unit-law-mul-ℤ (inr (inr (succ-ℕ n))) =
  ap (add-ℤ one-ℤ) (right-unit-law-mul-ℤ (inr (inr n)))

left-neg-unit-law-mul-ℤ : (k : ℤ) → Id (mul-ℤ neg-one-ℤ k) (neg-ℤ k)
left-neg-unit-law-mul-ℤ k = refl

right-neg-unit-law-mul-ℤ : (k : ℤ) → Id (mul-ℤ k neg-one-ℤ) (neg-ℤ k)
right-neg-unit-law-mul-ℤ (inl zero-ℕ) = refl
right-neg-unit-law-mul-ℤ (inl (succ-ℕ n)) =
  ap (add-ℤ one-ℤ) (right-neg-unit-law-mul-ℤ (inl n))
right-neg-unit-law-mul-ℤ (inr (inl star)) = refl
right-neg-unit-law-mul-ℤ (inr (inr zero-ℕ)) = refl
right-neg-unit-law-mul-ℤ (inr (inr (succ-ℕ n))) =
  ap (add-ℤ neg-one-ℤ) (right-neg-unit-law-mul-ℤ (inr (inr n)))

left-successor-law-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ (succ-ℤ k) l) (add-ℤ l (mul-ℤ k l))
left-successor-law-mul-ℤ (inl zero-ℕ) l =
  inv (right-inverse-law-add-ℤ l)
left-successor-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( ( inv (left-unit-law-add-ℤ (mul-ℤ (inl n) l))) ∙
    ( ap
      ( λ x → add-ℤ x (mul-ℤ (inl n) l))
      ( inv (right-inverse-law-add-ℤ l)))) ∙
  ( associative-add-ℤ l (neg-ℤ l) (mul-ℤ (inl n) l))
left-successor-law-mul-ℤ (inr (inl star)) l =
  inv (right-unit-law-add-ℤ l)
left-successor-law-mul-ℤ (inr (inr n)) l = refl

left-predecessor-law-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ (pred-ℤ k) l) (add-ℤ (neg-ℤ l) (mul-ℤ k l))
left-predecessor-law-mul-ℤ (inl n) l = refl
left-predecessor-law-mul-ℤ (inr (inl star)) l =
  ( left-neg-unit-law-mul-ℤ l) ∙
  ( inv (right-unit-law-add-ℤ (neg-ℤ l)))
left-predecessor-law-mul-ℤ (inr (inr zero-ℕ)) l =
  inv (left-inverse-law-add-ℤ l)
left-predecessor-law-mul-ℤ (inr (inr (succ-ℕ x))) l =
   ( ap
     ( λ t → add-ℤ t (mul-ℤ (in-pos x) l))
     ( inv (left-inverse-law-add-ℤ l))) ∙
   ( associative-add-ℤ (neg-ℤ l) l (mul-ℤ (in-pos x) l))

-- can be defined using only induction on k.
right-successor-law-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ k (succ-ℤ l)) (add-ℤ k (mul-ℤ k l))
right-successor-law-mul-ℤ (inl zero-ℕ) (inl zero-ℕ) = refl
right-successor-law-mul-ℤ (inl zero-ℕ) (inl (succ-ℕ n)) = refl
right-successor-law-mul-ℤ (inl zero-ℕ) (inr (inl star)) = refl
right-successor-law-mul-ℤ (inl zero-ℕ) (inr (inr n)) = refl
right-successor-law-mul-ℤ (inl (succ-ℕ n)) (inl zero-ℕ) =
  ( right-zero-law-mul-ℤ (inl (succ-ℕ n))) ∙
  ( ( inv (right-inverse-law-add-ℤ (inl (succ-ℕ n)))) ∙
    ( ap
      ( add-ℤ (inl (succ-ℕ n)))
      ( inv (right-neg-unit-law-mul-ℤ (inl (succ-ℕ n))))))
right-successor-law-mul-ℤ (inl (succ-ℕ x)) (inl (succ-ℕ n)) =
  ( ap
    ( add-ℤ (neg-ℤ (inl n)))
    ( right-successor-law-mul-ℤ (inl x) (inl (succ-ℕ n)))) ∙
  ( ( inv
      ( associative-add-ℤ
        ( neg-ℤ (inl n))
        ( inl x)
        ( mul-ℤ (inl x) (inl (succ-ℕ n))))) ∙
    ( ( ap
        ( λ t → add-ℤ t (mul-ℤ (inl x) (inl (succ-ℕ n))))
        { x = add-ℤ (neg-ℤ (inl n)) (inl x)}
        { y = add-ℤ (inl (succ-ℕ x)) (neg-ℤ (inl (succ-ℕ n)))}
        ( ( right-successor-law-add-ℤ (neg-ℤ (inl n)) (inl (succ-ℕ x))) ∙
          ( commutative-add-ℤ (neg-ℤ (inl (succ-ℕ n))) (inl (succ-ℕ x))))) ∙
      ( associative-add-ℤ
        ( inl (succ-ℕ x))
        ( neg-ℤ (inl (succ-ℕ n)))
        ( mul-ℤ (inl x) (inl (succ-ℕ n))))))
right-successor-law-mul-ℤ (inl (succ-ℕ x)) (inr (inl star)) =
  ( right-unit-law-mul-ℤ (inl (succ-ℕ x))) ∙
  ( ( inv (right-unit-law-add-ℤ (inl (succ-ℕ x)))) ∙
    ( ap (add-ℤ (inl (succ-ℕ x))) (inv (right-zero-law-mul-ℤ (inl x)))))
right-successor-law-mul-ℤ (inl (succ-ℕ x)) (inr (inr n)) =
  ( left-predecessor-law-mul-ℤ (inl x) (inr (inr (succ-ℕ n)))) ∙
  ( ( ap
      ( add-ℤ (neg-ℤ (in-pos (succ-ℕ n))))
      ( right-successor-law-mul-ℤ (inl x) (inr (inr n)))) ∙
    ( ( inv
        ( associative-add-ℤ
          ( neg-ℤ (in-pos (succ-ℕ n)))
          ( inl x)
          ( mul-ℤ (inl x) (inr (inr n))))) ∙
      ( ( ap
          ( λ t → add-ℤ t (mul-ℤ (inl x) (in-pos n)))
          { x = add-ℤ (neg-ℤ (in-pos (succ-ℕ n))) (inl x)}
          { y = add-ℤ (inl (succ-ℕ x)) (neg-ℤ (in-pos n))}
          ( ( right-successor-law-add-ℤ
              ( neg-ℤ (in-pos (succ-ℕ n)))
              ( inl (succ-ℕ x))) ∙
            ( ( right-inverse-pred-ℤ (add-ℤ (inl n) (inl (succ-ℕ x)))) ∙
               commutative-add-ℤ (inl n) (inl (succ-ℕ x))))) ∙
        ( associative-add-ℤ
          ( inl (succ-ℕ x))
          ( inl n)
          ( mul-ℤ (inl x) (inr (inr n)))))))
right-successor-law-mul-ℤ (inr (inl star)) l = refl
right-successor-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
right-successor-law-mul-ℤ (inr (inr (succ-ℕ x))) l =
  ( left-successor-law-mul-ℤ (in-pos x) (succ-ℤ l)) ∙
  ( ( ap (add-ℤ (succ-ℤ l)) (right-successor-law-mul-ℤ (inr (inr x)) l)) ∙
    ( ( inv
        ( associative-add-ℤ (succ-ℤ l) (in-pos x) (mul-ℤ (in-pos x) l))) ∙
      ( ( ap
          ( λ t → add-ℤ t (mul-ℤ (in-pos x) l))
          { x = add-ℤ (succ-ℤ l) (in-pos x)}
          { y = add-ℤ (in-pos (succ-ℕ x)) l}
          ( ( left-successor-law-add-ℤ l (in-pos x)) ∙
            ( ap succ-ℤ (commutative-add-ℤ l (in-pos x))))) ∙
        ( associative-add-ℤ (in-pos (succ-ℕ x)) l (mul-ℤ (inr (inr x)) l)))))

neg-pred-ℤ :
  (k : ℤ) → Id (neg-ℤ (pred-ℤ k)) (succ-ℤ (neg-ℤ k))
neg-pred-ℤ (inl x) = refl
neg-pred-ℤ (inr (inl star)) = refl
neg-pred-ℤ (inr (inr zero-ℕ)) = refl
neg-pred-ℤ (inr (inr (succ-ℕ x))) = refl

right-predecessor-law-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ k (pred-ℤ l)) (add-ℤ (neg-ℤ k) (mul-ℤ k l))
right-predecessor-law-mul-ℤ (inl zero-ℕ) l =
  ( left-neg-unit-law-mul-ℤ (pred-ℤ l)) ∙
  ( neg-pred-ℤ l)
right-predecessor-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( left-predecessor-law-mul-ℤ (inl n) (pred-ℤ l)) ∙
  ( ( ap (add-ℤ (neg-ℤ (pred-ℤ l))) (right-predecessor-law-mul-ℤ (inl n) l)) ∙
    ( ( inv
        ( associative-add-ℤ (neg-ℤ (pred-ℤ l)) (in-pos n) (mul-ℤ (inl n) l))) ∙
      ( ( ap
          ( λ t → add-ℤ t (mul-ℤ (inl n) l))
          { x = add-ℤ (neg-ℤ (pred-ℤ l)) (inr (inr n))}
          { y = add-ℤ (neg-ℤ (inl (succ-ℕ n))) (neg-ℤ l)}
          ( ( ap (λ t → add-ℤ t (in-pos n)) (neg-pred-ℤ l)) ∙
            ( ( left-successor-law-add-ℤ (neg-ℤ l) (in-pos n)) ∙
              ( ( ap succ-ℤ (commutative-add-ℤ (neg-ℤ l) (in-pos n))) ∙
                ( inv (left-successor-law-add-ℤ (in-pos n) (neg-ℤ l))))))) ∙
        ( associative-add-ℤ (in-pos (succ-ℕ n)) (neg-ℤ l) (mul-ℤ (inl n) l)))))
right-predecessor-law-mul-ℤ (inr (inl star)) l = refl
right-predecessor-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
right-predecessor-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-successor-law-mul-ℤ (in-pos n) (pred-ℤ l)) ∙
  ( ( ap (add-ℤ (pred-ℤ l)) (right-predecessor-law-mul-ℤ (inr (inr n)) l)) ∙
    ( ( inv (associative-add-ℤ (pred-ℤ l) (inl n) (mul-ℤ (inr (inr n)) l))) ∙
      ( ( ap
          ( λ t → add-ℤ t (mul-ℤ (in-pos n) l))
          { x = add-ℤ (pred-ℤ l) (inl n)}
          { y = add-ℤ (neg-ℤ (in-pos (succ-ℕ n))) l}
          ( ( left-predecessor-law-add-ℤ l (inl n)) ∙
            ( ( ap pred-ℤ (commutative-add-ℤ l (inl n))) ∙
              ( inv (left-predecessor-law-add-ℤ (inl n) l))))) ∙
        ( associative-add-ℤ (inl (succ-ℕ n)) l (mul-ℤ (inr (inr n)) l)))))

right-negative-law-add-ℤ :
  (k l : ℤ) → Id (add-ℤ k (neg-ℤ l)) (neg-ℤ (add-ℤ (neg-ℤ k) l))
right-negative-law-add-ℤ (inl zero-ℕ) l =
  ( left-predecessor-law-add-ℤ zero-ℤ (neg-ℤ l)) ∙
  {!!}
right-negative-law-add-ℤ (inl (succ-ℕ x)) l = {!!}
right-negative-law-add-ℤ (inr k) l = {!!}

left-negative-law-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ (neg-ℤ k) l) (neg-ℤ (mul-ℤ k l))
left-negative-law-mul-ℤ (inl zero-ℕ) l =
  ( left-unit-law-mul-ℤ l) ∙
  ( inv (neg-neg-ℤ l))
left-negative-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( ap (λ t → mul-ℤ t l) (neg-pred-ℤ (inl n))) ∙
  ( ( left-successor-law-mul-ℤ (neg-ℤ (inl n)) l) ∙
    ( ( ap (add-ℤ l) (left-negative-law-mul-ℤ (inl n) l)) ∙
      ( right-negative-law-add-ℤ l (mul-ℤ (inl n) l))))
left-negative-law-mul-ℤ (inr k) l = {!!}

associative-mul-ℤ :
  (k l m : ℤ) → Id (mul-ℤ (mul-ℤ k l) m) (mul-ℤ k (mul-ℤ l m))
associative-mul-ℤ (inl zero-ℕ) l m = {!!}
associative-mul-ℤ (inl (succ-ℕ x)) l m = {!!}
associative-mul-ℤ (inr k) l m = {!!}

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
