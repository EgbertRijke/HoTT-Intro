{-# OPTIONS --without-K --exact-split --safe #-}

module 06-universes where

import 05-identity-types
open 05-identity-types public

-- Section 6.3 Pointed types

-- Definition 6.3.1

UU-pt : (i : Level) → UU (lsuc i)
UU-pt i = Σ (UU i) (λ X → X)

type-UU-pt : {i : Level} → UU-pt i → UU i
type-UU-pt = pr1

pt-UU-pt : {i : Level} (A : UU-pt i) → type-UU-pt A
pt-UU-pt = pr2

-- Definition 6.3.2

_→*_ : {i j : Level} → UU-pt i → UU-pt j → UU-pt (i ⊔ j)
A →* B =
  pair
    ( Σ (type-UU-pt A → type-UU-pt B) (λ f → Id (f (pt-UU-pt A)) (pt-UU-pt B)))
    ( pair
      ( const (type-UU-pt A) (type-UU-pt B) (pt-UU-pt B))
      ( refl))

-- Definition 6.3.3

Ω : {i : Level} → UU-pt i → UU-pt i
Ω A = pair (Id (pt-UU-pt A) (pt-UU-pt A)) refl

-- Definition 6.3.4

iterated-loop-space : {i : Level} → ℕ → UU-pt i → UU-pt i
iterated-loop-space zero-ℕ A = A
iterated-loop-space (succ-ℕ n) A = Ω (iterated-loop-space n A)

-- Section 6.4 Families and relations on the natural numbers

-- Definition 6.4.1

Fin : ℕ → UU lzero
Fin zero-ℕ = empty
Fin (succ-ℕ n) = coprod (Fin n) unit

-- Definition 6.4.2

-- Observational equality on the natural numbers

Eq-ℕ : ℕ → (ℕ → UU lzero)
Eq-ℕ zero-ℕ zero-ℕ = 𝟙
Eq-ℕ zero-ℕ (succ-ℕ n) = 𝟘
Eq-ℕ (succ-ℕ m) zero-ℕ = 𝟘
Eq-ℕ (succ-ℕ m) (succ-ℕ n) = Eq-ℕ m n

-- Lemma 6.4.3

refl-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
refl-Eq-ℕ zero-ℕ = star
refl-Eq-ℕ (succ-ℕ n) = refl-Eq-ℕ n

Eq-ℕ-eq : {x y : ℕ} → Id x y → Eq-ℕ x y
Eq-ℕ-eq {x} {.x} refl = refl-Eq-ℕ x

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

-- Exercises

-- Exercise 6.1

{- In this exercise we were asked to show that the observational equality on ℕ 
   is an equivalence relation. -}

symmetric-Eq-ℕ : (m n : ℕ) → Eq-ℕ m n → Eq-ℕ n m
symmetric-Eq-ℕ zero-ℕ zero-ℕ star = star
symmetric-Eq-ℕ (succ-ℕ m) (succ-ℕ n) t = symmetric-Eq-ℕ m n t

transitive-Eq-ℕ : (l m n : ℕ) → Eq-ℕ l m → Eq-ℕ m n → Eq-ℕ l n
transitive-Eq-ℕ zero-ℕ zero-ℕ zero-ℕ p q = star
transitive-Eq-ℕ (succ-ℕ l) (succ-ℕ m) (succ-ℕ n) p q =
  transitive-Eq-ℕ l m n p q

-- Exercise 6.2

{- In this exercise we were asked to show that any function on the natural 
   numbers preserves observational equality. The quick solution uses the fact 
   that observational equality is the least reflexive relation. -}
   
preserve_Eq-ℕ : (f : ℕ → ℕ) (n m : ℕ) → (Eq-ℕ n m) → (Eq-ℕ (f n) (f m))
preserve_Eq-ℕ f =
  least-reflexive-Eq-ℕ
    ( λ x y → Eq-ℕ (f x) (f y))
    ( λ x → refl-Eq-ℕ (f x))

-- Exercise 6.3

{- In this exercise we were asked to construct the relations ≤ and < on the 
   natural numbers, and show basic properties about them. -}

-- Exercise 6.3(a)

-- The definition of ≤ 

leq-ℕ : ℕ → ℕ → UU lzero
leq-ℕ zero-ℕ m = unit
leq-ℕ (succ-ℕ n) zero-ℕ = empty
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m

_≤_ = leq-ℕ

leq-zero-ℕ :
  (n : ℕ) → leq-ℕ zero-ℕ n
leq-zero-ℕ n = star

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

succ-leq-ℕ : (n : ℕ) → leq-ℕ n (succ-ℕ n)
succ-leq-ℕ zero-ℕ = star
succ-leq-ℕ (succ-ℕ n) = succ-leq-ℕ n

succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
succ-le-ℕ zero-ℕ = star
succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n

anti-symmetric-leq-ℕ : (m n : ℕ) → leq-ℕ m n → leq-ℕ n m → Id m n
anti-symmetric-leq-ℕ zero-ℕ zero-ℕ p q = refl
anti-symmetric-leq-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (anti-symmetric-leq-ℕ m n p q)

anti-symmetric-le-ℕ : (m n : ℕ) → le-ℕ m n → le-ℕ n m → Id m n
anti-symmetric-le-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (anti-symmetric-le-ℕ m n p q)

-- Exercise 6.5

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
  {x y : bool} → Eq-𝟚 x y → R x y
least-reflexive-Eq-𝟚 R ρ {true} {true} p = ρ true
least-reflexive-Eq-𝟚 R ρ {true} {false} p = ind-empty p
least-reflexive-Eq-𝟚 R ρ {false} {true} p = ind-empty p
least-reflexive-Eq-𝟚 R ρ {false} {false} p = ρ false

eq-Eq-𝟚 :
  {x y : bool} → Eq-𝟚 x y → Id x y
eq-Eq-𝟚 = least-reflexive-Eq-𝟚 Id (λ x → refl)

Eq-eq-𝟚 :
  {x y : bool} → Id x y → Eq-𝟚 x y
Eq-eq-𝟚 {x = x} refl = reflexive-Eq-𝟚 x

neq-neg-𝟚 : (b : bool) → ¬ (Id b (neg-𝟚 b))
neq-neg-𝟚 true = Eq-eq-𝟚
neq-neg-𝟚 false = Eq-eq-𝟚

-- Exercise 6.6

{- In this exercise we were asked to define the relations ≤ and < on the 
   integers. As a criterion of correctness, we were then also asked to show 
   that the type of all integers l satisfying k ≤ l satisfy the induction 
   principle of the natural numbers. -}

diff-ℤ : ℤ → ℤ → ℤ
diff-ℤ k l = add-ℤ (neg-ℤ k) l

is-non-negative-ℤ : ℤ → UU lzero
is-non-negative-ℤ (inl x) = empty
is-non-negative-ℤ (inr k) = unit

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

-- Extra material

-- We show that ℕ is an ordered semi-ring

concatenate-eq-leq-eq-ℕ :
  {m n m' n' : ℕ} → Id m' m → leq-ℕ m n → Id n n' → leq-ℕ m' n'
concatenate-eq-leq-eq-ℕ refl H refl = H

concatenate-leq-eq-ℕ :
  (m : ℕ) {n n' : ℕ} → leq-ℕ m n → Id n n' → leq-ℕ m n'
concatenate-leq-eq-ℕ m H refl = H

concatenate-eq-leq-ℕ :
  {m m' : ℕ} (n : ℕ) → Id m' m → leq-ℕ m n → leq-ℕ m' n
concatenate-eq-leq-ℕ n refl H = H

left-law-leq-add-ℕ : (k m n : ℕ) → leq-ℕ m n → leq-ℕ (add-ℕ m k) (add-ℕ n k)
left-law-leq-add-ℕ zero-ℕ m n = id
left-law-leq-add-ℕ (succ-ℕ k) m n H = left-law-leq-add-ℕ k m n H

right-law-leq-add-ℕ : (k m n : ℕ) → leq-ℕ m n → leq-ℕ (add-ℕ k m) (add-ℕ k n) 
right-law-leq-add-ℕ k m n H =
  concatenate-eq-leq-eq-ℕ
    ( commutative-add-ℕ k m)
    ( left-law-leq-add-ℕ k m n H)
    ( commutative-add-ℕ n k)

preserves-leq-add-ℕ :
  {m m' n n' : ℕ} → leq-ℕ m m' → leq-ℕ n n' → leq-ℕ (add-ℕ m n) (add-ℕ m' n')
preserves-leq-add-ℕ {m} {m'} {n} {n'} H K =
  transitive-leq-ℕ
    ( add-ℕ m n)
    ( add-ℕ m' n)
    ( add-ℕ m' n')
    ( left-law-leq-add-ℕ n m m' H)
    ( right-law-leq-add-ℕ m' n n' K)

{-
right-law-leq-mul-ℕ : (k m n : ℕ) → leq-ℕ m n → leq-ℕ (mul-ℕ k m) (mul-ℕ k n)
right-law-leq-mul-ℕ zero-ℕ m n H = star
right-law-leq-mul-ℕ (succ-ℕ k) m n H = {!!}
-}

{-
  preserves-leq-add-ℕ
    { m = mul-ℕ k m}
    { m' = mul-ℕ k n}
    ( right-law-leq-mul-ℕ k m n H) H

left-law-leq-mul-ℕ : (k m n : ℕ) → leq-ℕ m n → leq-ℕ (mul-ℕ m k) (mul-ℕ n k)
left-law-leq-mul-ℕ k m n H =
  concatenate-eq-leq-eq-ℕ
    ( commutative-mul-ℕ k m)
    ( commutative-mul-ℕ k n)
    ( right-law-leq-mul-ℕ k m n H)
-}

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
  path-ind-Eq-ℕ
    ( λ m n e → R (succ-ℕ m) (succ-ℕ n) e)
    ( λ n → ρ (succ-ℕ n)) m n e

comp-path-ind-Eq-ℕ :
  {i : Level} (R : (m n : ℕ) → Eq-ℕ m n → UU i)
  ( ρ : (n : ℕ) → R n n (refl-Eq-ℕ n)) →
  ( n : ℕ) → Id (path-ind-Eq-ℕ R ρ n n (refl-Eq-ℕ n)) (ρ n)
comp-path-ind-Eq-ℕ R ρ zero-ℕ = refl
comp-path-ind-Eq-ℕ R ρ (succ-ℕ n) =
  comp-path-ind-Eq-ℕ
    ( λ m n e → R (succ-ℕ m) (succ-ℕ n) e)
    ( λ n → ρ (succ-ℕ n)) n


{-
-- Graphs
Gph : (i : Level) → UU (lsuc i)
Gph i = Σ (UU i) (λ X → (X → X → (UU i)))

-- Reflexive graphs
rGph : (i : Level) →  UU (lsuc i)
rGph i = Σ (UU i) (λ X → Σ (X → X → (UU i)) (λ R → (x : X) → R x x))
-}

-- Exercise 3.7

{- With the construction of the divisibility relation we open the door to basic
   number theory. -}
   
divides : (d n : ℕ) → UU lzero
divides d n = Σ ℕ (λ m → Eq-ℕ (mul-ℕ d m) n)
