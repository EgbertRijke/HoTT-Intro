{-# OPTIONS --without-K #-}

module 05-identity-types where

import 04-relations
open 04-relations public

-- Section 5.1

{- We introduce the identity type. -}

data Id {i : Level} {A : UU i} (x : A) : A → UU i where
  refl : Id x x

{- In the following definition we give a construction of path induction.
   However, in the development of this library we will mostly use Agda's
   built-in methods to give constructions by path induction. -}

ind-Id :
  {i j : Level} {A : UU i} (x : A) (B : (y : A) (p : Id x y) → UU j) →
  (B x refl) → (y : A) (p : Id x y) → B y p
ind-Id x B b y refl = b

-- Section 5.2 The groupoid structure of types

inv :
  {i : Level} {A : UU i} {x y : A} → Id x y → Id y x
inv refl = refl

concat :
  {i : Level} {A : UU i} {x : A} (y : A) {z : A} →
  Id x y → Id y z → Id x z
concat x refl q = q

_∙_ :
  {i : Level} {A : UU i} {x y z : A} → Id x y → Id y z → Id x z
_∙_ {y = y} = concat y

assoc :
  {i : Level} {A : UU i} {x y z w : A} (p : Id x y) (q : Id y z)
  (r : Id z w) → Id ((p ∙ q) ∙ r) (p ∙ (q ∙ r))
assoc refl q r = refl

left-unit :
  {i : Level} {A : UU i} {x y : A} {p : Id x y} → Id (refl ∙ p) p
left-unit = refl

right-unit :
  {i : Level} {A : UU i} {x y : A} {p : Id x y} → Id (p ∙ refl) p
right-unit {p = refl} = refl

left-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id ((inv p) ∙ p) refl
left-inv refl = refl

right-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id (p ∙ (inv p)) refl
right-inv refl = refl

-- Section 5.3 The action on paths of functions

ap :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : Id x y) →
  Id (f x) (f y)
ap f refl = refl

ap-id :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (ap id p) p
ap-id refl = refl

ap-comp :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} (g : B → C)
  (f : A → B) {x y : A} (p : Id x y) → Id (ap (g ∘ f) p) (ap g (ap f p))
ap-comp g f refl = refl

ap-refl :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (x : A) →
  Id (ap f (refl {_} {_} {x})) refl
ap-refl f x = refl

ap-concat :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y z : A}
  (p : Id x y) (q : Id y z) → Id (ap f (p ∙ q)) ((ap f p) ∙ (ap f q))
ap-concat f refl q = refl

ap-inv :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A}
  (p : Id x y) → Id (ap f (inv p)) (inv (ap f p))
ap-inv f refl = refl

-- Section 5.4 Transport

tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A} (p : Id x y) → B x → B y
tr B refl b = b

apd :
  {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) {x y : A}
  (p : Id x y) → Id (tr B p (f x)) (f y)
apd f refl = refl

path-over :
  {i j : Level} {A :  UU i} (B : A → UU j) {x x' : A} (p : Id x x') →
  B x → B x' → UU j
path-over B p y y' = Id (tr B p y) y'

refl-path-over :
  {i j : Level} {A : UU i} (B : A → UU j) (x : A) (y : B x) →
  path-over B refl y y
refl-path-over B x y = refl

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

-- Exercises

-- Exercise 5.1

two-ℕ : ℕ
two-ℕ = succ-ℕ one-ℕ

is-even-ℕ : ℕ → UU lzero
is-even-ℕ n = Σ ℕ (λ m → Id (mul-ℕ two-ℕ m) n)

div-ℕ : ℕ → ℕ → UU lzero
div-ℕ m n = Σ ℕ (λ k → Id (mul-ℕ k m) n)

is-prime : ℕ → UU lzero
is-prime n = (one-ℕ < n) × ((m : ℕ) → (one-ℕ < m) → (div-ℕ m n) → Id m n)

{- The Goldbach conjecture asserts that every even number above 2 is the sum
   of two primes. -}

Goldbach-conjecture : UU lzero
Goldbach-conjecture =
  ( n : ℕ) → (two-ℕ < n) → (is-even-ℕ n) →
    Σ ℕ (λ p → (is-prime p) × (Σ ℕ (λ q → (is-prime q) × Id (add-ℕ p q) n)))

is-twin-prime : ℕ → UU lzero
is-twin-prime n = (is-prime n) × (is-prime (succ-ℕ (succ-ℕ n)))

{- The twin prime conjecture asserts that there are infinitely many twin 
   primes. We assert that there are infinitely twin primes by asserting that 
   for every n : ℕ there is a twin prime that is larger than n. -}
   
Twin-prime-conjecture : UU lzero
Twin-prime-conjecture = (n : ℕ) → Σ ℕ (λ p → (is-twin-prime p) × (leq-ℕ n p))

-- Exercise 5.2

distributive-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A}
  (q : Id y z) → Id (inv (p ∙ q)) ((inv q) ∙ (inv p))
distributive-inv-concat refl refl = refl

-- Exercise 5.3

inv-con :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z)
  (r : Id x z) → (Id (p ∙ q) r) → Id q ((inv p) ∙ r)
inv-con refl q r = id 

con-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z)
  (r : Id x z) → (Id (p ∙ q) r) → Id p (r ∙ (inv q))
con-inv p refl r =
  ( λ α → α ∙ (inv right-unit)) ∘ (concat (p ∙ refl) (inv right-unit))

-- Exercise 5.4

lift :
  {i j : Level} {A : UU i} {B : A → UU j} {x y : A} (p : Id x y)
  (b : B x) → Id (pair x b) (pair y (tr B p b))
lift refl b = refl

-- Exercise 5.5

abstract
  associative-add-ℕ :
    (x y z : ℕ) → Id (add-ℕ (add-ℕ x y) z) (add-ℕ x (add-ℕ y z))
  associative-add-ℕ zero-ℕ y z = refl 
  associative-add-ℕ (succ-ℕ x) y z = ap succ-ℕ (associative-add-ℕ x y z)

abstract
  right-unit-law-add-ℕ :
    (x : ℕ) → Id (add-ℕ x zero-ℕ) x
  right-unit-law-add-ℕ zero-ℕ = refl
  right-unit-law-add-ℕ (succ-ℕ x) = ap succ-ℕ (right-unit-law-add-ℕ x)
  
  left-unit-law-add-ℕ :
    (x : ℕ) → Id (add-ℕ zero-ℕ x) x
  left-unit-law-add-ℕ x = refl
  
  left-successor-law-add-ℕ :
    (x y : ℕ) → Id (add-ℕ (succ-ℕ x) y) (succ-ℕ (add-ℕ x y))
  left-successor-law-add-ℕ x y = refl
  
  right-successor-law-add-ℕ :
    (x y : ℕ) → Id (add-ℕ x (succ-ℕ y)) (succ-ℕ (add-ℕ x y))
  right-successor-law-add-ℕ zero-ℕ y = refl
  right-successor-law-add-ℕ (succ-ℕ x) y =
    ap succ-ℕ (right-successor-law-add-ℕ x y)

abstract
  commutative-add-ℕ :
    (x y : ℕ) → Id (add-ℕ x y) (add-ℕ y x)
  commutative-add-ℕ zero-ℕ y = inv (right-unit-law-add-ℕ y)
  commutative-add-ℕ (succ-ℕ x) y =
    (ap succ-ℕ (commutative-add-ℕ x y)) ∙ (inv (right-successor-law-add-ℕ y x))

abstract
  right-unit-law-mul-ℕ :
    (x : ℕ) → Id (mul-ℕ x one-ℕ) x
  right-unit-law-mul-ℕ zero-ℕ = refl
  right-unit-law-mul-ℕ (succ-ℕ x) =
    ( right-successor-law-add-ℕ (mul-ℕ x one-ℕ) zero-ℕ) ∙
    ( ap succ-ℕ (concat _ (right-unit-law-add-ℕ _) (right-unit-law-mul-ℕ x)))
  
  left-unit-law-mul-ℕ :
    (x : ℕ) → Id (mul-ℕ one-ℕ x) x
  left-unit-law-mul-ℕ x = refl

abstract
  left-successor-law-mul-ℕ :
    (x y : ℕ) → Id (mul-ℕ (succ-ℕ x) y) (add-ℕ (mul-ℕ x y) y)
  left-successor-law-mul-ℕ x y = refl

abstract
  right-successor-law-mul-ℕ :
    (x y : ℕ) → Id (mul-ℕ x (succ-ℕ y)) (add-ℕ x (mul-ℕ x y))
  right-successor-law-mul-ℕ zero-ℕ y = refl
  right-successor-law-mul-ℕ (succ-ℕ x) y =
    ( right-successor-law-add-ℕ (mul-ℕ x (succ-ℕ y)) y) ∙ 
    ( ( ap (λ t → succ-ℕ (add-ℕ t y)) (right-successor-law-mul-ℕ x y)) ∙
      ( ap succ-ℕ (associative-add-ℕ x (mul-ℕ x y) y)))

abstract
  left-distributive-mul-add-ℕ :
    (x y z : ℕ) → Id (mul-ℕ x (add-ℕ y z)) (add-ℕ (mul-ℕ x y) (mul-ℕ x z))
  left-distributive-mul-add-ℕ zero-ℕ y z = refl
  left-distributive-mul-add-ℕ (succ-ℕ x) y z =
    ( left-successor-law-mul-ℕ x (add-ℕ y z)) ∙ 
    ( ( ap (λ t → add-ℕ t (add-ℕ y z)) (left-distributive-mul-add-ℕ x y z)) ∙ 
      ( ( associative-add-ℕ (mul-ℕ x y) (mul-ℕ x z) (add-ℕ y z)) ∙
        ( ( ap ( add-ℕ (mul-ℕ x y)) 
               ( ( inv (associative-add-ℕ (mul-ℕ x z) y z)) ∙
                 ( ( ap (λ t → add-ℕ t z) (commutative-add-ℕ (mul-ℕ x z) y)) ∙
                   ( associative-add-ℕ y (mul-ℕ x z) z)))) ∙ 
          ( inv (associative-add-ℕ (mul-ℕ x y) y (add-ℕ (mul-ℕ x z) z))))))

abstract
  left-zero-law-mul-ℕ :
    (x : ℕ) → Id (mul-ℕ zero-ℕ x) zero-ℕ
  left-zero-law-mul-ℕ x = refl

abstract
  right-zero-law-mul-ℕ :
    (x : ℕ) → Id (mul-ℕ x zero-ℕ) zero-ℕ
  right-zero-law-mul-ℕ zero-ℕ = refl
  right-zero-law-mul-ℕ (succ-ℕ x) =
    ( right-unit-law-add-ℕ (mul-ℕ x zero-ℕ)) ∙ (right-zero-law-mul-ℕ x)

abstract
  commutative-mul-ℕ :
    (x y : ℕ) → Id (mul-ℕ x y) (mul-ℕ y x)
  commutative-mul-ℕ zero-ℕ y = inv (right-zero-law-mul-ℕ y)
  commutative-mul-ℕ (succ-ℕ x) y =
    ( commutative-add-ℕ (mul-ℕ x y) y) ∙ 
    ( ( ap (add-ℕ y) (commutative-mul-ℕ x y)) ∙
      ( inv (right-successor-law-mul-ℕ y x)))

abstract
  right-distributive-mul-add-ℕ :
    (x y z : ℕ) → Id (mul-ℕ (add-ℕ x y) z) (add-ℕ (mul-ℕ x z) (mul-ℕ y z))
  right-distributive-mul-add-ℕ x y z =
    ( commutative-mul-ℕ (add-ℕ x y) z) ∙ 
    ( ( left-distributive-mul-add-ℕ z x y) ∙ 
      ( ( ap (λ t → add-ℕ t (mul-ℕ z y)) (commutative-mul-ℕ z x)) ∙ 
        ( ap (λ t → add-ℕ (mul-ℕ x z) t) (commutative-mul-ℕ z y))))

abstract
  associative-mul-ℕ :
    (x y z : ℕ) → Id (mul-ℕ (mul-ℕ x y) z) (mul-ℕ x (mul-ℕ y z))
  associative-mul-ℕ zero-ℕ y z = refl
  associative-mul-ℕ (succ-ℕ x) y z =
    ( right-distributive-mul-add-ℕ (mul-ℕ x y) y z) ∙ 
    ( ap (λ t → add-ℕ t (mul-ℕ y z)) (associative-mul-ℕ x y z))

-- Exercise 5.6

Mac-Lane-pentagon :
  {i : Level} {A : UU i} {a b c d e : A}
  (p : Id a b) (q : Id b c) (r : Id c d) (s : Id d e) →
  let α₁ = (ap (λ t → t ∙ s) (assoc p q r))
      α₂ = (assoc p (q ∙ r) s)
      α₃ = (ap (λ t → p ∙ t) (assoc q r s))
      α₄ = (assoc (p ∙ q) r s)
      α₅ = (assoc p q (r ∙ s))
  in
  Id ((α₁ ∙ α₂) ∙ α₃) (α₄ ∙ α₅)
Mac-Lane-pentagon refl refl refl refl = refl
