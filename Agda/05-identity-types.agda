
{-# OPTIONS --without-K --exact-split --safe #-}

module 05-identity-types where

import 04-inductive-types
open 04-inductive-types public

--------------------------------------------------------------------------------

-- Section 5.1

-- Definition 5.1.1

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

--------------------------------------------------------------------------------

-- Section 5.2 The groupoidal structure of types

-- Definition 5.2.1

_∙_ :
  {i : Level} {A : UU i} {x y z : A} → Id x y → Id y z → Id x z
refl ∙ q = q

concat :
  {i : Level} {A : UU i} {x y : A} → Id x y → (z : A) → Id y z → Id x z
concat p z q = p ∙ q

-- Definition 5.2.2

inv :
  {i : Level} {A : UU i} {x y : A} → Id x y → Id y x
inv refl = refl

-- Definition 5.2.3

assoc :
  {i : Level} {A : UU i} {x y z w : A} (p : Id x y) (q : Id y z)
  (r : Id z w) → Id ((p ∙ q) ∙ r) (p ∙ (q ∙ r))
assoc refl q r = refl

-- Definition 5.2.4

left-unit :
  {i : Level} {A : UU i} {x y : A} {p : Id x y} → Id (refl ∙ p) p
left-unit = refl

right-unit :
  {i : Level} {A : UU i} {x y : A} {p : Id x y} → Id (p ∙ refl) p
right-unit {p = refl} = refl

-- Definition 5.2.5

left-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id ((inv p) ∙ p) refl
left-inv refl = refl

right-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id (p ∙ (inv p)) refl
right-inv refl = refl

--------------------------------------------------------------------------------

-- Section 5.3 The action on paths of functions

-- Definition 5.3.1

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

-- Definition 5.3.2

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

--------------------------------------------------------------------------------

-- Section 5.4 Transport

-- Definition 5.4.1

tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A} (p : Id x y) → B x → B y
tr B refl b = b

-- Definition 5.4.2

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

--------------------------------------------------------------------------------

-- Section 5.5 The uniqueness of refl

uniqueness-refl :
  {i : Level} {A : UU i} (a : A) (x : A) (p : Id a x) →
  Id {A = Σ A (Id a)} (pair a refl) (pair x p)
uniqueness-refl a a refl = refl

--------------------------------------------------------------------------------

-- Section 5.6 The laws of addition on ℕ

-- Proposition 5.6.1

right-unit-law-add-ℕ :
  (x : ℕ) → Id (add-ℕ x zero-ℕ) x
right-unit-law-add-ℕ x = refl

left-unit-law-add-ℕ :
  (x : ℕ) → Id (add-ℕ zero-ℕ x) x
left-unit-law-add-ℕ zero-ℕ = refl
left-unit-law-add-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-add-ℕ x)

-- Proposition 5.6.2

left-successor-law-add-ℕ :
  (x y : ℕ) → Id (add-ℕ (succ-ℕ x) y) (succ-ℕ (add-ℕ x y))
left-successor-law-add-ℕ x zero-ℕ = refl
left-successor-law-add-ℕ x (succ-ℕ y) =
  ap succ-ℕ (left-successor-law-add-ℕ x y)
                                        
right-successor-law-add-ℕ :
  (x y : ℕ) → Id (add-ℕ x (succ-ℕ y)) (succ-ℕ (add-ℕ x y))
right-successor-law-add-ℕ x y = refl

-- Proposition 5.6.3

associative-add-ℕ :
  (x y z : ℕ) → Id (add-ℕ (add-ℕ x y) z) (add-ℕ x (add-ℕ y z))
associative-add-ℕ x y zero-ℕ = refl 
associative-add-ℕ x y (succ-ℕ z) = ap succ-ℕ (associative-add-ℕ x y z)

-- Proposition 5.6.4

commutative-add-ℕ : (x y : ℕ) → Id (add-ℕ x y) (add-ℕ y x)
commutative-add-ℕ zero-ℕ y = left-unit-law-add-ℕ y
commutative-add-ℕ (succ-ℕ x) y =
  (left-successor-law-add-ℕ x y) ∙ (ap succ-ℕ (commutative-add-ℕ x y))

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 5.1

distributive-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A}
  (q : Id y z) → Id (inv (p ∙ q)) ((inv q) ∙ (inv p))
distributive-inv-concat refl refl = refl

-- Exercise 5.2

inv-con :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z)
  (r : Id x z) → (Id (p ∙ q) r) → Id q ((inv p) ∙ r)
inv-con refl q r = id 

con-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z)
  (r : Id x z) → (Id (p ∙ q) r) → Id p (r ∙ (inv q))
con-inv p refl r =
  ( λ α → α ∙ (inv right-unit)) ∘ (concat (inv right-unit) r)

-- Exercise 5.3

lift :
  {i j : Level} {A : UU i} {B : A → UU j} {x y : A} (p : Id x y)
  (b : B x) → Id (pair x b) (pair y (tr B p b))
lift refl b = refl

-- Exercise 5.4

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

-- Exercise 5.5

-- Exercise 5.5 (a)

abstract
  left-zero-law-mul-ℕ :
    (x : ℕ) → Id (mul-ℕ zero-ℕ x) zero-ℕ
  left-zero-law-mul-ℕ x = refl

  right-zero-law-mul-ℕ :
    (x : ℕ) → Id (mul-ℕ x zero-ℕ) zero-ℕ
  right-zero-law-mul-ℕ zero-ℕ = refl
  right-zero-law-mul-ℕ (succ-ℕ x) =
    ( right-unit-law-add-ℕ (mul-ℕ x zero-ℕ)) ∙ (right-zero-law-mul-ℕ x)

abstract
  right-unit-law-mul-ℕ :
    (x : ℕ) → Id (mul-ℕ x one-ℕ) x
  right-unit-law-mul-ℕ zero-ℕ = refl
  right-unit-law-mul-ℕ (succ-ℕ x) = ap succ-ℕ (right-unit-law-mul-ℕ x)

  left-unit-law-mul-ℕ :
    (x : ℕ) → Id (mul-ℕ one-ℕ x) x
  left-unit-law-mul-ℕ zero-ℕ = refl
  left-unit-law-mul-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-mul-ℕ x)

abstract
  left-successor-law-mul-ℕ :
    (x y : ℕ) → Id (mul-ℕ (succ-ℕ x) y) (add-ℕ (mul-ℕ x y) y)
  left-successor-law-mul-ℕ x y = refl

  right-successor-law-mul-ℕ :
    (x y : ℕ) → Id (mul-ℕ x (succ-ℕ y)) (add-ℕ x (mul-ℕ x y))
  right-successor-law-mul-ℕ zero-ℕ y = refl
  right-successor-law-mul-ℕ (succ-ℕ x) y =
    ( ( ap (λ t → succ-ℕ (add-ℕ t y)) (right-successor-law-mul-ℕ x y)) ∙
      ( ap succ-ℕ (associative-add-ℕ x (mul-ℕ x y) y))) ∙
    ( inv (left-successor-law-add-ℕ x (add-ℕ (mul-ℕ x y) y)))

-- Exercise 5.5 (b)

abstract
  commutative-mul-ℕ :
    (x y : ℕ) → Id (mul-ℕ x y) (mul-ℕ y x)
  commutative-mul-ℕ zero-ℕ y = inv (right-zero-law-mul-ℕ y)
  commutative-mul-ℕ (succ-ℕ x) y =
    ( commutative-add-ℕ (mul-ℕ x y) y) ∙ 
    ( ( ap (add-ℕ y) (commutative-mul-ℕ x y)) ∙
      ( inv (right-successor-law-mul-ℕ y x)))

-- Exercise 5.5 (c)

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
  right-distributive-mul-add-ℕ :
    (x y z : ℕ) → Id (mul-ℕ (add-ℕ x y) z) (add-ℕ (mul-ℕ x z) (mul-ℕ y z))
  right-distributive-mul-add-ℕ x y z =
    ( commutative-mul-ℕ (add-ℕ x y) z) ∙ 
    ( ( left-distributive-mul-add-ℕ z x y) ∙ 
      ( ( ap (λ t → add-ℕ t (mul-ℕ z y)) (commutative-mul-ℕ z x)) ∙ 
        ( ap (λ t → add-ℕ (mul-ℕ x z) t) (commutative-mul-ℕ z y))))

-- Exercise 5.5 (d)

abstract
  associative-mul-ℕ :
    (x y z : ℕ) → Id (mul-ℕ (mul-ℕ x y) z) (mul-ℕ x (mul-ℕ y z))
  associative-mul-ℕ zero-ℕ y z = refl
  associative-mul-ℕ (succ-ℕ x) y z =
    ( right-distributive-mul-add-ℕ (mul-ℕ x y) y z) ∙ 
    ( ap (λ t → add-ℕ t (mul-ℕ y z)) (associative-mul-ℕ x y z))

-- Exercise 5.6

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

-- Exercise 5.7

-- Exercise 5.7 (a)

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

-- Exercise 5.7 (b)

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

-- Exercise 5.7 (c)

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

-- Exercise 5.7 (d)

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

-- Exercise 5.8

-- Exercise 5.8 (a)

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

-- Exercise 5.8 (b)

neg-neg-ℤ : (k : ℤ) → Id (neg-ℤ (neg-ℤ k)) k
neg-neg-ℤ (inl n) = refl
neg-neg-ℤ (inr (inl star)) = refl
neg-neg-ℤ (inr (inr n)) = refl

neg-pred-ℤ :
  (k : ℤ) → Id (neg-ℤ (pred-ℤ k)) (succ-ℤ (neg-ℤ k))
neg-pred-ℤ (inl x) = refl
neg-pred-ℤ (inr (inl star)) = refl
neg-pred-ℤ (inr (inr zero-ℕ)) = refl
neg-pred-ℤ (inr (inr (succ-ℕ x))) = refl

pred-neg-ℤ :
  (k : ℤ) → Id (pred-ℤ (neg-ℤ k)) (neg-ℤ (succ-ℤ k))
pred-neg-ℤ (inl zero-ℕ) = refl
pred-neg-ℤ (inl (succ-ℕ x)) = refl
pred-neg-ℤ (inr (inl star)) = refl
pred-neg-ℤ (inr (inr x)) = refl

right-negative-law-add-ℤ :
  (k l : ℤ) → Id (add-ℤ k (neg-ℤ l)) (neg-ℤ (add-ℤ (neg-ℤ k) l))
right-negative-law-add-ℤ (inl zero-ℕ) l =
  ( left-predecessor-law-add-ℤ zero-ℤ (neg-ℤ l)) ∙
  ( pred-neg-ℤ l)
right-negative-law-add-ℤ (inl (succ-ℕ x)) l =
  ( left-predecessor-law-add-ℤ (inl x) (neg-ℤ l)) ∙
  ( ( ap pred-ℤ (right-negative-law-add-ℤ (inl x) l)) ∙
    ( pred-neg-ℤ (add-ℤ (inr (inr x)) l)))
right-negative-law-add-ℤ (inr (inl star)) l = refl
right-negative-law-add-ℤ (inr (inr zero-ℕ)) l = inv (neg-pred-ℤ l)
right-negative-law-add-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-successor-law-add-ℤ (in-pos n) (neg-ℤ l)) ∙
  ( ( ap succ-ℤ (right-negative-law-add-ℤ (inr (inr n)) l)) ∙
    ( inv (neg-pred-ℤ (add-ℤ (inl n) l))))

distributive-neg-add-ℤ :
  (k l : ℤ) → Id (neg-ℤ (add-ℤ k l)) (add-ℤ (neg-ℤ k) (neg-ℤ l))
distributive-neg-add-ℤ (inl zero-ℕ) l =
  ( ap neg-ℤ (left-predecessor-law-add-ℤ zero-ℤ l)) ∙
  ( neg-pred-ℤ l)
distributive-neg-add-ℤ (inl (succ-ℕ n)) l =
  ( neg-pred-ℤ (add-ℤ (inl n) l)) ∙
  ( ( ap succ-ℤ (distributive-neg-add-ℤ (inl n) l)) ∙
    ( ap (λ t → add-ℤ t (neg-ℤ l)) (inv (neg-pred-ℤ (inl n)))))
distributive-neg-add-ℤ (inr (inl star)) l = refl
distributive-neg-add-ℤ (inr (inr zero-ℕ)) l = inv (pred-neg-ℤ l)
distributive-neg-add-ℤ (inr (inr (succ-ℕ n))) l =
  ( inv (pred-neg-ℤ (add-ℤ (in-pos n) l))) ∙
  ( ap pred-ℤ (distributive-neg-add-ℤ (inr (inr n)) l))

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

right-successor-law-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ k (succ-ℤ l)) (add-ℤ k (mul-ℤ k l))
right-successor-law-mul-ℤ (inl zero-ℕ) l = inv (pred-neg-ℤ l)
right-successor-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( left-predecessor-law-mul-ℤ (inl n) (succ-ℤ l)) ∙
  ( ( ap (add-ℤ (neg-ℤ (succ-ℤ l))) (right-successor-law-mul-ℤ (inl n) l)) ∙
    ( ( inv (associative-add-ℤ (neg-ℤ (succ-ℤ l)) (inl n) (mul-ℤ (inl n) l))) ∙
      ( ( ap
          ( λ t → add-ℤ t (mul-ℤ (inl n) l))
          { x = add-ℤ (neg-ℤ (succ-ℤ l)) (inl n)}
          { y = add-ℤ (inl (succ-ℕ n)) (neg-ℤ l)}
          ( ( right-successor-law-add-ℤ (neg-ℤ (succ-ℤ l)) (inl (succ-ℕ n))) ∙
            ( ( ap succ-ℤ
                ( commutative-add-ℤ (neg-ℤ (succ-ℤ l)) (inl (succ-ℕ n)))) ∙
              ( ( inv
                  ( right-successor-law-add-ℤ
                    ( inl (succ-ℕ n))
                    ( neg-ℤ (succ-ℤ l)))) ∙
                ( ap
                  ( add-ℤ (inl (succ-ℕ n)))
                  ( ( ap succ-ℤ (inv (pred-neg-ℤ l))) ∙
                    ( right-inverse-pred-ℤ (neg-ℤ l)))))))) ∙
        ( associative-add-ℤ (inl (succ-ℕ n)) (neg-ℤ l) (mul-ℤ (inl n) l)))))
right-successor-law-mul-ℤ (inr (inl star)) l = refl
right-successor-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
right-successor-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-successor-law-mul-ℤ (in-pos n) (succ-ℤ l)) ∙
  ( ( ap (add-ℤ (succ-ℤ l)) (right-successor-law-mul-ℤ (inr (inr n)) l)) ∙
    ( ( inv (associative-add-ℤ (succ-ℤ l) (in-pos n) (mul-ℤ (in-pos n) l))) ∙
      ( ( ap
          ( λ t → add-ℤ t (mul-ℤ (in-pos n) l))
          { x = add-ℤ (succ-ℤ l) (in-pos n)}
          { y = add-ℤ (in-pos (succ-ℕ n)) l}
          ( ( left-successor-law-add-ℤ l (in-pos n)) ∙
            ( ( ap succ-ℤ (commutative-add-ℤ l (in-pos n))) ∙
              ( inv (left-successor-law-add-ℤ (in-pos n) l))))) ∙
        ( associative-add-ℤ (inr (inr (succ-ℕ n))) l (mul-ℤ (inr (inr n)) l)))))

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

-- Exercise 5.8 (c)

right-distributive-mul-add-ℤ :
  (k l m : ℤ) → Id (mul-ℤ (add-ℤ k l) m) (add-ℤ (mul-ℤ k m) (mul-ℤ l m))
right-distributive-mul-add-ℤ (inl zero-ℕ) l m =
  ( left-predecessor-law-mul-ℤ l m) ∙
  ( ap
    ( λ t → add-ℤ t (mul-ℤ l m))
    ( inv
      ( ( left-predecessor-law-mul-ℤ zero-ℤ m) ∙
        ( right-unit-law-add-ℤ (neg-ℤ m)))))
right-distributive-mul-add-ℤ (inl (succ-ℕ x)) l m =
  ( left-predecessor-law-mul-ℤ (add-ℤ (inl x) l) m) ∙
  ( ( ap (add-ℤ (neg-ℤ m)) (right-distributive-mul-add-ℤ (inl x) l m)) ∙
    ( inv (associative-add-ℤ (neg-ℤ m) (mul-ℤ (inl x) m) (mul-ℤ l m))))
right-distributive-mul-add-ℤ (inr (inl star)) l m = refl
right-distributive-mul-add-ℤ (inr (inr zero-ℕ)) l m =
  left-successor-law-mul-ℤ l m
right-distributive-mul-add-ℤ (inr (inr (succ-ℕ n))) l m =
  ( left-successor-law-mul-ℤ (add-ℤ (in-pos n) l) m) ∙
  ( ( ap (add-ℤ m) (right-distributive-mul-add-ℤ (inr (inr n)) l m)) ∙
    ( inv (associative-add-ℤ m (mul-ℤ (in-pos n) m) (mul-ℤ l m))))

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
left-negative-law-mul-ℤ (inr (inl star)) l = refl
left-negative-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
left-negative-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-predecessor-law-mul-ℤ (inl n) l) ∙
  ( ( ap (add-ℤ (neg-ℤ l)) (left-negative-law-mul-ℤ (inr (inr n)) l)) ∙
    ( inv (distributive-neg-add-ℤ l (mul-ℤ (in-pos n) l))))

-- Exercise 5.8 (d)

associative-mul-ℤ :
  (k l m : ℤ) → Id (mul-ℤ (mul-ℤ k l) m) (mul-ℤ k (mul-ℤ l m))
associative-mul-ℤ (inl zero-ℕ) l m =
  left-negative-law-mul-ℤ l m
associative-mul-ℤ (inl (succ-ℕ n)) l m =
  ( right-distributive-mul-add-ℤ (neg-ℤ l) (mul-ℤ (inl n) l) m) ∙
  ( ( ap (add-ℤ (mul-ℤ (neg-ℤ l) m)) (associative-mul-ℤ (inl n) l m)) ∙
    ( ap
      ( λ t → add-ℤ t (mul-ℤ (inl n) (mul-ℤ l m)))
      ( left-negative-law-mul-ℤ l m)))
associative-mul-ℤ (inr (inl star)) l m = refl
associative-mul-ℤ (inr (inr zero-ℕ)) l m = refl
associative-mul-ℤ (inr (inr (succ-ℕ n))) l m =
  ( right-distributive-mul-add-ℤ l (mul-ℤ (in-pos n) l) m) ∙
  ( ap (add-ℤ (mul-ℤ l m)) (associative-mul-ℤ (inr (inr n)) l m))

commutative-mul-ℤ :
  (k l : ℤ) → Id (mul-ℤ k l) (mul-ℤ l k)
commutative-mul-ℤ (inl zero-ℕ) l = inv (right-neg-unit-law-mul-ℤ l)
commutative-mul-ℤ (inl (succ-ℕ n)) l =
  ( ap (add-ℤ (neg-ℤ l)) (commutative-mul-ℤ (inl n) l)) ∙
  ( inv (right-predecessor-law-mul-ℤ l (inl n)))
commutative-mul-ℤ (inr (inl star)) l = inv (right-zero-law-mul-ℤ l)
commutative-mul-ℤ (inr (inr zero-ℕ)) l = inv (right-unit-law-mul-ℤ l)
commutative-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( ap (add-ℤ l) (commutative-mul-ℤ (inr (inr n)) l)) ∙
  ( inv (right-successor-law-mul-ℤ l (in-pos n)))

--------------------------------------------------------------------------------
