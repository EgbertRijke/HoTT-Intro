{-# OPTIONS --without-K --exact-split #-}

module 10-number-theory where

import 09-truncation-levels
open 09-truncation-levels public

-- Section 10.1 Decidability.

{- Recall that a proposition P is decidable if P + (¬ P) holds. -}

decidable-Prop :
  (l : Level) → UU (lsuc l)
decidable-Prop l = Σ (hProp l) (λ P → decide (pr1 P))

abstract
  is-decidable-Eq-ℕ :
    (m n : ℕ) → decide (Eq-ℕ m n)
  is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
  is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
  is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
  is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n

abstract
  is-decidable-leq-ℕ :
    (m n : ℕ) → decide (leq-ℕ m n)
  is-decidable-leq-ℕ zero-ℕ zero-ℕ = inl star
  is-decidable-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
  is-decidable-leq-ℕ (succ-ℕ m) zero-ℕ = inr id
  is-decidable-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-leq-ℕ m n

abstract
  is-decidable-le-ℕ :
    (m n : ℕ) → decide (le-ℕ m n)
  is-decidable-le-ℕ zero-ℕ zero-ℕ = inr id
  is-decidable-le-ℕ zero-ℕ (succ-ℕ n) = inl star
  is-decidable-le-ℕ (succ-ℕ m) zero-ℕ = inr id
  is-decidable-le-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-le-ℕ m n

{- We say that a type has decidable equality if we can decide whether x = y
   holds for any x,y:A. -}
   
has-decidable-equality : {l : Level} (A : UU l) → UU l
has-decidable-equality A = (x y : A) → decide (Id x y)

{- Next, we show that types with decidable equality are sets. To see this, we 
   will construct a fiberwise equivalence with the binary relation R that is
   defined by R x y := unit if (x = y), and empty otherwise. In order to define
   this relation, we first define a type family over ((x = y) + ¬(x = y)) that 
   returns unit on the left and empty on the right. -}
   
splitting-decidable-equality : {l : Level} (A : UU l) (x y : A) →
  decide (Id x y) → UU lzero
splitting-decidable-equality A x y (inl p) = unit
splitting-decidable-equality A x y (inr f) = empty

abstract
  is-prop-splitting-decidable-equality : {l : Level} (A : UU l) (x y : A) →
    (t : decide (Id x y)) →
    is-prop (splitting-decidable-equality A x y t)
  is-prop-splitting-decidable-equality A x y (inl p) = is-prop-unit
  is-prop-splitting-decidable-equality A x y (inr f) = is-prop-empty

reflexive-splitting-decidable-equality : {l : Level} (A : UU l) (x : A) →
  (t : decide (Id x x)) → splitting-decidable-equality A x x t
reflexive-splitting-decidable-equality A x (inl p) = star
reflexive-splitting-decidable-equality A x (inr f) =
  ind-empty {P = λ t → splitting-decidable-equality A x x (inr f)} (f refl)

eq-splitting-decidable-equality : {l : Level} (A : UU l) (x y : A) →
  (t : decide (Id x y)) →
  splitting-decidable-equality A x y t → Id x y
eq-splitting-decidable-equality A x y (inl p) t = p
eq-splitting-decidable-equality A x y (inr f) t =
  ind-empty {P = λ s → Id x y} t 

abstract
  is-set-has-decidable-equality : {l : Level} (A : UU l) →
    has-decidable-equality A → is-set A
  is-set-has-decidable-equality A d =
    is-set-prop-in-id
      ( λ x y → splitting-decidable-equality A x y (d x y))
      ( λ x y → is-prop-splitting-decidable-equality A x y (d x y))
      ( λ x → reflexive-splitting-decidable-equality A x (d x x))
      ( λ x y → eq-splitting-decidable-equality A x y (d x y))

abstract
  has-decidable-equality-coprod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    has-decidable-equality A → has-decidable-equality B →
    has-decidable-equality (coprod A B)
  has-decidable-equality-coprod dec-A dec-B (inl x) (inl y) =
    functor-coprod
      ( ap inl)
      ( λ f p → f (inv-is-equiv (is-emb-inl _ _ x y) p))
      ( dec-A x y)
  has-decidable-equality-coprod {A = A} {B = B} dec-A dec-B (inl x) (inr y) =
    inr
      ( λ p →
        inv-is-equiv
          ( is-equiv-map-raise _ empty)
          ( Eq-coprod-eq A B (inl x) (inr y) p))
  has-decidable-equality-coprod {A = A} {B = B} dec-A dec-B (inr x) (inl y) =
    inr
      ( λ p →
        inv-is-equiv
          ( is-equiv-map-raise _ empty)
          ( Eq-coprod-eq A B (inr x) (inl y) p))
  has-decidable-equality-coprod dec-A dec-B (inr x) (inr y) =
    functor-coprod
      ( ap inr)
      ( λ f p → f (inv-is-equiv (is-emb-inr _ _ x y) p))
      ( dec-B x y)

{- Decidable equality of Fin n. -}

has-decidable-equality-empty :
  has-decidable-equality empty
has-decidable-equality-empty ()

has-decidable-equality-unit :
  has-decidable-equality unit
has-decidable-equality-unit star star = inl refl

abstract
  has-decidable-equality-Fin :
    (n : ℕ) → has-decidable-equality (Fin n)
  has-decidable-equality-Fin zero-ℕ = has-decidable-equality-empty
  has-decidable-equality-Fin (succ-ℕ n) =
    has-decidable-equality-coprod
      ( has-decidable-equality-Fin n)
      ( has-decidable-equality-unit)

abstract
  is-set-Fin :
    (n : ℕ) → is-set (Fin n)
  is-set-Fin n =
    is-set-has-decidable-equality
      ( Fin n)
      ( has-decidable-equality-Fin n)

{- Decidable equality of ℕ. -}

Eq-ℕ-eq : (x y : ℕ) → Id x y → Eq-ℕ x y
Eq-ℕ-eq x .x refl = refl-Eq-ℕ x

abstract
  injective-succ-ℕ : (x y : ℕ) → Id (succ-ℕ x) (succ-ℕ y) → Id x y
  injective-succ-ℕ zero-ℕ zero-ℕ p = refl
  injective-succ-ℕ zero-ℕ (succ-ℕ y) p =
    ind-empty
      { P = λ t → Id zero-ℕ (succ-ℕ y)}
      ( Eq-ℕ-eq one-ℕ (succ-ℕ (succ-ℕ y)) p)
  injective-succ-ℕ (succ-ℕ x) zero-ℕ p =
    ind-empty
      { P = λ t → Id (succ-ℕ x) zero-ℕ}
      ( Eq-ℕ-eq (succ-ℕ (succ-ℕ x)) one-ℕ p)
  injective-succ-ℕ (succ-ℕ x) (succ-ℕ y) p =
    ap succ-ℕ (eq-Eq-ℕ x y (Eq-ℕ-eq (succ-ℕ (succ-ℕ x)) (succ-ℕ (succ-ℕ y)) p))

abstract
  has-decidable-equality-ℕ : has-decidable-equality ℕ
  has-decidable-equality-ℕ zero-ℕ zero-ℕ = inl refl
  has-decidable-equality-ℕ zero-ℕ (succ-ℕ y) = inr (Eq-ℕ-eq zero-ℕ (succ-ℕ y))
  has-decidable-equality-ℕ (succ-ℕ x) zero-ℕ = inr (Eq-ℕ-eq (succ-ℕ x) zero-ℕ)
  has-decidable-equality-ℕ (succ-ℕ x) (succ-ℕ y) =
    functor-coprod
      ( ap succ-ℕ)
      ( λ (f : ¬ (Id x y)) p → f (injective-succ-ℕ x y p))
      ( has-decidable-equality-ℕ x y)

{- The Pigeon hole principle. -}

{- First we write a function that counts the number of elements in a decidable
   subset of a finite set. -}

count-Fin-succ-ℕ :
  {l : Level} (n : ℕ) (P : Fin (succ-ℕ n) → decidable-Prop l) →
  ℕ → decide (pr1 (pr1 (P (inr star)))) → ℕ
count-Fin-succ-ℕ n P m (inl x) = succ-ℕ m
count-Fin-succ-ℕ n P m (inr x) = m

count-Fin :
  (l : Level) (n : ℕ) (P : Fin n → decidable-Prop l) → ℕ
count-Fin l zero-ℕ P = zero-ℕ
count-Fin l (succ-ℕ n) P =
  count-Fin-succ-ℕ n P
    ( count-Fin l n (P ∘ inl))
    ( pr2 (P (inr star)))

{- Next we prove the pigeonhole principle. -}

decidable-Eq-Fin :
  (n : ℕ) (i j : Fin n) → decidable-Prop lzero
decidable-Eq-Fin n i j =
  pair
    ( pair (Id i j) (is-set-Fin n i j))
    ( has-decidable-equality-Fin n i j)

{-
pigeonhole-principle :
  (m n : ℕ) (f : Fin n → Fin m) (H : le-ℕ m n) →
  Σ ( Fin m) (λ i →
    le-ℕ one-ℕ
      ( count-Fin lzero n
        ( λ j → decidable-Eq-Fin m (f j) i)))
pigeonhole-principle zero-ℕ (succ-ℕ n) f H = {!!}
pigeonhole-principle (succ-ℕ m) n f H = {!!}
-}

-- Exercises

-- Exercise 10.?

Eq-𝟚-eq : (x y : bool) → Id x y → Eq-𝟚 x y
Eq-𝟚-eq x .x refl = reflexive-Eq-𝟚 x

abstract
  has-decidable-equality-𝟚 : has-decidable-equality bool
  has-decidable-equality-𝟚 true true = inl refl
  has-decidable-equality-𝟚 true false = inr (Eq-𝟚-eq true false)
  has-decidable-equality-𝟚 false true = inr (Eq-𝟚-eq false true)
  has-decidable-equality-𝟚 false false = inl refl

-- Exercise 10.?

abstract
  has-decidable-equality-prod' : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    (x x' : A) (y y' : B) → decide (Id x x') → decide (Id y y') →
    decide (Id (pair x y) (pair x' y'))
  has-decidable-equality-prod' x x' y y' (inl p) (inl q) =
    inl (eq-pair-triv (pair p q))
  has-decidable-equality-prod' x x' y y' (inl p) (inr g) =
    inr (λ h → g (ap pr2 h))
  has-decidable-equality-prod' x x' y y' (inr f) (inl q) =
    inr (λ h → f (ap pr1 h))
  has-decidable-equality-prod' x x' y y' (inr f) (inr g) =
    inr (λ h → f (ap pr1 h))

abstract
  has-decidable-equality-prod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    has-decidable-equality A → has-decidable-equality B →
    has-decidable-equality (A × B)
  has-decidable-equality-prod dec-A dec-B (pair x y) (pair x' y') =
    has-decidable-equality-prod' x x' y y' (dec-A x x') (dec-B y y')

-- Exercise 10.?

decide-retract-of :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → decide B → decide A
decide-retract-of (pair i (pair r H)) (inl b) = inl (r b)
decide-retract-of (pair i (pair r H)) (inr f) = inr (f ∘ i)

abstract
  has-decidable-equality-retract-of :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    A retract-of B → has-decidable-equality B → has-decidable-equality A
  has-decidable-equality-retract-of (pair i (pair r H)) d x y =
    decide-retract-of
      ( Id-retract-of-Id (pair i (pair r H)) x y)
      ( d (i x) (i y))


{-

is-bounded-fam-ℕ :
  {l : Level} (n : ℕ) (P : ℕ → UU l) → UU l
is-bounded-fam-ℕ n P = (m : ℕ) → P m → leq-ℕ m n

bounds-fam-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
bounds-fam-ℕ P = Σ ℕ (λ n → is-bounded-fam-ℕ n P)

is-minimal-ℕ :
  {l : Level} (P : ℕ → UU l) → Σ ℕ P → UU l
is-minimal-ℕ P (pair n p) = (t : Σ ℕ P) → leq-ℕ n (pr1 t)

leq-zero-ℕ :
  (n : ℕ) → leq-ℕ zero-ℕ n
leq-zero-ℕ zero-ℕ = star
leq-zero-ℕ (succ-ℕ n) = star

eq-zero-leq-zero-ℕ :
  (n : ℕ) → leq-ℕ n zero-ℕ → Id n zero-ℕ
eq-zero-leq-zero-ℕ zero-ℕ star = refl
eq-zero-leq-zero-ℕ (succ-ℕ n) ()

fam-succ-ℕ :
  {l : Level} → (ℕ → UU l) → (ℕ → UU l)
fam-succ-ℕ P n = P (succ-ℕ n)

decide-fam-succ-ℕ :
  {l : Level} (P : ℕ → UU l) →
  ((n : ℕ) → decide (P n)) → ((n : ℕ) → decide (P (succ-ℕ n)))
decide-fam-succ-ℕ P d n = d (succ-ℕ n)

min-is-bounded-not-zero-ℕ :
  {l : Level} (P : ℕ → UU l) → ((n : ℕ) → decide (P n)) →
  Σ ℕ (λ n → is-bounded-fam-ℕ n P) →
  ¬ (P zero-ℕ) →
  Σ (Σ ℕ (fam-succ-ℕ P)) (is-minimal-ℕ (fam-succ-ℕ P)) →
  Σ (Σ ℕ P) (is-minimal-ℕ P)
min-is-bounded-not-zero-ℕ P d b np0 t = {!!}

min-is-bounded-ℕ :
  {l : Level} (P : ℕ → UU l) → ((n : ℕ) → decide (P n)) →
  Σ ℕ (λ n → is-bounded-fam-ℕ n P) →
  Σ ℕ P → Σ (Σ ℕ P) (is-minimal-ℕ P)
min-is-bounded-ℕ P d (pair zero-ℕ b) t =
  pair
    ( pair
      ( zero-ℕ)
      ( tr P (eq-zero-leq-zero-ℕ (pr1 t) (b (pr1 t) (pr2 t))) (pr2 t)))
    ( λ p → leq-zero-ℕ (pr1 p))
min-is-bounded-ℕ P d (pair (succ-ℕ n) b) t =
  ind-coprod
    ( λ (t : decide (P zero-ℕ)) → Σ (Σ ℕ P) (is-minimal-ℕ P))
    ( λ p0 → pair (pair zero-ℕ p0) (λ p → leq-zero-ℕ (pr1 p)))
    ( λ y → min-is-bounded-not-zero-ℕ P d (pair (succ-ℕ n) b) y
      ( min-is-bounded-ℕ
        ( fam-succ-ℕ P)
        ( decide-fam-succ-ℕ P d)
        {!!}
        {!!}))
    ( d zero-ℕ)

{- We show that every non-empty decidable subset of ℕ has a least element. -}

least-ℕ :
  {l : Level} (P : ℕ → UU l) → Σ ℕ P → UU l
least-ℕ P (pair n p) = (m : ℕ) → P m → leq-ℕ n m

least-element-non-empty-decidable-subset-ℕ :
  {l : Level} (P : ℕ → UU l) (d : (n : ℕ) → decide (P n)) →
  Σ ℕ P → Σ (Σ ℕ P) (least-ℕ P)
least-element-non-empty-decidable-subset-ℕ P d (pair zero-ℕ p) =
  pair (pair zero-ℕ p) {!!}
least-element-non-empty-decidable-subset-ℕ P d (pair (succ-ℕ n) p) = {!!}
-}
