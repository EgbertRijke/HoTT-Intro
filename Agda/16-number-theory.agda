{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module 16-number-theory where

import 15-sets
open 15-sets public

-- Section 10.1 Decidability.

{- Recall that a proposition P is decidable if P + (¬ P) holds. -}

classical-Prop :
  (l : Level) → UU (lsuc l)
classical-Prop l = Σ (UU-Prop l) (λ P → is-decidable (pr1 P))

is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n

is-decidable-leq-ℕ :
  (m n : ℕ) → is-decidable (leq-ℕ m n)
is-decidable-leq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-leq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-leq-ℕ m n

is-decidable-le-ℕ :
  (m n : ℕ) → is-decidable (le-ℕ m n)
is-decidable-le-ℕ zero-ℕ zero-ℕ = inr id
is-decidable-le-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-le-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-le-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-le-ℕ m n

{- Not every type is decidable. -}

case-elim :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ¬ B → coprod A B → A
case-elim nb (inl a) = a
case-elim nb (inr b) = ex-falso' (nb b)

is-prop-neg :
  {l : Level} {A : UU l} → is-prop (¬ A)
is-prop-neg {A = A} = is-prop-function-type is-prop-empty

neg-Prop :
  {l : Level} (A : UU l) → UU-Prop l
neg-Prop A = pair (¬ A) is-prop-neg

dn-Prop :
  {l : Level} (A : UU l) → UU-Prop l
dn-Prop A = pair (¬¬ A) is-prop-neg

simplify-not-all-2-element-types-decidable :
  {l : Level} →
  ((X : UU l) (p : type-trunc-Prop (bool ≃ X)) → is-decidable X) →
  ((X : UU l) (p : type-trunc-Prop (bool ≃ X)) → X)
simplify-not-all-2-element-types-decidable d X p =
  case-elim
    ( map-universal-property-trunc-Prop
      ( dn-Prop X)
      ( λ e → intro-dn (map-equiv e true))
      ( p))
    ( d X p)

not-all-2-element-types-decidable :
  {l : Level} → ¬ ((X : UU l) (p : type-trunc-Prop (bool ≃ X)) → is-decidable X)
not-all-2-element-types-decidable d = {!simplify-not-all-2-element-types-decidable d (raise _ bool) ?!}

not-all-types-decidable :
  {l : Level} → ¬ ((X : UU l) → is-decidable X)
not-all-types-decidable d =
  not-all-2-element-types-decidable (λ X p → d X)

{- We say that a type has decidable equality if we can decide whether 
   x = y holds for any x,y:A. -}
   
has-decidable-equality : {l : Level} (A : UU l) → UU l
has-decidable-equality A = (x y : A) → is-decidable (Id x y)

{- The type ℕ is an example of a type with decidable equality. -}

is-injective-succ-ℕ : (x y : ℕ) → Id (succ-ℕ x) (succ-ℕ y) → Id x y
is-injective-succ-ℕ zero-ℕ zero-ℕ p = refl
is-injective-succ-ℕ zero-ℕ (succ-ℕ y) p =
  ind-empty
    { P = λ t → Id zero-ℕ (succ-ℕ y)}
    ( Eq-ℕ-eq {-one-ℕ (succ-ℕ (succ-ℕ y))-} p)
is-injective-succ-ℕ (succ-ℕ x) zero-ℕ p =
  ind-empty
    { P = λ t → Id (succ-ℕ x) zero-ℕ}
    ( Eq-ℕ-eq {-(succ-ℕ (succ-ℕ x)) one-ℕ-} p)
is-injective-succ-ℕ (succ-ℕ x) (succ-ℕ y) p =
  ap succ-ℕ (eq-Eq-ℕ x y (Eq-ℕ-eq {-(succ-ℕ (succ-ℕ x)) (succ-ℕ (succ-ℕ y))-} p))

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ zero-ℕ zero-ℕ = inl refl
has-decidable-equality-ℕ zero-ℕ (succ-ℕ y) = inr (Eq-ℕ-eq {-zero-ℕ (succ-ℕ y)-})
has-decidable-equality-ℕ (succ-ℕ x) zero-ℕ = inr (Eq-ℕ-eq {-(succ-ℕ x) zero-ℕ-})
has-decidable-equality-ℕ (succ-ℕ x) (succ-ℕ y) =
  functor-coprod
    ( ap succ-ℕ)
    ( λ (f : ¬ (Id x y)) p → f (is-injective-succ-ℕ x y p))
    ( has-decidable-equality-ℕ x y)

{- Types with decidable equality are closed under coproducts. -}

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

has-decidable-equality-empty : has-decidable-equality empty
has-decidable-equality-empty ()

has-decidable-equality-unit :
  has-decidable-equality unit
has-decidable-equality-unit star star = inl refl

has-decidable-equality-Fin :
  (n : ℕ) → has-decidable-equality (Fin n)
has-decidable-equality-Fin zero-ℕ = has-decidable-equality-empty
has-decidable-equality-Fin (succ-ℕ n) =
  has-decidable-equality-coprod
    ( has-decidable-equality-Fin n)
    ( has-decidable-equality-unit)

decidable-Eq-Fin :
  (n : ℕ) (i j : Fin n) → classical-Prop lzero
decidable-Eq-Fin n i j =
  pair
    ( pair (Id i j) (is-set-Fin n i j))
    ( has-decidable-equality-Fin n i j)

{- Decidable equality of ℤ. -}

has-decidable-equality-ℤ : has-decidable-equality ℤ
has-decidable-equality-ℤ =
  has-decidable-equality-coprod
    has-decidable-equality-ℕ
    ( has-decidable-equality-coprod
      has-decidable-equality-unit
      has-decidable-equality-ℕ)

{- Next, we show that types with decidable equality are sets. To see this, we 
   will construct a fiberwise equivalence with the binary relation R that is
   defined by R x y := unit if (x = y), and empty otherwise. In order to define
   this relation, we first define a type family over ((x = y) + ¬(x = y)) that 
   returns unit on the left and empty on the right. -}
   
splitting-decidable-equality : {l : Level} (A : UU l) (x y : A) →
  is-decidable (Id x y) → UU lzero
splitting-decidable-equality A x y (inl p) = unit
splitting-decidable-equality A x y (inr f) = empty

is-prop-splitting-decidable-equality : {l : Level} (A : UU l) (x y : A) →
  (t : is-decidable (Id x y)) →
  is-prop (splitting-decidable-equality A x y t)
is-prop-splitting-decidable-equality A x y (inl p) = is-prop-unit
is-prop-splitting-decidable-equality A x y (inr f) = is-prop-empty

reflexive-splitting-decidable-equality : {l : Level} (A : UU l) (x : A) →
  (t : is-decidable (Id x x)) → splitting-decidable-equality A x x t
reflexive-splitting-decidable-equality A x (inl p) = star
reflexive-splitting-decidable-equality A x (inr f) =
  ind-empty {P = λ t → splitting-decidable-equality A x x (inr f)} (f refl)

eq-splitting-decidable-equality : {l : Level} (A : UU l) (x y : A) →
  (t : is-decidable (Id x y)) →
  splitting-decidable-equality A x y t → Id x y
eq-splitting-decidable-equality A x y (inl p) t = p
eq-splitting-decidable-equality A x y (inr f) t =
  ind-empty {P = λ s → Id x y} t 

is-set-has-decidable-equality : {l : Level} (A : UU l) →
  has-decidable-equality A → is-set A
is-set-has-decidable-equality A d =
  is-set-prop-in-id
    ( λ x y → splitting-decidable-equality A x y (d x y))
    ( λ x y → is-prop-splitting-decidable-equality A x y (d x y))
    ( λ x → reflexive-splitting-decidable-equality A x (d x x))
    ( λ x y → eq-splitting-decidable-equality A x y (d x y))

{- Closure of decidable types under retracts and equivalences. -}

is-decidable-retract-of :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → is-decidable B → is-decidable A
is-decidable-retract-of (pair i (pair r H)) (inl b) = inl (r b)
is-decidable-retract-of (pair i (pair r H)) (inr f) = inr (f ∘ i)

is-decidable-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (is-equiv-f : is-equiv f) → is-decidable B → is-decidable A
is-decidable-is-equiv {f = f} (pair (pair g G) (pair h H)) =
  is-decidable-retract-of (pair f (pair h H))

is-decidable-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-decidable B → is-decidable A
is-decidable-equiv e = is-decidable-is-equiv (is-equiv-map-equiv e)

is-decidable-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-decidable A → is-decidable B
is-decidable-equiv' e = is-decidable-equiv (inv-equiv e)

has-decidable-equality-retract-of :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → has-decidable-equality B → has-decidable-equality A
has-decidable-equality-retract-of (pair i (pair r H)) d x y =
  is-decidable-retract-of
    ( Id-retract-of-Id (pair i (pair r H)) x y)
    ( d (i x) (i y))

{- The well-ordering principle. -}

is-minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) (p : P n) → UU l
is-minimal-element-ℕ P n p =
  (m : ℕ) → P m → (leq-ℕ n m)

minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
minimal-element-ℕ P = Σ ℕ (λ n → Σ (P n) (is-minimal-element-ℕ P n))

is-minimal-element-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : (n : ℕ) → is-decidable (P n))
  (m : ℕ) (pm : P (succ-ℕ m))
  (is-min-m : is-minimal-element-ℕ (λ x → P (succ-ℕ x)) m pm) →
  ¬ (P zero-ℕ) → is-minimal-element-ℕ P (succ-ℕ m) pm
is-minimal-element-succ-ℕ P d m pm is-min-m neg-p0 zero-ℕ p0 =
  ind-empty (neg-p0 p0)
is-minimal-element-succ-ℕ P d zero-ℕ pm is-min-m neg-p0 (succ-ℕ n) psuccn =
  leq-zero-ℕ n
is-minimal-element-succ-ℕ P d (succ-ℕ m) pm is-min-m neg-p0 (succ-ℕ n) psuccn =
  is-minimal-element-succ-ℕ (λ x → P (succ-ℕ x)) (λ x → d (succ-ℕ x)) m pm
    ( λ m → is-min-m (succ-ℕ m))
    ( is-min-m zero-ℕ)
    ( n)
    ( psuccn)
  
well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : (n : ℕ) → is-decidable (P n))
  (n : ℕ) (p : P (succ-ℕ n)) →
  is-decidable (P zero-ℕ) →
  minimal-element-ℕ (λ m → P (succ-ℕ m)) → minimal-element-ℕ P
well-ordering-principle-succ-ℕ P d n p (inl p0) _ =
  pair zero-ℕ (pair p0 (λ m q → leq-zero-ℕ m))
well-ordering-principle-succ-ℕ P d n p
  (inr neg-p0) (pair m (pair pm is-min-m)) =
  pair
    ( succ-ℕ m)
    ( pair pm
      ( is-minimal-element-succ-ℕ P d m pm is-min-m neg-p0))

well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : (n : ℕ) → is-decidable (P n)) →
  Σ ℕ P → minimal-element-ℕ P
well-ordering-principle-ℕ P d (pair zero-ℕ p) =
  pair zero-ℕ (pair p (λ m q → leq-zero-ℕ m))
well-ordering-principle-ℕ P d (pair (succ-ℕ n) p) =
  well-ordering-principle-succ-ℕ P d n p (d zero-ℕ)
    ( well-ordering-principle-ℕ
      ( λ m → P (succ-ℕ m))
      ( λ m → d (succ-ℕ m))
      ( pair n p))

-- Exercise 6.7

-- We prove that the induction principle for ℕ implies strong induction.

-- We first prove some lemmas about inequality.

zero-ℕ-leq-ℕ :
  (n : ℕ) → leq-ℕ zero-ℕ n
zero-ℕ-leq-ℕ n = star

is-prop-leq-ℕ :
  (m n : ℕ) → is-prop (leq-ℕ m n)
is-prop-leq-ℕ zero-ℕ zero-ℕ = is-prop-unit
is-prop-leq-ℕ zero-ℕ (succ-ℕ n) = is-prop-unit
is-prop-leq-ℕ (succ-ℕ m) zero-ℕ = is-prop-empty
is-prop-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-prop-leq-ℕ m n

neg-succ-leq-ℕ :
  (n : ℕ) → ¬ (leq-ℕ (succ-ℕ n) n)
neg-succ-leq-ℕ zero-ℕ = id
neg-succ-leq-ℕ (succ-ℕ n) = neg-succ-leq-ℕ n

leq-eq-left-ℕ :
  {m m' : ℕ} → Id m m' → (n : ℕ) → leq-ℕ m n → leq-ℕ m' n
leq-eq-left-ℕ refl n = id

leq-eq-right-ℕ :
  (m : ℕ) {n n' : ℕ} → Id n n' → leq-ℕ m n → leq-ℕ m n'
leq-eq-right-ℕ m refl = id

-- Now we begin with the proof of the theorem
 
fam-strong-ind-ℕ :
  { l : Level} → (ℕ → UU l) → ℕ → UU l
fam-strong-ind-ℕ P n = (m : ℕ) → (leq-ℕ m n) → P m

-- We first take care of the zero case, with appropriate computation rule.

zero-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) → P zero-ℕ → fam-strong-ind-ℕ P zero-ℕ
zero-strong-ind-ℕ P p0 zero-ℕ t = p0
zero-strong-ind-ℕ P p0 (succ-ℕ m) ()

eq-zero-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) (t : leq-ℕ zero-ℕ zero-ℕ) →
  Id (zero-strong-ind-ℕ P p0 zero-ℕ t) p0
eq-zero-strong-ind-ℕ P p0 t = refl

-- Next, we take care of the successor case, with appropriate computation rule.

{- In the successor case, we need to define a map

   fam-strong-ind-ℕ P k → fam-strong-ind-ℕ P (succ-ℕ k).

   The dependent function in the codomain is defined by case analysis, where
   the cases are that either m ≤ k or m = k+1.
   -}

-- We use the following definition to get a map (m≤k+1) → coprod (m≤k) (m=k+1).

cases-leq-succ-ℕ :
  {m n : ℕ} → leq-ℕ m (succ-ℕ n) → coprod (leq-ℕ m n) (Id m (succ-ℕ n))
cases-leq-succ-ℕ {zero-ℕ} {n} star = inl star
cases-leq-succ-ℕ {succ-ℕ m} {zero-ℕ} p =
  inr (ap succ-ℕ (anti-symmetric-leq-ℕ m zero-ℕ p star))
cases-leq-succ-ℕ {succ-ℕ m} {succ-ℕ n} p =
  functor-coprod id (ap succ-ℕ) (cases-leq-succ-ℕ p)
   
cases-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( (n : ℕ) → (fam-strong-ind-ℕ P n) → P (succ-ℕ n)) →
  ( n : ℕ) (H : fam-strong-ind-ℕ P n) →
  ( m : ℕ) ( c : coprod (leq-ℕ m n) (Id m (succ-ℕ n))) → P m
cases-succ-strong-ind-ℕ P pS n H m (inl q) = H m q
cases-succ-strong-ind-ℕ P pS n H .(succ-ℕ n) (inr refl) = pS n H

succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  ( k : ℕ) → (fam-strong-ind-ℕ P k) → (fam-strong-ind-ℕ P (succ-ℕ k))
succ-strong-ind-ℕ P pS k H m p =
  cases-succ-strong-ind-ℕ P pS k H m (cases-leq-succ-ℕ p)

-- We use a similar case analysis to obtain the computation rule.

{-
exclusive-coprod-leq-eq-succ-ℕ :
  (m n : ℕ) → leq-ℕ m n → ¬ (Id m (succ-ℕ n))
exclusive-coprod-leq-eq-succ-ℕ zero-ℕ zero-ℕ star = {!Eq-eq-ℕ!}
exclusive-coprod-leq-eq-succ-ℕ zero-ℕ (succ-ℕ n) p = {!!}
exclusive-coprod-leq-eq-succ-ℕ (succ-ℕ m) (succ-ℕ n) p = {!!}

is-prop'-coprod-leq-eq-succ :
  (m n : ℕ) → is-prop' (coprod (leq-ℕ m n) (Id m (succ-ℕ n)))
is-prop'-coprod-leq-eq-succ m n =
  is-prop'-exclusive-coprod
    ( exclusive-coprod-leq-eq-succ-ℕ m n)
    ( is-prop'-is-prop (is-prop-leq-ℕ m n))
    ( is-prop'-is-prop (is-set-ℕ m (succ-ℕ n)))

tr-eq-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( pS : (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k))
  ( n : ℕ) (H : fam-strong-ind-ℕ P n)
  ( m : ℕ) (p : leq-ℕ m (succ-ℕ n))
  ( x : coprod (leq-ℕ m n) (Id m (succ-ℕ n))) (y : P m) →
  Id (succ-strong-ind-ℕ P pS n H m p) y →
  Id (cases-succ-strong-ind-ℕ P pS n H m x) y
tr-eq-succ-strong-ind-ℕ P pS n H m p x y =
  tr ( λ t → Id (cases-succ-strong-ind-ℕ P pS n H m t) y)
     ( is-prop'-coprod-leq-eq-succ m n (cases-leq-succ-ℕ p) x)
-}

cases-htpy-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( pS : (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  ( k : ℕ) (H : fam-strong-ind-ℕ P k) (m : ℕ)
  ( c : coprod (leq-ℕ m k) (Id m (succ-ℕ k))) →
  ( q : leq-ℕ m k) →
  Id
    ( cases-succ-strong-ind-ℕ P pS k H m c)
    ( H m q)
cases-htpy-succ-strong-ind-ℕ P pS k H m (inl p) q =
  ap (H m) (is-prop'-is-prop (is-prop-leq-ℕ m k) p q)
cases-htpy-succ-strong-ind-ℕ P pS k H m (inr α) q =
  ex-falso'
    ( neg-succ-leq-ℕ k (leq-eq-left-ℕ α k q))

htpy-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( pS : (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  ( k : ℕ) (H : fam-strong-ind-ℕ P k) (m : ℕ)
  ( p : leq-ℕ m (succ-ℕ k)) →
  ( q : leq-ℕ m k) →
  Id
    ( succ-strong-ind-ℕ P pS k H m p)
    ( H m q)
htpy-succ-strong-ind-ℕ P pS k H m p q =
  cases-htpy-succ-strong-ind-ℕ P pS k H m (cases-leq-succ-ℕ p) q

cases-eq-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( pS : (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  ( k : ℕ) (H : fam-strong-ind-ℕ P k)
  ( c : coprod (leq-ℕ (succ-ℕ k) k) (Id (succ-ℕ k) (succ-ℕ k))) →
  Id ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k) c))
     ( pS k H)
cases-eq-succ-strong-ind-ℕ P pS k H (inl p) = ex-falso' (neg-succ-leq-ℕ k p)
cases-eq-succ-strong-ind-ℕ P pS k H (inr α) =
  ap ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k)) ∘ inr)
     ( is-prop'-is-prop (is-set-ℕ (succ-ℕ k) (succ-ℕ k)) α refl)

eq-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( pS : (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  ( k : ℕ) (H : fam-strong-ind-ℕ P k)
  ( p : leq-ℕ (succ-ℕ k) (succ-ℕ k)) →
  Id ( (succ-strong-ind-ℕ P pS k H (succ-ℕ k) p))
     ( pS k H)
eq-succ-strong-ind-ℕ P pS k H p =
  cases-eq-succ-strong-ind-ℕ P pS k H (cases-leq-succ-ℕ p)

{- Now that we have the base case and inductive step covered, we can proceed
   by induction. -}

induction-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( fam-strong-ind-ℕ P zero-ℕ) →
  ( (k : ℕ) → (fam-strong-ind-ℕ P k) → (fam-strong-ind-ℕ P (succ-ℕ k))) →
  ( n : ℕ) → fam-strong-ind-ℕ P n
induction-strong-ind-ℕ P q0 qS zero-ℕ = q0
induction-strong-ind-ℕ P q0 qS (succ-ℕ n) =
  qS n (induction-strong-ind-ℕ P q0 qS n)

computation-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( q0 : fam-strong-ind-ℕ P zero-ℕ) →
  ( qS : (k : ℕ) → (fam-strong-ind-ℕ P k) → (fam-strong-ind-ℕ P (succ-ℕ k))) →
  ( n : ℕ) →
  Id ( induction-strong-ind-ℕ P q0 qS (succ-ℕ n))
     ( qS n (induction-strong-ind-ℕ P q0 qS n))
computation-succ-strong-ind-ℕ P q0 qS n = refl

{- However, to obtain the conclusion we need to make one more small step. -}

conclusion-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( ( n : ℕ) → fam-strong-ind-ℕ P n) → (n : ℕ) → P n
conclusion-strong-ind-ℕ P f n = f n n (reflexive-leq-ℕ n)

{- We are finally ready to put things together and define strong-ind-ℕ. -}

strong-ind-ℕ :
  { l : Level} → (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) → P n
strong-ind-ℕ P p0 pS = 
  conclusion-strong-ind-ℕ P
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS))

{- The computation rule for the base case holds by definition. -}

comp-zero-strong-ind-ℕ :
  { l : Level} → (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  Id (strong-ind-ℕ P p0 pS zero-ℕ) p0
comp-zero-strong-ind-ℕ P p0 pS = refl

{- For the computation rule of the inductive step, we use our hard work. -}

cases-leq-succ-reflexive-leq-ℕ :
  {n : ℕ} → Id (cases-leq-succ-ℕ {succ-ℕ n} {n} (reflexive-leq-ℕ n)) (inr refl)
cases-leq-succ-reflexive-leq-ℕ {zero-ℕ} = refl
cases-leq-succ-reflexive-leq-ℕ {succ-ℕ n} =
  ap (functor-coprod id (ap succ-ℕ)) cases-leq-succ-reflexive-leq-ℕ
  
cases-eq-comp-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( α :
    ( m : ℕ) (p : leq-ℕ m n) →
    Id ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
         ( λ k z m₁ z₁ →
           cases-succ-strong-ind-ℕ P pS k z m₁ (cases-leq-succ-ℕ z₁))
         n m p)
     ( strong-ind-ℕ P p0 pS m)) →
  ( m : ℕ) (p : leq-ℕ m (succ-ℕ n)) →
  ( q : coprod (leq-ℕ m n) (Id m (succ-ℕ n))) →
  Id ( succ-strong-ind-ℕ P pS n
       ( induction-strong-ind-ℕ P
         ( zero-strong-ind-ℕ P p0)
         ( succ-strong-ind-ℕ P pS) n) m p)
     ( strong-ind-ℕ P p0 pS m)
cases-eq-comp-succ-strong-ind-ℕ P p0 pS n α m p (inl x) =
  ( htpy-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n)
    m p x) ∙
  ( α m x)
cases-eq-comp-succ-strong-ind-ℕ P p0 pS n α .(succ-ℕ n) p (inr refl) =
  ( eq-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n)
    ( p)) ∙
  ( inv
    ( ap
      ( cases-succ-strong-ind-ℕ P pS n
        ( induction-strong-ind-ℕ P
          ( zero-strong-ind-ℕ P p0)
          ( λ k H m p₁ →
            cases-succ-strong-ind-ℕ P pS k H m (cases-leq-succ-ℕ p₁))
          n)
        ( succ-ℕ n))
       cases-leq-succ-reflexive-leq-ℕ))

eq-comp-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( m : ℕ) (p : leq-ℕ m n) →
  Id ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
       ( λ k z m₁ z₁ →
         cases-succ-strong-ind-ℕ P pS k z m₁ (cases-leq-succ-ℕ z₁))
       n m p)
     ( strong-ind-ℕ P p0 pS m)
eq-comp-succ-strong-ind-ℕ P p0 pS zero-ℕ zero-ℕ star = refl
eq-comp-succ-strong-ind-ℕ P p0 pS zero-ℕ (succ-ℕ m) ()
eq-comp-succ-strong-ind-ℕ P p0 pS (succ-ℕ n) m p =
  cases-eq-comp-succ-strong-ind-ℕ P p0 pS n
    ( eq-comp-succ-strong-ind-ℕ P p0 pS n) m p
    ( cases-leq-succ-ℕ p)

comp-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  Id (strong-ind-ℕ P p0 pS (succ-ℕ n)) (pS n (λ m p → strong-ind-ℕ P p0 pS m))
comp-succ-strong-ind-ℕ P p0 pS n = 
  ( eq-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS)
      ( n))
    ( reflexive-leq-ℕ n)) ∙
  ( ap ( pS n)
       ( eq-htpy
         ( λ m → eq-htpy
           ( λ p → eq-comp-succ-strong-ind-ℕ P p0 pS n m p))))

total-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (fam-strong-ind-ℕ P k) → P (succ-ℕ k)) →
  Σ ( (n : ℕ) → P n)
    ( λ h →
      ( Id (h zero-ℕ) p0) ×
      ( (n : ℕ) → Id (h (succ-ℕ n)) (pS n (λ m p → h m))))
total-strong-ind-ℕ P p0 pS =
  pair
    ( strong-ind-ℕ P p0 pS)
    ( pair
      ( comp-zero-strong-ind-ℕ P p0 pS)
      ( comp-succ-strong-ind-ℕ P p0 pS))

-- The Euclidean algorithm

subtract-ℕ : ℕ → ℕ → ℕ
subtract-ℕ zero-ℕ zero-ℕ = zero-ℕ
subtract-ℕ zero-ℕ (succ-ℕ b) = zero-ℕ
subtract-ℕ (succ-ℕ a) zero-ℕ = succ-ℕ a
subtract-ℕ (succ-ℕ a) (succ-ℕ b) = subtract-ℕ a b

leq-subtract-ℕ : (a b : ℕ) → leq-ℕ (subtract-ℕ a b) a
leq-subtract-ℕ zero-ℕ zero-ℕ = star
leq-subtract-ℕ zero-ℕ (succ-ℕ b) = star
leq-subtract-ℕ (succ-ℕ a) zero-ℕ = reflexive-leq-ℕ a
leq-subtract-ℕ (succ-ℕ a) (succ-ℕ b) =
  transitive-leq-ℕ (subtract-ℕ a b) a (succ-ℕ a)
    ( leq-subtract-ℕ a b)
    ( succ-leq-ℕ a)

decide-order-ℕ : (a b : ℕ) → coprod (leq-ℕ b a) (le-ℕ a b)
decide-order-ℕ zero-ℕ zero-ℕ = inl star
decide-order-ℕ zero-ℕ (succ-ℕ b) = inr star
decide-order-ℕ (succ-ℕ a) zero-ℕ = inl star
decide-order-ℕ (succ-ℕ a) (succ-ℕ b) = decide-order-ℕ a b

cases-gcd-euclid :
  ( a b : ℕ)
  ( F : (x : ℕ) (p : leq-ℕ x a) → ℕ → ℕ)
  ( G : (y : ℕ) (q : leq-ℕ y b) → ℕ) →
  ( coprod (leq-ℕ b a) (le-ℕ a b)) → ℕ
cases-gcd-euclid a b F G (inl t) =
  F (subtract-ℕ a b) (leq-subtract-ℕ a b) (succ-ℕ b)
cases-gcd-euclid a b F G (inr t) =
  G (subtract-ℕ b a) (leq-subtract-ℕ b a)

succ-gcd-euclid : (a : ℕ) (F : (x : ℕ) → (leq-ℕ x a) → ℕ → ℕ) → ℕ → ℕ
succ-gcd-euclid a F =
  strong-ind-ℕ
    ( λ x → ℕ)
    ( succ-ℕ a)
    ( λ b G →
      ind-coprod
        { A = leq-ℕ b a}
        { B = le-ℕ a b}
        ( λ x → ℕ)
        ( λ t → F (subtract-ℕ a b) (leq-subtract-ℕ a b) (succ-ℕ b))
        ( λ t → G (subtract-ℕ b a) (leq-subtract-ℕ b a))
        ( decide-order-ℕ a b))

comp-zero-succ-gcd-euclid :
  (a : ℕ) (F : (x : ℕ) → (leq-ℕ x a) → ℕ → ℕ) →
  Id (succ-gcd-euclid a F zero-ℕ) (succ-ℕ a)
comp-zero-succ-gcd-euclid a F =
  comp-zero-strong-ind-ℕ
    ( λ x → ℕ)
    ( succ-ℕ a)
    ( λ b G →
      ind-coprod
        { A = leq-ℕ b a}
        { B = le-ℕ a b}
        ( λ x → ℕ)
        ( λ t → F (subtract-ℕ a b) (leq-subtract-ℕ a b) (succ-ℕ b))
        ( λ t → G (subtract-ℕ b a) (leq-subtract-ℕ b a))
        ( decide-order-ℕ a b))

comp-succ-succ-gcd-euclid :
  (a : ℕ) (F : (x : ℕ) → (leq-ℕ x a) → ℕ → ℕ) (b : ℕ) →
  Id (succ-gcd-euclid a F (succ-ℕ b))
     ( ind-coprod
       { A = leq-ℕ b a}
       { B = le-ℕ a b}
       ( λ x → ℕ)
       ( λ t → F (subtract-ℕ a b) (leq-subtract-ℕ a b) (succ-ℕ b))
       ( λ t → succ-gcd-euclid a F (subtract-ℕ b a))
       ( decide-order-ℕ a b))
comp-succ-succ-gcd-euclid a F b =
  comp-succ-strong-ind-ℕ
    ( λ x → ℕ)
    ( succ-ℕ a)
    ( λ k z →
         ind-coprod (λ _ → ℕ)
         (λ x → F (subtract-ℕ a k) (leq-subtract-ℕ a k) (succ-ℕ k))
         (λ y → z (subtract-ℕ k a) (leq-subtract-ℕ k a))
         (decide-order-ℕ a k))
    ( b)

gcd-euclid : ℕ → ℕ → ℕ
gcd-euclid =
  strong-ind-ℕ
    ( λ x → ℕ → ℕ)
    ( id)
    ( succ-gcd-euclid)

comp-succ-gcd-euclid :
  (a : ℕ) →
  Id (gcd-euclid (succ-ℕ a)) (succ-gcd-euclid a (λ x p → gcd-euclid x))
comp-succ-gcd-euclid =
  comp-succ-strong-ind-ℕ (λ x → ℕ → ℕ) id succ-gcd-euclid

-- Properties of the greatest common divisor

left-zero-law-gcd-euclid : (gcd-euclid zero-ℕ) ~ id
left-zero-law-gcd-euclid =
  htpy-eq (comp-zero-strong-ind-ℕ (λ x → ℕ → ℕ) id succ-gcd-euclid)

right-zero-law-gcd-euclid : (a : ℕ) → Id (gcd-euclid a zero-ℕ) a
right-zero-law-gcd-euclid zero-ℕ = refl
right-zero-law-gcd-euclid (succ-ℕ a) =
   ( ap
     ( λ t →
       cases-succ-strong-ind-ℕ (λ x → ℕ → ℕ) succ-gcd-euclid a
       ( induction-strong-ind-ℕ
         ( λ x → ℕ → ℕ)
         ( zero-strong-ind-ℕ (λ x → ℕ → ℕ) (λ a₁ → a₁))
         ( λ k H m p →
           cases-succ-strong-ind-ℕ (λ x → ℕ → ℕ) succ-gcd-euclid k H m
           (cases-leq-succ-ℕ p))
         ( a))
       ( succ-ℕ a) t zero-ℕ)
     cases-leq-succ-reflexive-leq-ℕ) ∙
  ( comp-zero-succ-gcd-euclid a (λ x _ z → z))

is-prop-le-ℕ : (a b : ℕ) → is-prop (le-ℕ a b)
is-prop-le-ℕ zero-ℕ zero-ℕ = is-prop-empty
is-prop-le-ℕ zero-ℕ (succ-ℕ b) = is-prop-unit
is-prop-le-ℕ (succ-ℕ a) zero-ℕ = is-prop-empty
is-prop-le-ℕ (succ-ℕ a) (succ-ℕ b) = is-prop-le-ℕ a b

is-prop'-le-ℕ : (a b : ℕ) → is-prop' (le-ℕ a b)
is-prop'-le-ℕ a b = is-prop'-is-prop (is-prop-le-ℕ a b)

left-lesser-law-gcd-euclid : (a b : ℕ) → (le-ℕ a b) →
  Id (gcd-euclid a b) (gcd-euclid a (subtract-ℕ b a))
left-lesser-law-gcd-euclid zero-ℕ (succ-ℕ b) H = refl
left-lesser-law-gcd-euclid (succ-ℕ a) (succ-ℕ b) H =
  ( htpy-eq (comp-succ-gcd-euclid a) (succ-ℕ b)) ∙ {!!}


{-  ( (comp-succ-succ-gcd-euclid a (λ x t → gcd-euclid x) b) ∙
    ( ( {!!} ∙ apd (λ t → (ind-coprod (λ x → ℕ)
     (λ t → gcd-euclid (subtract-ℕ a b) (succ-ℕ b))
     (λ t → succ-gcd-euclid a (λ x t₁ → gcd-euclid x) (subtract-ℕ b a))
     t)) (ap inr (is-prop'-le-ℕ a b {!!} {!!}))) ∙ {!!}
{-      ( inv (ap (λ t → cases-succ-strong-ind-ℕ (λ x → ℕ → ℕ) succ-gcd-euclid a
        (induction-strong-ind-ℕ (λ x → ℕ → ℕ)
        (zero-strong-ind-ℕ (λ x → ℕ → ℕ) (λ a₁ → a₁))
        (λ k H₁ m p →
        cases-succ-strong-ind-ℕ (λ x → ℕ → ℕ) succ-gcd-euclid k H₁ m
        (cases-leq-succ-ℕ p))
        a)
        (succ-ℕ a) t
        (subtract-ℕ (succ-ℕ b) (succ-ℕ a))) cases-leq-succ-reflexive-leq-ℕ))-}))
-}            

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

{- The Pigeon hole principle. -}

{- First we write a function that counts the number of elements in a decidable
   subset of a finite set. -}

count-Fin-succ-ℕ :
  {l : Level} (n : ℕ) (P : Fin (succ-ℕ n) → classical-Prop l) →
  ℕ → is-decidable (pr1 (pr1 (P (inr star)))) → ℕ
count-Fin-succ-ℕ n P m (inl x) = succ-ℕ m
count-Fin-succ-ℕ n P m (inr x) = m

count-Fin :
  {l : Level} (n : ℕ) (P : Fin n → classical-Prop l) → ℕ
count-Fin zero-ℕ P = zero-ℕ
count-Fin (succ-ℕ n) P =
  count-Fin-succ-ℕ n P
    ( count-Fin n (P ∘ inl))
    ( pr2 (P (inr star)))

{- Next we prove the pigeonhole principle. -}

max-Fin :
  (n : ℕ) → Fin (succ-ℕ n)
max-Fin n = inr star

contraction-Fin-one-ℕ :
  (t : Fin one-ℕ) → Id (inr star) t
contraction-Fin-one-ℕ (inr star) = refl

is-contr-Fin-one-ℕ :
  is-contr (Fin one-ℕ)
is-contr-Fin-one-ℕ = pair (inr star) contraction-Fin-one-ℕ

skip :
  (n : ℕ) → Fin (succ-ℕ n) → Fin n → Fin (succ-ℕ n)
skip (succ-ℕ n) (inl i) (inl j) = inl (skip n i j)
skip (succ-ℕ n) (inl i) (inr star) = inr star
skip (succ-ℕ n) (inr star) j = inl j

repeat :
  (n : ℕ) → Fin n → Fin (succ-ℕ n) → Fin n
repeat (succ-ℕ n) (inl i) (inl j) = inl (repeat n i j)
repeat (succ-ℕ n) (inl j) (inr star) = inr star
repeat (succ-ℕ n) (inr star) (inl j) = j
repeat (succ-ℕ n) (inr star) (inr star) = inr star

repeat-repeat :
  (n : ℕ) (i j : Fin n) →
    ((repeat n i) ∘ (repeat (succ-ℕ n) (skip n (inl i) j))) ~
    ((repeat n j) ∘ (repeat (succ-ℕ n) (skip n (inl j) i)))
repeat-repeat zero-ℕ () j k
repeat-repeat (succ-ℕ n) (inl i) (inl j) (inl k) =
  ap inl (repeat-repeat n i j k)
repeat-repeat (succ-ℕ n) (inl i) (inl j) (inr star) = refl
repeat-repeat (succ-ℕ n) (inl i) (inr star) (inr star) = refl
repeat-repeat (succ-ℕ n) (inr star) (inl j) (inr star) = refl
repeat-repeat (succ-ℕ n) (inr star) (inr star) (inl k) = refl
repeat-repeat (succ-ℕ n) (inr star) (inr star) (inr star) = refl
repeat-repeat (succ-ℕ zero-ℕ) (inl ()) (inr star) (inl k)
repeat-repeat (succ-ℕ (succ-ℕ n)) (inl i) (inr star) (inl k) = refl
repeat-repeat (succ-ℕ zero-ℕ) (inr star) (inl ()) (inl k) 
repeat-repeat (succ-ℕ (succ-ℕ n)) (inr star) (inl j) (inl k) = refl

{-
skip-repeat :
  (n : ℕ) (i : Fin n) → ((skip n (inl i)) ∘ (repeat n i)) ~ id
skip-repeat (succ-ℕ n) (inl x) (inl y) = ap inl (skip-repeat n x y)
skip-repeat (succ-ℕ n) (inl x) (inr star) = refl
skip-repeat (succ-ℕ n) (inr star) (inl (inl x)) = ap inl {!ap (skip n) ?!}
skip-repeat (succ-ℕ n) (inr star) (inl (inr star)) = {!!}
skip-repeat (succ-ℕ n) (inr star) (inr star) = {!!}
-}

map-lift-Fin :
  (m n : ℕ) (f : Fin (succ-ℕ m) → Fin (succ-ℕ n))
  (i : Fin (succ-ℕ n)) (H : fib f i → empty) →
  Fin m → Fin n
map-lift-Fin m n f (inl i) H = (repeat n i) ∘ (f ∘ inl)
map-lift-Fin m (succ-ℕ n) f (inr star) H =
  ( repeat (succ-ℕ n) (max-Fin n)) ∘
  ( f ∘ inl)
map-lift-Fin zero-ℕ zero-ℕ f (inr star) H = ind-empty
map-lift-Fin (succ-ℕ m) zero-ℕ f (inr star) H =
  ex-falso
    ( H (pair (inr star) (inv (contraction-Fin-one-ℕ (f (inr star))))))

{-
is-lift-lift-Fin :
  (m n : ℕ) (f : Fin (succ-ℕ m) → Fin (succ-ℕ n))
  (i : Fin (succ-ℕ n)) (H : fib f i → empty) →
  (f ∘ inl) ~ ((skip n i) ∘ (map-lift-Fin m n f i H))
is-lift-lift-Fin m n f (inl i) H x = {!!}
is-lift-lift-Fin m n f (inr i) H x = {!!}
-}

-- The greatest common divisor

{- First we show that mul-ℕ n is an embedding whenever n > 0. In order to do
   this, we have to show that add-ℕ n is injective. -}

is-injective-add-ℕ' :
  (n : ℕ) → is-injective is-set-ℕ is-set-ℕ (λ m → add-ℕ m n)
is-injective-add-ℕ' zero-ℕ k l p = p
is-injective-add-ℕ' (succ-ℕ n) k l p =
  is-injective-add-ℕ' n k l (is-injective-succ-ℕ (add-ℕ k n) (add-ℕ l n) p)
   
is-injective-add-ℕ :
  (n : ℕ) → is-injective is-set-ℕ is-set-ℕ (add-ℕ n)
is-injective-add-ℕ n k l p = is-injective-add-ℕ' n k l
  (((commutative-add-ℕ k n) ∙ p) ∙ (commutative-add-ℕ n l))

is-emb-add-ℕ :
  (n : ℕ) → is-emb (add-ℕ n)
is-emb-add-ℕ n =
  is-emb-is-injective is-set-ℕ is-set-ℕ (add-ℕ n) (is-injective-add-ℕ n)

equiv-fib-add-fib-add-ℕ' :
  (m n : ℕ) → fib (add-ℕ' m) n ≃ fib (add-ℕ m) n
equiv-fib-add-fib-add-ℕ' m n =
  equiv-tot (λ k → equiv-concat (commutative-add-ℕ m k) n)

leq-fib-add-ℕ' :
  (m n : ℕ) → fib (add-ℕ' m) n → (leq-ℕ m n)
leq-fib-add-ℕ' zero-ℕ n (pair k p) = leq-zero-ℕ n
leq-fib-add-ℕ' (succ-ℕ m) (succ-ℕ n) (pair k p) =
  leq-fib-add-ℕ' m n (pair k (is-injective-succ-ℕ (add-ℕ k m) n p))

leq-fib-add-ℕ :
  (m n : ℕ) → fib (add-ℕ m) n → (leq-ℕ m n)
leq-fib-add-ℕ m .m (pair zero-ℕ refl) = reflexive-leq-ℕ m
leq-fib-add-ℕ m .(add-ℕ m (succ-ℕ k)) (pair (succ-ℕ k) refl) =
  transitive-leq-ℕ m (add-ℕ m k) (succ-ℕ (add-ℕ m k))
    ( leq-fib-add-ℕ m (add-ℕ m k) (pair k refl))
    ( succ-leq-ℕ (add-ℕ m k))

fib-add-leq-ℕ :
  (m n : ℕ) → (leq-ℕ m n) → fib (add-ℕ m) n
fib-add-leq-ℕ zero-ℕ zero-ℕ star = pair zero-ℕ refl
fib-add-leq-ℕ zero-ℕ (succ-ℕ n) star = {!!}
fib-add-leq-ℕ (succ-ℕ m) (succ-ℕ n) p = {!!}

{-
fib-add-leq-ℕ zero-ℕ zero-ℕ H = pair zero-ℕ refl
fib-add-leq-ℕ zero-ℕ (succ-ℕ n) H = pair (succ-ℕ n) refl
fib-add-leq-ℕ (succ-ℕ m) (succ-ℕ n) H =
  pair
    ( pr1 (fib-add-leq-ℕ m n H))
    ( ap succ-ℕ (pr2 (fib-add-leq-ℕ m n H)))
-}

is-equiv-leq-fib-add-ℕ :
  (m n : ℕ) → is-equiv (leq-fib-add-ℕ m n)
is-equiv-leq-fib-add-ℕ m n =
  is-equiv-is-prop
    ( is-prop-map-is-emb _ (is-emb-add-ℕ m) n)
    ( is-prop-leq-ℕ m n)
    ( fib-add-leq-ℕ m n)

is-equiv-fib-add-leq-ℕ :
  (m n : ℕ) → is-equiv (fib-add-leq-ℕ m n)
is-equiv-fib-add-leq-ℕ m n =
  is-equiv-is-prop
    ( is-prop-leq-ℕ m n)
    ( is-prop-map-is-emb _ (is-emb-add-ℕ m) n)
    ( leq-fib-add-ℕ m n)

is-injective-mul-ℕ :
  (n : ℕ) → (le-ℕ zero-ℕ n) → is-injective is-set-ℕ is-set-ℕ (mul-ℕ n)
is-injective-mul-ℕ (succ-ℕ n) star zero-ℕ zero-ℕ p = refl
is-injective-mul-ℕ (succ-ℕ n) star zero-ℕ (succ-ℕ l) p =
  ind-empty
    ( Eq-ℕ-eq
      {- ( zero-ℕ)-}
      {- ( succ-ℕ (add-ℕ (mul-ℕ n (succ-ℕ l)) l))-}
      ( ( inv (right-zero-law-mul-ℕ n)) ∙
        ( ( inv (right-unit-law-add-ℕ (mul-ℕ n zero-ℕ))) ∙
          ( p ∙ (right-successor-law-add-ℕ (mul-ℕ n (succ-ℕ l)) l)))))
is-injective-mul-ℕ (succ-ℕ n) star (succ-ℕ k) zero-ℕ p =
  ind-empty
    ( Eq-ℕ-eq
      {- ( succ-ℕ (add-ℕ (mul-ℕ n (succ-ℕ k)) k))-}
      {- ( zero-ℕ)-}
      ( ( inv (right-successor-law-add-ℕ (mul-ℕ n (succ-ℕ k)) k)) ∙
        ( p ∙ ( right-zero-law-mul-ℕ (succ-ℕ n)))))
is-injective-mul-ℕ (succ-ℕ n) star (succ-ℕ k) (succ-ℕ l) p =
  ap succ-ℕ
    ( is-injective-mul-ℕ (succ-ℕ n) star k l
      ( is-injective-add-ℕ (succ-ℕ n)
        ( mul-ℕ (succ-ℕ n) k)
        ( mul-ℕ (succ-ℕ n) l)
        ( ( inv (right-successor-law-mul-ℕ (succ-ℕ n) k) ∙ p) ∙
          ( right-successor-law-mul-ℕ (succ-ℕ n) l))))

is-emb-mul-ℕ :
  (n : ℕ) → (le-ℕ zero-ℕ n) → is-emb (mul-ℕ n)
is-emb-mul-ℕ n le =
  is-emb-is-injective is-set-ℕ is-set-ℕ
    ( mul-ℕ n)
    ( is-injective-mul-ℕ n le)

is-emb-mul-ℕ' :
  (n : ℕ) → (le-ℕ zero-ℕ n) → is-emb (λ m → mul-ℕ m n)
is-emb-mul-ℕ' n t =
  is-emb-htpy'
    ( mul-ℕ n)
    ( λ m → mul-ℕ m n)
    ( commutative-mul-ℕ n)
    ( is-emb-mul-ℕ n t)

{- We conclude that the division relation is a property. -}

div-ℕ : ℕ → ℕ → UU lzero
div-ℕ m n = Σ ℕ (λ k → Id (mul-ℕ k m) n)

is-prop-div-ℕ :
  (m n : ℕ) → (le-ℕ zero-ℕ m) → is-prop (div-ℕ m n)
is-prop-div-ℕ (succ-ℕ m) n star =
  is-prop-map-is-emb
    ( λ z → mul-ℕ z (succ-ℕ m))
    ( is-emb-mul-ℕ' (succ-ℕ m) star)
    n

{- We now construct the division with remainder. -}

le-mul-ℕ :
  (d n k : ℕ) → UU lzero
le-mul-ℕ d n k = le-ℕ n (mul-ℕ k d)

is-decidable-le-mul-ℕ :
  (d n k : ℕ) → is-decidable (le-mul-ℕ d n k)
is-decidable-le-mul-ℕ d n k =
  is-decidable-le-ℕ n (mul-ℕ k d)

order-preserving-succ-ℕ :
  (n n' : ℕ) → (leq-ℕ n n') → (leq-ℕ (succ-ℕ n) (succ-ℕ n'))
order-preserving-succ-ℕ n n' H = H

order-preserving-add-ℕ :
  (m n m' n' : ℕ) →
  (leq-ℕ m m') → (leq-ℕ n n') → (leq-ℕ (add-ℕ m n) (add-ℕ m' n'))
order-preserving-add-ℕ = {!!}

{-
order-preserving-add-ℕ zero-ℕ zero-ℕ m' n' Hm Hn = star
order-preserving-add-ℕ zero-ℕ (succ-ℕ n) zero-ℕ (succ-ℕ n') Hm Hn = Hn
order-preserving-add-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ m') (succ-ℕ n') Hm Hn =
  leq-eq-right-ℕ n
    ( inv (right-successor-law-add-ℕ m' n'))
    ( order-preserving-add-ℕ zero-ℕ n (succ-ℕ m') n' Hm Hn)
order-preserving-add-ℕ (succ-ℕ m) n (succ-ℕ m') n' Hm Hn =
  order-preserving-add-ℕ m n m' n' Hm Hn
-}

le-eq-right-ℕ :
  (m : ℕ) {n n' : ℕ} → Id n n' → le-ℕ m n' → le-ℕ m n
le-eq-right-ℕ m refl = id

le-add-ℕ :
  (m n : ℕ) → (leq-ℕ one-ℕ n) → le-ℕ m (add-ℕ m n)
le-add-ℕ = {!!}

{-
le-add-ℕ zero-ℕ (succ-ℕ n) star = star
le-add-ℕ (succ-ℕ m) (succ-ℕ n) star = le-add-ℕ m (succ-ℕ n) star
-}

le-mul-self-ℕ :
  (d n : ℕ) → (leq-ℕ one-ℕ d) → (leq-ℕ one-ℕ n) → le-mul-ℕ d n n
le-mul-self-ℕ (succ-ℕ d) (succ-ℕ n) star star =
  le-eq-right-ℕ
    ( succ-ℕ n)
    ( right-successor-law-mul-ℕ (succ-ℕ n) d)
    ( le-add-ℕ (succ-ℕ n) (mul-ℕ (succ-ℕ n) d) {!leq-eq-right-ℕ !})

leq-multiple-ℕ :
  (n m : ℕ) → (leq-ℕ one-ℕ m) → leq-ℕ n (mul-ℕ n m)
leq-multiple-ℕ n (succ-ℕ m) H =
  leq-eq-right-ℕ n
    ( inv (right-successor-law-mul-ℕ n m))
    ( leq-fib-add-ℕ n (add-ℕ n (mul-ℕ n m)) (pair (mul-ℕ n m) refl))

least-factor-least-larger-multiple-ℕ :
  (d n : ℕ) → (leq-ℕ one-ℕ d) →
  minimal-element-ℕ (λ k → leq-ℕ n (mul-ℕ k d))
least-factor-least-larger-multiple-ℕ d n H =
  well-ordering-principle-ℕ
    ( λ k → leq-ℕ n (mul-ℕ k d))
    ( λ k → is-decidable-leq-ℕ n (mul-ℕ k d))
    ( pair n (leq-multiple-ℕ n d H))

factor-least-larger-multiple-ℕ :
  (d n : ℕ) → (leq-ℕ one-ℕ d) → ℕ
factor-least-larger-multiple-ℕ d n H =
  pr1 (least-factor-least-larger-multiple-ℕ d n H)

least-larger-multiple-ℕ :
  (d n : ℕ) → (leq-ℕ one-ℕ d) → ℕ
least-larger-multiple-ℕ d n H =
  mul-ℕ (factor-least-larger-multiple-ℕ d n H) d

leq-least-larger-multiple-ℕ :
  (d n : ℕ) (H : leq-ℕ one-ℕ d) →
  leq-ℕ n (least-larger-multiple-ℕ d n H)
leq-least-larger-multiple-ℕ d n H =
  pr1 (pr2 (least-factor-least-larger-multiple-ℕ d n H))

is-minimal-least-larger-multiple-ℕ :
  (d n : ℕ) (H : leq-ℕ one-ℕ d) (k : ℕ) (K : leq-ℕ n (mul-ℕ k d)) →
  leq-ℕ (factor-least-larger-multiple-ℕ d n H) k
is-minimal-least-larger-multiple-ℕ d n H =
  pr2 (pr2 (least-factor-least-larger-multiple-ℕ d n H))

is-decidable-div-is-decidable-eq-least-larger-multiple-ℕ :
  (d n : ℕ) (H : leq-ℕ one-ℕ d) →
  is-decidable (Id (least-larger-multiple-ℕ d n H) n) → is-decidable (div-ℕ d n)
is-decidable-div-is-decidable-eq-least-larger-multiple-ℕ d n H (inl p) =
  inl (pair (factor-least-larger-multiple-ℕ d n H) p)
is-decidable-div-is-decidable-eq-least-larger-multiple-ℕ d n H (inr f) =
  inr (λ x → {!!})

is-decidable-div-ℕ' :
  (d n : ℕ) → (leq-ℕ one-ℕ d) → is-decidable (div-ℕ d n)
is-decidable-div-ℕ' d n H = {!!}

is-decidable-div-ℕ :
  (d n : ℕ) → is-decidable (div-ℕ d n)
is-decidable-div-ℕ zero-ℕ zero-ℕ = inl (pair zero-ℕ refl)
is-decidable-div-ℕ zero-ℕ (succ-ℕ n) =
  inr ( λ p →
    Eq-ℕ-eq {-zero-ℕ (succ-ℕ n)-} ((inv (right-zero-law-mul-ℕ (pr1 p))) ∙ (pr2 p)))
is-decidable-div-ℕ (succ-ℕ d) n =
  is-decidable-div-ℕ' (succ-ℕ d) n (leq-zero-ℕ d)

-- Operations on decidable bounded subsets of ℕ

iterated-operation-ℕ :
  (strict-upper-bound : ℕ) (operation : ℕ → ℕ → ℕ) (base-value : ℕ) → ℕ
iterated-operation-ℕ zero-ℕ μ e = e
iterated-operation-ℕ (succ-ℕ b) μ e = μ (iterated-operation-ℕ b μ e) b

iterated-sum-ℕ :
  (summand : ℕ → ℕ) (b : ℕ) → ℕ
iterated-sum-ℕ f zero-ℕ = zero-ℕ
iterated-sum-ℕ f (succ-ℕ b) = add-ℕ (iterated-sum-ℕ f b) (f (succ-ℕ b))

ranged-sum-ℕ :
  (summand : ℕ → ℕ) (l u : ℕ) → ℕ
ranged-sum-ℕ f zero-ℕ u = iterated-sum-ℕ f u
ranged-sum-ℕ f (succ-ℕ l) zero-ℕ = zero-ℕ
ranged-sum-ℕ f (succ-ℕ l) (succ-ℕ u) =
  ranged-sum-ℕ (f ∘ succ-ℕ) l u

succ-iterated-operation-fam-ℕ :
  { l : Level}
  ( P : ℕ → UU l) (is-decidable-P : (n : ℕ) → is-decidable (P n)) →
  ( predecessor-strict-upper-bound : ℕ) (operation : ℕ → ℕ → ℕ) →
  is-decidable (P predecessor-strict-upper-bound) → ℕ → ℕ
succ-iterated-operation-fam-ℕ
  P is-decidable-P b μ (inl p) m = μ m b
succ-iterated-operation-fam-ℕ
  P is-decidable-P b μ (inr f) m = m

iterated-operation-fam-ℕ :
  { l : Level} (P : ℕ → UU l) (is-decidable-P : (n : ℕ) → is-decidable (P n)) →
  ( strict-upper-bound : ℕ) (operation : ℕ → ℕ → ℕ) (base-value : ℕ) → ℕ
iterated-operation-fam-ℕ P d zero-ℕ μ e = e
iterated-operation-fam-ℕ P d (succ-ℕ b) μ e =
  succ-iterated-operation-fam-ℕ P d b μ (d b)
    ( iterated-operation-fam-ℕ P d b μ e)

Sum-fam-ℕ :
  { l : Level} (P : ℕ → UU l) (is-decidable-P : (n : ℕ) → is-decidable (P n)) →
  ( upper-bound : ℕ) ( summand : ℕ → ℕ) → ℕ
Sum-fam-ℕ P d b f = iterated-operation-fam-ℕ P d (succ-ℕ b) (λ x y → add-ℕ x (f y)) zero-ℕ

{-
iterated-operation-fam-ℕ
  P is-decidable-P zero-ℕ is-bounded-P μ base-value =
  base-value
iterated-operation-fam-ℕ
  P is-decidable-P (succ-ℕ b) is-bounded-P μ base-value =
  succ-iterated-operation-ℕ P is-decidable-P b is-bounded-P μ
    ( is-decidable-P b)
    ( iterated-operation-ℕ
      ( introduce-bound-on-fam-ℕ b P)
      ( is-decidable-introduce-bound-on-fam-ℕ b P is-decidable-P)
      ( b)
      ( is-bounded-introduce-bound-on-fam-ℕ b P)
      ( μ)
      ( base-value))

product-decidable-bounded-fam-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( is-decidable-P : (n : ℕ) → is-decidable (P n))
  ( b : ℕ) ( is-bounded-P : is-bounded-fam-ℕ b P) → ℕ
product-decidable-bounded-fam-ℕ P is-decidable-P b is-bounded-P =
  iterated-operation-ℕ P is-decidable-P b is-bounded-P mul-ℕ one-ℕ

twenty-four-ℕ : ℕ
twenty-four-ℕ =
  product-decidable-bounded-fam-ℕ
    ( λ x → le-ℕ x five-ℕ)
    ( λ x → is-decidable-le-ℕ x five-ℕ)
    ( five-ℕ)
    ( λ x → id)
-}

{-
test-zero-twenty-four-ℕ : Id twenty-four-ℕ zero-ℕ
test-zero-twenty-four-ℕ = refl

test-twenty-four-ℕ : Id twenty-four-ℕ (factorial four-ℕ)
test-twenty-four-ℕ = refl
-}

-- Exercises

-- Exercise 10.?

abstract
  has-decidable-equality-𝟚 : has-decidable-equality bool
  has-decidable-equality-𝟚 true true = inl refl
  has-decidable-equality-𝟚 true false = inr (Eq-𝟚-eq true false)
  has-decidable-equality-𝟚 false true = inr (Eq-𝟚-eq false true)
  has-decidable-equality-𝟚 false false = inl refl

-- Exercise 10.?

abstract
  has-decidable-equality-prod' : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    (x x' : A) (y y' : B) → is-decidable (Id x x') → is-decidable (Id y y') →
    is-decidable (Id (pair x y) (pair x' y'))
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


{-

bounds-fam-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
bounds-fam-ℕ P = Σ ℕ (λ n → is-bounded-fam-ℕ n P)

is-minimal-ℕ :
  {l : Level} (P : ℕ → UU l) → Σ ℕ P → UU l
is-minimal-ℕ P (pair n p) = (t : Σ ℕ P) → leq-ℕ n (pr1 t)

eq-zero-leq-zero-ℕ :
  (n : ℕ) → leq-ℕ n zero-ℕ → Id n zero-ℕ
eq-zero-leq-zero-ℕ zero-ℕ star = refl
eq-zero-leq-zero-ℕ (succ-ℕ n) ()

fam-succ-ℕ :
  {l : Level} → (ℕ → UU l) → (ℕ → UU l)
fam-succ-ℕ P n = P (succ-ℕ n)

is-decidable-fam-succ-ℕ :
  {l : Level} (P : ℕ → UU l) →
  ((n : ℕ) → is-decidable (P n)) → ((n : ℕ) → is-decidable (P (succ-ℕ n)))
is-decidable-fam-succ-ℕ P d n = d (succ-ℕ n)

min-is-bounded-not-zero-ℕ :
  {l : Level} (P : ℕ → UU l) → ((n : ℕ) → is-decidable (P n)) →
  Σ ℕ (λ n → is-bounded-fam-ℕ n P) →
  ¬ (P zero-ℕ) →
  Σ (Σ ℕ (fam-succ-ℕ P)) (is-minimal-ℕ (fam-succ-ℕ P)) →
  Σ (Σ ℕ P) (is-minimal-ℕ P)
min-is-bounded-not-zero-ℕ P d b np0 t = {!!}

min-is-bounded-ℕ :
  {l : Level} (P : ℕ → UU l) → ((n : ℕ) → is-decidable (P n)) →
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
    ( λ (t : is-decidable (P zero-ℕ)) → Σ (Σ ℕ P) (is-minimal-ℕ P))
    ( λ p0 → pair (pair zero-ℕ p0) (λ p → leq-zero-ℕ (pr1 p)))
    ( λ y → min-is-bounded-not-zero-ℕ P d (pair (succ-ℕ n) b) y
      ( min-is-bounded-ℕ
        ( fam-succ-ℕ P)
        ( is-decidable-fam-succ-ℕ P d)
        {!!}
        {!!}))
    ( d zero-ℕ)

{- We show that every non-empty decidable subset of ℕ has a least element. -}

least-ℕ :
  {l : Level} (P : ℕ → UU l) → Σ ℕ P → UU l
least-ℕ P (pair n p) = (m : ℕ) → P m → leq-ℕ n m

least-element-non-empty-decidable-subset-ℕ :
  {l : Level} (P : ℕ → UU l) (d : (n : ℕ) → is-decidable (P n)) →
  Σ ℕ P → Σ (Σ ℕ P) (least-ℕ P)
least-element-non-empty-decidable-subset-ℕ P d (pair zero-ℕ p) =
  pair (pair zero-ℕ p) {!!}
least-element-non-empty-decidable-subset-ℕ P d (pair (succ-ℕ n) p) = {!!}
-}

{-
zero-Fin :
  (n : ℕ) → Fin (succ-ℕ n)
zero-Fin zero-ℕ = inr star
zero-Fin (succ-ℕ n) = inl (zero-Fin n)

succ-Fin :
  (n : ℕ) → Fin n → Fin n
succ-Fin (succ-ℕ n) (inr star) = zero-Fin n
succ-Fin (succ-ℕ (succ-ℕ n)) (inl (inl x)) = inl (succ-Fin (succ-ℕ n) (inl x))
succ-Fin (succ-ℕ (succ-ℕ n)) (inl (inr star)) = inr star

iterated-succ-Fin :
  (k : ℕ) → (n : ℕ) → Fin n → Fin n
iterated-succ-Fin zero-ℕ n = id
iterated-succ-Fin (succ-ℕ k) n = (succ-Fin n) ∘ (iterated-succ-Fin k n)

quotient-ℕ-Fin :
  (n : ℕ) → Fin (succ-ℕ n)
quotient-ℕ-Fin n = iterated-succ-Fin n (succ-ℕ n) (zero-Fin n)

pred-Fin :
  (n : ℕ) → Fin n → Fin n
pred-Fin (succ-ℕ zero-ℕ) (inr star) = inr star
pred-Fin (succ-ℕ (succ-ℕ n)) (inl x) = {!!}
pred-Fin (succ-ℕ (succ-ℕ n)) (inr star) = inl (inr star)

add-Fin :
  (n : ℕ) → Fin n → Fin n → Fin n
add-Fin (succ-ℕ n) (inl x) j = {!!}
add-Fin (succ-ℕ n) (inr x) j = {!!}


idempotent-succ-Fin :
  (n : ℕ) (i : Fin n) → Id (iterated-succ-Fin n n i) i
idempotent-succ-Fin (succ-ℕ zero-ℕ) (inr star) = refl
idempotent-succ-Fin (succ-ℕ (succ-ℕ n)) (inl x) = {!!}
idempotent-succ-Fin (succ-ℕ (succ-ℕ n)) (inr x) = {!!}

-}

in-nat-ℤ : ℕ → ℤ
in-nat-ℤ zero-ℕ = zero-ℤ
in-nat-ℤ (succ-ℕ n) = in-pos n

div-ℤ :
  (k l : ℤ) → UU lzero
div-ℤ k l = Σ ℤ (λ x → Id (mul-ℤ x k) l)

_≡_mod_ :
  (k l : ℤ) (n : ℕ) → UU lzero
k ≡ l mod n = div-ℤ (in-nat-ℤ n) (add-ℤ k (neg-ℤ l))

-- From before


is-even-ℕ : ℕ → UU lzero
is-even-ℕ n = div-ℕ two-ℕ n

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

-- Exercise

unit-classical-Prop : classical-Prop lzero
unit-classical-Prop =
  pair (pair {!!} {!!}) {!!}

raise-unit-classical-Prop :
  (l : Level) → classical-Prop l
raise-unit-classical-Prop l =
  pair
    ( pair
      ( raise l unit)
      ( is-prop-is-equiv' unit
        ( map-raise l unit)
        ( is-equiv-map-raise l unit)
        ( is-prop-unit)))
    ( inl (map-raise l unit star))

bool-classical-Prop :
  (l : Level) → classical-Prop l → bool
bool-classical-Prop l (pair P (inl x)) = true
bool-classical-Prop l (pair P (inr x)) = false

classical-Prop-bool :
  (l : Level) → bool → classical-Prop l
classical-Prop-bool l true = raise-unit-classical-Prop l
classical-Prop-bool l false = {!!}
