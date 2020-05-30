{-# OPTIONS --without-K --exact-split #-}

module 07-finite-sets where

import 06-universes
open 06-universes public

--------------------------------------------------------------------------------

{- We introduce the finite types as a family indexed by ℕ. -}

Fin : ℕ → UU lzero
Fin zero-ℕ = empty
Fin (succ-ℕ k) = coprod (Fin k) unit

inl-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
inl-Fin k = inl

zero-Fin : {k : ℕ} → Fin (succ-ℕ k)
zero-Fin {zero-ℕ} = inr star
zero-Fin {succ-ℕ k} = inl zero-Fin

neg-one-Fin : {k : ℕ} → Fin (succ-ℕ k)
neg-one-Fin {k} = inr star

succ-Fin : {k : ℕ} → Fin k → Fin k
succ-Fin {succ-ℕ zero-ℕ} x = x
succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inl x)) = inl (succ-Fin (inl x))
succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inr x)) = neg-one-Fin
succ-Fin {succ-ℕ (succ-ℕ k)} (inr x) = zero-Fin

{- We show that the successor of neg-one-Fin is zero-Fin. -}

succ-neg-one-Fin : {k : ℕ} → Id (succ-Fin (neg-one-Fin {k})) zero-Fin
succ-neg-one-Fin {zero-ℕ} = refl
succ-neg-one-Fin {succ-ℕ k} = refl

--------------------------------------------------------------------------------

{- Observational equality on finite sets -}

Eq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit

refl-Eq-Fin : {k : ℕ} (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin {succ-ℕ k} (inl x) = refl-Eq-Fin x
refl-Eq-Fin {succ-ℕ k} (inr x) = star

Eq-Fin-eq : {k : ℕ} {x y : Fin k} → Id x y → Eq-Fin k x y
Eq-Fin-eq {k} refl = refl-Eq-Fin {k} _

eq-Eq-Fin :
  {k : ℕ} {x y : Fin k} → Eq-Fin k x y → Id x y
eq-Eq-Fin {succ-ℕ k} {inl x} {inl y} e = ap inl (eq-Eq-Fin e)
eq-Eq-Fin {succ-ℕ k} {inr star} {inr star} star = refl

--------------------------------------------------------------------------------

{- The inclusion function Fin n → Fin (succ-ℕ n) is injective. -}

is-injective-inl-Fin :
  {k : ℕ} {x y : Fin k} → Id (inl-Fin k x) (inl-Fin k y) → Id x y
is-injective-inl-Fin p = eq-Eq-Fin (Eq-Fin-eq p)

--------------------------------------------------------------------------------

{- We show that Fin n has decidable equality, for each n : ℕ. -}

is-decidable-Eq-Fin :
  (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin zero-ℕ () y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = inr id
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = inl star

is-decidable-eq-Fin :
  (k : ℕ) (x y : Fin k) → is-decidable (Id x y)
is-decidable-eq-Fin k x y =
  functor-coprod eq-Eq-Fin (functor-neg Eq-Fin-eq) (is-decidable-Eq-Fin k x y)

--------------------------------------------------------------------------------

{- We define the predecessor function on finite sets. -}

pred-Fin : {k : ℕ} → Fin (succ-ℕ k) → Fin (succ-ℕ k)
pred-Fin {zero-ℕ} x = zero-Fin
pred-Fin {succ-ℕ k} x with (is-decidable-Eq-Fin (succ-ℕ (succ-ℕ k)) x zero-Fin)
pred-Fin {succ-ℕ k} (inl x) | inl e = neg-one-Fin
pred-Fin {succ-ℕ k} (inl x) | inr f = inl (pred-Fin x)
pred-Fin {succ-ℕ k} (inr x) | inr f = inl neg-one-Fin

-- We show that the predecessor of zero is negative one --

pred-zero-Fin :
  {k : ℕ} → Id (pred-Fin {k} zero-Fin) neg-one-Fin
pred-zero-Fin {zero-ℕ} = refl
pred-zero-Fin {succ-ℕ k} with is-decidable-Eq-Fin (succ-ℕ k) zero-Fin zero-Fin
pred-zero-Fin {succ-ℕ k} | inl e = refl
pred-zero-Fin {succ-ℕ k} | inr f =
  ex-falso (f (refl-Eq-Fin {succ-ℕ k} zero-Fin))

-- We compute the predecessor of an element of the form inl that is not zero --

pred-inl-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) (f : ¬ (Eq-Fin (succ-ℕ k) x zero-Fin)) →
  Id (pred-Fin (inl x)) (inl (pred-Fin x))
pred-inl-Fin {k} x f with is-decidable-Eq-Fin (succ-ℕ k) x zero-Fin
pred-inl-Fin {k} x f | inl e = ex-falso (f e)
pred-inl-Fin {k} x f | inr g = refl

-- We show that the predecessor function is a section of the successor function

succ-pred-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (succ-Fin (pred-Fin x)) x
succ-pred-Fin {k} x with (is-decidable-Eq-Fin (succ-ℕ k) x zero-Fin)
succ-pred-Fin {zero-ℕ} (inr star) | d = refl
succ-pred-Fin {succ-ℕ k} (inl x) | inl e =
  ( ( ap (succ-Fin ∘ pred-Fin) {x = inl x} {y = zero-Fin} (eq-Eq-Fin e)) ∙
    ( ( ap succ-Fin pred-zero-Fin) ∙
      ( succ-neg-one-Fin))) ∙
  ( inv {x = inl x} {y = zero-Fin} (eq-Eq-Fin e))
succ-pred-Fin {succ-ℕ (succ-ℕ k)} (inl (inl (inl x))) | inr f =
  ( ap succ-Fin (pred-inl-Fin (inl (inl x)) f)) ∙
  ( ( ap (succ-Fin ∘ inl) (pred-inl-Fin (inl x) f)) ∙
    ( ( ap inl
        ( ( ap succ-Fin (inv (pred-inl-Fin (inl x) f))) ∙
          ( succ-pred-Fin (inl (inl x)))))))
succ-pred-Fin {succ-ℕ (succ-ℕ zero-ℕ)} (inl (inl (inr star))) | inr f =
  ex-falso (f star)
succ-pred-Fin {succ-ℕ (succ-ℕ (succ-ℕ k))} (inl (inl (inr star))) | inr f =
  ( ap succ-Fin (pred-inl-Fin (inl (inr star)) f)) ∙
  ( ap inl (succ-pred-Fin (inl (inr star))))
succ-pred-Fin {succ-ℕ zero-ℕ} (inl (inr x)) | inr f = ex-falso (f star)
succ-pred-Fin {succ-ℕ (succ-ℕ k)} (inl (inr x)) | inr f =
  ap inl (succ-pred-Fin (inr x))
succ-pred-Fin {succ-ℕ k} (inr star) | inr f = refl

-- We show that the predecessor function is a retract of the successor function

neq-zero-succ-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) →
  ¬ (Eq-Fin (succ-ℕ (succ-ℕ k)) (succ-Fin (inl x)) zero-Fin)
neq-zero-succ-Fin {succ-ℕ k} (inl (inl x)) e = neq-zero-succ-Fin (inl x) e

pred-succ-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (pred-Fin (succ-Fin x)) x
pred-succ-Fin {zero-ℕ} (inr star) = refl
pred-succ-Fin {succ-ℕ zero-ℕ} (inl (inr star)) = refl
pred-succ-Fin {succ-ℕ zero-ℕ} (inr star) = refl
pred-succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inl (inl x))) =
  ( pred-inl-Fin (inl (succ-Fin (inl x))) (neq-zero-succ-Fin (inl x))) ∙
  ( ( ap inl (pred-inl-Fin (succ-Fin (inl x)) (neq-zero-succ-Fin (inl x)))) ∙
    ( ap (inl ∘ inl) (pred-succ-Fin (inl x))))
pred-succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inl (inr star))) = refl
pred-succ-Fin {succ-ℕ (succ-ℕ k)} (inl (inr star)) = refl
pred-succ-Fin {succ-ℕ (succ-ℕ k)} (inr star) = pred-zero-Fin

{- In the terminology of the next chapter, we conclude that the successor 
   function is an equivalence. -}

{- We show here that the successor function is injective. -}

is-injective-succ-Fin :
  {k : ℕ} {x y : Fin (succ-ℕ k)} → Id (succ-Fin x) (succ-Fin y) → Id x y
is-injective-succ-Fin {k} {x} {y} p =
  ( inv (pred-succ-Fin x)) ∙
  ( ( ap pred-Fin p) ∙
    ( pred-succ-Fin y))

--------------------------------------------------------------------------------

-- We introduce the divisibility relation. --

div-ℕ : ℕ → ℕ → UU lzero
div-ℕ m n = Σ ℕ (λ k → Id (mul-ℕ k m) n)

-- We show some basic properties of the divisibility relation --

{- In the following three constructions we show that if any two of the three
   numbers x, y, and x + y, is divisible by d, then so is the third. -}

div-add-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d y → div-ℕ d (add-ℕ x y)
div-add-ℕ d x y (pair n p) (pair m q) =
  pair
    ( add-ℕ n m)
    ( ( right-distributive-mul-add-ℕ n m d) ∙
      ( ap-add-ℕ p q))

div-left-summand-ℕ :
  (d x y : ℕ) → div-ℕ d y → div-ℕ d (add-ℕ x y) → div-ℕ d x
div-left-summand-ℕ zero-ℕ x y (pair m q) (pair n p) =
  pair zero-ℕ
    ( ( inv (right-zero-law-mul-ℕ n)) ∙
      ( p ∙ (ap (add-ℕ x) ((inv q) ∙ (right-zero-law-mul-ℕ m)))))
div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p) =
  pair
    ( dist-ℕ m n)
    ( is-injective-add-ℕ (mul-ℕ m (succ-ℕ d)) (mul-ℕ (dist-ℕ m n) (succ-ℕ d)) x
      ( ( inv
          ( ( right-distributive-mul-add-ℕ m (dist-ℕ m n) (succ-ℕ d)) ∙
            ( commutative-add-ℕ
              ( mul-ℕ m (succ-ℕ d))
              ( mul-ℕ (dist-ℕ m n) (succ-ℕ d))))) ∙ 
        ( ( ap
            ( mul-ℕ' (succ-ℕ d))
            ( leq-dist-ℕ m n
              ( leq-leq-mul-ℕ' m n d
                ( concatenate-eq-leq-eq-ℕ q
                  ( leq-add-ℕ' y x)
                  ( inv p))))) ∙
          ( p ∙ (ap (add-ℕ x) (inv q))))))

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (add-ℕ x y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 =
  div-left-summand-ℕ d y x H1 (tr (div-ℕ d) (commutative-add-ℕ x y) H2)

-- Some lemmas that will help us showing that cong is an equivalence relation

order-two-elements-ℕ :
  (x y : ℕ) → coprod (leq-ℕ x y) (leq-ℕ y x)
order-two-elements-ℕ zero-ℕ zero-ℕ = inl star
order-two-elements-ℕ zero-ℕ (succ-ℕ y) = inl star
order-two-elements-ℕ (succ-ℕ x) zero-ℕ = inr star
order-two-elements-ℕ (succ-ℕ x) (succ-ℕ y) = order-two-elements-ℕ x y

cases-order-three-elements-ℕ :
  (x y z : ℕ) → UU lzero
cases-order-three-elements-ℕ x y z =
  coprod
    ( coprod ((leq-ℕ x y) × (leq-ℕ y z)) ((leq-ℕ x z) × (leq-ℕ z y)))
    ( coprod
      ( coprod ((leq-ℕ y z) × (leq-ℕ z x)) ((leq-ℕ y x) × (leq-ℕ x z)))
      ( coprod ((leq-ℕ z x) × (leq-ℕ x y)) ((leq-ℕ z y) × (leq-ℕ y x))))

order-three-elements-ℕ :
  (x y z : ℕ) → cases-order-three-elements-ℕ x y z
order-three-elements-ℕ zero-ℕ zero-ℕ zero-ℕ = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ zero-ℕ (succ-ℕ z) = inl (inl (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) zero-ℕ = inl (inr (pair star star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) =
  inl (functor-coprod (pair star) (pair star) (order-two-elements-ℕ y z))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ zero-ℕ =
  inr (inl (inl (pair star star)))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) =
  inr (inl (functor-coprod (pair star) (pair star) (order-two-elements-ℕ z x)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ =
  inr (inr (functor-coprod (pair star) (pair star) (order-two-elements-ℕ x y)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) =
  order-three-elements-ℕ x y z

triangle-equality-dist-ℕ :
  (x y z : ℕ) → (leq-ℕ x y) → (leq-ℕ y z) →
  Id (add-ℕ (dist-ℕ x y) (dist-ℕ y z)) (dist-ℕ x z)
triangle-equality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ H1 H2 = refl
triangle-equality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ z) star star =
  ap succ-ℕ (left-unit-law-add-ℕ z)
triangle-equality-dist-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) star H2 =
  left-successor-law-add-ℕ y (dist-ℕ y z) ∙
  ap succ-ℕ (leq-dist-ℕ y z H2)
triangle-equality-dist-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) H1 H2 =
  triangle-equality-dist-ℕ x y z H1 H2

cases-dist-ℕ :
  (x y z : ℕ) → UU lzero
cases-dist-ℕ x y z = 
  coprod
    ( Id (add-ℕ (dist-ℕ x y) (dist-ℕ y z)) (dist-ℕ x z))
    ( coprod
      ( Id (add-ℕ (dist-ℕ y z) (dist-ℕ x z)) (dist-ℕ x y))
      ( Id (add-ℕ (dist-ℕ x z) (dist-ℕ x y)) (dist-ℕ y z)))

is-total-dist-ℕ :
  (x y z : ℕ) → cases-dist-ℕ x y z
is-total-dist-ℕ x y z with order-three-elements-ℕ x y z
is-total-dist-ℕ x y z | inl (inl (pair H1 H2)) =
  inl (triangle-equality-dist-ℕ x y z H1 H2)
is-total-dist-ℕ x y z | inl (inr (pair H1 H2)) = 
  inr
    ( inl
      ( ( commutative-add-ℕ (dist-ℕ y z) (dist-ℕ x z)) ∙
        ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ y z)) ∙
          ( triangle-equality-dist-ℕ x z y H1 H2))))
is-total-dist-ℕ x y z | inr (inl (inl (pair H1 H2))) =
  inr
    ( inl
      ( ( ap (add-ℕ (dist-ℕ y z)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ y z x H1 H2) ∙
          ( symmetric-dist-ℕ y x))))
is-total-dist-ℕ x y z | inr (inl (inr (pair H1 H2))) =
  inr
    ( inr
      ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ x y)) ∙
        ( ( commutative-add-ℕ (dist-ℕ x z) (dist-ℕ y x)) ∙
          ( triangle-equality-dist-ℕ y x z H1 H2)))) 
is-total-dist-ℕ x y z | inr (inr (inl (pair H1 H2))) =
  inr
    ( inr
      ( ( ap (add-ℕ' (dist-ℕ x y)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ z x y H1 H2) ∙
          ( symmetric-dist-ℕ z y))))
is-total-dist-ℕ x y z | inr (inr (inr (pair H1 H2))) =
  inl
    ( ( ap-add-ℕ (symmetric-dist-ℕ x y) (symmetric-dist-ℕ y z)) ∙
      ( ( commutative-add-ℕ (dist-ℕ y x) (dist-ℕ z y)) ∙
        ( ( triangle-equality-dist-ℕ z y x H1 H2) ∙
          ( symmetric-dist-ℕ z x))))

--------------------------------------------------------------------------------

{- We define the congruence relation on ℕ and show that it is an equivalence
   relation on ℕ. -}

cong-ℕ :
  ℕ → ℕ → ℕ → UU lzero
cong-ℕ k x y = div-ℕ k (dist-ℕ x y)

eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 → cong-ℕ k x1 x4
eq-cong-eq-ℕ k refl H refl = H

reflexive-cong-ℕ :
  (k x : ℕ) → cong-ℕ k x x
reflexive-cong-ℕ k x =
  pair zero-ℕ ((left-zero-law-mul-ℕ (succ-ℕ k)) ∙ (dist-eq-ℕ x x refl))

cong-identification-ℕ :
  (k : ℕ) {x y : ℕ} → Id x y → cong-ℕ k x y
cong-identification-ℕ k {x} refl = reflexive-cong-ℕ k x

symmetric-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k y x
symmetric-cong-ℕ k x y (pair d p) =
  pair d (p ∙ (symmetric-dist-ℕ x y))

transitive-cong-ℕ :
  (k x y z : ℕ) →
  cong-ℕ k x y → cong-ℕ k y z → cong-ℕ k x z
transitive-cong-ℕ k x y z d e with is-total-dist-ℕ x y z
transitive-cong-ℕ k x y z d e | inl α =
  tr (div-ℕ k) α (div-add-ℕ k (dist-ℕ x y) (dist-ℕ y z) d e)
transitive-cong-ℕ k x y z d e | inr (inl α) =
  div-right-summand-ℕ k (dist-ℕ y z) (dist-ℕ x z) e (tr (div-ℕ k) (inv α) d)
transitive-cong-ℕ k x y z d e | inr (inr α) =
  div-left-summand-ℕ k (dist-ℕ x z) (dist-ℕ x y) d (tr (div-ℕ k) (inv α) e)

concatenate-cong-eq-cong-ℕ :
  {k x1 x2 x3 x4 : ℕ} →
  cong-ℕ k x1 x2 → Id x2 x3 → cong-ℕ k x3 x4 → cong-ℕ k x1 x4
concatenate-cong-eq-cong-ℕ {k} {x} {y} {.y} {z} H refl K =
  transitive-cong-ℕ k x y z H K
  
eq-cong-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 x5 x6 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 →
  cong-ℕ k x4 x5 → Id x5 x6 → cong-ℕ k x1 x6
eq-cong-eq-cong-eq-ℕ k {x} {.x} {y} {.y} {z} {.z} refl H refl K refl =
  transitive-cong-ℕ k x y z H K

--------------------------------------------------------------------------------

-- We show that zero-ℕ is congruent to n modulo n.

cong-zero-ℕ :
  (k : ℕ) → cong-ℕ k k zero-ℕ
cong-zero-ℕ k =
  pair one-ℕ ((left-unit-law-mul-ℕ k) ∙ (inv (right-zero-law-dist-ℕ k)))

-- We show that congruence is translation invariant --

translation-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (add-ℕ z x) (add-ℕ z y)
translation-invariant-cong-ℕ k x y z (pair d p) =
  pair d (p ∙ inv (translation-invariant-dist-ℕ z x y))

translation-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (add-ℕ x z) (add-ℕ y z)
translation-invariant-cong-ℕ' k x y z H =
  eq-cong-eq-ℕ k
    ( commutative-add-ℕ x z)
    ( translation-invariant-cong-ℕ k x y z H)
    ( commutative-add-ℕ z y)

step-invariant-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k (succ-ℕ x) (succ-ℕ y)
step-invariant-cong-ℕ k x y = translation-invariant-cong-ℕ' k x y one-ℕ

-- We show that congruence is invariant under scalar multiplication --

scalar-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y →  cong-ℕ k (mul-ℕ z x) (mul-ℕ z y)
scalar-invariant-cong-ℕ k x y z (pair d p) =
  pair
    ( mul-ℕ z d)
    ( ( associative-mul-ℕ z d k) ∙
      ( ( ap (mul-ℕ z) p) ∙
        ( inv (linear-dist-ℕ x y z))))

scalar-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (mul-ℕ x z) (mul-ℕ y z)
scalar-invariant-cong-ℕ' k x y z H =
  eq-cong-eq-ℕ k
    ( commutative-mul-ℕ x z)
    ( scalar-invariant-cong-ℕ k x y z H)
    ( commutative-mul-ℕ z y)

-- We show that addition respects the congruence relation --

is-congruence-add-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k x x' → cong-ℕ k y y' → cong-ℕ k (add-ℕ x y) (add-ℕ x' y')
is-congruence-add-ℕ k {x} {y} {x'} {y'} H K =
  transitive-cong-ℕ k (add-ℕ x y) (add-ℕ x y') (add-ℕ x' y')
    ( translation-invariant-cong-ℕ k y y' x K)
    ( translation-invariant-cong-ℕ' k x x' y' H)

-- We show that multiplication respects the congruence relation --

is-congruence-mul-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ  k x x' → cong-ℕ k y y' → cong-ℕ k (mul-ℕ x y) (mul-ℕ x' y')
is-congruence-mul-ℕ k {x} {y} {x'} {y'} H K =
  transitive-cong-ℕ k (mul-ℕ x y) (mul-ℕ x y') (mul-ℕ x' y')
    ( scalar-invariant-cong-ℕ k y y' x K)
    ( scalar-invariant-cong-ℕ' k x x' y' H)

--------------------------------------------------------------------------------

-- We show that cong-ℕ zero-ℕ is the discrete equivalence relation --

is-discrete-cong-zero-ℕ :
  (x y : ℕ) → cong-ℕ zero-ℕ x y → Id x y
is-discrete-cong-zero-ℕ x y (pair k p) =
  eq-dist-ℕ x y ((inv (right-zero-law-mul-ℕ k)) ∙ p)

-- We show that cong-ℕ one-ℕ is the indiscrete equivalence relation --

div-one-ℕ :
  (x : ℕ) → div-ℕ one-ℕ x
div-one-ℕ x = pair x (right-unit-law-mul-ℕ x)

is-indiscrete-cong-one-ℕ :
  (x y : ℕ) → cong-ℕ one-ℕ x y
is-indiscrete-cong-one-ℕ x y = div-one-ℕ (dist-ℕ x y)

--------------------------------------------------------------------------------

{- The modulo function -}

mod-succ-ℕ : (k : ℕ) → ℕ → Fin (succ-ℕ k)
mod-succ-ℕ k zero-ℕ = zero-Fin
mod-succ-ℕ zero-ℕ (succ-ℕ n) = zero-Fin
mod-succ-ℕ (succ-ℕ k) (succ-ℕ n) = succ-Fin (mod-succ-ℕ (succ-ℕ k) n)

mod-two-ℕ : ℕ → Fin two-ℕ
mod-two-ℕ = mod-succ-ℕ one-ℕ

mod-three-ℕ : ℕ → Fin three-ℕ
mod-three-ℕ = mod-succ-ℕ two-ℕ

zero-law-mod-succ-ℕ :
  (k : ℕ) → Id (mod-succ-ℕ k zero-ℕ) zero-Fin
zero-law-mod-succ-ℕ n = refl

successor-law-mod-succ-ℕ :
  (n m : ℕ) → le-ℕ m (succ-ℕ n) → Id (mod-succ-ℕ (succ-ℕ n) m) (inl (mod-succ-ℕ n m))
successor-law-mod-succ-ℕ zero-ℕ zero-ℕ star = refl
successor-law-mod-succ-ℕ (succ-ℕ n) zero-ℕ star = refl
successor-law-mod-succ-ℕ (succ-ℕ n) (succ-ℕ m) p =
  ( ( ap succ-Fin (successor-law-mod-succ-ℕ (succ-ℕ n) m
      ( transitive-le-ℕ m (succ-ℕ n) (succ-ℕ (succ-ℕ n)) p
        ( succ-le-ℕ (succ-ℕ n))))) ∙
    ( ap succ-Fin (ap inl (successor-law-mod-succ-ℕ n m p)))) ∙
  ( ap inl (ap succ-Fin (inv (successor-law-mod-succ-ℕ n m p))))

neg-one-law-mod-succ-ℕ :
  (k : ℕ) → Id (mod-succ-ℕ k k) neg-one-Fin
neg-one-law-mod-succ-ℕ zero-ℕ = refl
neg-one-law-mod-succ-ℕ (succ-ℕ k) =
  ap succ-Fin
    ( ( successor-law-mod-succ-ℕ k k (succ-le-ℕ k)) ∙
      ( ap inl (neg-one-law-mod-succ-ℕ k)))

--------------------------------------------------------------------------------

-- We show that mod-succ-ℕ is a periodic function with period succ-ℕ n --

is-periodic-ℕ :
  (k : ℕ) {l : Level} {A : UU l} (f : ℕ → A) → UU l
is-periodic-ℕ k f = (x : ℕ) → Id (f x) (f (add-ℕ k x))

base-case-is-periodic-mod-succ-ℕ :
  (k : ℕ) → Id (mod-succ-ℕ k (succ-ℕ k)) zero-Fin
base-case-is-periodic-mod-succ-ℕ zero-ℕ = refl
base-case-is-periodic-mod-succ-ℕ (succ-ℕ k) =
  ap succ-Fin (neg-one-law-mod-succ-ℕ (succ-ℕ k))

is-periodic-mod-succ-ℕ :
  (k : ℕ) → is-periodic-ℕ (succ-ℕ k) (mod-succ-ℕ k)
is-periodic-mod-succ-ℕ k zero-ℕ =
  (zero-law-mod-succ-ℕ k) ∙ (inv (base-case-is-periodic-mod-succ-ℕ k))
is-periodic-mod-succ-ℕ zero-ℕ (succ-ℕ x) = refl
is-periodic-mod-succ-ℕ (succ-ℕ k) (succ-ℕ x) =
  ap succ-Fin (is-periodic-mod-succ-ℕ (succ-ℕ k) x)

--------------------------------------------------------------------------------

-- We show that mod-succ-ℕ sends congruent elements to equal elements --

zero-class-mod-succ-ℕ :
  (k x : ℕ) (d : div-ℕ (succ-ℕ k) x) → Id (mod-succ-ℕ k x) zero-Fin
zero-class-mod-succ-ℕ k .zero-ℕ (pair zero-ℕ refl) = zero-law-mod-succ-ℕ k
zero-class-mod-succ-ℕ k x (pair (succ-ℕ d) p) =
  ( inv (ap (mod-succ-ℕ k) p)) ∙
  ( ( ap (mod-succ-ℕ k) (commutative-add-ℕ (mul-ℕ d (succ-ℕ k)) (succ-ℕ k))) ∙
    ( ( inv (is-periodic-mod-succ-ℕ k (mul-ℕ d (succ-ℕ k)))) ∙
      ( zero-class-mod-succ-ℕ k (mul-ℕ d (succ-ℕ k)) (pair d refl))))

eq-cong-ℕ :
  (k x y : ℕ) → cong-ℕ (succ-ℕ k) x y → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y)
eq-cong-ℕ k zero-ℕ zero-ℕ H = refl
eq-cong-ℕ k zero-ℕ (succ-ℕ y) H =
  ( zero-law-mod-succ-ℕ k) ∙ ( inv (zero-class-mod-succ-ℕ k (succ-ℕ y) H))
eq-cong-ℕ k (succ-ℕ x) zero-ℕ H =
  ( zero-class-mod-succ-ℕ k (succ-ℕ x) H) ∙ (inv (zero-law-mod-succ-ℕ k))
eq-cong-ℕ zero-ℕ (succ-ℕ x) (succ-ℕ y) H = refl
eq-cong-ℕ (succ-ℕ k) (succ-ℕ x) (succ-ℕ y) H =
  ap succ-Fin (eq-cong-ℕ (succ-ℕ k) x y H)

--------------------------------------------------------------------------------

{- We define the inclusion of Fin k into ℕ. -}

nat-Fin : {k : ℕ} → Fin k → ℕ
nat-Fin {succ-ℕ k} (inl x) = nat-Fin x
nat-Fin {succ-ℕ k} (inr x) = k

zero-law-nat-Fin :
  {k : ℕ} → Id (nat-Fin (zero-Fin {k})) zero-ℕ
zero-law-nat-Fin {zero-ℕ} = refl 
zero-law-nat-Fin {succ-ℕ k} = zero-law-nat-Fin {k}

neg-one-law-nat-Fin :
  {k : ℕ} → Id (nat-Fin (neg-one-Fin {k})) k
neg-one-law-nat-Fin {k} = refl

{- We show that nat-Fin commutes with successor on elements of the form
   inl-Fin n x. -}

nat-succ-inl-Fin :
  {k : ℕ} (x : Fin k) →
  Id (nat-Fin (succ-Fin (inl-Fin k x))) (succ-ℕ (nat-Fin (inl-Fin k x))) 
nat-succ-inl-Fin {succ-ℕ k} (inl x) = nat-succ-inl-Fin x
nat-succ-inl-Fin {succ-ℕ k} (inr x) = refl

{- We show that nat-Fin x ≤ k. -}

upper-bound-nat-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → leq-ℕ (nat-Fin x) k
upper-bound-nat-Fin {zero-ℕ} (inr star) = star
upper-bound-nat-Fin {succ-ℕ k} (inl x) =
  transitive-leq-ℕ
    ( nat-Fin x)
    ( k)
    ( succ-ℕ k)
    ( upper-bound-nat-Fin x)
    ( succ-leq-ℕ k)
upper-bound-nat-Fin {succ-ℕ k} (inr star) = reflexive-leq-ℕ (succ-ℕ k)

--------------------------------------------------------------------------------

-- We show that nat-Fin is an injective function --

neq-leq-ℕ : {m n : ℕ} → leq-ℕ m n → ¬ (Id m (succ-ℕ n))
neq-leq-ℕ {zero-ℕ} {n} p q = Eq-ℕ-eq q
neq-leq-ℕ {succ-ℕ m} {succ-ℕ n} p q =
  neq-leq-ℕ p (is-injective-succ-ℕ m (succ-ℕ n) q)

is-injective-nat-Fin : {k : ℕ} {x y : Fin (succ-ℕ k)} →
  Id (nat-Fin x) (nat-Fin y) → Id x y
is-injective-nat-Fin {zero-ℕ} {inr star} {inr star} p = refl
is-injective-nat-Fin {succ-ℕ k} {inl x} {inl y} p =
  ap inl (is-injective-nat-Fin p)
is-injective-nat-Fin {succ-ℕ k} {inl x} {inr star} p =
  ex-falso (neq-leq-ℕ (upper-bound-nat-Fin x) p)
is-injective-nat-Fin {succ-ℕ k} {inr star} {inl y} p =
  ex-falso (neq-leq-ℕ (upper-bound-nat-Fin y) (inv p))
is-injective-nat-Fin {succ-ℕ k} {inr star} {inr star} p = refl

--------------------------------------------------------------------------------

-- Now we show that Fin (succ-ℕ n) is a retract of ℕ --

leq-le-ℕ :
  {x y z : ℕ} → leq-ℕ x y → le-ℕ y z → le-ℕ x z
leq-le-ℕ {zero-ℕ} {zero-ℕ} {succ-ℕ z} star star = star
leq-le-ℕ {zero-ℕ} {succ-ℕ y} {succ-ℕ z} p q = star
leq-le-ℕ {succ-ℕ x} {succ-ℕ y} {succ-ℕ z} p q = leq-le-ℕ {x} {y} {z} p q

issec-nat-Fin : (k : ℕ) (x : Fin (succ-ℕ k)) → Id (mod-succ-ℕ k (nat-Fin x)) x
issec-nat-Fin zero-ℕ (inr star) = refl
issec-nat-Fin (succ-ℕ k) (inl x) =
  ( successor-law-mod-succ-ℕ k (nat-Fin x)
    ( leq-le-ℕ {nat-Fin x} {k} {succ-ℕ k} (upper-bound-nat-Fin {k} x) (succ-le-ℕ k))) ∙
  ( ap inl (issec-nat-Fin k x))
issec-nat-Fin (succ-ℕ k) (inr star) = neg-one-law-mod-succ-ℕ (succ-ℕ k)

--------------------------------------------------------------------------------

-- We show that nat-Fin commutes with the successor for x < neg-one-Fin --

nat-succ-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) (p : ¬ (Eq-Fin (succ-ℕ k) x neg-one-Fin)) →
  Id (nat-Fin (succ-Fin x)) (succ-ℕ (nat-Fin x))
nat-succ-Fin {zero-ℕ} (inr star) p = ex-falso (p star)
nat-succ-Fin {succ-ℕ k} (inl (inl x)) p =
  nat-succ-Fin (inl x) id
nat-succ-Fin {succ-ℕ k} (inl (inr star)) p = refl
nat-succ-Fin {succ-ℕ k} (inr star) p = ex-falso (p star)

--------------------------------------------------------------------------------

-- We show that (nat-Fin (mod-succ-ℕ n x)) is congruent to x modulo n+1. --

cong-nat-mod-succ-ℕ :
  (k x : ℕ) → cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
cong-nat-mod-succ-ℕ k x with
  is-decidable-eq-Fin (succ-ℕ k) (mod-succ-ℕ k x) zero-Fin
cong-nat-mod-succ-ℕ zero-ℕ zero-ℕ | d = pair zero-ℕ refl
cong-nat-mod-succ-ℕ zero-ℕ (succ-ℕ x) | d = div-one-ℕ (dist-ℕ zero-ℕ (succ-ℕ x))
cong-nat-mod-succ-ℕ (succ-ℕ k) zero-ℕ | d =
  eq-cong-eq-ℕ (succ-ℕ (succ-ℕ k))
    ( zero-law-nat-Fin {succ-ℕ k})
    ( reflexive-cong-ℕ (succ-ℕ (succ-ℕ k)) zero-ℕ)
    ( refl)
cong-nat-mod-succ-ℕ (succ-ℕ k) (succ-ℕ x) | inl p =
  eq-cong-eq-cong-eq-ℕ
    ( succ-ℕ (succ-ℕ k))
    ( ap nat-Fin {x = mod-succ-ℕ (succ-ℕ k) (succ-ℕ x)} p ∙
      zero-law-nat-Fin {succ-ℕ k})
    ( symmetric-cong-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( zero-ℕ)
      ( succ-ℕ (succ-ℕ k))
      ( cong-zero-ℕ (succ-ℕ (succ-ℕ k))))
    ( ap
      ( succ-ℕ ∘ nat-Fin)
      { x = neg-one-Fin}
      { y = mod-succ-ℕ (succ-ℕ k) x}
      ( is-injective-succ-Fin (inv p)))
    ( step-invariant-cong-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( nat-Fin (mod-succ-ℕ (succ-ℕ k) x))
      ( x)
      ( cong-nat-mod-succ-ℕ (succ-ℕ k) x))
    ( refl)
cong-nat-mod-succ-ℕ (succ-ℕ k) (succ-ℕ x) | inr f =
  eq-cong-eq-ℕ
    ( succ-ℕ (succ-ℕ k))
    ( nat-succ-Fin
      ( mod-succ-ℕ (succ-ℕ k) x)
      ( (f ∘ ap succ-Fin) ∘
        ( eq-Eq-Fin
          { succ-ℕ (succ-ℕ k)}
          { x = mod-succ-ℕ (succ-ℕ k) x}
          { y = neg-one-Fin})))
    ( step-invariant-cong-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( nat-Fin (mod-succ-ℕ (succ-ℕ k) x))
      ( x)
      ( cong-nat-mod-succ-ℕ (succ-ℕ k) x))
    ( refl)

--------------------------------------------------------------------------------

{- We show that if mod-succ-ℕ n = is mod-succ-ℕ n x, then x and y must be
   congruent modulo succ-ℕ n. -}

cong-eq-ℕ :
  (k x y : ℕ) → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y) → cong-ℕ (succ-ℕ k) x y
cong-eq-ℕ k x y p =
  concatenate-cong-eq-cong-ℕ {succ-ℕ k} {x}
    ( symmetric-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k x)) x
      ( cong-nat-mod-succ-ℕ k x))
    ( ap nat-Fin p)
    ( cong-nat-mod-succ-ℕ k y)

--------------------------------------------------------------------------------

{- We show that if x and y are congruent modulo (succ-ℕ n), then we will have
   an identification mod-succ-ℕ n x = mod-succ-ℕ n y. -}

upper-bound-dist-ℕ :
  (b x y : ℕ) → leq-ℕ x b → leq-ℕ y b → leq-ℕ (dist-ℕ x y) b
upper-bound-dist-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
upper-bound-dist-ℕ (succ-ℕ b) zero-ℕ zero-ℕ H K = star
upper-bound-dist-ℕ (succ-ℕ b) zero-ℕ (succ-ℕ y) H K = K
upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) zero-ℕ H K = H
upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) (succ-ℕ y) H K =
  transitive-leq-ℕ
    ( dist-ℕ x y)
    ( b)
    ( succ-ℕ b)
    ( upper-bound-dist-ℕ b x y H K)
    ( succ-leq-ℕ b)

contradiction-leq-ℕ :
  (x y : ℕ) → leq-ℕ x y → leq-ℕ (succ-ℕ y) x → empty
contradiction-leq-ℕ (succ-ℕ x) (succ-ℕ y) H K = contradiction-leq-ℕ x y H K

eq-zero-div-ℕ :
  (d x : ℕ) → leq-ℕ x d → div-ℕ (succ-ℕ d) x → Id x zero-ℕ
eq-zero-div-ℕ d zero-ℕ H D = refl
eq-zero-div-ℕ d (succ-ℕ x) H (pair (succ-ℕ k) p) =
  ex-falso
    ( contradiction-leq-ℕ d x
      ( concatenate-eq-leq-eq-ℕ
        { x1 = succ-ℕ d}
        { x2 = succ-ℕ d}
        { x3 = succ-ℕ (add-ℕ (mul-ℕ k (succ-ℕ d)) d)}
        { x4 = succ-ℕ x}
        ( refl)
        ( leq-add-ℕ' d (mul-ℕ k (succ-ℕ d)))
        ( p)) H)

eq-cong-nat-Fin :
  (k : ℕ) (x y : Fin k) → cong-ℕ k (nat-Fin x) (nat-Fin y) → Id x y
eq-cong-nat-Fin (succ-ℕ k) x y H =
  is-injective-nat-Fin
    ( eq-dist-ℕ
      ( nat-Fin x)
      ( nat-Fin y)
      ( inv
        ( eq-zero-div-ℕ k
          ( dist-ℕ (nat-Fin x) (nat-Fin y))
          ( upper-bound-dist-ℕ k
            ( nat-Fin x)
            ( nat-Fin y)
            ( upper-bound-nat-Fin x)
            ( upper-bound-nat-Fin y))
          ( H))))

eq-mod-succ-ℕ :
  (k x y : ℕ) → cong-ℕ (succ-ℕ k) x y → Id (mod-succ-ℕ k x) (mod-succ-ℕ k y)
eq-mod-succ-ℕ k x y H =
  eq-cong-nat-Fin
    ( succ-ℕ k)
    ( mod-succ-ℕ k x)
    ( mod-succ-ℕ k y)
    ( transitive-cong-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k x))
      ( x)
      ( nat-Fin (mod-succ-ℕ k y))
      ( cong-nat-mod-succ-ℕ k x)
      ( transitive-cong-ℕ (succ-ℕ k) x y (nat-Fin (mod-succ-ℕ k y)) H
        ( symmetric-cong-ℕ (succ-ℕ k) (nat-Fin (mod-succ-ℕ k y)) y
          ( cong-nat-mod-succ-ℕ k y))))

{- This completes the proof that 

   (mod-succ-ℕ n x = mod-succ-ℕ n y) ↔ (cong-ℕ (succ-ℕ n) x y). -}

--------------------------------------------------------------------------------

-- Now we start defining the finite cyclic groups ℤ/n.

-- Addition on finite sets --

add-Fin : {k : ℕ} → Fin k → Fin k → Fin k
add-Fin {succ-ℕ k} x y = mod-succ-ℕ k (add-ℕ (nat-Fin x) (nat-Fin y))

add-Fin' : {k : ℕ} → Fin k → Fin k → Fin k
add-Fin' x y = add-Fin y x

ap-add-Fin :
  {k : ℕ} {x y x' y' : Fin k} →
  Id x x' → Id y y' → Id (add-Fin x y) (add-Fin x' y')
ap-add-Fin refl refl = refl

cong-add-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin (add-Fin x y)) (add-ℕ (nat-Fin x) (nat-Fin y))
cong-add-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (add-ℕ (nat-Fin x) (nat-Fin y))

--------------------------------------------------------------------------------

-- We show that addition is associative --

associative-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (add-Fin (add-Fin x y) z) (add-Fin x (add-Fin y z))
associative-add-Fin {succ-ℕ k} x y z =
  eq-cong-ℕ k
    ( add-ℕ (nat-Fin (add-Fin x y)) (nat-Fin z))
    ( add-ℕ (nat-Fin x) (nat-Fin (add-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = add-ℕ (nat-Fin (add-Fin x y)) (nat-Fin z)}
      { x2 = add-ℕ (add-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = add-ℕ (nat-Fin x) (add-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = add-ℕ (nat-Fin x) (nat-Fin (add-Fin y z))}
      ( is-congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (add-Fin x y)}
        { y = nat-Fin z}
        { x' = add-ℕ (nat-Fin x) (nat-Fin y)}
        { y' = nat-Fin z}
        ( cong-add-Fin x y)
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin z)))
      ( associative-add-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( is-congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin x}
        { y = add-ℕ (nat-Fin y) (nat-Fin z)}
        { x' = nat-Fin x}
        { y' = nat-Fin (add-Fin y z)}
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin x))
        ( symmetric-cong-ℕ
          ( succ-ℕ k)
          ( nat-Fin (add-Fin y z))
          ( add-ℕ (nat-Fin y) (nat-Fin z))
          ( cong-add-Fin y z))))

--------------------------------------------------------------------------------

-- addition is commutative --

commutative-add-Fin : {k : ℕ} (x y : Fin k) → Id (add-Fin x y) (add-Fin y x)
commutative-add-Fin {succ-ℕ k} x y =
  eq-cong-ℕ k
    ( add-ℕ (nat-Fin x) (nat-Fin y))
    ( add-ℕ (nat-Fin y) (nat-Fin x))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( commutative-add-ℕ (nat-Fin x) (nat-Fin y)))

--------------------------------------------------------------------------------

-- We prove the unit laws for add-Fin --

left-unit-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin zero-Fin x) x
left-unit-law-add-Fin {k} x =
  ( eq-cong-ℕ k
    ( add-ℕ (nat-Fin (zero-Fin {k})) (nat-Fin x))
    ( nat-Fin x)
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( ( ap (add-ℕ' (nat-Fin x)) (zero-law-nat-Fin {succ-ℕ k})) ∙
        ( left-unit-law-add-ℕ (nat-Fin x))))) ∙
  ( issec-nat-Fin k x)

right-unit-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin x zero-Fin) x
right-unit-law-add-Fin x =
  ( commutative-add-Fin x zero-Fin) ∙
  ( left-unit-law-add-Fin x)

--------------------------------------------------------------------------------

-- We define the negative of x : Fin (succ-ℕ n) --

neg-Fin :
  {k : ℕ} → Fin k → Fin k
neg-Fin {succ-ℕ k} x =
  mod-succ-ℕ k (dist-ℕ (nat-Fin x) (succ-ℕ k))

cong-neg-Fin :
  {k : ℕ} (x : Fin k) →
  cong-ℕ k (nat-Fin (neg-Fin x)) (dist-ℕ (nat-Fin x) k)
cong-neg-Fin {succ-ℕ k} x = 
  cong-nat-mod-succ-ℕ k (dist-ℕ (nat-Fin x) (succ-ℕ k))

left-inverse-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin (neg-Fin x) x) zero-Fin
left-inverse-law-add-Fin {k} x =
  eq-cong-ℕ k (add-ℕ (nat-Fin (neg-Fin x)) (nat-Fin x)) zero-ℕ
    ( concatenate-cong-eq-cong-ℕ
      { succ-ℕ k}
      { x1 = add-ℕ (nat-Fin (neg-Fin x)) (nat-Fin x)}
      { x2 = add-ℕ (dist-ℕ (nat-Fin x) (succ-ℕ k)) (nat-Fin x)}
      { x3 = succ-ℕ k}
      { x4 = zero-ℕ}
      ( is-congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (neg-Fin x)}
        { y = nat-Fin x}
        ( cong-neg-Fin x)
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin x)))
      ( ( ap ( add-ℕ (dist-ℕ (nat-Fin x) (succ-ℕ k)))
             ( inv (left-zero-law-dist-ℕ (nat-Fin x)))) ∙
        ( ( commutative-add-ℕ
            ( dist-ℕ (nat-Fin x) (succ-ℕ k))
            ( dist-ℕ zero-ℕ (nat-Fin x))) ∙
          ( triangle-equality-dist-ℕ zero-ℕ (nat-Fin x) (succ-ℕ k) star
            ( preserves-leq-succ-ℕ (nat-Fin x) k (upper-bound-nat-Fin x)))))
      ( symmetric-cong-ℕ
          ( succ-ℕ k)
          ( zero-ℕ)
          ( succ-ℕ k)
          ( cong-zero-ℕ (succ-ℕ k))))

right-inverse-law-add-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (add-Fin x (neg-Fin x)) zero-Fin
right-inverse-law-add-Fin x =
  ( commutative-add-Fin x (neg-Fin x)) ∙ (left-inverse-law-add-Fin x)

--------------------------------------------------------------------------------

{- We define the multiplication on the types Fin n. -}

mul-Fin :
  {k : ℕ} → Fin k → Fin k → Fin k
mul-Fin {succ-ℕ k} x y = mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

ap-mul-Fin :
  {k : ℕ} {x y x' y' : Fin k} →
  Id x x' → Id y y' → Id (mul-Fin x y) (mul-Fin x' y')
ap-mul-Fin refl refl = refl

cong-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin (mul-Fin x y)) (mul-ℕ (nat-Fin x) (nat-Fin y))
cong-mul-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (mul-ℕ (nat-Fin x) (nat-Fin y))

associative-mul-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin (mul-Fin x y) z) (mul-Fin x (mul-Fin y z))
associative-mul-Fin {succ-ℕ k} x y z =
  eq-cong-ℕ k
    ( mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z))
    ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = mul-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin z)}
      { x2 = mul-ℕ (mul-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z))}
      ( is-congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (mul-Fin x y)}
        { y = nat-Fin z}
        ( cong-mul-Fin x y)
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin z)))
      ( associative-mul-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( symmetric-cong-ℕ
        ( succ-ℕ k)
        ( mul-ℕ (nat-Fin x) (nat-Fin (mul-Fin y z)))
        ( mul-ℕ (nat-Fin x) (mul-ℕ (nat-Fin y) (nat-Fin z)))
        ( is-congruence-mul-ℕ
          ( succ-ℕ k)
          { x = nat-Fin x}
          { y = nat-Fin (mul-Fin y z)}
          ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin x))
          ( cong-mul-Fin y z))))

commutative-mul-Fin :
  {k : ℕ} (x y : Fin k) → Id (mul-Fin x y) (mul-Fin y x)
commutative-mul-Fin {succ-ℕ k} x y =
  eq-cong-ℕ k
    ( mul-ℕ (nat-Fin x) (nat-Fin y))
    ( mul-ℕ (nat-Fin y) (nat-Fin x))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( commutative-mul-ℕ (nat-Fin x) (nat-Fin y)))

one-Fin : {k : ℕ} → Fin (succ-ℕ k)
one-Fin {k} = mod-succ-ℕ k one-ℕ

nat-one-Fin : {k : ℕ} → Id (nat-Fin (one-Fin {succ-ℕ k})) one-ℕ
nat-one-Fin {zero-ℕ} = refl
nat-one-Fin {succ-ℕ k} = nat-one-Fin {k}

left-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin one-Fin x) x
left-unit-law-mul-Fin {zero-ℕ} (inr star) = refl
left-unit-law-mul-Fin {succ-ℕ k} x =
  ( eq-cong-ℕ (succ-ℕ k)
    ( mul-ℕ (nat-Fin (one-Fin {succ-ℕ k})) (nat-Fin x))
    ( nat-Fin x)
    ( cong-identification-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( ( ap ( mul-ℕ' (nat-Fin x))
             ( nat-one-Fin {k})) ∙
        ( left-unit-law-mul-ℕ (nat-Fin x))))) ∙
  ( issec-nat-Fin (succ-ℕ k) x)

right-unit-law-mul-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → Id (mul-Fin x one-Fin) x
right-unit-law-mul-Fin x =
  ( commutative-mul-Fin x one-Fin) ∙
  ( left-unit-law-mul-Fin x)

--------------------------------------------------------------------------------

left-distributive-mul-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin x (add-Fin y z)) (add-Fin (mul-Fin x y) (mul-Fin x z))
left-distributive-mul-add-Fin {succ-ℕ k} x y z =
  eq-cong-ℕ k
    ( mul-ℕ (nat-Fin x) (nat-Fin (add-Fin y z)))
    ( add-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin (mul-Fin x z)))
    ( concatenate-cong-eq-cong-ℕ
      { k = succ-ℕ k}
      { x1 = mul-ℕ ( nat-Fin x) (nat-Fin (add-Fin y z))}
      { x2 = mul-ℕ ( nat-Fin x) (add-ℕ (nat-Fin y) (nat-Fin z))}
      { x3 = add-ℕ ( mul-ℕ (nat-Fin x) (nat-Fin y))
                   ( mul-ℕ (nat-Fin x) (nat-Fin z))}
      { x4 = add-ℕ (nat-Fin (mul-Fin x y)) (nat-Fin (mul-Fin x z))}
      ( is-congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin x}
        { y = nat-Fin (add-Fin y z)}
        { x' = nat-Fin x}
        { y' = add-ℕ (nat-Fin y) (nat-Fin z)}
        ( reflexive-cong-ℕ (succ-ℕ k) (nat-Fin x))
        ( cong-add-Fin y z))
      ( left-distributive-mul-add-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( symmetric-cong-ℕ (succ-ℕ k)
        ( add-ℕ ( nat-Fin (mul-Fin x y))
                ( nat-Fin (mul-Fin x z)))
        ( add-ℕ ( mul-ℕ (nat-Fin x) (nat-Fin y))
                ( mul-ℕ (nat-Fin x) (nat-Fin z)))
        ( is-congruence-add-ℕ
          ( succ-ℕ k)
          { x = nat-Fin (mul-Fin x y)}
          { y = nat-Fin (mul-Fin x z)}
          { x' = mul-ℕ (nat-Fin x) (nat-Fin y)}
          { y' = mul-ℕ (nat-Fin x) (nat-Fin z)}
          ( cong-mul-Fin x y)
          ( cong-mul-Fin x z))))

right-distributive-mul-add-Fin :
  {k : ℕ} (x y z : Fin k) →
  Id (mul-Fin (add-Fin x y) z) (add-Fin (mul-Fin x z) (mul-Fin y z))
right-distributive-mul-add-Fin {k} x y z =
  ( commutative-mul-Fin (add-Fin x y) z) ∙
  ( ( left-distributive-mul-add-Fin z x y) ∙
    ( ap-add-Fin (commutative-mul-Fin z x) (commutative-mul-Fin z y)))
