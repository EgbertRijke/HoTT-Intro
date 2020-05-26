{-# OPTIONS --without-K --exact-split #-}

module 07-finite-sets where

import 06-universes
open 06-universes public

--------------------------------------------------------------------------------

{- We introduce the finite types as a family indexed by ℕ. -}

Fin : ℕ → UU lzero
Fin zero-ℕ = empty
Fin (succ-ℕ n) = coprod (Fin n) unit

inl-Fin :
  (n : ℕ) → Fin n → Fin (succ-ℕ n)
inl-Fin n = inl

zero-Fin : {n : ℕ} → Fin (succ-ℕ n)
zero-Fin {zero-ℕ} = inr star
zero-Fin {succ-ℕ n} = inl zero-Fin

neg-one-Fin : {n : ℕ} → Fin (succ-ℕ n)
neg-one-Fin {n} = inr star

succ-Fin : {n : ℕ} → Fin n → Fin n
succ-Fin {succ-ℕ zero-ℕ} x = x
succ-Fin {succ-ℕ (succ-ℕ n)} (inl (inl x)) = inl (succ-Fin (inl x))
succ-Fin {succ-ℕ (succ-ℕ n)} (inl (inr x)) = neg-one-Fin
succ-Fin {succ-ℕ (succ-ℕ n)} (inr x) = zero-Fin

{- We show that the successor of neg-one-Fin is zero-Fin. -}

succ-neg-one-Fin : {n : ℕ} → Id (succ-Fin (neg-one-Fin {n})) zero-Fin
succ-neg-one-Fin {zero-ℕ} = refl
succ-neg-one-Fin {succ-ℕ n} = refl

--------------------------------------------------------------------------------

{- Observational equality on finite sets -}

Eq-Fin : (n : ℕ) → Fin n → Fin n → UU lzero
Eq-Fin (succ-ℕ n) (inl x) (inl y) = Eq-Fin n x y
Eq-Fin (succ-ℕ n) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ n) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ n) (inr x) (inr y) = unit

refl-Eq-Fin : {n : ℕ} (x : Fin n) → Eq-Fin n x x
refl-Eq-Fin {succ-ℕ n} (inl x) = refl-Eq-Fin x
refl-Eq-Fin {succ-ℕ n} (inr x) = star

Eq-Fin-eq : {n : ℕ} {x y : Fin n} → Id x y → Eq-Fin n x y
Eq-Fin-eq {n} refl = refl-Eq-Fin {n} _

eq-Eq-Fin :
  {n : ℕ} {x y : Fin n} → Eq-Fin n x y → Id x y
eq-Eq-Fin {succ-ℕ n} {inl x} {inl y} e = ap inl (eq-Eq-Fin e)
eq-Eq-Fin {succ-ℕ n} {inr star} {inr star} star = refl

--------------------------------------------------------------------------------

{- The inclusion function Fin n → Fin (succ-ℕ n) is injective. -}

is-injective-inl-Fin :
  {n : ℕ} {x y : Fin n} → Id (inl-Fin n x) (inl-Fin n y) → Id x y
is-injective-inl-Fin p = eq-Eq-Fin (Eq-Fin-eq p)

--------------------------------------------------------------------------------

{- We show that Fin n has decidable equality, for each n : ℕ. -}

is-decidable-Eq-Fin :
  (n : ℕ) (x y : Fin n) → is-decidable (Eq-Fin n x y)
is-decidable-Eq-Fin zero-ℕ () y
is-decidable-Eq-Fin (succ-ℕ n) (inl x) (inl y) = is-decidable-Eq-Fin n x y
is-decidable-Eq-Fin (succ-ℕ n) (inl x) (inr y) = inr id
is-decidable-Eq-Fin (succ-ℕ n) (inr x) (inl y) = inr id
is-decidable-Eq-Fin (succ-ℕ n) (inr x) (inr y) = inl star

is-decidable-eq-Fin :
  (n : ℕ) (x y : Fin n) → is-decidable (Id x y)
is-decidable-eq-Fin n x y =
  functor-coprod eq-Eq-Fin (functor-neg Eq-Fin-eq) (is-decidable-Eq-Fin n x y)

--------------------------------------------------------------------------------

{- We define the predecessor function on finite sets. -}

pred-Fin : {n : ℕ} → Fin (succ-ℕ n) → Fin (succ-ℕ n)
pred-Fin {zero-ℕ} x = zero-Fin
pred-Fin {succ-ℕ n} x with (is-decidable-Eq-Fin (succ-ℕ (succ-ℕ n)) x zero-Fin)
pred-Fin {succ-ℕ n} (inl x) | inl e = neg-one-Fin
pred-Fin {succ-ℕ n} (inl x) | inr f = inl (pred-Fin x)
pred-Fin {succ-ℕ n} (inr x) | inr f = inl neg-one-Fin

-- We show that the predecessor of zero is negative one --

pred-zero-Fin :
  {n : ℕ} → Id (pred-Fin {n} zero-Fin) neg-one-Fin
pred-zero-Fin {zero-ℕ} = refl
pred-zero-Fin {succ-ℕ n} with is-decidable-Eq-Fin (succ-ℕ n) zero-Fin zero-Fin
pred-zero-Fin {succ-ℕ n} | inl e = refl
pred-zero-Fin {succ-ℕ n} | inr f =
  ex-falso (f (refl-Eq-Fin {succ-ℕ n} zero-Fin))

-- We compute the predecessor of an element of the form inl that is not zero --

pred-inl-Fin :
  {n : ℕ} (x : Fin (succ-ℕ n)) (f : ¬ (Eq-Fin (succ-ℕ n) x zero-Fin)) →
  Id (pred-Fin (inl x)) (inl (pred-Fin x))
pred-inl-Fin {n} x f with is-decidable-Eq-Fin (succ-ℕ n) x zero-Fin
pred-inl-Fin {n} x f | inl e = ex-falso (f e)
pred-inl-Fin {n} x f | inr g = refl

-- We show that the predecessor function is a section of the successor function

succ-pred-Fin :
  {n : ℕ} (x : Fin (succ-ℕ n)) → Id (succ-Fin (pred-Fin x)) x
succ-pred-Fin {n} x with (is-decidable-Eq-Fin (succ-ℕ n) x zero-Fin)
succ-pred-Fin {zero-ℕ} (inr star) | d = refl
succ-pred-Fin {succ-ℕ n} (inl x) | inl e =
  ( ( ap (succ-Fin ∘ pred-Fin) {x = inl x} {y = zero-Fin} (eq-Eq-Fin e)) ∙
    ( ( ap succ-Fin pred-zero-Fin) ∙
      ( succ-neg-one-Fin))) ∙
  ( inv {x = inl x} {y = zero-Fin} (eq-Eq-Fin e))
succ-pred-Fin {succ-ℕ (succ-ℕ n)} (inl (inl (inl x))) | inr f =
  ( ap succ-Fin (pred-inl-Fin (inl (inl x)) f)) ∙
  ( ( ap (succ-Fin ∘ inl) (pred-inl-Fin (inl x) f)) ∙
    ( ( ap inl
        ( ( ap succ-Fin (inv (pred-inl-Fin (inl x) f))) ∙
          ( succ-pred-Fin (inl (inl x)))))))
succ-pred-Fin {succ-ℕ (succ-ℕ zero-ℕ)} (inl (inl (inr star))) | inr f =
  ex-falso (f star)
succ-pred-Fin {succ-ℕ (succ-ℕ (succ-ℕ n))} (inl (inl (inr star))) | inr f =
  ( ap succ-Fin (pred-inl-Fin (inl (inr star)) f)) ∙
  ( ap inl (succ-pred-Fin (inl (inr star))))
succ-pred-Fin {succ-ℕ zero-ℕ} (inl (inr x)) | inr f = ex-falso (f star)
succ-pred-Fin {succ-ℕ (succ-ℕ n)} (inl (inr x)) | inr f =
  ap inl (succ-pred-Fin (inr x))
succ-pred-Fin {succ-ℕ n} (inr star) | inr f = refl

-- We show that the predecessor function is a retract of the successor function

neq-zero-succ-Fin :
  {n : ℕ} (x : Fin (succ-ℕ n)) →
  ¬ (Eq-Fin (succ-ℕ (succ-ℕ n)) (succ-Fin (inl x)) zero-Fin)
neq-zero-succ-Fin {succ-ℕ n} (inl (inl x)) e = neq-zero-succ-Fin (inl x) e

pred-succ-Fin :
  {n : ℕ} (x : Fin (succ-ℕ n)) → Id (pred-Fin (succ-Fin x)) x
pred-succ-Fin {zero-ℕ} (inr star) = refl
pred-succ-Fin {succ-ℕ zero-ℕ} (inl (inr star)) = refl
pred-succ-Fin {succ-ℕ zero-ℕ} (inr star) = refl
pred-succ-Fin {succ-ℕ (succ-ℕ n)} (inl (inl (inl x))) =
  ( pred-inl-Fin (inl (succ-Fin (inl x))) (neq-zero-succ-Fin (inl x))) ∙
  ( ( ap inl (pred-inl-Fin (succ-Fin (inl x)) (neq-zero-succ-Fin (inl x)))) ∙
    ( ap (inl ∘ inl) (pred-succ-Fin (inl x))))
pred-succ-Fin {succ-ℕ (succ-ℕ n)} (inl (inl (inr star))) = refl
pred-succ-Fin {succ-ℕ (succ-ℕ n)} (inl (inr star)) = refl
pred-succ-Fin {succ-ℕ (succ-ℕ n)} (inr star) = pred-zero-Fin

{- In the terminology of the next chapter, we conclude that the successor 
   function is an equivalence. -}

{- We show here that the successor function is injective. -}

is-injective-succ-Fin :
  {n : ℕ} {x y : Fin (succ-ℕ n)} → Id (succ-Fin x) (succ-Fin y) → Id x y
is-injective-succ-Fin {n} {x} {y} p =
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
  (x y z : ℕ) → (leq-ℕ x y) × (leq-ℕ y z) →
  Id (add-ℕ (dist-ℕ x y) (dist-ℕ y z)) (dist-ℕ x z)
triangle-equality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ (pair H1 H2) = refl
triangle-equality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ z) (pair star star) =
  ap succ-ℕ (left-unit-law-add-ℕ z)
triangle-equality-dist-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) (pair star H2) =
  left-successor-law-add-ℕ y (dist-ℕ y z) ∙
  ap succ-ℕ (leq-dist-ℕ y z H2)
triangle-equality-dist-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) (pair H1 H2) =
  triangle-equality-dist-ℕ x y z (pair H1 H2)

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
is-total-dist-ℕ x y z | inl (inl H) =
  inl (triangle-equality-dist-ℕ x y z H)
is-total-dist-ℕ x y z | inl (inr H) = 
  inr
    ( inl
      ( ( commutative-add-ℕ (dist-ℕ y z) (dist-ℕ x z)) ∙
        ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ y z)) ∙
          ( triangle-equality-dist-ℕ x z y H))))
is-total-dist-ℕ x y z | inr (inl (inl H)) =
  inr
    ( inl
      ( ( ap (add-ℕ (dist-ℕ y z)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ y z x H) ∙
          ( symmetric-dist-ℕ y x))))
is-total-dist-ℕ x y z | inr (inl (inr H)) =
  inr
    ( inr
      ( ( ap (add-ℕ (dist-ℕ x z)) (symmetric-dist-ℕ x y)) ∙
        ( ( commutative-add-ℕ (dist-ℕ x z) (dist-ℕ y x)) ∙
          ( triangle-equality-dist-ℕ y x z H)))) 
is-total-dist-ℕ x y z | inr (inr (inl H)) =
  inr
    ( inr
      ( ( ap (add-ℕ' (dist-ℕ x y)) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ z x y H) ∙
          ( symmetric-dist-ℕ z y))))
is-total-dist-ℕ x y z | inr (inr (inr H)) =
  inl
    ( ( ap-add-ℕ (symmetric-dist-ℕ x y) (symmetric-dist-ℕ y z)) ∙
      ( ( commutative-add-ℕ (dist-ℕ y x) (dist-ℕ z y)) ∙
        ( ( triangle-equality-dist-ℕ z y x H) ∙
          ( symmetric-dist-ℕ z x))))

--------------------------------------------------------------------------------

{- We define the congruence relation on ℕ and show that it is an equivalence
   relation on ℕ. -}

cong-ℕ :
  ℕ → ℕ → ℕ → UU lzero
cong-ℕ k m n = div-ℕ k (dist-ℕ m n)

eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 → cong-ℕ k x1 x4
eq-cong-eq-ℕ k refl H refl = H

reflexive-cong-ℕ :
  (k x : ℕ) → cong-ℕ k x x
reflexive-cong-ℕ k x =
  pair zero-ℕ ((left-zero-law-mul-ℕ (succ-ℕ k)) ∙ (dist-eq-ℕ x x refl))

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
  {n x1 x2 x3 x4 : ℕ} →
  cong-ℕ n x1 x2 → Id x2 x3 → cong-ℕ n x3 x4 → cong-ℕ n x1 x4
concatenate-cong-eq-cong-ℕ {n} {x} {y} {.y} {z} H refl K =
  transitive-cong-ℕ n x y z H K
  
eq-cong-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 x5 x6 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 →
  cong-ℕ k x4 x5 → Id x5 x6 → cong-ℕ k x1 x6
eq-cong-eq-cong-eq-ℕ k {x} {.x} {y} {.y} {z} {.z} refl H refl K refl =
  transitive-cong-ℕ k x y z H K

--------------------------------------------------------------------------------

-- We show that zero-ℕ is congruent to n modulo n.

n-cong-zero-ℕ :
  (n : ℕ) → cong-ℕ n n zero-ℕ
n-cong-zero-ℕ n =
  pair one-ℕ ((left-unit-law-mul-ℕ n) ∙ (inv (right-zero-law-dist-ℕ n)))

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

mod-succ-ℕ : (n : ℕ) → ℕ → Fin (succ-ℕ n)
mod-succ-ℕ zero-ℕ n = zero-Fin
mod-succ-ℕ (succ-ℕ n) zero-ℕ = zero-Fin
mod-succ-ℕ (succ-ℕ n) (succ-ℕ m) = succ-Fin (mod-succ-ℕ (succ-ℕ n) m)

mod-two-ℕ : ℕ → Fin two-ℕ
mod-two-ℕ = mod-succ-ℕ one-ℕ

mod-three-ℕ : ℕ → Fin three-ℕ
mod-three-ℕ = mod-succ-ℕ two-ℕ

zero-law-mod-succ-ℕ :
  (n : ℕ) → Id (mod-succ-ℕ n zero-ℕ) zero-Fin
zero-law-mod-succ-ℕ zero-ℕ = refl
zero-law-mod-succ-ℕ (succ-ℕ n) = refl

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
  (n : ℕ) → Id (mod-succ-ℕ n n) neg-one-Fin
neg-one-law-mod-succ-ℕ zero-ℕ = refl
neg-one-law-mod-succ-ℕ (succ-ℕ n) =
  ap succ-Fin
    ( ( successor-law-mod-succ-ℕ n n (succ-le-ℕ n)) ∙
      ( ap inl (neg-one-law-mod-succ-ℕ n)))

--------------------------------------------------------------------------------

-- We show that mod-succ-ℕ is a periodic function with period succ-ℕ n --

is-periodic-ℕ :
  (n : ℕ) {l : Level} {A : UU l} (f : ℕ → A) → UU l
is-periodic-ℕ n f = (x : ℕ) → Id (f x) (f (add-ℕ n x))

base-case-is-periodic-mod-succ-ℕ :
  (n : ℕ) → Id (mod-succ-ℕ n (succ-ℕ n)) zero-Fin
base-case-is-periodic-mod-succ-ℕ zero-ℕ = refl
base-case-is-periodic-mod-succ-ℕ (succ-ℕ n) =
  ap succ-Fin (neg-one-law-mod-succ-ℕ (succ-ℕ n))

is-periodic-mod-succ-ℕ :
  (n : ℕ) → is-periodic-ℕ (succ-ℕ n) (mod-succ-ℕ n)
is-periodic-mod-succ-ℕ n zero-ℕ =
  (zero-law-mod-succ-ℕ n) ∙ (inv (base-case-is-periodic-mod-succ-ℕ n))
is-periodic-mod-succ-ℕ zero-ℕ (succ-ℕ x) = refl
is-periodic-mod-succ-ℕ (succ-ℕ n) (succ-ℕ x) =
  ap succ-Fin (is-periodic-mod-succ-ℕ (succ-ℕ n) x)

--------------------------------------------------------------------------------

-- We show that mod-succ-ℕ sends congruent elements to equal elements --

zero-class-mod-succ-ℕ :
  (n x : ℕ) (d : div-ℕ (succ-ℕ n) x) → Id (mod-succ-ℕ n x) zero-Fin
zero-class-mod-succ-ℕ n .zero-ℕ (pair zero-ℕ refl) = zero-law-mod-succ-ℕ n
zero-class-mod-succ-ℕ n x (pair (succ-ℕ k) p) =
  ( inv (ap (mod-succ-ℕ n) p)) ∙
  ( ( ap (mod-succ-ℕ n) (commutative-add-ℕ (mul-ℕ k (succ-ℕ n)) (succ-ℕ n))) ∙
    ( ( inv (is-periodic-mod-succ-ℕ n (mul-ℕ k (succ-ℕ n)))) ∙
      ( zero-class-mod-succ-ℕ n (mul-ℕ k (succ-ℕ n)) (pair k refl))))

eq-cong-ℕ :
  (n x y : ℕ) → cong-ℕ (succ-ℕ n) x y → Id (mod-succ-ℕ n x) (mod-succ-ℕ n y)
eq-cong-ℕ n zero-ℕ zero-ℕ H = refl
eq-cong-ℕ n zero-ℕ (succ-ℕ y) H =
  ( zero-law-mod-succ-ℕ n) ∙ ( inv (zero-class-mod-succ-ℕ n (succ-ℕ y) H))
eq-cong-ℕ n (succ-ℕ x) zero-ℕ H =
  ( zero-class-mod-succ-ℕ n (succ-ℕ x) H) ∙ (inv (zero-law-mod-succ-ℕ n))
eq-cong-ℕ zero-ℕ (succ-ℕ x) (succ-ℕ y) H = refl
eq-cong-ℕ (succ-ℕ n) (succ-ℕ x) (succ-ℕ y) H =
  ap succ-Fin (eq-cong-ℕ (succ-ℕ n) x y H)

--------------------------------------------------------------------------------

{- We define the inclusion of Fin n into ℕ. -}

nat-Fin : {n : ℕ} → Fin n → ℕ
nat-Fin {succ-ℕ n} (inl x) = nat-Fin x
nat-Fin {succ-ℕ n} (inr x) = n

zero-law-nat-Fin :
  {n : ℕ} → Id (nat-Fin (zero-Fin {n})) zero-ℕ
zero-law-nat-Fin {zero-ℕ} = refl 
zero-law-nat-Fin {succ-ℕ n} = zero-law-nat-Fin {n}

neg-one-law-nat-Fin :
  {n : ℕ} → Id (nat-Fin (neg-one-Fin {n})) n
neg-one-law-nat-Fin {n} = refl

{- We show that nat-Fin commutes with successor on elements of the form
   inl-Fin n x. -}

nat-succ-inl-Fin :
  {n : ℕ} (x : Fin n) →
  Id (nat-Fin (succ-Fin (inl-Fin n x))) (succ-ℕ (nat-Fin (inl-Fin n x))) 
nat-succ-inl-Fin {succ-ℕ n} (inl x) = nat-succ-inl-Fin x
nat-succ-inl-Fin {succ-ℕ n} (inr x) = refl

{- We show that nat-Fin x ≤ n. -}

upper-bound-nat-Fin : {n : ℕ} (x : Fin (succ-ℕ n)) → leq-ℕ (nat-Fin x) n
upper-bound-nat-Fin {zero-ℕ} (inr star) = star
upper-bound-nat-Fin {succ-ℕ n} (inl x) =
  transitive-leq-ℕ
    ( nat-Fin x)
    ( n)
    ( succ-ℕ n)
    ( upper-bound-nat-Fin x)
    ( succ-leq-ℕ n)
upper-bound-nat-Fin {succ-ℕ n} (inr star) = reflexive-leq-ℕ (succ-ℕ n)

--------------------------------------------------------------------------------

-- We show that nat-Fin is an injective function --

neq-leq-ℕ : {m n : ℕ} → leq-ℕ m n → ¬ (Id m (succ-ℕ n))
neq-leq-ℕ {zero-ℕ} {n} p q = Eq-ℕ-eq q
neq-leq-ℕ {succ-ℕ m} {succ-ℕ n} p q =
  neq-leq-ℕ p (is-injective-succ-ℕ m (succ-ℕ n) q)

is-injective-nat-Fin : {n : ℕ} {x y : Fin (succ-ℕ n)} →
  Id (nat-Fin x) (nat-Fin y) → Id x y
is-injective-nat-Fin {zero-ℕ} {inr star} {inr star} p = refl
is-injective-nat-Fin {succ-ℕ n} {inl x} {inl y} p =
  ap inl (is-injective-nat-Fin p)
is-injective-nat-Fin {succ-ℕ n} {inl x} {inr star} p =
  ex-falso (neq-leq-ℕ (upper-bound-nat-Fin x) p)
is-injective-nat-Fin {succ-ℕ n} {inr star} {inl y} p =
  ex-falso (neq-leq-ℕ (upper-bound-nat-Fin y) (inv p))
is-injective-nat-Fin {succ-ℕ n} {inr star} {inr star} p = refl

--------------------------------------------------------------------------------

-- Now we show that Fin (succ-ℕ n) is a retract of ℕ --

leq-le-ℕ :
  {x y z : ℕ} → leq-ℕ x y → le-ℕ y z → le-ℕ x z
leq-le-ℕ {zero-ℕ} {zero-ℕ} {succ-ℕ z} star star = star
leq-le-ℕ {zero-ℕ} {succ-ℕ y} {succ-ℕ z} p q = star
leq-le-ℕ {succ-ℕ x} {succ-ℕ y} {succ-ℕ z} p q = leq-le-ℕ {x} {y} {z} p q

issec-nat-Fin : (n : ℕ) (x : Fin (succ-ℕ n)) → Id (mod-succ-ℕ n (nat-Fin x)) x
issec-nat-Fin zero-ℕ (inr star) = refl
issec-nat-Fin (succ-ℕ n) (inl x) =
  ( successor-law-mod-succ-ℕ n (nat-Fin x)
    ( leq-le-ℕ {nat-Fin x} {n} {succ-ℕ n} (upper-bound-nat-Fin {n} x) (succ-le-ℕ n))) ∙
  ( ap inl (issec-nat-Fin n x))
issec-nat-Fin (succ-ℕ n) (inr star) = neg-one-law-mod-succ-ℕ (succ-ℕ n)

--------------------------------------------------------------------------------

{- We introduce the ≤ ordering on Fin n. -}

leq-Fin :
  {n : ℕ} → (x y : Fin n) → UU lzero
leq-Fin {succ-ℕ n} (inl x) (inl y) = leq-Fin x y
leq-Fin {succ-ℕ n} (inl x) (inr y) = unit
leq-Fin {succ-ℕ n} (inr x) (inl y) = empty
leq-Fin {succ-ℕ n} (inr x) (inr y) = unit

refl-leq-Fin :
  {n : ℕ} (x : Fin n) → leq-Fin x x
refl-leq-Fin {succ-ℕ n} (inl x) = refl-leq-Fin x
refl-leq-Fin {succ-ℕ n} (inr x) = star

--------------------------------------------------------------------------------

{- We introduce the < ordering on Fin n. -}

le-Fin :
  {n : ℕ} → (x y : Fin n) → UU lzero
le-Fin {succ-ℕ n} (inl x) (inl y) = le-Fin x y
le-Fin {succ-ℕ n} (inl x) (inr y) = unit
le-Fin {succ-ℕ n} (inr x) (inl y) = empty
le-Fin {succ-ℕ n} (inr x) (inr y) = empty

le-Fin' :
  {n : ℕ} → (x y : Fin n) → UU lzero
le-Fin' x y = le-Fin y x

le-neg-one-Fin :
  {n : ℕ} (x : Fin (succ-ℕ n)) →
  ¬ (Eq-Fin (succ-ℕ n) (succ-Fin x) zero-Fin) → le-Fin x neg-one-Fin
le-neg-one-Fin {n} (inl x) f = star
le-neg-one-Fin {n} (inr star) f =
  ex-falso (f (Eq-Fin-eq {n = succ-ℕ n} succ-neg-one-Fin))

neq-neg-one-Fin :
  {n : ℕ} (x : Fin (succ-ℕ n)) →
  ¬ (Eq-Fin (succ-ℕ n) (succ-Fin x) zero-Fin) →
  ¬ (Eq-Fin (succ-ℕ n) x neg-one-Fin)
neq-neg-one-Fin {n} (inr star) f e =
  ex-falso (f (Eq-Fin-eq {succ-ℕ n} succ-neg-one-Fin))

--------------------------------------------------------------------------------

-- We show that nat-Fin commutes with the successor for x < neg-one-Fin --

successor-law-nat-Fin :
  {n : ℕ} (x : Fin (succ-ℕ n)) (p : le-Fin x neg-one-Fin) →
  Id (succ-ℕ (nat-Fin x)) (nat-Fin (succ-Fin x))
successor-law-nat-Fin {succ-ℕ n} (inl (inl x)) star =
  successor-law-nat-Fin (inl x) star
successor-law-nat-Fin {succ-ℕ n} (inl (inr x)) star = refl

successor-law-nat-Fin' :
  {n : ℕ} (x : Fin (succ-ℕ n)) (p : ¬ (Eq-Fin (succ-ℕ n) x neg-one-Fin)) →
  Id (succ-ℕ (nat-Fin x)) (nat-Fin (succ-Fin x))
successor-law-nat-Fin' {zero-ℕ} (inr star) p = ex-falso (p star)
successor-law-nat-Fin' {succ-ℕ n} (inl (inl x)) p =
  successor-law-nat-Fin (inl x) star
successor-law-nat-Fin' {succ-ℕ n} (inl (inr star)) p = refl
successor-law-nat-Fin' {succ-ℕ n} (inr star) p = ex-falso (p star)

--------------------------------------------------------------------------------

-- We show that (nat-Fin (mod-succ-ℕ x)) is the remainder after division --

is-remainder-div-ℕ :
  {n : ℕ} → ℕ → Fin n → UU lzero
is-remainder-div-ℕ {n} x i = cong-ℕ n (nat-Fin i) x

is-remainder-div-mod-succ-ℕ :
  (n x : ℕ) → is-remainder-div-ℕ x (mod-succ-ℕ n x)
is-remainder-div-mod-succ-ℕ n x with
  is-decidable-eq-Fin (succ-ℕ n) (mod-succ-ℕ n x) zero-Fin
is-remainder-div-mod-succ-ℕ zero-ℕ x | d = div-one-ℕ (dist-ℕ zero-ℕ x)
is-remainder-div-mod-succ-ℕ (succ-ℕ n) zero-ℕ | d =
  eq-cong-eq-ℕ (succ-ℕ (succ-ℕ n))
    ( zero-law-nat-Fin {succ-ℕ n})
    ( reflexive-cong-ℕ (succ-ℕ (succ-ℕ n)) zero-ℕ)
    ( refl)
is-remainder-div-mod-succ-ℕ (succ-ℕ n) (succ-ℕ x) | inl p =
  eq-cong-eq-cong-eq-ℕ
    ( succ-ℕ (succ-ℕ n))
    { x1 = nat-Fin (mod-succ-ℕ (succ-ℕ n) (succ-ℕ x))}
    { x2 = zero-ℕ}
    { x3 = succ-ℕ (succ-ℕ n)}
    { x4 = succ-ℕ (nat-Fin (mod-succ-ℕ (succ-ℕ n) x))}
    { x5 = succ-ℕ x}
    { x6 = succ-ℕ x}
    ( ap nat-Fin {x = mod-succ-ℕ (succ-ℕ n) (succ-ℕ x)} p ∙
      zero-law-nat-Fin {succ-ℕ n})
    ( symmetric-cong-ℕ
      ( succ-ℕ (succ-ℕ n))
      ( zero-ℕ)
      ( succ-ℕ (succ-ℕ n))
      ( n-cong-zero-ℕ (succ-ℕ (succ-ℕ n))))
    ( ap
      ( succ-ℕ ∘ nat-Fin)
      { x = neg-one-Fin}
      { y = mod-succ-ℕ (succ-ℕ n) x}
      ( is-injective-succ-Fin (inv p)))
    ( step-invariant-cong-ℕ
      ( succ-ℕ (succ-ℕ n))
      ( nat-Fin (mod-succ-ℕ (succ-ℕ n) x))
      ( x)
      ( is-remainder-div-mod-succ-ℕ (succ-ℕ n) x))
    ( refl)
is-remainder-div-mod-succ-ℕ (succ-ℕ n) (succ-ℕ x) | inr f =
  eq-cong-eq-ℕ
    ( succ-ℕ (succ-ℕ n))
    { x1 = nat-Fin (mod-succ-ℕ (succ-ℕ n) (succ-ℕ x))}
    { x2 = succ-ℕ (nat-Fin (mod-succ-ℕ (succ-ℕ n) x))}
    { x3 = succ-ℕ x}
    { x4 = succ-ℕ x}
    ( inv
      ( successor-law-nat-Fin'
        ( mod-succ-ℕ (succ-ℕ n) x)
        ( (f ∘ ap succ-Fin) ∘
          ( eq-Eq-Fin
            { succ-ℕ (succ-ℕ n)}
            { x = mod-succ-ℕ (succ-ℕ n) x}
            { y = neg-one-Fin}))))
    ( step-invariant-cong-ℕ
      ( succ-ℕ (succ-ℕ n))
      ( nat-Fin (mod-succ-ℕ (succ-ℕ n) x))
      ( x)
      ( is-remainder-div-mod-succ-ℕ (succ-ℕ n) x))
    ( refl)

--------------------------------------------------------------------------------

{- We show that if mod-succ-ℕ n = is mod-succ-ℕ n x, then x and y must be
   congruent modulo succ-ℕ n. -}

cong-eq-ℕ :
  (n x y : ℕ) → Id (mod-succ-ℕ n x) (mod-succ-ℕ n y) → cong-ℕ (succ-ℕ n) x y
cong-eq-ℕ n x y p =
  concatenate-cong-eq-cong-ℕ {succ-ℕ n} {x}
    ( symmetric-cong-ℕ (succ-ℕ n) (nat-Fin (mod-succ-ℕ n x)) x
      ( is-remainder-div-mod-succ-ℕ n x))
    ( ap nat-Fin p)
    ( is-remainder-div-mod-succ-ℕ n y)

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
  (n x : ℕ) → leq-ℕ x n → div-ℕ (succ-ℕ n) x → Id x zero-ℕ
eq-zero-div-ℕ n zero-ℕ H D = refl
eq-zero-div-ℕ n (succ-ℕ x) H (pair (succ-ℕ d) p) =
  ex-falso
    ( contradiction-leq-ℕ n x
      ( concatenate-eq-leq-eq-ℕ
        { x1 = succ-ℕ n}
        { x2 = succ-ℕ n}
        { x3 = succ-ℕ (add-ℕ (mul-ℕ d (succ-ℕ n)) n)}
        { x4 = succ-ℕ x}
        ( refl)
        ( leq-add-ℕ' n (mul-ℕ d (succ-ℕ n)))
        ( p)) H)

eq-cong-nat-Fin :
  (n : ℕ) (x y : Fin n) → cong-ℕ n (nat-Fin x) (nat-Fin y) → Id x y
eq-cong-nat-Fin (succ-ℕ n) x y H =
  is-injective-nat-Fin
    ( eq-dist-ℕ
      ( nat-Fin x)
      ( nat-Fin y)
      ( inv
        ( eq-zero-div-ℕ n
          ( dist-ℕ (nat-Fin x) (nat-Fin y))
          ( upper-bound-dist-ℕ n
            ( nat-Fin x)
            ( nat-Fin y)
            ( upper-bound-nat-Fin x)
            ( upper-bound-nat-Fin y))
          ( H))))

eq-mod-succ-ℕ :
  (n x y : ℕ) → cong-ℕ (succ-ℕ n) x y → Id (mod-succ-ℕ n x) (mod-succ-ℕ n y)
eq-mod-succ-ℕ n x y H =
  eq-cong-nat-Fin
    ( succ-ℕ n)
    ( mod-succ-ℕ n x)
    ( mod-succ-ℕ n y)
    ( transitive-cong-ℕ
      ( succ-ℕ n)
      ( nat-Fin (mod-succ-ℕ n x))
      ( x)
      ( nat-Fin (mod-succ-ℕ n y))
      ( is-remainder-div-mod-succ-ℕ n x)
      ( transitive-cong-ℕ (succ-ℕ n) x y (nat-Fin (mod-succ-ℕ n y)) H
        ( symmetric-cong-ℕ (succ-ℕ n) (nat-Fin (mod-succ-ℕ n y)) y
          ( is-remainder-div-mod-succ-ℕ n y))))

{- This completes the proof that 

   (mod-succ-ℕ n x = mod-succ-ℕ n y) ↔ (cong-ℕ (succ-ℕ n) x y).
-}

--------------------------------------------------------------------------------

-- Addition on finite sets --

add-Fin : {n : ℕ} → Fin n → Fin n → Fin n
add-Fin {succ-ℕ n} x y = mod-succ-ℕ n (add-ℕ (nat-Fin x) (nat-Fin y))

add-Fin' : {n : ℕ} → Fin n → Fin n → Fin n
add-Fin' x y = add-Fin y x

cong-add-Fin :
  {n : ℕ} (x y : Fin n) →
  cong-ℕ n (nat-Fin (add-Fin x y)) (add-ℕ (nat-Fin x) (nat-Fin y))
cong-add-Fin {succ-ℕ n} x y =
  is-remainder-div-mod-succ-ℕ n (add-ℕ (nat-Fin x) (nat-Fin y))

--------------------------------------------------------------------------------

-- We show that addition is associative --

associative-add-Fin :
  {n : ℕ} (x y z : Fin n) →
  Id (add-Fin (add-Fin x y) z) (add-Fin x (add-Fin y z))
associative-add-Fin {succ-ℕ n} x y z =
  eq-cong-ℕ n
    ( add-ℕ (nat-Fin (add-Fin x y)) (nat-Fin z))
    ( add-ℕ (nat-Fin x) (nat-Fin (add-Fin y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 = add-ℕ (nat-Fin (add-Fin x y)) (nat-Fin z)}
      { x2 = add-ℕ (add-ℕ (nat-Fin x) (nat-Fin y)) (nat-Fin z)}
      { x3 = add-ℕ (nat-Fin x) (add-ℕ (nat-Fin y) (nat-Fin z))}
      { x4 = add-ℕ (nat-Fin x) (nat-Fin (add-Fin y z))}
      ( is-congruence-add-ℕ
        ( succ-ℕ n)
        { x = nat-Fin (add-Fin x y)}
        { y = nat-Fin z}
        { x' = add-ℕ (nat-Fin x) (nat-Fin y)}
        { y' = nat-Fin z}
        ( cong-add-Fin x y)
        ( reflexive-cong-ℕ (succ-ℕ n) (nat-Fin z)))
      ( associative-add-ℕ (nat-Fin x) (nat-Fin y) (nat-Fin z))
      ( is-congruence-add-ℕ
        ( succ-ℕ n)
        { x = nat-Fin x}
        { y = add-ℕ (nat-Fin y) (nat-Fin z)}
        { x' = nat-Fin x}
        { y' = nat-Fin (add-Fin y z)}
        ( reflexive-cong-ℕ (succ-ℕ n) (nat-Fin x))
        ( symmetric-cong-ℕ
          ( succ-ℕ n)
          ( nat-Fin (add-Fin y z))
          ( add-ℕ (nat-Fin y) (nat-Fin z))
          ( cong-add-Fin y z))))

--------------------------------------------------------------------------------

-- addition is commutative --

commutative-add-Fin : {n : ℕ} (x y : Fin n) → Id (add-Fin x y) (add-Fin y x)
commutative-add-Fin {succ-ℕ n} x y =
  ap (mod-succ-ℕ n) (commutative-add-ℕ (nat-Fin x) (nat-Fin y))

--------------------------------------------------------------------------------

-- We prove the unit laws for add-Fin --

left-unit-law-add-Fin :
  {n : ℕ} (x : Fin (succ-ℕ n)) → Id (add-Fin zero-Fin x) x
left-unit-law-add-Fin {zero-ℕ} (inr star) = refl
left-unit-law-add-Fin {succ-ℕ n} x =
  ( ap (mod-succ-ℕ (succ-ℕ n))
       ( ( ap (add-ℕ' (nat-Fin x)) (zero-law-nat-Fin {n})) ∙
         ( left-unit-law-add-ℕ (nat-Fin x)))) ∙
  ( issec-nat-Fin (succ-ℕ n) x)

right-unit-law-add-Fin :
  {n : ℕ} (x : Fin (succ-ℕ n)) → Id (add-Fin x zero-Fin) x
right-unit-law-add-Fin x =
  ( commutative-add-Fin x zero-Fin) ∙
  ( left-unit-law-add-Fin x)

--------------------------------------------------------------------------------

-- We define the negative of x : Fin (succ-ℕ n) --

neg-Fin :
  {n : ℕ} (x : Fin (succ-ℕ n)) → Fin (succ-ℕ n)
neg-Fin {n} x =
  mod-succ-ℕ n (dist-ℕ (succ-ℕ n) (nat-Fin x))

left-inverse-law-neg-Fin :
  {n : ℕ} (x : Fin (succ-ℕ n)) → Id (add-Fin (neg-Fin x) x) zero-Fin
left-inverse-law-neg-Fin {n} x =
  ( eq-cong-ℕ n
    ( add-ℕ
      ( nat-Fin (mod-succ-ℕ n (dist-ℕ (succ-ℕ n) (nat-Fin x))))
      ( nat-Fin x))
    ( zero-ℕ)
    ( transitive-cong-ℕ
      ( succ-ℕ n)
      ( add-ℕ
        ( nat-Fin (mod-succ-ℕ n (dist-ℕ (succ-ℕ n) (nat-Fin x))))
        ( nat-Fin x))
      ( succ-ℕ n)
      ( zero-ℕ)
      {!!}
      ( n-cong-zero-ℕ (succ-ℕ n)))) ∙
  ( zero-law-mod-succ-ℕ n)

preserves-leq-succ-ℕ :
  (m n : ℕ) → leq-ℕ m n → leq-ℕ m (succ-ℕ n)
preserves-leq-succ-ℕ m n p = transitive-leq-ℕ m n (succ-ℕ n) p (succ-leq-ℕ n)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

{- We show that Eq-Fin is a proposition. -}

{-
path-Eq-Fin :
  {n : ℕ} {x y : Fin n} (e e' : Eq-Fin n x y) → Id e e'
path-Eq-Fin {succ-ℕ n} {inl x} {inl y} e e' = path-Eq-Fin {n} {x} {y} e e'
path-Eq-Fin {succ-ℕ n} {inr x} {inr y} star star = refl
-}

{-
is-prop-Eq-Fin :
  {n : ℕ} {x y : Fin n} → is-prop (Eq-Fin n x y)
is-prop-Eq-Fin {zero-ℕ} {()} {y}
is-prop-Eq-Fin {succ-ℕ n} {inl x} {inl x'} = is-prop-Eq-Fin {n} {x} {x'}
is-prop-Eq-Fin {succ-ℕ n} {inl x} {inr y'} = is-prop-empty
is-prop-Eq-Fin {succ-ℕ n} {inr y} {inl x'} = is-prop-empty
is-prop-Eq-Fin {succ-ℕ n} {inr y} {inr y'} = is-prop-unit
-}
--------------------------------------------------------------------------------

{- We conclude that is-decidable-Eq-Fin is a proposition. -}

{-
is-prop-is-decidable-Eq-Fin :
  {n : ℕ} {x y : Fin n} → is-prop (is-decidable (Eq-Fin n x y))
is-prop-is-decidable-Eq-Fin {n} {x} {y} =
  is-prop-is-decidable (is-prop-Eq-Fin {n} {x} {y})

path-is-decidable-Eq-Fin :
  {n : ℕ} {x y : Fin n} (d d' : is-decidable (Eq-Fin n x y)) → Id d d'
path-is-decidable-Eq-Fin {n} {x} {y} =
  is-prop'-is-prop (is-prop-is-decidable-Eq-Fin {n} {x} {y})

refl-is-decidable-Eq-Fin :
  (n : ℕ) (x : Fin n) →
  Id (is-decidable-Eq-Fin n x x) (inl (refl-Eq-Fin x))
refl-is-decidable-Eq-Fin zero-ℕ ()
refl-is-decidable-Eq-Fin (succ-ℕ n) (inl x) = refl-is-decidable-Eq-Fin n x
refl-is-decidable-Eq-Fin (succ-ℕ n) (inr x) = refl
-}

{-
-- We define multiplication with remainder

mul-with-remainder-succ-ℕ :
  (n : ℕ) → ℕ × (Fin (succ-ℕ n)) → ℕ
mul-with-remainder-succ-ℕ n (pair k d) = add-ℕ (mul-ℕ k (succ-ℕ n)) (nat-Fin d)

-- We define division with remainder

leq-nat-Fin-mod-succ-ℕ :
  (n x : ℕ) → leq-ℕ (nat-Fin (mod-succ-ℕ n x)) x
leq-nat-Fin-mod-succ-ℕ zero-ℕ x = star
leq-nat-Fin-mod-succ-ℕ (succ-ℕ n) zero-ℕ =
  tr
   ( λ t → leq-ℕ t zero-ℕ)
   ( inv (zero-law-nat-Fin {n}))
   ( reflexive-leq-ℕ zero-ℕ)
leq-nat-Fin-mod-succ-ℕ (succ-ℕ n) (succ-ℕ x) with
  is-decidable-Eq-Fin (succ-ℕ (succ-ℕ n)) neg-one-Fin (mod-succ-ℕ (succ-ℕ n) x)
leq-nat-Fin-mod-succ-ℕ (succ-ℕ n) (succ-ℕ x) | inl p =
  concatenate-eq-leq-ℕ
    { zero-ℕ}
    { nat-Fin (succ-Fin (mod-succ-ℕ (succ-ℕ n) x))}
    ( succ-ℕ x)
    ( ( ap
        ( nat-Fin ∘ succ-Fin)
        { x = mod-succ-ℕ (succ-ℕ n) x}
        { y = neg-one-Fin}
        ( inv (eq-Eq-Fin p))) ∙
      ( zero-law-nat-Fin {succ-ℕ n}))
    ( reflexive-leq-ℕ zero-ℕ)
leq-nat-Fin-mod-succ-ℕ (succ-ℕ n) (succ-ℕ x) | inr f = {!successor-law-nat-Fin!}

division-with-remainder-succ-ℕ :
  (n x : ℕ) → Σ (ℕ × (Fin (succ-ℕ n))) (λ y → Id (mul-with-remainder-succ-ℕ n y) x)
division-with-remainder-succ-ℕ n x with is-remainder-div-mod-succ-ℕ n x
division-with-remainder-succ-ℕ n x | pair k α =
  pair
    ( pair k  (mod-succ-ℕ n x))
    ( rewrite-left-dist-add-ℕ
      ( mul-ℕ k (succ-ℕ n))
      ( nat-Fin (mod-succ-ℕ n x))
      ( x)
      {! leq-nat-Fin-mod-succ-ℕ!}
      ( α))
-}
