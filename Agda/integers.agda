{-# OPTIONS --without-K --exact-split #-}

module integers where

import rings-with-properties
open rings-with-properties public

--------------------------------------------------------------------------------

{- We exhibit ℤ as an abelian group, and as a ring. -}

add-ℤ-Semi-Group : Semi-Group lzero
add-ℤ-Semi-Group = pair ℤ-Set (pair add-ℤ associative-add-ℤ)

is-unital-add-ℤ-Semi-Group : is-unital add-ℤ-Semi-Group
is-unital-add-ℤ-Semi-Group = pair zero-ℤ (pair left-unit-law-add-ℤ right-unit-law-add-ℤ)

add-ℤ-Monoid : Monoid lzero
add-ℤ-Monoid = pair add-ℤ-Semi-Group is-unital-add-ℤ-Semi-Group

has-inverses-add-ℤ-Monoid : is-group' add-ℤ-Semi-Group is-unital-add-ℤ-Semi-Group
has-inverses-add-ℤ-Monoid = pair neg-ℤ (pair left-inverse-law-add-ℤ right-inverse-law-add-ℤ)

is-group-add-ℤ-Semi-Group : is-group add-ℤ-Semi-Group
is-group-add-ℤ-Semi-Group = pair is-unital-add-ℤ-Semi-Group has-inverses-add-ℤ-Monoid

ℤ-Group : Group lzero
ℤ-Group = pair add-ℤ-Semi-Group is-group-add-ℤ-Semi-Group

ℤ-Ab : Ab lzero
ℤ-Ab = pair ℤ-Group commutative-add-ℤ

has-mul-ℤ-Ab : has-mul-Ab ℤ-Ab
has-mul-ℤ-Ab =
  pair
    ( pair mul-ℤ associative-mul-ℤ)
    ( pair
      ( pair one-ℤ (pair left-unit-law-mul-ℤ right-unit-law-mul-ℤ))
      ( pair left-distributive-mul-add-ℤ right-distributive-mul-add-ℤ))

ℤ-Ring : Ring lzero
ℤ-Ring = pair ℤ-Ab has-mul-ℤ-Ab

ℤ-Comm-Ring : Comm-Ring lzero
ℤ-Comm-Ring = pair ℤ-Ring commutative-mul-ℤ

mul-ℤ-Semi-Group : Semi-Group lzero
mul-ℤ-Semi-Group = pair ℤ-Set (pair mul-ℤ associative-mul-ℤ)

mul-ℤ-Monoid : Monoid lzero
mul-ℤ-Monoid =
  pair
    ( mul-ℤ-Semi-Group)
    ( pair one-ℤ (pair left-unit-law-mul-ℤ right-unit-law-mul-ℤ))

--------------------------------------------------------------------------------

{- We characterize the identity type of ℤ. -}

Eq-ℤ : ℤ → ℤ → UU lzero
Eq-ℤ (inl x) (inl y) = Eq-ℕ x y
Eq-ℤ (inl x) (inr y) = empty
Eq-ℤ (inr x) (inl x₁) = empty
Eq-ℤ (inr (inl x)) (inr (inl y)) = unit
Eq-ℤ (inr (inl x)) (inr (inr y)) = empty
Eq-ℤ (inr (inr x)) (inr (inl y)) = empty
Eq-ℤ (inr (inr x)) (inr (inr y)) = Eq-ℕ x y

is-prop-Eq-ℤ :
  (x y : ℤ) → is-prop (Eq-ℤ x y)
is-prop-Eq-ℤ (inl x) (inl y) = is-prop-Eq-ℕ x y
is-prop-Eq-ℤ (inl x) (inr y) = is-prop-empty
is-prop-Eq-ℤ (inr x) (inl x₁) = is-prop-empty
is-prop-Eq-ℤ (inr (inl x)) (inr (inl y)) = is-prop-unit
is-prop-Eq-ℤ (inr (inl x)) (inr (inr y)) = is-prop-empty
is-prop-Eq-ℤ (inr (inr x)) (inr (inl y)) = is-prop-empty
is-prop-Eq-ℤ (inr (inr x)) (inr (inr y)) = is-prop-Eq-ℕ x y

refl-Eq-ℤ :
  (x : ℤ) → Eq-ℤ x x
refl-Eq-ℤ (inl x) = refl-Eq-ℕ x
refl-Eq-ℤ (inr (inl x)) = star
refl-Eq-ℤ (inr (inr x)) = refl-Eq-ℕ x

Eq-ℤ-eq :
  {x y : ℤ} → Id x y → Eq-ℤ x y
Eq-ℤ-eq {x} {.x} refl = refl-Eq-ℤ x

contraction-total-Eq-ℤ :
  (x : ℤ) (y : Σ ℤ (Eq-ℤ x)) → Id (pair x (refl-Eq-ℤ x)) y
contraction-total-Eq-ℤ (inl x) (pair (inl y) e) =
  eq-pair
    ( ap inl (eq-Eq-ℕ x y e))
    ( is-prop'-is-prop
      ( is-prop-Eq-ℕ x y)
      ( tr
        ( Eq-ℤ (inl x))
        ( ap inl (eq-Eq-ℕ x y e))
        ( refl-Eq-ℤ (inl x)))
      ( e))
contraction-total-Eq-ℤ (inr (inl star)) (pair (inr (inl star)) e) =
  eq-pair refl (is-prop'-is-prop is-prop-unit (refl-Eq-ℤ zero-ℤ) e)
contraction-total-Eq-ℤ (inr (inr x)) (pair (inr (inr y)) e) =
  eq-pair
    ( ap (inr ∘ inr) (eq-Eq-ℕ x y e))
    ( is-prop'-is-prop
      ( is-prop-Eq-ℕ x y)
      ( tr
        ( Eq-ℤ (inr (inr x)))
        ( ap (inr ∘ inr) (eq-Eq-ℕ x y e))
        ( refl-Eq-ℤ (inr (inr x))))
      ( e))

is-contr-total-Eq-ℤ :
  (x : ℤ) → is-contr (Σ ℤ (Eq-ℤ x))
is-contr-total-Eq-ℤ x =
  pair (pair x (refl-Eq-ℤ x)) (contraction-total-Eq-ℤ x)

is-equiv-Eq-ℤ-eq :
  (x y : ℤ) → is-equiv (Eq-ℤ-eq {x} {y})
is-equiv-Eq-ℤ-eq x =
  fundamental-theorem-id x
    ( refl-Eq-ℤ x)
    ( is-contr-total-Eq-ℤ x)
    ( λ y → Eq-ℤ-eq {x} {y})

eq-Eq-ℤ :
  {x y : ℤ} → Eq-ℤ x y → Id x y
eq-Eq-ℤ {x} {y} = inv-is-equiv (is-equiv-Eq-ℤ-eq x y)

--------------------------------------------------------------------------------

{- We prove some basic arithmetic properties of the integers. -}

add-ℤ' : ℤ → ℤ → ℤ
add-ℤ' x y = add-ℤ y x

--------------------------------------------------------------------------------

{- We show that addition from the left and from the right are both equivalences.
   We conclude that they are both injective maps. -}

is-equiv-add-ℤ :
  (x : ℤ) → is-equiv (add-ℤ x)
is-equiv-add-ℤ x =
  is-equiv-has-inverse
    ( add-ℤ (neg-ℤ x))
    ( λ y →
      ( inv (associative-add-ℤ x (neg-ℤ x) y)) ∙
      ( ( ap (add-ℤ' y) (right-inverse-law-add-ℤ x)) ∙
        ( left-unit-law-add-ℤ y)))
    ( λ y →
       ( inv (associative-add-ℤ (neg-ℤ x) x y)) ∙
       ( ( ap (add-ℤ' y) (left-inverse-law-add-ℤ x)) ∙
         ( left-unit-law-add-ℤ y)))

is-equiv-add-ℤ' :
  (y : ℤ) → is-equiv (add-ℤ' y)
is-equiv-add-ℤ' y =
  is-equiv-has-inverse
    ( λ x → add-ℤ x (neg-ℤ y))
    ( λ x →
      ( associative-add-ℤ x (neg-ℤ y) y) ∙
      ( ( ap (add-ℤ x) (left-inverse-law-add-ℤ y)) ∙
        ( right-unit-law-add-ℤ x)))
    ( λ x →
       ( associative-add-ℤ x y (neg-ℤ y)) ∙
       ( ( ap (add-ℤ x) (right-inverse-law-add-ℤ y)) ∙
         ( right-unit-law-add-ℤ x)))

is-emb-add-ℤ :
  (x : ℤ) → is-emb (add-ℤ x)
is-emb-add-ℤ x =
  is-emb-is-equiv (add-ℤ x) (is-equiv-add-ℤ x)

is-injective-add-ℤ :
  (x y z : ℤ) → Id (add-ℤ x y) (add-ℤ x z) → Id y z
is-injective-add-ℤ x y z = inv-is-equiv (is-emb-add-ℤ x y z)

is-emb-add-ℤ' :
  (y : ℤ) → is-emb (add-ℤ' y)
is-emb-add-ℤ' y = is-emb-is-equiv (add-ℤ' y) (is-equiv-add-ℤ' y)

is-injective-add-ℤ' :
  (y x w : ℤ) → Id (add-ℤ x y) (add-ℤ w y) → Id x w
is-injective-add-ℤ' y x w = inv-is-equiv (is-emb-add-ℤ' y x w)

--------------------------------------------------------------------------------

{- We show that multiplication by neg-one-ℤ is an equivalence. -}

is-equiv-neg-ℤ : is-equiv neg-ℤ
is-equiv-neg-ℤ =
  is-equiv-has-inverse neg-ℤ neg-neg-ℤ neg-neg-ℤ

is-emb-neg-ℤ : is-emb neg-ℤ
is-emb-neg-ℤ = is-emb-is-equiv neg-ℤ is-equiv-neg-ℤ

is-injective-neg-ℤ :
  (x y : ℤ) → Id (neg-ℤ x) (neg-ℤ y) → Id x y
is-injective-neg-ℤ x y = inv-is-equiv (is-emb-neg-ℤ x y)

--------------------------------------------------------------------------------

{- We show that if x = mul-ℤ x y for some non-zero integer x, then y = 1. -}

--------------------------------------------------------------------------------

{- We show that multiplication by a non-zero integer is an embedding. -}

{-
is-injective-mul-ℤ :
  (x y z : ℤ) → ¬ (Id zero-ℤ x) → Id (mul-ℤ x y) (mul-ℤ x z) → Id y z
is-injective-mul-ℤ (inl zero-ℕ) y z p q = is-injective-neg-ℤ y z q
is-injective-mul-ℤ (inl (succ-ℕ x)) y z p q = {!!}
is-injective-mul-ℤ (inr x) y z p q = {!x!}

neq-zero-mul-ℤ :
  (x y : ℤ) → ¬ (Id zero-ℤ x) → ¬ (Id zero-ℤ y) → ¬ (Id zero-ℤ (mul-ℤ x y))
neq-zero-mul-ℤ x y Hx Hy = {!!}
-}

--------------------------------------------------------------------------------

{- We prove some interchange laws and moves on iterated multiplications. -}

interchange-2-3-mul-ℤ :
  {a b c d : ℤ} →
  Id (mul-ℤ (mul-ℤ a b) (mul-ℤ c d)) (mul-ℤ (mul-ℤ a c) (mul-ℤ b d))
interchange-2-3-mul-ℤ {a} {b} {c} {d} =
  ( associative-mul-ℤ a b (mul-ℤ c d)) ∙
  ( ( ap ( mul-ℤ a)
         ( ( inv (associative-mul-ℤ b c d)) ∙
           ( ( ap (λ t → mul-ℤ t d) (commutative-mul-ℤ b c)) ∙
             ( associative-mul-ℤ c b d)))) ∙
    ( inv (associative-mul-ℤ a c (mul-ℤ b d))))

interchange-1-3-mul-ℤ :
  {a b c d : ℤ} →
  Id (mul-ℤ (mul-ℤ a b) (mul-ℤ c d)) (mul-ℤ (mul-ℤ c b) (mul-ℤ a d))
interchange-1-3-mul-ℤ {a} {b} {c} {d} =
  ( ap (λ t → mul-ℤ t (mul-ℤ c d)) (commutative-mul-ℤ a b)) ∙
  ( ( interchange-2-3-mul-ℤ {b}) ∙
    ( ap (λ t → mul-ℤ t (mul-ℤ a d)) (commutative-mul-ℤ b c)))

move-four-mul-ℤ :
  {a b c d : ℤ} →
  Id (mul-ℤ (mul-ℤ a b) (mul-ℤ c d)) (mul-ℤ (mul-ℤ a d) (mul-ℤ b c))
move-four-mul-ℤ {a} {b} {c} {d} =
   ( associative-mul-ℤ a b (mul-ℤ c d)) ∙
   ( ( ap ( mul-ℤ a)
          ( ( inv (associative-mul-ℤ b c d)) ∙
            ( commutative-mul-ℤ (mul-ℤ b c) d))) ∙
     ( inv (associative-mul-ℤ a d (mul-ℤ b c))))

move-five-mul-ℤ :
  {a b c d : ℤ} →
  Id (mul-ℤ (mul-ℤ a b) (mul-ℤ c d)) (mul-ℤ (mul-ℤ b c) (mul-ℤ a d))
move-five-mul-ℤ {a} {b} {c} {d} =
  ( interchange-2-3-mul-ℤ {a} {b} {c} {d}) ∙
  ( ( ap (λ t → mul-ℤ t (mul-ℤ b d)) (commutative-mul-ℤ a c)) ∙
    ( ( interchange-2-3-mul-ℤ {c}) ∙
      ( ap (λ t → mul-ℤ t (mul-ℤ a d)) (commutative-mul-ℤ c b))))
