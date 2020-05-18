{-# OPTIONS --without-K --exact-split #-}

module rational-numbers where

import 16-number-theory
open 16-number-theory public

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

{- We show that multiplication by a non-zero integer is an embedding. -}

neq-zero-mul-ℤ :
  (x y : ℤ) → ¬ (Id zero-ℤ x) → ¬ (Id zero-ℤ y) → ¬ (Id zero-ℤ (mul-ℤ x y))
neq-zero-mul-ℤ x y Hx Hy = {!!}

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

--------------------------------------------------------------------------------

{- We introduce the type of non-zero integers. -}

ℤ\0 : UU lzero
ℤ\0 = Σ ℤ (λ k → ¬ (Id zero-ℤ k))

int-ℤ\0 : ℤ\0 → ℤ
int-ℤ\0 = pr1

{- We first show that multiplication by a non-zero integer is an injective
   function. -}

mul-ℤ-ℤ\0 : ℤ → ℤ\0 → ℤ
mul-ℤ-ℤ\0 x y = mul-ℤ x (int-ℤ\0 y)

mul-ℤ\0 : ℤ\0 → ℤ\0 → ℤ\0
mul-ℤ\0 (pair x Hx) (pair y Hy) = pair (mul-ℤ x y) (neq-zero-mul-ℤ x y Hx Hy)

postulate is-emb-mul-ℤ-ℤ\0 : (y : ℤ\0) → is-emb (λ x → mul-ℤ-ℤ\0 x y)

is-injective-mul-ℤ-ℤ\0 :
  (y : ℤ\0) (x1 x2 : ℤ) → Id (mul-ℤ-ℤ\0 x1 y) (mul-ℤ-ℤ\0 x2 y) → Id x1 x2
is-injective-mul-ℤ-ℤ\0 y x1 x2 = inv-is-equiv (is-emb-mul-ℤ-ℤ\0 y x1 x2)

--------------------------------------------------------------------------------

{- We introduce the prerational numbers. -}

ℚ' : UU lzero
ℚ' = ℤ × ℤ\0

--------------------------------------------------------------------------------

{- We introduce the equivalence relation on the prerational numbers that will
   define the rational numbers. -}

equiv-ℚ' : ℚ' → ℚ' → UU lzero
equiv-ℚ' (pair x1 x2) (pair y1 y2) =
  Id (mul-ℤ-ℤ\0 x1 y2) (mul-ℤ-ℤ\0 y1 x2)

refl-equiv-ℚ' :
  (x : ℚ') → equiv-ℚ' x x
refl-equiv-ℚ' (pair x1 x2) = refl

symmetric-equiv-ℚ' :
  (x y : ℚ') → equiv-ℚ' x y → equiv-ℚ' y x
symmetric-equiv-ℚ' (pair x1 x2) (pair y1 y2) = inv

transitive-equiv-ℚ' :
  (x y z : ℚ') →
  equiv-ℚ' x y → equiv-ℚ' y z → equiv-ℚ' x z
transitive-equiv-ℚ' (pair x1 x2) (pair y1 y2) (pair z1 z2) p q =
  is-injective-mul-ℤ-ℤ\0 y2
    ( mul-ℤ-ℤ\0 x1 z2)
    ( mul-ℤ-ℤ\0 z1 x2)
    ( ( associative-mul-ℤ x1 (int-ℤ\0 z2) (int-ℤ\0 y2)) ∙
      ( ( ap ( mul-ℤ x1)
             ( commutative-mul-ℤ (int-ℤ\0 z2) (int-ℤ\0 y2))) ∙
        ( ( inv (associative-mul-ℤ x1 (int-ℤ\0 y2) (int-ℤ\0 z2))) ∙
          ( ( ap ( λ t → mul-ℤ t (int-ℤ\0 z2))
                 ( p ∙ (commutative-mul-ℤ y1 (int-ℤ\0 x2)))) ∙
            ( ( associative-mul-ℤ (int-ℤ\0 x2) y1 (int-ℤ\0 z2)) ∙
              ( ( ap (mul-ℤ (int-ℤ\0 x2)) q) ∙
                ( ( inv (associative-mul-ℤ (int-ℤ\0 x2) z1 (int-ℤ\0 y2))) ∙
                  ( ap ( λ t → mul-ℤ-ℤ\0 t y2)
                       ( commutative-mul-ℤ (int-ℤ\0 x2) z1)))))))))

--------------------------------------------------------------------------------

{- We define addition on the prerational numbers. -}

add-ℚ' : ℚ' → ℚ' → ℚ'
add-ℚ' (pair x1 x2) (pair y1 y2) =
  pair (add-ℤ (mul-ℤ-ℤ\0 x1 y2) (mul-ℤ-ℤ\0 y1 x2)) (mul-ℤ\0 x2 y2)

ap-add-ℤ :
  {a b a' b' : ℤ} →
  Id a a' → Id b b' → Id (add-ℤ a b) (add-ℤ a' b')
ap-add-ℤ refl refl = refl

equiv-add-ℚ' :
  (x y x' y' : ℚ') → equiv-ℚ' x x' → equiv-ℚ' y y' →
  equiv-ℚ' (add-ℚ' x y) (add-ℚ' x' y')
equiv-add-ℚ'
  ( pair x1 (pair x2 Hx))
  ( pair y1 (pair y2 Hy))
  ( pair x1' (pair x2' Hx'))
  ( pair y1' (pair y2' Hy')) e f =
  ( right-distributive-mul-add-ℤ
    ( mul-ℤ x1 y2)
    ( mul-ℤ y1 x2)
    ( mul-ℤ x2' y2')) ∙
  ( ( ap-add-ℤ
      ( ( interchange-2-3-mul-ℤ {x1}) ∙
        ( ( ap (λ t → mul-ℤ t (mul-ℤ y2 y2')) e) ∙
          ( move-four-mul-ℤ {x1'})))
      ( ( move-five-mul-ℤ {y1}) ∙
        ( ( ap (mul-ℤ (mul-ℤ x2 x2')) f) ∙
          ( interchange-1-3-mul-ℤ {x2} {x2'} {y1'})))) ∙
    ( inv
      ( right-distributive-mul-add-ℤ
        ( mul-ℤ x1' y2')
        ( mul-ℤ y1' x2')
        ( mul-ℤ x2 y2))))

--------------------------------------------------------------------------------

{- We define multiplication on the prerational numbers. -}

mul-ℚ' : ℚ' → ℚ' → ℚ'
mul-ℚ' (pair x1 x2) (pair y1 y2) = pair (mul-ℤ x1 y1) (mul-ℤ\0 x2 y2)

ap-mul-ℤ :
  {a b a' b' : ℤ} →
  Id a a' → Id b b' → Id (mul-ℤ a b) (mul-ℤ a' b')
ap-mul-ℤ refl refl = refl

equiv-mul-ℚ' :
  (x y x' y' : ℚ') → equiv-ℚ' x x' → equiv-ℚ' y y' →
  equiv-ℚ' (mul-ℚ' x y) (mul-ℚ' x' y')
equiv-mul-ℚ'
  ( pair x1 (pair x2 Hx))
  ( pair y1 (pair y2 Hy))
  ( pair x1' (pair x2' Hx'))
  ( pair y1' (pair y2' Hy')) e f =
  ( interchange-2-3-mul-ℤ {x1} {y1} {x2'}) ∙
  ( ( ap-mul-ℤ e f) ∙
    ( interchange-2-3-mul-ℤ {x1'}))
