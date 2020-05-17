{-# OPTIONS --without-K --exact-split --safe #-}

module lists where

import 10-truncation-levels
open 10-truncation-levels public

unit-list :
  {l1 : Level} {A : UU l1} → A → list A
unit-list a = cons a nil

functor-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  list A → list B
functor-list f nil = nil
functor-list f (cons a x) = cons (f a) (functor-list f x)

identity-law-functor-list :
  {l1 : Level} {A : UU l1} →
  functor-list (id {A = A}) ~ id
identity-law-functor-list nil = refl
identity-law-functor-list (cons a x) =
  ap (cons a) (identity-law-functor-list x)

composition-law-functor-list :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (f : A → B) (g : B → C) →
  functor-list (g ∘ f) ~ (functor-list g ∘ functor-list f)
composition-law-functor-list f g nil = refl
composition-law-functor-list f g (cons a x) =
  ap (cons (g (f a))) (composition-law-functor-list f g x)

assoc-concat-list :
  {l1 : Level} {A : UU l1} (x y z : list A) →
  Id (concat-list (concat-list x y) z) (concat-list x (concat-list y z))
assoc-concat-list nil y z = refl
assoc-concat-list (cons a x) y z = ap (cons a) (assoc-concat-list x y z)

left-unit-law-concat :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list nil x) x
left-unit-law-concat x = refl

right-unit-law-concat :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list x nil) x
right-unit-law-concat nil = refl
right-unit-law-concat (cons a x) = ap (cons a) (right-unit-law-concat x)

length-nil :
  {l1 : Level} {A : UU l1} →
  Id (length-list {A = A} nil) zero-ℕ
length-nil = refl

length-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id (length-list (concat-list x y)) (add-ℕ (length-list x) (length-list y))
length-concat-list nil y = inv (left-unit-law-add-ℕ (length-list y))
length-concat-list (cons a x) y =
  ( ap succ-ℕ (length-concat-list x y)) ∙
  ( inv (left-successor-law-add-ℕ (length-list x) (length-list y)))



