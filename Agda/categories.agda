{-# OPTIONS --without-K --exact-split #-}

module categories where

import 21-image
open 21-image public

{- We introduce precategories and categories. -}

Precat :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Precat l1 l2 =
  Σ (UU l1) (λ Obj → Σ (Obj → Obj → hSet l2) (λ Hom →
    Σ ({X : Obj} → type-Set (Hom X X)) (λ i →
      Σ ( {X Y Z : Obj} →
          type-Set (Hom Y Z) → type-Set (Hom X Y) → type-Set (Hom X Z))
          ( λ comp →
            ( {X Y Z W : Obj} (f : type-Set (Hom X Y)) (g : type-Set (Hom Y Z))
              (h : type-Set (Hom Z W)) →
              Id (comp (comp h g) f) (comp h (comp g f))) ×
            ( ( {X Y : Obj} (f : type-Set (Hom X Y)) → Id (comp i f) f) ×
              ( {X Y : Obj} (f : type-Set (Hom X Y)) → Id (comp f i) f))))))

obj-Precat :
  {l1 l2 : Level} (C : Precat l1 l2) → UU l1
obj-Precat C = pr1 C

hom-Precat :
  {l1 l2 : Level} (C : Precat l1 l2) → obj-Precat C → obj-Precat C → hSet l2
hom-Precat C = pr1 (pr2 C)

id-Precat :
  {l1 l2 : Level} (C : Precat l1 l2)
  {X : obj-Precat C} → type-Set (hom-Precat C X X)
id-Precat C = pr1 (pr2 (pr2 C))

comp-Precat :
  {l1 l2 : Level} (C : Precat l1 l2)
  {X Y Z : obj-Precat C} → type-Set (hom-Precat C Y Z) →
  type-Set (hom-Precat C X Y) → type-Set (hom-Precat C X Z)
comp-Precat C = pr1 (pr2 (pr2 (pr2 C)))

assoc-Precat :
  {l1 l2 : Level} (C : Precat l1 l2)
  {X Y Z W : obj-Precat C} (f : type-Set (hom-Precat C X Y)) →
  ( g : type-Set (hom-Precat C Y Z)) ( h : type-Set (hom-Precat C Z W)) →
  Id (comp-Precat C (comp-Precat C h g) f) (comp-Precat C h (comp-Precat C g f))
assoc-Precat C = pr1 (pr2 (pr2 (pr2 (pr2 C))))

left-unit-Precat :
  {l1 l2 : Level} (C : Precat l1 l2)
  {X Y : obj-Precat C} (f : type-Set (hom-Precat C X Y)) →
  Id (comp-Precat C (id-Precat C) f) f
left-unit-Precat C = pr1 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))

right-unit-Precat :
  {l1 l2 : Level} (C : Precat l1 l2)
  {X Y : obj-Precat C} (f : type-Set (hom-Precat C X Y)) →
  Id (comp-Precat C f (id-Precat C)) f
right-unit-Precat C = pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))

{- We define the notion of isomorphism in a precategory. -}

is-iso-Precat :
  {l1 l2 : Level} (C : Precat l1 l2) {X Y : obj-Precat C} →
  (type-Set (hom-Precat C X Y)) → UU l2
is-iso-Precat C {X} {Y} f =
  Σ ( type-Set (hom-Precat C Y X)) (λ g →
    Id (comp-Precat C f g) (id-Precat C) ×
    Id (comp-Precat C g f) (id-Precat C))

iso-Precat :
  {l1 l2 : Level} (C : Precat l1 l2) →
  obj-Precat C → obj-Precat C → hSet l2
iso-Precat C X Y =
  {!!}

