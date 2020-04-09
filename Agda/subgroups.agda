{-# OPTIONS --without-K --exact-split #-}

module subgroups where

import 13-groups
open 13-groups public

{- Subsets of groups -}

subset-Group :
  (l : Level) {l1 : Level} (G : Group l1) → UU ((lsuc l) ⊔ l1)
subset-Group l G = type-Group G → UU-Prop l

is-set-subset-Group :
  (l : Level) {l1 : Level} (G : Group l1) → is-set (subset-Group l G)
is-set-subset-Group l G =
  is-set-function-type (is-set-UU-Prop l)

{- Defining subgroups -}

contains-unit-subset-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) → UU l2
contains-unit-subset-Group G P = type-Prop (P (unit-Group G))

is-prop-contains-unit-subset-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) →
  is-prop (contains-unit-subset-Group G P)
is-prop-contains-unit-subset-Group G P = is-prop-type-Prop (P (unit-Group G))

closed-under-mul-subset-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) → UU (l1 ⊔ l2)
closed-under-mul-subset-Group G P =
  (x y : type-Group G) →
  type-Prop (P x) → type-Prop (P y) → type-Prop (P (mul-Group G x y))

is-prop-closed-under-mul-subset-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) →
  is-prop (closed-under-mul-subset-Group G P)
is-prop-closed-under-mul-subset-Group G P =
  is-prop-Π (λ x →
    is-prop-Π (λ y →
      is-prop-function-type
        ( is-prop-function-type
          ( is-prop-type-Prop (P (mul-Group G x y))))))

closed-under-inv-subset-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) → UU (l1 ⊔ l2)
closed-under-inv-subset-Group G P =
  (x : type-Group G) → type-Prop (P x) → type-Prop (P (inv-Group G x))

is-prop-closed-under-inv-subset-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) →
  is-prop (closed-under-inv-subset-Group G P)
is-prop-closed-under-inv-subset-Group G P =
  is-prop-Π
    ( λ x → is-prop-function-type (is-prop-type-Prop (P (inv-Group G x))))

is-subgroup-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) → UU (l1 ⊔ l2)
is-subgroup-Group G P =
  ( contains-unit-subset-Group G P) ×
  ( ( closed-under-mul-subset-Group G P) ×
    ( closed-under-inv-subset-Group G P))

is-prop-is-subgroup-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) →
  is-prop (is-subgroup-Group G P)
is-prop-is-subgroup-Group G P =
  is-prop-prod
    ( is-prop-contains-unit-subset-Group G P)
    ( is-prop-prod
      ( is-prop-closed-under-mul-subset-Group G P)
      ( is-prop-closed-under-inv-subset-Group G P))

{- Introducing the type of all subgroups of a group G -}

Subgroup :
  (l : Level) {l1 : Level} (G : Group l1) → UU ((lsuc l) ⊔ l1)
Subgroup l G = Σ (type-Group G → UU-Prop l) (is-subgroup-Group G)

subset-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  ( Subgroup l2 G) → ( subset-Group l2 G)
subset-Subgroup G = pr1

is-emb-subset-Subgroup :
  {l1 l2 : Level} (G : Group l1) → is-emb (subset-Subgroup {l2 = l2} G)
is-emb-subset-Subgroup G = is-emb-pr1-is-subtype (is-prop-is-subgroup-Group G)

type-subset-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  (type-Group G → UU l2)
type-subset-Subgroup G P x = type-Prop (subset-Subgroup G P x)

is-prop-type-subset-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  (x : type-Group G) → is-prop (type-subset-Subgroup G P x)
is-prop-type-subset-Subgroup G P x =
  is-prop-type-Prop (subset-Subgroup G P x)

is-subgroup-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  is-subgroup-Group G (subset-Subgroup G P)
is-subgroup-Subgroup G = pr2

contains-unit-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  contains-unit-subset-Group G (subset-Subgroup G P)
contains-unit-Subgroup G P = pr1 (is-subgroup-Subgroup G P)

closed-under-mul-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  closed-under-mul-subset-Group G (subset-Subgroup G P)
closed-under-mul-Subgroup G P = pr1 (pr2 (is-subgroup-Subgroup G P))

closed-under-inv-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  closed-under-inv-subset-Group G (subset-Subgroup G P)
closed-under-inv-Subgroup G P = pr2 (pr2 (is-subgroup-Subgroup G P))

{- Given a subgroup, we construct a group -}

type-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) → UU (l1 ⊔ l2)
type-group-Subgroup G P =
  Σ (type-Group G) (type-subset-Subgroup G P)

incl-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  type-group-Subgroup G P → type-Group G
incl-group-Subgroup G P = pr1

is-emb-incl-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  is-emb (incl-group-Subgroup G P)
is-emb-incl-group-Subgroup G P =
  is-emb-pr1-is-subtype (is-prop-type-subset-Subgroup G P)

eq-subgroup-eq-group :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  {x y : type-group-Subgroup G P} →
  Id (incl-group-Subgroup G P x) (incl-group-Subgroup G P y) → Id x y
eq-subgroup-eq-group G P {x} {y} =
  inv-is-equiv (is-emb-incl-group-Subgroup G P x y)

set-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) → Subgroup l2 G → UU-Set (l1 ⊔ l2)
set-group-Subgroup G P =
  pair ( type-group-Subgroup G P)
       ( λ x y →
         is-prop-is-equiv
           ( Id (pr1 x) (pr1 y))
           ( ap (incl-group-Subgroup G P))
           ( is-emb-incl-group-Subgroup G P x y)
           ( is-set-type-Group G (pr1 x) (pr1 y)))

unit-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) → type-group-Subgroup G P
unit-group-Subgroup G P =
  pair ( unit-Group G)
       ( contains-unit-Subgroup G P)

mul-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  ( x y : type-group-Subgroup G P) → type-group-Subgroup G P
mul-group-Subgroup G P x y =
  pair ( mul-Group G (pr1 x) (pr1 y))
       ( closed-under-mul-Subgroup G P (pr1 x) (pr1 y) (pr2 x) (pr2 y))

inv-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  type-group-Subgroup G P → type-group-Subgroup G P
inv-group-Subgroup G P x =
  pair (inv-Group G (pr1 x)) (closed-under-inv-Subgroup G P (pr1 x) (pr2 x))

is-associative-mul-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  ( x y z : type-group-Subgroup G P) →
  Id (mul-group-Subgroup G P (mul-group-Subgroup G P x y) z)
     (mul-group-Subgroup G P x (mul-group-Subgroup G P y z))
is-associative-mul-group-Subgroup G P x y z =
  eq-subgroup-eq-group G P (is-associative-mul-Group G (pr1 x) (pr1 y) (pr1 z))

left-unit-law-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  ( x : type-group-Subgroup G P) →
  Id (mul-group-Subgroup G P (unit-group-Subgroup G P) x) x
left-unit-law-group-Subgroup G P x =
  eq-subgroup-eq-group G P (left-unit-law-Group G (pr1 x))

right-unit-law-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  ( x : type-group-Subgroup G P) →
  Id (mul-group-Subgroup G P x (unit-group-Subgroup G P)) x
right-unit-law-group-Subgroup G P x =
  eq-subgroup-eq-group G P (right-unit-law-Group G (pr1 x))

left-inverse-law-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  ( x : type-group-Subgroup G P) →
  Id ( mul-group-Subgroup G P (inv-group-Subgroup G P x) x)
     ( unit-group-Subgroup G P)
left-inverse-law-group-Subgroup G P x =
  eq-subgroup-eq-group G P (left-inverse-law-Group G (pr1 x))

right-inverse-law-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  ( x : type-group-Subgroup G P) →
  Id ( mul-group-Subgroup G P x (inv-group-Subgroup G P x))
     ( unit-group-Subgroup G P)
right-inverse-law-group-Subgroup G P x =
  eq-subgroup-eq-group G P (right-inverse-law-Group G (pr1 x))

group-Subgroup :
  {l1 l2 : Level} (G : Group l1) → Subgroup l2 G → Group (l1 ⊔ l2)
group-Subgroup G P =
  pair
    ( pair
      ( set-group-Subgroup G P)
      ( pair
        ( mul-group-Subgroup G P)
        ( is-associative-mul-group-Subgroup G P)))
    ( pair
      ( pair
        ( unit-group-Subgroup G P)
        ( pair
          ( left-unit-law-group-Subgroup G P)
          ( right-unit-law-group-Subgroup G P)))
      ( pair
        ( inv-group-Subgroup G P)
        ( pair
          ( left-inverse-law-group-Subgroup G P)
          ( right-inverse-law-group-Subgroup G P))))

{- We show that the inclusion from group-Subgroup G P → G is a group 
   homomorphism -}

preserves-mul-incl-group-Subgroup :
  { l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  preserves-mul-Group (group-Subgroup G P) G (incl-group-Subgroup G P)
preserves-mul-incl-group-Subgroup G P (pair x p) (pair y q) = refl

hom-group-Subgroup :
  { l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  hom-Group (group-Subgroup G P) G
hom-group-Subgroup G P =
  pair (incl-group-Subgroup G P) (preserves-mul-incl-group-Subgroup G P)

{- We define another type of subgroups of G as the type of group inclusions -}

emb-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) → UU (l1 ⊔ l2)
emb-Group G H = Σ (hom-Group G H) (λ f → is-emb (map-hom-Group G H f))

emb-Group-Slice :
  (l : Level) {l1 : Level} (G : Group l1) → UU ((lsuc l) ⊔ l1)
emb-Group-Slice l G =
  Σ ( Group l)
    ( λ H → emb-Group H G)

emb-group-slice-Subgroup :
  { l1 l2 : Level} (G : Group l1) →
  Subgroup l2 G → emb-Group-Slice (l1 ⊔ l2) G
emb-group-slice-Subgroup G P =
  pair
    ( group-Subgroup G P)
    ( pair
      ( hom-group-Subgroup G P)
      ( is-emb-incl-group-Subgroup G P))
