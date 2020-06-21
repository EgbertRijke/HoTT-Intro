{-# OPTIONS --without-K --exact-split #-}

module rings where

import abelian-groups
open abelian-groups public

has-mul-Ab :
  { l1 : Level} (A : Ab l1) → UU l1
has-mul-Ab A =
  Σ ( has-associative-bin-op (set-Ab A))
    ( λ μ →
      ( is-unital (pair (set-Ab A) μ)) ×
      ( ( (a b c : type-Ab A) →
          Id (pr1 μ a (add-Ab A b c)) (add-Ab A (pr1 μ a b) (pr1 μ a c))) ×
        ( (a b c : type-Ab A) →
          Id (pr1 μ (add-Ab A a b) c) (add-Ab A (pr1 μ a c) (pr1 μ b c)))))

Ring : (l1 : Level) → UU (lsuc l1)
Ring l1 = Σ (Ab l1) has-mul-Ab

{- Basic infrastructure of rings -}

ab-Ring : {l1 : Level} → Ring l1 → Ab l1
ab-Ring R = pr1 R

group-Ring :
  {l : Level} (R : Ring l) → Group l
group-Ring R = group-Ab (ab-Ring R)

set-Ring :
  {l : Level} (R : Ring l) → UU-Set l
set-Ring R = set-Ab (ab-Ring R)

type-Ring :
  {l : Level} (R : Ring l) → UU l
type-Ring R = type-Ab (ab-Ring R)

is-set-type-Ring :
  {l : Level} (R : Ring l) → is-set (type-Ring R)
is-set-type-Ring R = is-set-type-Ab (ab-Ring R)

associative-add-Ring :
  {l : Level} (R : Ring l) → has-associative-bin-op (set-Ring R)
associative-add-Ring R = associative-add-Ab (ab-Ring R)

add-Ring :
  {l : Level} (R : Ring l) → type-Ring R → type-Ring R → type-Ring R
add-Ring R = add-Ab (ab-Ring R)

is-associative-add-Ring :
  {l : Level} (R : Ring l) (x y z : type-Ring R) →
  Id (add-Ring R (add-Ring R x y) z) (add-Ring R x (add-Ring R y z))
is-associative-add-Ring R = is-associative-add-Ab (ab-Ring R)

additive-semi-group-Ring :
  {l : Level} (R : Ring l) → Semi-Group l
additive-semi-group-Ring R = semi-group-Ab (ab-Ring R)

is-group-additive-semi-group-Ring :
  {l : Level} (R : Ring l) → is-group (additive-semi-group-Ring R)
is-group-additive-semi-group-Ring R = is-group-Ab (ab-Ring R)

has-zero-Ring :
  {l : Level} (R : Ring l) → is-unital (additive-semi-group-Ring R)
has-zero-Ring R = has-zero-Ab (ab-Ring R)

zero-Ring :
  {l : Level} (R : Ring l) → type-Ring R
zero-Ring R = zero-Ab (ab-Ring R)

left-zero-law-add-Ring :
  {l : Level} (R : Ring l) (x : type-Ring R) →
  Id (add-Ring R (zero-Ring R) x) x
left-zero-law-add-Ring R = left-zero-law-Ab (ab-Ring R)

right-zero-law-add-Ring :
  {l : Level} (R : Ring l) (x : type-Ring R) →
  Id (add-Ring R x (zero-Ring R)) x
right-zero-law-add-Ring R = right-zero-law-Ab (ab-Ring R)

has-negatives-Ring :
  {l : Level} (R : Ring l) →
  is-group' (additive-semi-group-Ring R) (has-zero-Ring R)
has-negatives-Ring R = has-negatives-Ab (ab-Ring R)

neg-Ring :
  {l : Level} (R : Ring l) → type-Ring R → type-Ring R
neg-Ring R = neg-Ab (ab-Ring R)

left-negative-law-Ring :
  {l : Level} (R : Ring l) (x : type-Ring R) →
  Id (add-Ring R (neg-Ring R x) x) (zero-Ring R)
left-negative-law-Ring R = left-negative-law-Ab (ab-Ring R)

right-negative-law-Ring :
  {l : Level} (R : Ring l) (x : type-Ring R) →
  Id (add-Ring R x (neg-Ring R x)) (zero-Ring R)
right-negative-law-Ring R = right-negative-law-Ab (ab-Ring R)

is-commutative-add-Ring :
  {l : Level} (R : Ring l) (x y : type-Ring R) →
  Id (add-Ring R x y) (add-Ring R y x)
is-commutative-add-Ring R = is-commutative-add-Ab (ab-Ring R)

has-associative-mul-Ring :
  {l : Level} (R : Ring l) → has-associative-bin-op (set-Ring R)
has-associative-mul-Ring R = pr1 (pr2 R)

mul-Ring :
  {l : Level} (R : Ring l) → type-Ring R → type-Ring R → type-Ring R
mul-Ring R = pr1 (has-associative-mul-Ring R)

is-associative-mul-Ring :
  {l : Level} (R : Ring l) (x y z : type-Ring R) →
  Id (mul-Ring R (mul-Ring R x y) z) (mul-Ring R x (mul-Ring R y z))
is-associative-mul-Ring R = pr2 (has-associative-mul-Ring R)

multiplicative-semi-group-Ring :
  {l : Level} (R : Ring l) → Semi-Group l
multiplicative-semi-group-Ring R =
  pair (set-Ring R) (has-associative-mul-Ring R)

is-unital-Ring :
  {l : Level} (R : Ring l) → is-unital (multiplicative-semi-group-Ring R)
is-unital-Ring R = pr1 (pr2 (pr2 R))

multiplicative-monoid-Ring :
  {l : Level} (R : Ring l) → Monoid l
multiplicative-monoid-Ring R =
  pair (multiplicative-semi-group-Ring R) (is-unital-Ring R)

unit-Ring :
  {l : Level} (R : Ring l) → type-Ring R
unit-Ring R = unit-Monoid (multiplicative-monoid-Ring R)

left-unit-law-mul-Ring :
  {l : Level} (R : Ring l) (x : type-Ring R) →
  Id (mul-Ring R (unit-Ring R) x) x
left-unit-law-mul-Ring R = left-unit-law-Monoid (multiplicative-monoid-Ring R)

right-unit-law-mul-Ring :
  {l : Level} (R : Ring l) (x : type-Ring R) →
  Id (mul-Ring R x (unit-Ring R)) x
right-unit-law-mul-Ring R = right-unit-law-Monoid (multiplicative-monoid-Ring R)

left-distributive-law-mul-add-Ring :
  {l : Level} (R : Ring l) (x y z : type-Ring R) →
  Id ( mul-Ring R x (add-Ring R y z))
     ( add-Ring R (mul-Ring R x y) (mul-Ring R x z))
left-distributive-law-mul-add-Ring R =
  pr1 (pr2 (pr2 (pr2 R)))

right-distributive-law-mul-add-Ring :
  {l : Level} (R : Ring l) (x y z : type-Ring R) →
  Id ( mul-Ring R (add-Ring R x y) z)
     ( add-Ring R (mul-Ring R x z) (mul-Ring R y z))
right-distributive-law-mul-add-Ring R =
  pr2 (pr2 (pr2 (pr2 R)))

{- Ring homomorphisms -}

preserves-mul-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ab (ab-Ring R1) (ab-Ring R2) → UU (l1 ⊔ l2)
preserves-mul-hom-Ab R1 R2 f =
  (x y : type-Ring R1) →
  Id ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (mul-Ring R1 x y))
     ( mul-Ring R2
       ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f x)
       ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f y))

is-prop-preserves-mul-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : hom-Ab (ab-Ring R1) (ab-Ring R2)) →
  is-prop (preserves-mul-hom-Ab R1 R2 f)
is-prop-preserves-mul-hom-Ab R1 R2 f =
  is-prop-Π
    ( λ x →
      is-prop-Π
        ( λ y →
          is-set-type-Ring R2
            ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (mul-Ring R1 x y))
            ( mul-Ring R2
              ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f x)
              ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f y))))

preserves-unit-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ab (ab-Ring R1) (ab-Ring R2) → UU l2
preserves-unit-hom-Ab R1 R2 f =
  Id (map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (unit-Ring R1)) (unit-Ring R2)

is-prop-preserves-unit-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : hom-Ab (ab-Ring R1) (ab-Ring R2)) →
  is-prop (preserves-unit-hom-Ab R1 R2 f)
is-prop-preserves-unit-hom-Ab R1 R2 f =
  is-set-type-Ring R2
    ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (unit-Ring R1))
    ( unit-Ring R2)

is-ring-homomorphism-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : hom-Ab (ab-Ring R1) (ab-Ring R2)) → UU (l1 ⊔ l2)
is-ring-homomorphism-hom-Ab R1 R2 f =
  preserves-mul-hom-Ab R1 R2 f × preserves-unit-hom-Ab R1 R2 f

is-prop-is-ring-homomorphism-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : hom-Ab (ab-Ring R1) (ab-Ring R2)) →
  is-prop (is-ring-homomorphism-hom-Ab R1 R2 f)
is-prop-is-ring-homomorphism-hom-Ab R1 R2 f =
  is-prop-prod
    ( is-prop-preserves-mul-hom-Ab R1 R2 f)
    ( is-prop-preserves-unit-hom-Ab R1 R2 f)

hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R : Ring l2) → UU (l1 ⊔ l2)
hom-Ring R1 R2 =
  Σ (hom-Ab (ab-Ring R1) (ab-Ring R2)) (is-ring-homomorphism-hom-Ab R1 R2)

{- Basic infrastructure for ring homomorphisms. -}

hom-Ab-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ring R1 R2 → hom-Ab (ab-Ring R1) (ab-Ring R2)
hom-Ab-hom-Ring R1 R2 = pr1

map-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ring R1 R2 → type-Ring R1 → type-Ring R2
map-hom-Ring R1 R2 f =
  map-hom-Ab (ab-Ring R1) (ab-Ring R2) (hom-Ab-hom-Ring R1 R2 f)

preserves-add-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : hom-Ring R1 R2) →
  preserves-add (ab-Ring R1) (ab-Ring R2) (map-hom-Ring R1 R2 f)
preserves-add-hom-Ring R1 R2 f =
  preserves-add-Ab (ab-Ring R1) (ab-Ring R2) (hom-Ab-hom-Ring R1 R2 f)

preserves-mul-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : hom-Ring R1 R2) → preserves-mul-hom-Ab R1 R2 (hom-Ab-hom-Ring R1 R2 f)
preserves-mul-hom-Ring R1 R2 f = pr1 (pr2 f)

preserves-unit-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : hom-Ring R1 R2) → preserves-unit-hom-Ab R1 R2 (hom-Ab-hom-Ring R1 R2 f)
preserves-unit-hom-Ring R1 R2 f = pr2 (pr2 f)

is-ring-homomorphism-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : hom-Ring R1 R2) →
  prod ( preserves-mul-hom-Ab R1 R2 (hom-Ab-hom-Ring R1 R2 f))
       ( preserves-unit-hom-Ab R1 R2 (hom-Ab-hom-Ring R1 R2 f))
is-ring-homomorphism-hom-Ring R1 R2 f =
  pair ( preserves-mul-hom-Ring R1 R2 f)
       ( preserves-unit-hom-Ring R1 R2 f)

{- We characterize the identity type of ring homomorphisms -}

htpy-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ring R1 R2 → hom-Ring R1 R2 → UU (l1 ⊔ l2)
htpy-hom-Ring R1 R2 f g = map-hom-Ring R1 R2 f ~ map-hom-Ring R1 R2 g

reflexive-htpy-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : hom-Ring R1 R2) → htpy-hom-Ring R1 R2 f f
reflexive-htpy-hom-Ring R1 R2 f = refl-htpy

htpy-hom-Ring-eq :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f g : hom-Ring R1 R2) → Id f g → htpy-hom-Ring R1 R2 f g
htpy-hom-Ring-eq R1 R2 f .f refl = reflexive-htpy-hom-Ring R1 R2 f

is-contr-total-htpy-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  is-contr (Σ (hom-Ring R1 R2) (htpy-hom-Ring R1 R2 f))
is-contr-total-htpy-hom-Ring R1 R2 f =
  is-contr-total-Eq-substructure
    ( is-contr-total-htpy-hom-Ab
      ( ab-Ring R1)
      ( ab-Ring R2)
      ( hom-Ab-hom-Ring R1 R2 f))
    ( is-prop-is-ring-homomorphism-hom-Ab R1 R2)
    ( hom-Ab-hom-Ring R1 R2 f)
    ( reflexive-htpy-hom-Ring R1 R2 f)
    ( is-ring-homomorphism-hom-Ring R1 R2 f)

is-equiv-htpy-hom-Ring-eq :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f g : hom-Ring R1 R2) →
  is-equiv (htpy-hom-Ring-eq R1 R2 f g)
is-equiv-htpy-hom-Ring-eq R1 R2 f =
  fundamental-theorem-id f
    ( reflexive-htpy-hom-Ring R1 R2 f)
    ( is-contr-total-htpy-hom-Ring R1 R2 f)
    ( htpy-hom-Ring-eq R1 R2 f)

equiv-htpy-hom-Ring-eq :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f g : hom-Ring R1 R2) →
  Id f g ≃ htpy-hom-Ring R1 R2 f g
equiv-htpy-hom-Ring-eq R1 R2 f g =
  pair
    ( htpy-hom-Ring-eq R1 R2 f g)
    ( is-equiv-htpy-hom-Ring-eq R1 R2 f g)

eq-htpy-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f g : hom-Ring R1 R2) →
  htpy-hom-Ring R1 R2 f g → Id f g
eq-htpy-hom-Ring R1 R2 f g =
  inv-is-equiv (is-equiv-htpy-hom-Ring-eq R1 R2 f g)

is-set-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) → is-set (hom-Ring R1 R2)
is-set-hom-Ring R1 R2 =
  is-trunc-succ-subtype
    ( neg-one-𝕋)
    ( is-prop-is-ring-homomorphism-hom-Ab R1 R2)
    ( is-set-hom-Ab (ab-Ring R1) (ab-Ring R2))

{- We define the categorical structure of rings -}

preserves-mul-id-hom-Ring :
  {l : Level} (R : Ring l) → preserves-mul-hom-Ab R R (id-hom-Ab (ab-Ring R))
preserves-mul-id-hom-Ring R x y = refl

preserves-unit-id-hom-Ring :
  {l : Level} (R : Ring l) → preserves-unit-hom-Ab R R (id-hom-Ab (ab-Ring R))
preserves-unit-id-hom-Ring R = refl

is-ring-homomorphism-id-hom-Ring :
  {l : Level} (R : Ring l) → is-ring-homomorphism-hom-Ab R R (id-hom-Ab (ab-Ring R))
is-ring-homomorphism-id-hom-Ring R =
  pair (preserves-mul-id-hom-Ring R) (preserves-unit-id-hom-Ring R)

id-hom-Ring :
  {l : Level} (R : Ring l) → hom-Ring R R
id-hom-Ring R = pair (id-hom-Ab (ab-Ring R)) (is-ring-homomorphism-id-hom-Ring R)

hom-Ab-comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : hom-Ring R2 R3) (f : hom-Ring R1 R2) →
  hom-Ab (ab-Ring R1) (ab-Ring R3) 
hom-Ab-comp-hom-Ring R1 R2 R3 g f =
  comp-hom-Ab
    ( ab-Ring R1)
    ( ab-Ring R2)
    ( ab-Ring R3)
    ( hom-Ab-hom-Ring R2 R3 g)
    ( hom-Ab-hom-Ring R1 R2 f)

preserves-mul-comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : hom-Ring R2 R3) (f : hom-Ring R1 R2) →
  preserves-mul-hom-Ab R1 R3 (hom-Ab-comp-hom-Ring R1 R2 R3 g f)
preserves-mul-comp-hom-Ring R1 R2 R3 g f x y =
  ( ap (map-hom-Ring R2 R3 g) (preserves-mul-hom-Ring R1 R2 f x y)) ∙
  ( preserves-mul-hom-Ring R2 R3 g
    ( map-hom-Ring R1 R2 f x)
    ( map-hom-Ring R1 R2 f y))

preserves-unit-comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : hom-Ring R2 R3) (f : hom-Ring R1 R2) →
  preserves-unit-hom-Ab R1 R3 (hom-Ab-comp-hom-Ring R1 R2 R3 g f)
preserves-unit-comp-hom-Ring R1 R2 R3 g f =
  ( ap (map-hom-Ring R2 R3 g) (preserves-unit-hom-Ring R1 R2 f)) ∙
  ( preserves-unit-hom-Ring R2 R3 g)

is-ring-homomorphism-comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : hom-Ring R2 R3) (f : hom-Ring R1 R2) →
  is-ring-homomorphism-hom-Ab R1 R3 (hom-Ab-comp-hom-Ring R1 R2 R3 g f)
is-ring-homomorphism-comp-hom-Ring R1 R2 R3 g f =
  pair ( preserves-mul-comp-hom-Ring R1 R2 R3 g f)
       ( preserves-unit-comp-hom-Ring R1 R2 R3 g f)

comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  hom-Ring R2 R3 → hom-Ring R1 R2 → hom-Ring R1 R3
comp-hom-Ring R1 R2 R3 g f =
  pair ( hom-Ab-comp-hom-Ring R1 R2 R3 g f)
       ( is-ring-homomorphism-comp-hom-Ring R1 R2 R3 g f)

{- We prove the laws of a category for Rings -}

is-associative-comp-hom-Ring :
  { l1 l2 l3 l4 : Level}
  ( R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) (R4 : Ring l4) →
  ( h : hom-Ring R3 R4) (g : hom-Ring R2 R3) (f : hom-Ring R1 R2) →
  Id (comp-hom-Ring R1 R2 R4 (comp-hom-Ring R2 R3 R4 h g) f)
     (comp-hom-Ring R1 R3 R4 h (comp-hom-Ring R1 R2 R3 g f))
is-associative-comp-hom-Ring R1 R2 R3 R4 h g f =
  eq-htpy-hom-Ring R1 R4
    ( comp-hom-Ring R1 R2 R4 (comp-hom-Ring R2 R3 R4 h g) f)
    ( comp-hom-Ring R1 R3 R4 h (comp-hom-Ring R1 R2 R3 g f))
    ( refl-htpy)

left-unit-law-comp-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  Id (comp-hom-Ring R1 R2 R2 (id-hom-Ring R2) f) f
left-unit-law-comp-hom-Ring R1 R2 f =
  eq-htpy-hom-Ring R1 R2
    ( comp-hom-Ring R1 R2 R2 (id-hom-Ring R2) f)
    ( f)
    ( refl-htpy)

right-unit-law-comp-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  Id (comp-hom-Ring R1 R1 R2 f (id-hom-Ring R1)) f
right-unit-law-comp-hom-Ring R1 R2 f =
  eq-htpy-hom-Ring R1 R2
    ( comp-hom-Ring R1 R1 R2 f (id-hom-Ring R1))
    ( f)
    ( refl-htpy)

{- We show that the forgetful map ab-Ring is a functor -}

id-law-ab-Ring :
  { l1 : Level} (R1 : Ring l1) →
  Id (hom-Ab-hom-Ring R1 R1 (id-hom-Ring R1)) (id-hom-Ab (ab-Ring R1))
id-law-ab-Ring R1 =
  eq-htpy-hom-Ab
    ( ab-Ring R1)
    ( ab-Ring R1)
    ( refl-htpy)

comp-law-ab-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : hom-Ring R2 R3) (f : hom-Ring R1 R2) →
  Id ( hom-Ab-hom-Ring R1 R3 (comp-hom-Ring R1 R2 R3 g f))
     ( comp-hom-Ab
       ( ab-Ring R1)
       ( ab-Ring R2)
       ( ab-Ring R3)
       ( hom-Ab-hom-Ring R2 R3 g)
       ( hom-Ab-hom-Ring R1 R2 f))
comp-law-ab-Ring R1 R2 R3 g f =
  eq-htpy-hom-Ab
    ( ab-Ring R1)
    ( ab-Ring R3)
    ( refl-htpy)

{- We introduce ring isomorphisms -}

is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ring R1 R2 → UU (l1 ⊔ l2)
is-iso-hom-Ring R1 R2 f =
  Σ ( hom-Ring R2 R1)
    ( λ g →
      ( Id (comp-hom-Ring R2 R1 R2 f g) (id-hom-Ring R2)) ×
      ( Id (comp-hom-Ring R1 R2 R1 g f) (id-hom-Ring R1)))

{- Infrastructure for invertible ring homomorphisms -}

inv-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  is-iso-hom-Ring R1 R2 f → hom-Ring R2 R1
inv-is-iso-hom-Ring R1 R2 f = pr1

is-sec-inv-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  ( is-iso-f : is-iso-hom-Ring R1 R2 f) →
  Id (comp-hom-Ring R2 R1 R2 f (inv-is-iso-hom-Ring R1 R2 f is-iso-f))
     (id-hom-Ring R2)
is-sec-inv-is-iso-hom-Ring R1 R2 f is-iso-f = pr1 (pr2 is-iso-f)

is-retr-inv-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  ( is-iso-f : is-iso-hom-Ring R1 R2 f) →
  Id (comp-hom-Ring R1 R2 R1 (inv-is-iso-hom-Ring R1 R2 f is-iso-f) f)
     (id-hom-Ring R1)
is-retr-inv-is-iso-hom-Ring R1 R2 f is-iso-f = pr2 (pr2 is-iso-f)

inv-map-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  is-iso-hom-Ring R1 R2 f → type-Ring R2 → type-Ring R1
inv-map-is-iso-hom-Ring R1 R2 f is-iso-f =
  map-hom-Ring R2 R1 (inv-is-iso-hom-Ring R1 R2 f is-iso-f)

is-sec-inv-map-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  ( is-iso-f : is-iso-hom-Ring R1 R2 f) →
  ( (map-hom-Ring R1 R2 f) ∘ (inv-map-is-iso-hom-Ring R1 R2 f is-iso-f)) ~ id
is-sec-inv-map-is-iso-hom-Ring R1 R2 f is-iso-f =
  htpy-hom-Ring-eq R2 R2
    ( comp-hom-Ring R2 R1 R2 f (inv-is-iso-hom-Ring R1 R2 f is-iso-f))
    ( id-hom-Ring R2)
    ( is-sec-inv-is-iso-hom-Ring R1 R2 f is-iso-f)

is-retr-inv-map-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  ( is-iso-f : is-iso-hom-Ring R1 R2 f) →
  ( (inv-map-is-iso-hom-Ring R1 R2 f is-iso-f) ∘ (map-hom-Ring R1 R2 f)) ~ id
is-retr-inv-map-is-iso-hom-Ring R1 R2 f is-iso-f =
  htpy-hom-Ring-eq R1 R1
    ( comp-hom-Ring R1 R2 R1 (inv-is-iso-hom-Ring R1 R2 f is-iso-f) f)
    ( id-hom-Ring R1)
    ( is-retr-inv-is-iso-hom-Ring R1 R2 f is-iso-f)

{- Being invertible is a property -}

is-prop-is-iso-hom-Ring' :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  is-prop' (is-iso-hom-Ring R1 R2 f)
is-prop-is-iso-hom-Ring' R1 R2 f inv-f inv-f' =
  eq-subtype
    ( λ g →
      is-prop-prod
        ( is-set-hom-Ring R2 R2 (comp-hom-Ring R2 R1 R2 f g) (id-hom-Ring R2))
        ( is-set-hom-Ring R1 R1 (comp-hom-Ring R1 R2 R1 g f) (id-hom-Ring R1)))
    ( eq-htpy-hom-Ring R2 R1
      ( inv-is-iso-hom-Ring R1 R2 f inv-f)
      ( inv-is-iso-hom-Ring R1 R2 f inv-f')
      ( λ x →
        ( inv
          ( ap ( map-hom-Ring R2 R1 (pr1 inv-f))
               ( is-sec-inv-map-is-iso-hom-Ring R1 R2 f inv-f' x))) ∙
        ( is-retr-inv-map-is-iso-hom-Ring R1 R2 f inv-f
          ( map-hom-Ring R2 R1 (pr1 inv-f') x))))

is-prop-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  is-prop (is-iso-hom-Ring R1 R2 f)
is-prop-is-iso-hom-Ring R1 R2 f =
  is-prop-is-prop' (is-prop-is-iso-hom-Ring' R1 R2 f)

iso-Ring :
  { l1 l2 : Level} → Ring l1 → Ring l2 → UU (l1 ⊔ l2)
iso-Ring R1 R2 = Σ (hom-Ring R1 R2) (is-iso-hom-Ring R1 R2)

hom-iso-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  iso-Ring R1 R2 → hom-Ring R1 R2
hom-iso-Ring R1 R2 = pr1

is-iso-hom-iso-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : iso-Ring R1 R2) → is-iso-hom-Ring R1 R2 (hom-iso-Ring R1 R2 f)
is-iso-hom-iso-Ring R1 R2 = pr2

inv-hom-iso-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  iso-Ring R1 R2 → hom-Ring R2 R1
inv-hom-iso-Ring R1 R2 f =
  inv-is-iso-hom-Ring R1 R2
    ( hom-iso-Ring R1 R2 f)
    ( is-iso-hom-iso-Ring R1 R2 f)

is-iso-id-hom-Ring :
  { l1 : Level} (R1 : Ring l1) → is-iso-hom-Ring R1 R1 (id-hom-Ring R1)
is-iso-id-hom-Ring R1 =
  pair ( id-hom-Ring R1)
       ( pair
         ( left-unit-law-comp-hom-Ring R1 R1 (id-hom-Ring R1))
         ( left-unit-law-comp-hom-Ring R1 R1 (id-hom-Ring R1)))

id-iso-Ring :
  { l1 : Level} (R1 : Ring l1) → iso-Ring R1 R1
id-iso-Ring R1 = pair (id-hom-Ring R1) (is-iso-id-hom-Ring R1)

iso-eq-Ring :
  { l : Level} (R1 R2 : Ring l) → Id R1 R2 → iso-Ring R1 R2
iso-eq-Ring R1 .R1 refl = id-iso-Ring R1

{- We first show that a ring homomorphism is an isomorphism if and only if
   the underlying homomorphism of abelian groups is an isomorphism. -}
   
is-iso-hom-Ab-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ring R1 R2 → UU (l1 ⊔ l2)
is-iso-hom-Ab-hom-Ring R1 R2 f =
  is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) (hom-Ab-hom-Ring R1 R2 f)

is-iso-hom-Ab-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  is-iso-hom-Ring R1 R2 f →
  is-iso-hom-Ab-hom-Ring R1 R2 f
is-iso-hom-Ab-is-iso-hom-Ring R1 R2 f is-iso-f = 
  pair ( hom-Ab-hom-Ring R2 R1 (inv-is-iso-hom-Ring R1 R2 f is-iso-f))
       ( pair
         ( ap ( hom-Ab-hom-Ring R2 R2)
              ( is-sec-inv-is-iso-hom-Ring R1 R2 f is-iso-f))
         ( ap ( hom-Ab-hom-Ring R1 R1)
              ( is-retr-inv-is-iso-hom-Ring R1 R2 f is-iso-f)))

abstract
  preserves-mul-inv-is-iso-hom-Ab :
    { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
    ( f : hom-Ab (ab-Ring R1) (ab-Ring R2)) →
    ( is-iso-f : is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f) →
    ( pres-mul-f : preserves-mul-hom-Ab R1 R2 f) →
    preserves-mul-hom-Ab R2 R1
      ( inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f)
  preserves-mul-inv-is-iso-hom-Ab R1 R2 f is-iso-f pres-mul-f x y =
    ( inv
      ( ap
        ( map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f)
        ( ( pres-mul-f
            ( map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f x)
            ( map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f y)) ∙
          ( ( ap ( mul-Ring R2
                   ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f
                     ( map-inv-is-iso-hom-Ab
                       ( ab-Ring R1)
                       ( ab-Ring R2)
                       f is-iso-f x)))
                 ( is-sec-map-inv-is-iso-hom-Ab
                   ( ab-Ring R1)
                   ( ab-Ring R2)
                   ( f)
                   ( is-iso-f)
                   ( y))) ∙
            ( ap ( λ z → mul-Ring R2 z y)
                 ( is-sec-map-inv-is-iso-hom-Ab
                   ( ab-Ring R1)
                   ( ab-Ring R2)
                   ( f)
                   ( is-iso-f)
                   ( x))))))) ∙
    ( is-retr-map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f
      ( mul-Ring R1
        ( map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f x)
        ( map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f y)))

preserves-unit-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2)
  ( f : hom-Ab (ab-Ring R1) (ab-Ring R2)) →
  ( is-iso-f : is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f)
  ( pres-unit-f : preserves-unit-hom-Ab R1 R2 f) →
  preserves-unit-hom-Ab R2 R1
    ( inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f) 
preserves-unit-inv-is-iso-hom-Ab R1 R2 f is-iso-f pres-unit-f =
  ( inv
    ( ap
      ( map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f)
      ( pres-unit-f))) ∙
  ( is-retr-map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f
    ( unit-Ring R1))

is-ring-homomorphism-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2)
  ( f : hom-Ab (ab-Ring R1) (ab-Ring R2)) →
  ( is-iso-f : is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f) →
  ( is-ring-hom-f : is-ring-homomorphism-hom-Ab R1 R2 f) →
  is-ring-homomorphism-hom-Ab R2 R1
    ( inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f)
is-ring-homomorphism-inv-is-iso-hom-Ab
  R1 R2 f is-iso-f (pair pres-mul-f pres-unit-f) =
  pair
    ( preserves-mul-inv-is-iso-hom-Ab R1 R2 f is-iso-f pres-mul-f)
    ( preserves-unit-inv-is-iso-hom-Ab R1 R2 f is-iso-f pres-unit-f)

inv-hom-Ring-is-iso-hom-Ab :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  ( is-iso-f : is-iso-hom-Ab
                 ( ab-Ring R1)
                 ( ab-Ring R2)
                 ( hom-Ab-hom-Ring R1 R2 f)) →
  hom-Ring R2 R1
inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f =
  pair
    ( inv-is-iso-hom-Ab
      ( ab-Ring R1)
      ( ab-Ring R2)
      ( hom-Ab-hom-Ring R1 R2 f)
      ( is-iso-f))
    ( is-ring-homomorphism-inv-is-iso-hom-Ab R1 R2
      ( hom-Ab-hom-Ring R1 R2 f)
      ( is-iso-f)
      ( is-ring-homomorphism-hom-Ring R1 R2 f))

abstract
  is-iso-hom-Ring-is-iso-hom-Ab :
    { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2)
    ( f : hom-Ring R1 R2) →
    is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) (hom-Ab-hom-Ring R1 R2 f) →
    is-iso-hom-Ring R1 R2 f
  is-iso-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f =
    pair
      ( inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f)
      ( pair
        ( eq-htpy-hom-Ring R2 R2
          ( comp-hom-Ring R2 R1 R2 f
            ( inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f))
          ( id-hom-Ring R2)
          ( htpy-hom-Ab-eq (ab-Ring R2) (ab-Ring R2)
            ( hom-Ab-hom-Ring R2 R2
              ( comp-hom-Ring R2 R1 R2 f
                ( inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f)))
            ( id-hom-Ab (ab-Ring R2))
            ( is-sec-inv-is-iso-hom-Ab
              ( ab-Ring R1)
              ( ab-Ring R2)
              ( hom-Ab-hom-Ring R1 R2 f)
              ( is-iso-f))))
        ( eq-htpy-hom-Ring R1 R1
          ( comp-hom-Ring R1 R2 R1
            ( inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f)
            ( f))
          ( id-hom-Ring R1)
          ( htpy-hom-Ab-eq (ab-Ring R1) (ab-Ring R1)
            ( hom-Ab-hom-Ring R1 R1
              ( comp-hom-Ring R1 R2 R1
                ( inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f)
                ( f)))
            ( id-hom-Ab (ab-Ring R1))
            ( is-retr-inv-is-iso-hom-Ab
              ( ab-Ring R1)
              ( ab-Ring R2)
              ( hom-Ab-hom-Ring R1 R2 f)
              ( is-iso-f)))))

iso-Ab-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) → UU (l1 ⊔ l2)
iso-Ab-Ring R1 R2 =
  Σ ( iso-Ab (ab-Ring R1) (ab-Ring R2))
    ( λ f →
      is-ring-homomorphism-hom-Ab R1 R2
        ( hom-iso-Ab (ab-Ring R1) (ab-Ring R2) f))

iso-Ab-iso-Ab-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  iso-Ab-Ring R1 R2 → iso-Ab (ab-Ring R1) (ab-Ring R2)
iso-Ab-iso-Ab-Ring R1 R2 = pr1

iso-Ab-iso-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  iso-Ring R1 R2 → iso-Ab (ab-Ring R1) (ab-Ring R2)
iso-Ab-iso-Ring R1 R2 f =
  pair ( hom-Ab-hom-Ring R1 R2 (hom-iso-Ring R1 R2 f))
       ( is-iso-hom-Ab-is-iso-hom-Ring R1 R2
         ( hom-iso-Ring R1 R2 f)
         ( is-iso-hom-iso-Ring R1 R2 f))

equiv-iso-Ab-iso-Ring :
  { l1 : Level} (R1 : Ring l1) (R2 : Ring l1) →
  (iso-Ring R1 R2) ≃ (iso-Ab-Ring R1 R2)
equiv-iso-Ab-iso-Ring R1 R2 =
  ( ( ( inv-equiv
        ( equiv-Σ-assoc
          ( hom-Ab (ab-Ring R1) (ab-Ring R2))
          ( is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2))
          ( λ f → is-ring-homomorphism-hom-Ab R1 R2 (pr1 f)))) ∘e
      ( equiv-tot
        ( λ f →
          equiv-swap-prod
            ( is-ring-homomorphism-hom-Ab R1 R2 f)
            ( is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f)))) ∘e
    ( equiv-Σ-assoc
      ( hom-Ab (ab-Ring R1) (ab-Ring R2))
      ( is-ring-homomorphism-hom-Ab R1 R2)
      ( λ f → is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) (pr1 f)))) ∘e
  ( equiv-total-subtype
    ( is-prop-is-iso-hom-Ring R1 R2)
    ( λ f →
      is-prop-is-iso-hom-Ab
        ( ab-Ring R1)
        ( ab-Ring R2)
        ( hom-Ab-hom-Ring R1 R2 f))
    ( is-iso-hom-Ab-is-iso-hom-Ring R1 R2)
    ( is-iso-hom-Ring-is-iso-hom-Ab R1 R2))

abstract
  is-contr-total-iso-Ring :
    { l : Level} (R : Ring l) → is-contr (Σ (Ring l) (iso-Ring R))
  is-contr-total-iso-Ring {l} R =
    is-contr-equiv
      ( Σ (Ring l) (iso-Ab-Ring R))
      ( equiv-tot (equiv-iso-Ab-iso-Ring R))
      ( is-contr-total-Eq-structure
        ( λ A μ f →
          is-ring-homomorphism-hom-Ab R (pair A μ) (hom-iso-Ab (ab-Ring R) A f))
        ( is-contr-total-iso-Ab (ab-Ring R))
        ( pair (ab-Ring R) (id-iso-Ab (ab-Ring R)))
        ( is-contr-total-Eq-structure
          ( λ μ H pres-mul → Id (unit-Ring R) (pr1 (pr1 H)))
          ( is-contr-total-Eq-substructure
            ( is-contr-total-Eq-Π
              ( λ x m → (y : type-Ring R) → Id (mul-Ring R x y) (m y))
              ( λ x → is-contr-total-htpy (mul-Ring R x))
              ( mul-Ring R))
            ( λ μ → is-prop-Π (λ x → is-prop-Π (λ y → is-prop-Π (λ z →
              is-set-type-Ring R (μ (μ x y) z) (μ x (μ y z))))))
            ( mul-Ring R)
            ( λ x y → refl)
            ( is-associative-mul-Ring R))
          ( pair (pair (mul-Ring R) (is-associative-mul-Ring R)) (λ x y → refl))
          ( is-contr-total-Eq-substructure
            ( is-contr-total-Eq-substructure
              ( is-contr-total-path (unit-Ring R))
              ( λ x →
                is-prop-prod
                  ( is-prop-Π (λ y → is-set-type-Ring R (mul-Ring R x y) y))
                  ( is-prop-Π (λ y → is-set-type-Ring R (mul-Ring R y x) y)))
              ( unit-Ring R)
              ( refl)
              ( pair (left-unit-law-mul-Ring R) (right-unit-law-mul-Ring R)))
            ( λ u →
              is-prop-prod
                ( is-prop-Π (λ x → is-prop-Π (λ y → is-prop-Π (λ z →
                  is-set-type-Ring R
                    ( mul-Ring R x (add-Ring R y z))
                    ( add-Ring R (mul-Ring R x y) (mul-Ring R x z))))))
                ( is-prop-Π (λ x → is-prop-Π (λ y → is-prop-Π (λ z →
                  is-set-type-Ring R
                    ( mul-Ring R (add-Ring R x y) z)
                    ( add-Ring R (mul-Ring R x z) (mul-Ring R y z)))))))
            ( is-unital-Ring R)
            ( refl)
            ( pair
              ( left-distributive-law-mul-add-Ring R)
              ( right-distributive-law-mul-add-Ring R)))))

is-equiv-iso-eq-Ring :
  { l : Level} (R S : Ring l) → is-equiv (iso-eq-Ring R S)
is-equiv-iso-eq-Ring R =
  fundamental-theorem-id R
    ( id-iso-Ring R)
    ( is-contr-total-iso-Ring R)
    ( iso-eq-Ring R)
    
eq-iso-Ring :
  { l : Level} (R S : Ring l) → iso-Ring R S → Id R S
eq-iso-Ring R S = inv-is-equiv (is-equiv-iso-eq-Ring R S)
