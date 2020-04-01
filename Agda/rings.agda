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

preserves-mul-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ab (ab-Ring R1) (ab-Ring R2) → UU (l1 ⊔ l2)
preserves-mul-Ring R1 R2 f =
  (x y : type-Ring R1) →
  Id ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (mul-Ring R1 x y))
     ( mul-Ring R2
       ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f x)
       ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f y))

preserves-unit-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ab (ab-Ring R1) (ab-Ring R2) → UU l2
preserves-unit-Ring R1 R2 f =
  Id (map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (unit-Ring R1)) (unit-Ring R2)

hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R : Ring l2) → UU (l1 ⊔ l2)
hom-Ring R1 R2 =
  Σ ( hom-Ab (ab-Ring R1) (ab-Ring R2))
    ( λ f → (preserves-mul-Ring R1 R2 f) × (preserves-unit-Ring R1 R2 f))

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
  (f : hom-Ring R1 R2) → preserves-mul-Ring R1 R2 (hom-Ab-hom-Ring R1 R2 f)
preserves-mul-hom-Ring R1 R2 f = pr1 (pr2 f)

preserves-unit-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : hom-Ring R1 R2) → preserves-unit-Ring R1 R2 (hom-Ab-hom-Ring R1 R2 f)
preserves-unit-hom-Ring R1 R2 f = pr2 (pr2 f)
