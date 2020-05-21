{-# OPTIONS --without-K --exact-split #-}

module rings-with-properties where

import rings
open rings public

--------------------------------------------------------------------------------

{- Commutative rings -}

is-commutative-Ring :
  { l : Level} → Ring l → UU l
is-commutative-Ring R =
  (x y : type-Ring R) → Id (mul-Ring R x y) (mul-Ring R y x)

is-prop-is-commutative-Ring :
  { l : Level} (R : Ring l) → is-prop (is-commutative-Ring R)
is-prop-is-commutative-Ring R =
  is-prop-Π
    ( λ x →
      is-prop-Π
      ( λ y →
        is-set-type-Ring R (mul-Ring R x y) (mul-Ring R y x)))

Comm-Ring :
  ( l : Level) → UU (lsuc l)
Comm-Ring l = Σ (Ring l) is-commutative-Ring

ring-Comm-Ring :
  { l : Level} → Comm-Ring l → Ring l
ring-Comm-Ring = pr1

is-commutative-Comm-Ring :
  { l : Level} (R : Comm-Ring l) → is-commutative-Ring (ring-Comm-Ring R)
is-commutative-Comm-Ring = pr2

hom-Comm-Ring :
  { l1 l2 : Level} → Comm-Ring l1 → Comm-Ring l2 → UU (l1 ⊔ l2)
hom-Comm-Ring R1 R2 = hom-Ring (ring-Comm-Ring R1) (ring-Comm-Ring R2)

iso-Comm-Ring :
  { l1 l2 : Level} → Comm-Ring l1 → Comm-Ring l2 → UU (l1 ⊔ l2)
iso-Comm-Ring R1 R2 = iso-Ring (ring-Comm-Ring R1) (ring-Comm-Ring R2)

is-contr-total-iso-Comm-Ring :
  { l1 : Level} (R1 : Comm-Ring l1) →
  is-contr (Σ (Comm-Ring l1) (iso-Comm-Ring R1))
is-contr-total-iso-Comm-Ring R1 =
  is-contr-total-Eq-substructure
    ( is-contr-total-iso-Ring (ring-Comm-Ring R1))
    ( is-prop-is-commutative-Ring)
    ( ring-Comm-Ring R1)
    ( id-iso-Ring (ring-Comm-Ring R1))
    ( is-commutative-Comm-Ring R1)

--------------------------------------------------------------------------------

{- Division rings -}

zero-neq-one-Ring :
  { l : Level} → Ring l → UU l
zero-neq-one-Ring R = ¬ (Id (zero-Ring R) (unit-Ring R))

has-left-inverse-Ring :
  { l : Level} (R : Ring l) → type-Ring R → UU l
has-left-inverse-Ring R x =
  Σ (type-Ring R) (λ y → Id (mul-Ring R y x) (unit-Ring R))

has-right-inverse-Ring :
  {l : Level} (R : Ring l) → type-Ring R → UU l
has-right-inverse-Ring R x =
  Σ (type-Ring R) (λ y → Id (mul-Ring R x y) (unit-Ring R))

has-two-sided-inverse-Ring :
  {l : Level} (R : Ring l) → type-Ring R → UU l
has-two-sided-inverse-Ring R x =
  ( has-left-inverse-Ring R x) × (has-right-inverse-Ring R x)
  
is-invertible-Ring :
  {l : Level} (R : Ring l) → type-Ring R → UU l
is-invertible-Ring R x =
  Σ ( type-Ring R)
    ( λ y →
      Id (mul-Ring R y x) (unit-Ring R) ×
      Id (mul-Ring R x y) (unit-Ring R))

is-division-Ring :
  { l : Level} → Ring l → UU l
is-division-Ring R =
  (zero-neq-one-Ring R) ×
  ((x : type-Ring R) → ¬ (Id (zero-Ring R) x) → is-invertible-Ring R x)

--------------------------------------------------------------------------------

{- Fields -}

is-field-Comm-Ring :
  { l : Level} → Comm-Ring l → UU l
is-field-Comm-Ring R = is-division-Ring (ring-Comm-Ring R)
