{-# OPTIONS --without-K --exact-split #-}

module rings-with-properties where

import rings
open rings public

{- Commutative rings -}

is-commutative-Ring :
  { l : Level} → Ring l → UU l
is-commutative-Ring R =
  (x y : type-Ring R) → Id (mul-Ring R x y) (mul-Ring R y x)

Comm-Ring :
  ( l : Level) → UU (lsuc l)
Comm-Ring l = Σ (Ring l) is-commutative-Ring

ring-Comm-Ring :
  { l : Level} → Comm-Ring l → Ring l
ring-Comm-Ring = pr1

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

{- Fields -}

is-field-Comm-Ring :
  { l : Level} → Comm-Ring l → UU l
is-field-Comm-Ring R = is-division-Ring (ring-Comm-Ring R)

{- Subrings -}

subset-Ring :
  (l : Level) {l1 : Level} → Ring l1 → UU ((lsuc l) ⊔ l1)
subset-Ring l R = type-Ring R → UU-Prop l

is-additive-subset-Ring :
  {l l1 : Level} (R : Ring l1) (S : subset-Ring l R) → UU _
is-additive-subset-Ring R S = {!!}
