{-# OPTIONS --without-K --exact-split #-}

module ideals where

import abelian-subgroups
import rings
open abelian-subgroups public
open rings public

{- Subsets of rings -}

subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
subset-Ring l R = type-Ring R → UU-Prop l

is-set-subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → is-set (subset-Ring l R)
is-set-subset-Ring l R =
  is-set-function-type (is-set-UU-Prop l)

{- Closure properties of subsets of rings -}

is-additive-subgroup-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-additive-subgroup-subset-Ring R = is-subgroup-Ab (ab-Ring R)

is-closed-under-mul-left-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-closed-under-mul-left-subset-Ring R P =
  (x : type-Ring R) (y : type-Ring R) →
  type-Prop (P y) → type-Prop (P (mul-Ring R x y))

is-closed-under-mul-right-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-closed-under-mul-right-subset-Ring R P =
  (x : type-Ring R) (y : type-Ring R) →
  type-Prop (P x) → type-Prop (P (mul-Ring R x y))

{- The definition of left and right ideals -}

is-left-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-left-ideal-subset-Ring R P =
  is-additive-subgroup-subset-Ring R P ×
  is-closed-under-mul-left-subset-Ring R P

Left-Ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
Left-Ideal-Ring l R = Σ (subset-Ring l R) (is-left-ideal-subset-Ring R)

is-right-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-right-ideal-subset-Ring R P =
  is-additive-subgroup-subset-Ring R P ×
  is-closed-under-mul-right-subset-Ring R P

Right-Ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
Right-Ideal-Ring l R = Σ (subset-Ring l R) (is-right-ideal-subset-Ring R)

is-two-sided-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-two-sided-ideal-subset-Ring R P =
  is-additive-subgroup-subset-Ring R P ×
  ( is-closed-under-mul-left-subset-Ring R P ×
    is-closed-under-mul-right-subset-Ring R P)

Two-Sided-Ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
Two-Sided-Ideal-Ring l R =
  Σ (subset-Ring l R) (is-two-sided-ideal-subset-Ring R)

{- Special ideals -}

