{-# OPTIONS --without-K --exact-split #-}

module subrings where

import rings
open rings public

--------------------------------------------------------------------------------

{- Subrings -}

subset-Ring :
  (l : Level) {l1 : Level} → Ring l1 → UU ((lsuc l) ⊔ l1)
subset-Ring l R = type-Ring R → UU-Prop l

is-additive-subset-Ring :
  {l l1 : Level} (R : Ring l1) (S : subset-Ring l R) → UU _
is-additive-subset-Ring R S = {!!}
