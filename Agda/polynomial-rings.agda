{-# OPTIONS --without-K --exact-split #-}

module polynomial-rings where

import rings
open rings public

{- We state the universal property of the polynomial ring R[x]. -}

precomp-universal-property-polynomial-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3)
  (f : hom-Ring R S) (s : type-Ring S) →
  hom-Ring S T → (hom-Ring R T) × (type-Ring T)
precomp-universal-property-polynomial-Ring R S T f s g =
  pair (comp-hom-Ring R S T g f) (map-hom-Ring S T g s)

universal-property-polynomial-Ring :
  (l : Level) {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  (f : hom-Ring R S) (s : type-Ring S) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-polynomial-Ring l R S f s =
  (T : Ring l) →
  is-equiv (precomp-universal-property-polynomial-Ring R S T f s)
