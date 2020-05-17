{-# OPTIONS --without-K --exact-split #-}

module dn-sheaves where

import rings
open rings public

{- We postulate a propositional resizing axiom -}

raise-UU-Prop :
  (l : Level) → UU-Prop lzero → UU-Prop l
raise-UU-Prop l (pair P is-prop-P) =
  pair ( raise l P)
       ( is-prop-is-equiv' P
         ( map-raise l P)
         ( is-equiv-map-raise l P)
         ( is-prop-P))

postulate propositional-resizing : {l : Level} → is-equiv (raise-UU-Prop l)

lower-UU-Prop :
  {l : Level} → UU-Prop l → UU-Prop lzero
lower-UU-Prop = inv-is-equiv propositional-resizing

issec-lower-UU-Prop :
  {l : Level} (P : UU-Prop l) → Id (raise-UU-Prop l (lower-UU-Prop P)) P
issec-lower-UU-Prop = issec-inv-is-equiv propositional-resizing

isretr-lower-UU-Prop :
  {l : Level} (P : UU-Prop lzero) → Id (lower-UU-Prop (raise-UU-Prop l P)) P
isretr-lower-UU-Prop = isretr-inv-is-equiv propositional-resizing
  
{- We define what it means for a type to be a double-negation-sheaf -}

is-dn-sheaf :
  {l : Level} (X : UU l) → UU (l ⊔ (lsuc lzero))
is-dn-sheaf X =
  (P : UU-Prop lzero) → is-equiv (λ (f : ¬¬ (type-Prop P) → X) → f ∘ intro-dn)

universal-property-dn-sheafification :
  (l : Level) {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-dn-sheaf Y → UU ((lsuc l) ⊔ l1 ⊔ l2)
universal-property-dn-sheafification l {Y = Y} f is-dn-sheaf-Y =
  (Z : UU l) (H : is-dn-sheaf Z) → is-equiv (λ (h : Y → Z) → h ∘ f)

postulate dn-sheafification : {l : Level} → UU l → UU l

postulate unit-dn-sheafification : {l : Level} (X : UU l) → X → dn-sheafification X

postulate is-dn-sheaf-dn-sheafification : {l : Level} (X : UU l) → is-dn-sheaf (dn-sheafification X)

postulate is-dn-sheafification : {l1 l2 : Level} (X : UU l1) → universal-property-dn-sheafification l2 (unit-dn-sheafification X) (is-dn-sheaf-dn-sheafification X)

{- We show that on propositions, dn-sheafification agrees with double negation. -}

is-dn-sheaf-dn : {l : Level} (P : UU l) → is-dn-sheaf (¬¬ P)
is-dn-sheaf-dn P Q =
  is-equiv-is-prop
    ( is-prop-function-type (¬¬ (type-Prop Q)) (¬¬ P) is-prop-neg)
    ( is-prop-function-type (type-Prop Q) (¬¬ P) is-prop-neg)
    ( dn-extend)

is-dn-sheafification-intro-dn :
  (k : Level) {l : Level} (P : UU l) →
  universal-property-dn-sheafification k (intro-dn {P = P}) (is-dn-sheaf-dn P)
is-dn-sheafification-intro-dn k {l} P X is-dn-sheaf-X =
  is-equiv-top-is-equiv-bottom-square
    ( λ f → f ∘ ( functor-dn {!map-raise l ?!}))
    {!!}
    {!!}
    {!!}
    {!!}
    {!!}
    {!!}
    {!!}
