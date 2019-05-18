{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module 21-image where

import 20-sequences
open 20-sequences public

{- We give the formal specification of propositional truncation. -}

precomp-Prop :
  { l1 l2 l3 : Level} {A : UU l1} (P : hProp l2) →
  (A → type-Prop P) → (Q : hProp l3) →
  (type-Prop P → type-Prop Q) → A → type-Prop Q
precomp-Prop P f Q g = g ∘ f

universal-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (P : hProp l2) →
  ( A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-propositional-truncation l P f =
  (Q : hProp l) → is-equiv (precomp-Prop P f Q)

universal-property-propositional-truncation' :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (P : hProp l2) →
  ( A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-propositional-truncation' l {A = A} P f =
  (Q : hProp l) → (A → type-Prop Q) → (type-Prop P → type-Prop Q)

universal-property-propositional-truncation-simplify :
  { l1 l2 : Level} {A : UU l1} (P : hProp l2)
  ( f : A → type-Prop P) →
  ( (l : Level) → universal-property-propositional-truncation' l P f) →
  ( (l : Level) → universal-property-propositional-truncation l P f)
universal-property-propositional-truncation-simplify P f up-P l Q =
  is-equiv-is-prop
    ( is-prop-Π (λ x → is-prop-type-Prop Q))
    ( is-prop-Π (λ x → is-prop-type-Prop Q))
    ( up-P l Q)
  
precomp-Π-Prop :
  { l1 l2 l3 : Level} {A : UU l1} (P : hProp l2) →
  ( f : A → type-Prop P) (Q : type-Prop P → hProp l3) →
  ( g : (p : type-Prop P) → type-Prop (Q p)) → (x : A) → type-Prop (Q (f x))
precomp-Π-Prop P f Q g x = g (f x)

dependent-universal-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (P : hProp l2) →
  ( A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
dependent-universal-property-propositional-truncation l P f =
  (Q : type-Prop P → hProp l) → is-equiv (precomp-Π-Prop P f Q)

{- We introduce the image inclusion of a map. -}

precomp-emb :
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} ( i : B ↪ X) (q : hom-slice f (map-emb i)) →
  {C : UU l4} ( j : C ↪ X) (r : hom-slice (map-emb i) (map-emb j)) →
  hom-slice f (map-emb j)
precomp-emb f i q j r =
  pair
    ( ( map-hom-slice (map-emb i) (map-emb j) r) ∘
      ( map-hom-slice f (map-emb i) q))
    ( ( triangle-hom-slice f (map-emb i) q) ∙h
      ( ( triangle-hom-slice (map-emb i) (map-emb j) r) ·r
        ( map-hom-slice f (map-emb i) q)))

is-prop-hom-slice :
  { l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) → is-prop (hom-slice f (map-emb i))
is-prop-hom-slice {X = X} f i =
  is-prop-is-equiv
    ( (x : X) → fib f x → fib (map-emb i) x)
    ( fiberwise-hom-hom-slice f (map-emb i))
    ( is-equiv-fiberwise-hom-hom-slice f (map-emb i))
    ( is-prop-Π
      ( λ x → is-prop-Π
        ( λ p → is-prop-map-is-emb (map-emb i) (is-emb-map-emb i) x)))

universal-property-image :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
universal-property-image l {X = X} f i q =
  ( C : UU l) (j : C ↪ X) → is-equiv (precomp-emb f i q j)

universal-property-image' :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
universal-property-image' l {X = X} f i q =
  ( C : UU l) (j : C ↪ X) →
    hom-slice f (map-emb j) → hom-slice (map-emb i) (map-emb j)

universal-property-image-universal-property-image' :
  ( l : Level) {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
  { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
  universal-property-image' l f i q → universal-property-image l f i q
universal-property-image-universal-property-image' l f i q up' C j =
  is-equiv-is-prop
    ( is-prop-hom-slice (map-emb i) j)
    ( is-prop-hom-slice f j)
    ( up' C j)
  

