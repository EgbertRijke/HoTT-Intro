{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module 13-image where

import 12-univalence
open 12-univalence public

-- Section 13 Propositional truncations, the image of a map, and the replacement axiom

-- Section 13.1 Propositional truncations

-- Definition 13.1.1

hom-Prop :
  { l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → UU (l1 ⊔ l2)
hom-Prop P Q = type-Prop P → type-Prop Q

precomp-Prop :
  { l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) →
  (A → type-Prop P) → (Q : UU-Prop l3) →
  (hom-Prop P Q) → (A → type-Prop Q)
precomp-Prop P f Q g = g ∘ f

is-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
  ( A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
is-propositional-truncation l P f =
  (Q : UU-Prop l) → is-equiv (precomp-Prop P f Q)

-- Remark 13.1.2

is-propositional-truncation' :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
  ( A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
is-propositional-truncation' l {A = A} P f =
  (Q : UU-Prop l) → (A → type-Prop Q) → (hom-Prop P Q)

is-propositional-truncation-simpl :
  { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2)
  ( f : A → type-Prop P) →
  ( (l : Level) → is-propositional-truncation' l P f) →
  ( (l : Level) → is-propositional-truncation l P f)
is-propositional-truncation-simpl P f up-P l Q =
  is-equiv-is-prop
    ( is-prop-Π (λ x → is-prop-type-Prop Q))
    ( is-prop-Π (λ x → is-prop-type-Prop Q))
    ( up-P l Q)

-- Example 13.1.3

is-propositional-truncation-const-star :
  { l1 : Level} (A : UU-pt l1)
  ( l : Level) → is-propositional-truncation l unit-Prop (const (type-UU-pt A) unit star)
is-propositional-truncation-const-star A =
  is-propositional-truncation-simpl
    ( unit-Prop)
    ( const (type-UU-pt A) unit star)
    ( λ l P f → const unit (type-Prop P) (f (pt-UU-pt A)))

-- Example 13.1.4

is-propositional-truncation-id :
  { l1 : Level} (P : UU-Prop l1) →
  ( l : Level) → is-propositional-truncation l P id
is-propositional-truncation-id P l Q =
  is-equiv-id (hom-Prop P Q)

-- Proposition 13.1.5

abstract
  is-equiv-is-equiv-precomp-Prop :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (f : hom-Prop P Q) →
    ((l : Level) (R : UU-Prop l) →
    is-equiv (precomp-Prop Q f R)) → is-equiv f
  is-equiv-is-equiv-precomp-Prop P Q f is-equiv-precomp-f =
    is-equiv-is-equiv-precomp-subuniverse id (λ l → is-prop) P Q f
      is-equiv-precomp-f

triangle-3-for-2-is-ptruncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P')
  (h : hom-Prop P P') (H : (h ∘ f) ~ f') →
  {l : Level} (Q : UU-Prop l) →
  ( precomp-Prop P' f' Q) ~
  ( (precomp-Prop P f Q) ∘ (precomp h (type-Prop Q)))
triangle-3-for-2-is-ptruncation P P' f f' h H Q g =
  eq-htpy (λ p → inv (ap g (H p)))

is-equiv-is-ptruncation-is-ptruncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P')
  (h : hom-Prop P P') (H : (h ∘ f) ~ f') →
  ((l : Level) → is-propositional-truncation l P f) →
  ((l : Level) → is-propositional-truncation l P' f') →
  is-equiv h
is-equiv-is-ptruncation-is-ptruncation P P' f f' h H is-ptr-P is-ptr-P' =
  is-equiv-is-equiv-precomp-Prop P P' h
    ( λ l Q →
      is-equiv-right-factor
        ( precomp-Prop P' f' Q)
        ( precomp-Prop P f Q)
        ( precomp h (type-Prop Q))
        ( triangle-3-for-2-is-ptruncation P P' f f' h H Q)
        ( is-ptr-P l Q)
        ( is-ptr-P' l Q))

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
  
-- Section 13.4

is-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-small l A = Σ (UU l) (λ X → A ≃ X)

is-small-map :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → UU (lsuc l ⊔ (l1 ⊔ l2))
is-small-map l {B = B} f = (b : B) → is-small l (fib f b)

is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-locally-small l A = (x y : A) → is-small l (Id x y)

is-prop-is-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-small l A)
is-prop-is-small l A =
  is-prop-is-contr-if-inh
    ( λ Xe →
      is-contr-equiv'
        ( Σ (UU l) (λ Y → (pr1 Xe) ≃ Y))
        ( equiv-tot ((λ Y → {!equiv-precomp!}))) {!!})
