{-# OPTIONS --without-K --exact-split #-}

module 15-sets where

import 14-propositional-truncation
open 14-propositional-truncation public

{- Equivalence relations -}

Rel-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Rel-Prop l A = A → (A → UU-Prop l)

type-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) → A → A → UU l2
type-Rel-Prop R x y = pr1 (R x y)

is-prop-type-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) →
  (x y : A) → is-prop (type-Rel-Prop R x y)
is-prop-type-Rel-Prop R x y = pr2 (R x y)

is-reflexive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-reflexive-Rel-Prop {A = A} R =
  (x : A) → type-Rel-Prop R x x

is-symmetric-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-symmetric-Rel-Prop {A = A} R =
  (x y : A) → type-Rel-Prop R x y → type-Rel-Prop R y x

is-transitive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-transitive-Rel-Prop {A = A} R =
  (x y z : A) → type-Rel-Prop R x y → type-Rel-Prop R y z → type-Rel-Prop R x z

is-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) → UU (l1 ⊔ l2)
is-equivalence-relation R =
  is-reflexive-Rel-Prop R ×
    ( is-symmetric-Rel-Prop R × is-transitive-Rel-Prop R)

Eq-Rel :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Eq-Rel l A = Σ (Rel-Prop l A) is-equivalence-relation

rel-prop-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} → Eq-Rel l2 A → Rel-Prop l2 A
rel-prop-Eq-Rel = pr1

type-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} → Eq-Rel l2 A → A → A → UU l2
type-Eq-Rel R = type-Rel-Prop (rel-prop-Eq-Rel R)

is-equivalence-relation-rel-prop-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-equivalence-relation (rel-prop-Eq-Rel R)
is-equivalence-relation-rel-prop-Eq-Rel R = pr2 R

refl-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-reflexive-Rel-Prop (rel-prop-Eq-Rel R)
refl-Eq-Rel R = pr1 (is-equivalence-relation-rel-prop-Eq-Rel R)

symm-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-symmetric-Rel-Prop (rel-prop-Eq-Rel R)
symm-Eq-Rel R = pr1 (pr2 (is-equivalence-relation-rel-prop-Eq-Rel R))

trans-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-transitive-Rel-Prop (rel-prop-Eq-Rel R)
trans-Eq-Rel R = pr2 (pr2 (is-equivalence-relation-rel-prop-Eq-Rel R))

{- Section 15.2 The universal property of set quotients -}

identifies-Eq-Rel :
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  {B : UU l3} → (A → B) → UU (l1 ⊔ (l2 ⊔ l3))
identifies-Eq-Rel {A = A} R f =
  (x y : A) → type-Eq-Rel R x y → Id (f x) (f y)

precomp-map-universal-property-Eq-Rel :
  {l l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU-Set l3} (f : A → type-Set B) (H : identifies-Eq-Rel R f) →
  (X : UU-Set l) → (hom-Set B X) → Σ (A → type-Set X) (identifies-Eq-Rel R)
precomp-map-universal-property-Eq-Rel R f H X g =
  pair (g ∘ f) (λ x y r → ap g (H x y r))

universal-property-set-quotient :
  (l : Level) {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU-Set l3} (f : A → type-Set B) (H : identifies-Eq-Rel R f) → UU _
universal-property-set-quotient l R {B} f H =
  (X : UU-Set l) → is-equiv (precomp-map-universal-property-Eq-Rel R {B} f H X) 
  
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

total-subtype :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
total-subtype {A = A} P = Σ A (λ x → pr1 (P x))

equiv-subtype-equiv :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} (e : A ≃ B)
  (C : A → UU-Prop l3) (D : B → UU-Prop l4) →
  ((x : A) → (C x) ↔ (D (map-equiv e x))) →
  total-subtype C ≃ total-subtype D
equiv-subtype-equiv e C D H =
  equiv-toto (λ y → type-Prop (D y)) e
    ( λ x → equiv-iff (C x) (D (map-equiv e x)) (H x))

equiv-comp-equiv' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (C : UU l3) → (B ≃ C) ≃ (A ≃ C)
equiv-comp-equiv' e C =
  equiv-subtype-equiv
    ( equiv-precomp-equiv e C)
    ( is-equiv-Prop)
    ( is-equiv-Prop)
    ( λ g →
      pair
        ( is-equiv-comp' g (map-equiv e) (is-equiv-map-equiv e))
        ( λ is-equiv-eg →
          is-equiv-left-factor'
            g (map-equiv e) is-equiv-eg (is-equiv-map-equiv e)))

is-prop-is-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-small l A)
is-prop-is-small l A =
  is-prop-is-contr-if-inh
    ( λ Xe →
      is-contr-equiv'
        ( Σ (UU l) (λ Y → (pr1 Xe) ≃ Y))
        ( equiv-tot ((λ Y → equiv-comp-equiv' (pr2 Xe) Y)))
        ( is-contr-total-equiv (pr1 Xe)))

is-prop-is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-locally-small l A)
is-prop-is-locally-small l A =
  is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-small l (Id x y)))
