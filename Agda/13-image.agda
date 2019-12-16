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

is-prop-hom-Prop :
  { l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → is-prop (hom-Prop P Q)
is-prop-hom-Prop P Q =
  is-prop-function-type
    ( type-Prop P)
    ( type-Prop Q)
    ( is-prop-type-Prop Q)

equiv-Prop :
  { l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → UU (l1 ⊔ l2)
equiv-Prop P Q = (type-Prop P) ≃ (type-Prop Q)

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

universal-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (f : A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-propositional-truncation l {A = A} P f =
  (Q : UU-Prop l) (g : A → type-Prop Q) →
  is-contr (Σ (hom-Prop P Q) (λ h → (h ∘ f) ~  g))

-- Some unnumbered remarks after Definition 13.1.3

universal-property-is-propositional-truncation :
  (l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (f : A → type-Prop P) →
  is-propositional-truncation l P f →
  universal-property-propositional-truncation l P f
universal-property-is-propositional-truncation l P f is-ptr-f Q g =
  is-contr-equiv'
    ( Σ (hom-Prop P Q) (λ h → Id (h ∘ f) g))
    ( equiv-tot (λ h → equiv-funext))
    ( is-contr-map-is-equiv (is-ptr-f Q) g)

map-is-propositional-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
  ({l : Level} → is-propositional-truncation l P f) →
  (Q : UU-Prop l3) (g : A → type-Prop Q) → hom-Prop P Q
map-is-propositional-truncation P f is-ptr-f Q g =
  pr1
    ( center
      ( universal-property-is-propositional-truncation _ P f is-ptr-f Q g))

htpy-is-propositional-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
  (is-ptr-f : {l : Level} → is-propositional-truncation l P f) →
  (Q : UU-Prop l3) (g : A → type-Prop Q) →
  ((map-is-propositional-truncation P f is-ptr-f Q g) ∘ f) ~ g
htpy-is-propositional-truncation P f is-ptr-f Q g =
  pr2
    ( center
      ( universal-property-is-propositional-truncation _ P f is-ptr-f Q g))

is-propositional-truncation-universal-property :
  (l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (f : A → type-Prop P) →
  universal-property-propositional-truncation l P f →
  is-propositional-truncation l P f
is-propositional-truncation-universal-property l P f up-f Q =
  is-equiv-is-contr-map
    ( λ g → is-contr-equiv
      ( Σ (hom-Prop P Q) (λ h → (h ∘ f) ~ g))
      ( equiv-tot (λ h → equiv-funext))
      ( up-f Q g))

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

is-ptruncation-is-ptruncation-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P')
  (h : hom-Prop P P') (H : (h ∘ f) ~ f') →
  is-equiv h →
  ((l : Level) → is-propositional-truncation l P f) →
  ((l : Level) → is-propositional-truncation l P' f')
is-ptruncation-is-ptruncation-is-equiv P P' f f' h H is-equiv-h is-ptr-f l Q =
  is-equiv-comp
    ( precomp-Prop P' f' Q)
    ( precomp-Prop P f Q)
    ( precomp h (type-Prop Q))
    ( triangle-3-for-2-is-ptruncation P P' f f' h H Q)
    ( is-equiv-precomp-is-equiv h is-equiv-h (type-Prop Q))
    ( is-ptr-f l Q)

is-ptruncation-is-equiv-is-ptruncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P')
  (h : hom-Prop P P') (H : (h ∘ f) ~ f') →
  ((l : Level) → is-propositional-truncation l P' f') →
  is-equiv h →
  ((l : Level) → is-propositional-truncation l P f)
is-ptruncation-is-equiv-is-ptruncation P P' f f' h H is-ptr-f' is-equiv-h l Q =
  is-equiv-left-factor
    ( precomp-Prop P' f' Q)
    ( precomp-Prop P f Q)
    ( precomp h (type-Prop Q))
    ( triangle-3-for-2-is-ptruncation P P' f f' h H Q)
    ( is-ptr-f' l Q)
    ( is-equiv-precomp-is-equiv h is-equiv-h (type-Prop Q))

-- Corollary 13.1.6

is-uniquely-unique-propositional-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
  (f : A → type-Prop P) (f' : A → type-Prop P') →
  ({l : Level} → is-propositional-truncation l P f) →
  ({l : Level} → is-propositional-truncation l P' f') →
  is-contr (Σ (equiv-Prop P P') (λ e → (map-equiv e ∘ f) ~ f'))
is-uniquely-unique-propositional-truncation P P' f f' is-ptr-f is-ptr-f' =
  is-contr-total-Eq-substructure
    ( universal-property-is-propositional-truncation _ P f is-ptr-f P' f')
    ( is-subtype-is-equiv)
    ( map-is-propositional-truncation P f is-ptr-f P' f')
    ( htpy-is-propositional-truncation P f is-ptr-f P' f')
    ( is-equiv-is-ptruncation-is-ptruncation  P P' f f'
      ( map-is-propositional-truncation P f is-ptr-f P' f')
      ( htpy-is-propositional-truncation P f is-ptr-f P' f')
      ( λ l → is-ptr-f)
      ( λ l → is-ptr-f'))

-- Axiom 13.1.8

postulate trunc-Prop : {l : Level} → UU l → UU-Prop l

type-trunc-Prop : {l : Level} → UU l → UU l
type-trunc-Prop A = pr1 (trunc-Prop A)

is-prop-type-trunc-Prop : {l : Level} (A : UU l) → is-prop (type-trunc-Prop A)
is-prop-type-trunc-Prop A = pr2 (trunc-Prop A)

postulate unit-trunc-Prop : {l : Level} (A : UU l) → A → type-Prop (trunc-Prop A)

postulate is-propositional-truncation-trunc-Prop : {l1 l2 : Level} (A : UU l1) → is-propositional-truncation l2 (trunc-Prop A) (unit-trunc-Prop A)

universal-property-trunc-Prop : {l1 l2 : Level} (A : UU l1) →
  universal-property-propositional-truncation l2
    ( trunc-Prop A)
    ( unit-trunc-Prop A)
universal-property-trunc-Prop A =
  universal-property-is-propositional-truncation _
    ( trunc-Prop A)
    ( unit-trunc-Prop A)
    ( is-propositional-truncation-trunc-Prop A)

-- Proposition 13.1.9

unique-functor-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-contr
    ( Σ ( hom-Prop (trunc-Prop A) (trunc-Prop B))
        ( λ h → (h ∘ (unit-trunc-Prop A)) ~ ((unit-trunc-Prop B) ∘ f)))
unique-functor-trunc-Prop {l1} {l2} {A} {B} f =
  universal-property-trunc-Prop A (trunc-Prop B) ((unit-trunc-Prop B) ∘ f)

functor-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → hom-Prop (trunc-Prop A) (trunc-Prop B)
functor-trunc-Prop f =
  pr1 (center (unique-functor-trunc-Prop f))

htpy-functor-trunc-Prop :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ( (functor-trunc-Prop f) ∘ (unit-trunc-Prop A)) ~ ((unit-trunc-Prop B) ∘ f)
htpy-functor-trunc-Prop f =
  pr2 (center (unique-functor-trunc-Prop f))

htpy-uniqueness-functor-trunc-Prop :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ( h : hom-Prop (trunc-Prop A) (trunc-Prop B)) →
  ( ( h ∘ (unit-trunc-Prop A)) ~ ((unit-trunc-Prop B) ∘ f)) →
  (functor-trunc-Prop f) ~ h
htpy-uniqueness-functor-trunc-Prop f h H =
  htpy-eq (ap pr1 (contraction (unique-functor-trunc-Prop f) (pair h H)))

id-functor-trunc-Prop :
  { l1 : Level} {A : UU l1} → functor-trunc-Prop (id {A = A}) ~ id
id-functor-trunc-Prop {l1} {A} =
  htpy-uniqueness-functor-trunc-Prop id id refl-htpy

comp-functor-trunc-Prop :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  ( g : B → C) (f : A → B) →
  ( functor-trunc-Prop (g ∘ f)) ~
  ( (functor-trunc-Prop g) ∘ (functor-trunc-Prop f))
comp-functor-trunc-Prop g f =
  htpy-uniqueness-functor-trunc-Prop
    ( g ∘ f)
    ( (functor-trunc-Prop g) ∘ (functor-trunc-Prop f))
    ( ( (functor-trunc-Prop g) ·l (htpy-functor-trunc-Prop f)) ∙h
      ( ( htpy-functor-trunc-Prop g) ·r f))

-- Section 13.2 Propositional truncations as higher inductive types

-- Definition 13.2.1

case-paths-induction-principle-propositional-truncation :
  { l : Level} {l1 l2 : Level} {A : UU l1}
  ( P : UU-Prop l2) (α : (p q : type-Prop P) → Id p q) (f : A → type-Prop P) →
  ( B : type-Prop P → UU l) → UU (l ⊔ l2)
case-paths-induction-principle-propositional-truncation P α f B =
  (p q : type-Prop P) (x : B p) (y : B q) → Id (tr B (α p q) x) y
  
induction-principle-propositional-truncation :
  (l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (α : (p q : type-Prop P) → Id p q) (f : A → type-Prop P) →
  UU (lsuc l ⊔ l1 ⊔ l2)
induction-principle-propositional-truncation l {l1} {l2} {A} P α f =
  ( B : type-Prop P → UU l) →
  ( g : (x : A) → (B (f x))) →
  ( β : case-paths-induction-principle-propositional-truncation P α f B) →
  Σ ((p : type-Prop P) → B p) (λ h → (x : A) → Id (h (f x)) (g x))

-- Lemma 13.2.2

is-prop-case-paths-induction-principle-propositional-truncation :
  { l : Level} {l1 l2 : Level} {A : UU l1}
  ( P : UU-Prop l2) (α : (p q : type-Prop P) → Id p q) (f : A → type-Prop P) →
  ( B : type-Prop P → UU l) →
  case-paths-induction-principle-propositional-truncation P α f B →
  ( p : type-Prop P) → is-prop (B p)
is-prop-case-paths-induction-principle-propositional-truncation P α f B β p =
  is-prop-is-contr-if-inh (λ x → pair (tr B (α p p) x) (β p p x))

case-paths-induction-principle-propositional-truncation-is-prop :
  { l : Level} {l1 l2 : Level} {A : UU l1}
  ( P : UU-Prop l2) (α : (p q : type-Prop P) → Id p q) (f : A → type-Prop P) →
  ( B : type-Prop P → UU l) →
  ( (p : type-Prop P) → is-prop (B p)) →
  case-paths-induction-principle-propositional-truncation P α f B
case-paths-induction-principle-propositional-truncation-is-prop
  P α f B is-prop-B p q x y =
  is-prop'-is-prop (is-prop-B q) (tr B (α p q) x) y

-- Definition 13.2.3

dependent-universal-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  ( P : UU-Prop l2) (f : A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
dependent-universal-property-propositional-truncation l {l1} {l2} {A} P f =
  ( Q : type-Prop P → UU-Prop l) → is-equiv (precomp-Π f (type-Prop ∘ Q))

-- Theorem 13.2.4

dependent-universal-property-is-propositional-truncation :
  { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
  ( {l : Level} → is-propositional-truncation l P f) →
  ( {l : Level} → dependent-universal-property-propositional-truncation l P f)
dependent-universal-property-is-propositional-truncation P f is-ptr-f Q = {!!}

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
