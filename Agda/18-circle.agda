{-# OPTIONS --without-K --exact-split #-}

module 18-circle where

import 17-groups
open 17-groups public

{- Section 11.1 The induction principle of the circle -}

free-loops :
  { l1 : Level} (X : UU l1) → UU l1
free-loops X = Σ X (λ x → Id x x)

base-free-loop :
  { l1 : Level} {X : UU l1} → free-loops X → X
base-free-loop = pr1

loop-free-loop :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  Id (base-free-loop l) (base-free-loop l)
loop-free-loop = pr2

-- Now we characterize the identity types of free loops

Eq-free-loops :
  { l1 : Level} {X : UU l1} (l l' : free-loops X) → UU l1
Eq-free-loops (pair x l) l' =
  Σ (Id x (pr1 l')) (λ p → Id (l ∙ p) (p ∙ (pr2 l')))

reflexive-Eq-free-loops :
  { l1 : Level} {X : UU l1} (l : free-loops X) → Eq-free-loops l l
reflexive-Eq-free-loops (pair x l) = pair refl right-unit

Eq-free-loops-eq :
  { l1 : Level} {X : UU l1} (l l' : free-loops X) →
  Id l l' → Eq-free-loops l l'
Eq-free-loops-eq l .l refl = reflexive-Eq-free-loops l

abstract
  is-contr-total-Eq-free-loops :
    { l1 : Level} {X : UU l1} (l : free-loops X) →
    is-contr (Σ (free-loops X) (Eq-free-loops l))
  is-contr-total-Eq-free-loops (pair x l) =
    is-contr-total-Eq-structure
      ( λ x l' p → Id (l ∙ p) (p ∙ l'))
      ( is-contr-total-path x)
      ( pair x refl)
      ( is-contr-is-equiv'
        ( Σ (Id x x) (λ l' → Id l l'))
        ( tot (λ l' α → right-unit ∙ α))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ l' → is-equiv-concat right-unit l'))
        ( is-contr-total-path l))

abstract
  is-equiv-Eq-free-loops-eq :
    { l1 : Level} {X : UU l1} (l l' : free-loops X) →
    is-equiv (Eq-free-loops-eq l l')
  is-equiv-Eq-free-loops-eq l =
    fundamental-theorem-id l
      ( reflexive-Eq-free-loops l)
      ( is-contr-total-Eq-free-loops l)
      ( Eq-free-loops-eq l) 

{- We introduce dependent free loops, which are used in the induction principle
   of the circle. -}
   
dependent-free-loops :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2) → UU l2
dependent-free-loops l P =
  Σ ( P (base-free-loop l))
    ( λ p₀ → Id (tr P (loop-free-loop l) p₀) p₀)

Eq-dependent-free-loops :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2) →
  ( p p' : dependent-free-loops l P) → UU l2
Eq-dependent-free-loops (pair x l) P (pair y p) p' =
  Σ ( Id y (pr1 p'))
    ( λ q → Id (p ∙ q) ((ap (tr P l) q) ∙ (pr2 p')))

reflexive-Eq-dependent-free-loops :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2) →
  ( p : dependent-free-loops l P) → Eq-dependent-free-loops l P p p
reflexive-Eq-dependent-free-loops (pair x l) P (pair y p) =
  pair refl right-unit

Eq-dependent-free-loops-eq :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2) →
  ( p p' : dependent-free-loops l P) →
  Id p p' → Eq-dependent-free-loops l P p p'
Eq-dependent-free-loops-eq l P p .p refl =
  reflexive-Eq-dependent-free-loops l P p

abstract
  is-contr-total-Eq-dependent-free-loops :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2) →
    ( p : dependent-free-loops l P) →
    is-contr (Σ (dependent-free-loops l P) (Eq-dependent-free-loops l P p))
  is-contr-total-Eq-dependent-free-loops (pair x l) P (pair y p) =
    is-contr-total-Eq-structure
      ( λ y' p' q → Id (p ∙ q) ((ap (tr P l) q) ∙ p'))
      ( is-contr-total-path y)
      ( pair y refl)
      ( is-contr-is-equiv'
        ( Σ (Id (tr P l y) y) (λ p' → Id p p'))
        ( tot (λ p' α → right-unit ∙ α))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ p' → is-equiv-concat right-unit p'))
        ( is-contr-total-path p))

abstract
  is-equiv-Eq-dependent-free-loops-eq :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2)
    ( p p' : dependent-free-loops l P) →
    is-equiv (Eq-dependent-free-loops-eq l P p p')
  is-equiv-Eq-dependent-free-loops-eq l P p =
    fundamental-theorem-id p
      ( reflexive-Eq-dependent-free-loops l P p)
      ( is-contr-total-Eq-dependent-free-loops l P p)
      ( Eq-dependent-free-loops-eq l P p)

eq-Eq-dependent-free-loops :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2)
  ( p p' : dependent-free-loops l P) →
  Eq-dependent-free-loops l P p p' → Id p p'
eq-Eq-dependent-free-loops l P p p' =
  inv-is-equiv (is-equiv-Eq-dependent-free-loops-eq l P p p')

{- We now define the induction principle of the circle. -}

ev-free-loop' :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2) →
  ( (x : X) → P x) → dependent-free-loops l P
ev-free-loop' (pair x₀ p) P f = pair (f x₀) (apd f p)

induction-principle-circle :
  { l1 : Level} (l2 : Level) {X : UU l1} (l : free-loops X) →
  UU ((lsuc l2) ⊔ l1)
induction-principle-circle l2 {X} l =
  (P : X → UU l2) → sec (ev-free-loop' l P)

{- Section 11.2 The universal property of the circle -}

{- We first state the universal property of the circle -}

ev-free-loop :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (Y : UU l2) →
  ( X → Y) → free-loops Y
ev-free-loop l Y f = pair (f (pr1 l)) (ap f (pr2 l))

universal-property-circle :
  { l1 : Level} (l2 : Level) {X : UU l1} (l : free-loops X) → UU _
universal-property-circle l2 l =
  ( Y : UU l2) → is-equiv (ev-free-loop l Y)

{- A fairly straightforward proof of the universal property of the circle
   factors through the dependent universal property of the circle. -}

dependent-universal-property-circle :
  { l1 : Level} (l2 : Level) {X : UU l1} (l : free-loops X) →
  UU ((lsuc l2) ⊔ l1)
dependent-universal-property-circle l2 {X} l =
  ( P : X → UU l2) → is-equiv (ev-free-loop' l P)

{- We first prove that the dependent universal property of the circle follows
   from the induction principle of the circle. To show this, we have to show
   that the section of ev-free-loop' is also a retraction. This construction
   is also by the induction principle of the circle, but it requires (a minimal
   amount of) preparations. -}

Eq-subst :
  { l1 l2 : Level} {X : UU l1} {P : X → UU l2} (f g : (x : X) → P x) →
  X → UU _
Eq-subst f g x = Id (f x) (g x)

tr-Eq-subst :
  { l1 l2 : Level} {X : UU l1} {P : X → UU l2} (f g : (x : X) → P x)
  { x y : X} (p : Id x y) (q : Id (f x) (g x)) (r : Id (f y) (g y))→
  ( Id ((apd f p) ∙ r) ((ap (tr P p) q) ∙ (apd g p))) →
  ( Id (tr (Eq-subst f g) p q) r)
tr-Eq-subst f g refl q .((ap id q) ∙ refl) refl =
  inv (right-unit ∙ (ap-id q))

dependent-free-loops-htpy :
  {l1 l2 : Level} {X : UU l1} {l : free-loops X} {P : X → UU l2}
  {f g : (x : X) → P x} →
  ( Eq-dependent-free-loops l P (ev-free-loop' l P f) (ev-free-loop' l P g)) →
  ( dependent-free-loops l (λ x → Id (f x) (g x)))
dependent-free-loops-htpy {l = (pair x l)} (pair p q) =
  pair p (tr-Eq-subst _ _ l p p q)

isretr-ind-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
  ( ind-circle : induction-principle-circle l2 l) (P : X → UU l2) →
  ( (pr1 (ind-circle P)) ∘ (ev-free-loop' l P)) ~ id
isretr-ind-circle l ind-circle P f =
  eq-htpy
    ( pr1
      ( ind-circle
        ( λ t → Id (pr1 (ind-circle P) (ev-free-loop' l P f) t) (f t)))
      ( dependent-free-loops-htpy
        ( Eq-dependent-free-loops-eq l P _ _
          ( pr2 (ind-circle P) (ev-free-loop' l P f)))))

abstract
  dependent-universal-property-induction-principle-circle :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
    induction-principle-circle l2 l → dependent-universal-property-circle l2 l
  dependent-universal-property-induction-principle-circle l ind-circle P =
    is-equiv-has-inverse
      ( pr1 (ind-circle P))
      ( pr2 (ind-circle P))
      ( isretr-ind-circle l ind-circle P)

{- We use the dependent universal property to derive a uniqeness property of
   dependent functions on the circle. -}

dependent-uniqueness-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
  dependent-universal-property-circle l2 l →
  { P : X → UU l2} (k : dependent-free-loops l P) →
  is-contr
    ( Σ ( (x : X) → P x)
        ( λ h → Eq-dependent-free-loops l P (ev-free-loop' l P h) k))
dependent-uniqueness-circle l dup-circle {P} k =
  is-contr-is-equiv'
    ( fib (ev-free-loop' l P) k)
    ( tot (λ h → Eq-dependent-free-loops-eq l P (ev-free-loop' l P h) k))
    ( is-equiv-tot-is-fiberwise-equiv
      (λ h → is-equiv-Eq-dependent-free-loops-eq l P (ev-free-loop' l P h) k))
    ( is-contr-map-is-equiv (dup-circle P) k)

{- Now that we have established the dependent universal property, we can
   reduce the (non-dependent) universal property to the dependent case. We do
   so by constructing a commuting triangle relating ev-free-loop to 
   ev-free-loop' via a comparison equivalence. -}

tr-const :
  {i j : Level} {A : UU i} {B : UU j} {x y : A} (p : Id x y) (b : B) →
  Id (tr (λ (a : A) → B) p b) b
tr-const refl b = refl

apd-const :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A}
  (p : Id x y) → Id (apd f p) ((tr-const p (f x)) ∙ (ap f p))
apd-const f refl = refl

comparison-free-loops :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (Y : UU l2) →
  free-loops Y → dependent-free-loops l (λ x → Y)
comparison-free-loops l Y =
  tot (λ y l' → (tr-const (pr2 l) y) ∙ l')

abstract
  is-equiv-comparison-free-loops :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X) (Y : UU l2) →
    is-equiv (comparison-free-loops l Y)
  is-equiv-comparison-free-loops l Y =
    is-equiv-tot-is-fiberwise-equiv
      ( λ y → is-equiv-concat (tr-const (pr2 l) y) y)

triangle-comparison-free-loops :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (Y : UU l2) →
  ( (comparison-free-loops l Y) ∘ (ev-free-loop l Y)) ~
  ( ev-free-loop' l (λ x → Y))
triangle-comparison-free-loops (pair x l) Y f =
  eq-Eq-dependent-free-loops
    ( pair x l)
    ( λ x → Y)
    ( comparison-free-loops (pair x l) Y (ev-free-loop (pair x l) Y f))
    ( ev-free-loop' (pair x l) (λ x → Y) f)
    ( pair refl (right-unit ∙ (inv (apd-const f l))))

abstract
  universal-property-dependent-universal-property-circle :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
    ( dependent-universal-property-circle l2 l) →
    ( universal-property-circle l2 l)
  universal-property-dependent-universal-property-circle l dup-circle Y =
    is-equiv-right-factor
      ( ev-free-loop' l (λ x → Y))
      ( comparison-free-loops l Y)
      ( ev-free-loop l Y)
      ( htpy-inv (triangle-comparison-free-loops l Y))
      ( is-equiv-comparison-free-loops l Y)
      ( dup-circle (λ x → Y))

{- Now we get the universal property of the circle from the induction principle
   of the circle by composing the earlier two proofs. -}

abstract
  universal-property-induction-principle-circle :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
    induction-principle-circle l2 l → universal-property-circle l2 l
  universal-property-induction-principle-circle l =
    ( universal-property-dependent-universal-property-circle l) ∘
    ( dependent-universal-property-induction-principle-circle l)

unique-mapping-property-circle :
  { l1 : Level} (l2 : Level) {X : UU l1} (l : free-loops X) →
  UU (l1 ⊔ (lsuc l2))
unique-mapping-property-circle l2 {X} l =
  ( Y : UU l2) (l' : free-loops Y) →
    is-contr (Σ (X → Y) (λ f → Eq-free-loops (ev-free-loop l Y f) l'))

abstract
  unique-mapping-property-universal-property-circle :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
    universal-property-circle l2 l →
    unique-mapping-property-circle l2 l
  unique-mapping-property-universal-property-circle l up-circle Y l' =
    is-contr-is-equiv'
      ( fib (ev-free-loop l Y) l')
      ( tot (λ f → Eq-free-loops-eq (ev-free-loop l Y f) l'))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ f → is-equiv-Eq-free-loops-eq (ev-free-loop l Y f) l'))
      ( is-contr-map-is-equiv (up-circle Y) l')

{- We assume that we have a circle. -}

postulate 𝕊¹ : UU lzero

postulate base-𝕊¹ : 𝕊¹

postulate loop-𝕊¹ : Id base-𝕊¹ base-𝕊¹

free-loop-𝕊¹ : free-loops 𝕊¹
free-loop-𝕊¹ = pair base-𝕊¹ loop-𝕊¹

postulate ind-𝕊¹ : {l : Level} → induction-principle-circle l free-loop-𝕊¹

dependent-universal-property-𝕊¹ :
  {l : Level} → dependent-universal-property-circle l free-loop-𝕊¹
dependent-universal-property-𝕊¹ =
  dependent-universal-property-induction-principle-circle free-loop-𝕊¹ ind-𝕊¹

dependent-uniqueness-𝕊¹ :
  {l : Level} {P : 𝕊¹ → UU l} (k : dependent-free-loops free-loop-𝕊¹ P) →
  is-contr (Σ ((x : 𝕊¹) → P x) (λ h → Eq-dependent-free-loops free-loop-𝕊¹ P (ev-free-loop' free-loop-𝕊¹ P h) k))
dependent-uniqueness-𝕊¹ {l} {P} k =
  dependent-uniqueness-circle free-loop-𝕊¹ dependent-universal-property-𝕊¹ k

universal-property-𝕊¹ :
  {l : Level} → universal-property-circle l free-loop-𝕊¹
universal-property-𝕊¹ =
  universal-property-dependent-universal-property-circle
    free-loop-𝕊¹
    dependent-universal-property-𝕊¹

-- Section 14.3 Multiplication on the circle



{- Exercises -}

-- Exercise 11.1

{- The dependent universal property of the circle (and hence also the induction
   principle of the circle, implies that the circle is connected in the sense
   that for any family of propositions parametrized by the circle, if the
   proposition at the base holds, then it holds for any x : circle. -}

abstract
  is-connected-circle' :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
    ( dup-circle : dependent-universal-property-circle l2 l)
    ( P : X → UU l2) (is-prop-P : (x : X) → is-prop (P x)) →
    P (base-free-loop l) → (x : X) → P x
  is-connected-circle' l dup-circle P is-prop-P p =
    inv-is-equiv
      ( dup-circle P)
      ( pair p (center (is-prop-P _ (tr P (pr2 l) p) p)))
