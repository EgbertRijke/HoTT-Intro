{-# OPTIONS --without-K #-}

module 13-circle where

import 12-univalence
open 12-univalence public

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
reflexive-Eq-free-loops (pair x l) = pair refl (right-unit l)

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
      ( is-contr-total-path _ x)
      ( pair x refl)
      ( is-contr-is-equiv'
        ( Σ (Id x x) (λ l' → Id l l'))
        ( tot (λ l' α → (right-unit l) ∙ α))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ l' → is-equiv-concat (right-unit l) l'))
        ( is-contr-total-path _ l))

abstract
  is-equiv-Eq-free-loops-eq :
    { l1 : Level} {X : UU l1} (l l' : free-loops X) →
    is-equiv (Eq-free-loops-eq l l')
  is-equiv-Eq-free-loops-eq l =
    id-fundamental-gen l
      ( reflexive-Eq-free-loops l)
      ( is-contr-total-Eq-free-loops l)
      ( Eq-free-loops-eq l) 
  
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
  pair refl (right-unit p)

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
      ( is-contr-total-path _ y)
      ( pair y refl)
      ( is-contr-is-equiv'
        ( Σ (Id (tr P l y) y) (λ p' → Id p p'))
        ( tot (λ p' α → (right-unit p) ∙ α))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ p' → is-equiv-concat (right-unit p) p'))
        ( is-contr-total-path _ p))

abstract
  is-equiv-Eq-dependent-free-loops-eq :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2)
    ( p p' : dependent-free-loops l P) →
    is-equiv (Eq-dependent-free-loops-eq l P p p')
  is-equiv-Eq-dependent-free-loops-eq l P p =
    id-fundamental-gen p
      ( reflexive-Eq-dependent-free-loops l P p)
      ( is-contr-total-Eq-dependent-free-loops l P p)
      ( Eq-dependent-free-loops-eq l P p)

eq-Eq-dependent-free-loops :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2)
  ( p p' : dependent-free-loops l P) →
  Eq-dependent-free-loops l P p p' → Id p p'
eq-Eq-dependent-free-loops l P p p' =
  inv-is-equiv (is-equiv-Eq-dependent-free-loops-eq l P p p')

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
  inv ((right-unit _) ∙ (ap-id q))

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
    is-equiv-has-inverse'
      ( pr1 (ind-circle P))
      ( pr2 (ind-circle P))
      ( isretr-ind-circle l ind-circle P)

{- Now that we have established the dependent universal property, we can
   reduce the (non-dependent) universal property to the dependent case. We do
   so by constructing a commuting triangle relating ev-free-loop to 
   ev-free-loop' via a comparison equivalence. -}

tr-triv :
  {i j : Level} {A : UU i} {B : UU j} {x y : A} (p : Id x y) (b : B) →
  Id (tr (λ (a : A) → B) p b) b
tr-triv refl b = refl

apd-triv :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A}
  (p : Id x y) → Id (apd f p) ((tr-triv p (f x)) ∙ (ap f p))
apd-triv f refl = refl

comparison-free-loops :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (Y : UU l2) →
  free-loops Y → dependent-free-loops l (λ x → Y)
comparison-free-loops l Y =
  tot (λ y l' → (tr-triv (pr2 l) y) ∙ l')

abstract
  is-equiv-comparison-free-loops :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X) (Y : UU l2) →
    is-equiv (comparison-free-loops l Y)
  is-equiv-comparison-free-loops l Y =
    is-equiv-tot-is-fiberwise-equiv
      ( λ y → is-equiv-concat (tr-triv (pr2 l) y) y)

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
    ( pair refl ((right-unit _) ∙ (inv (apd-triv f l))))

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

{- We show that if a type with a free loop satisfies the induction principle
   of the circle with respect to any universe level, then it satisfies the
   induction principle with respect to the zeroth universe level. -}

naturality-tr-fiberwise-transformation :
  { l1 l2 l3 : Level} {X : UU l1} {P : X → UU l2} {Q : X → UU l3}
  ( f : (x : X) → P x → Q x) {x y : X} (α : Id x y) (p : P x) →
  Id (tr Q α (f x p)) (f y (tr P α p))
naturality-tr-fiberwise-transformation f refl p = refl

functor-dependent-free-loops :
  { l1 l2 l3 : Level} {X : UU l1} (l : free-loops X)
  { P : X → UU l2} {Q : X → UU l3} (f : (x : X) → P x → Q x) →
  dependent-free-loops l P → dependent-free-loops l Q
functor-dependent-free-loops l {P} {Q} f =
  toto
    ( λ q₀ → Id (tr Q (loop-free-loop l) q₀) q₀)
    ( f (base-free-loop l))
    ( λ p₀ α →
      ( naturality-tr-fiberwise-transformation f (loop-free-loop l) p₀) ∙
      ( ap (f (base-free-loop l)) α))

coherence-square-functor-dependent-free-loops :
  { l1 l2 l3 : Level} {X : UU l1} {P : X → UU l2} {Q : X → UU l3}
  ( f : (x : X) → P x → Q x) {x y : X} (α : Id x y)
  ( h : (x : X) → P x) →
  Id ( ( naturality-tr-fiberwise-transformation f α (h x)) ∙
       ( ap (f y) (apd h α)))
     ( apd (postcomp-Π f h) α)
coherence-square-functor-dependent-free-loops f refl h = refl
  
square-functor-dependent-free-loops :
  { l1 l2 l3 : Level} {X : UU l1} (l : free-loops X)
  { P : X → UU l2} {Q : X → UU l3} (f : (x : X) → P x → Q x) →
  ( (functor-dependent-free-loops l f) ∘ (ev-free-loop' l P)) ~
  ( (ev-free-loop' l Q) ∘ (postcomp-Π f))
square-functor-dependent-free-loops (pair x l) {P} {Q} f h =
  eq-Eq-dependent-free-loops (pair x l) Q
    ( functor-dependent-free-loops (pair x l) f
      ( ev-free-loop' (pair x l) P h))
    ( ev-free-loop' (pair x l) Q (postcomp-Π f h))
    ( pair refl
      ( ( right-unit _) ∙
        ( coherence-square-functor-dependent-free-loops f l h)))

abstract
  is-equiv-functor-dependent-free-loops-is-fiberwise-equiv :
    { l1 l2 l3 : Level} {X : UU l1} (l : free-loops X)
    { P : X → UU l2} {Q : X → UU l3} {f : (x : X) → P x → Q x}
    ( is-equiv-f : (x : X) → is-equiv (f x)) →
    is-equiv (functor-dependent-free-loops l f)
  is-equiv-functor-dependent-free-loops-is-fiberwise-equiv
    (pair x l) {P} {Q} {f} is-equiv-f =
    is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map
      ( λ q₀ → Id (tr Q l q₀) q₀)
      ( _)
      ( _)
      ( is-equiv-f x)
      ( λ p₀ →
        is-equiv-comp'
          ( concat
            ( f x (tr P l p₀))
            ( naturality-tr-fiberwise-transformation f l p₀))
          ( ap (f x))
          ( is-emb-is-equiv (f x) (is-equiv-f x) (tr P l p₀) p₀)
          ( is-equiv-concat
            ( naturality-tr-fiberwise-transformation f l p₀)
            ( f x p₀)))

abstract
  lower-dependent-universal-property-circle :
    { l1 l2 : Level} (l3 : Level) {X : UU l1} (l : free-loops X) →
    dependent-universal-property-circle (l2 ⊔ l3) l →
    dependent-universal-property-circle l3 l
  lower-dependent-universal-property-circle {l1} {l2} l3 l dup-circle P =
    is-equiv-left-is-equiv-right-square
      ( ev-free-loop' l P)
      ( ev-free-loop' l (λ x → raise l2 (P x)))
      ( postcomp-Π (λ x → map-raise l2 (P x)))
      ( functor-dependent-free-loops l (λ x → map-raise l2 (P x)))
      ( square-functor-dependent-free-loops l (λ x → map-raise l2 (P x)))
      ( is-equiv-postcomp-Π _ (λ x → is-equiv-map-raise l2 (P x)))
      ( is-equiv-functor-dependent-free-loops-is-fiberwise-equiv l
        ( λ x → is-equiv-map-raise l2 (P x)))
      ( dup-circle (λ x → raise l2 (P x)))

abstract
  lower-lzero-dependent-universal-property-circle :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
    dependent-universal-property-circle l2 l →
    dependent-universal-property-circle lzero l
  lower-lzero-dependent-universal-property-circle =
    lower-dependent-universal-property-circle lzero

{- The dependent universal property of the circle (and hence also the induction
   principle of the circle, implies that the circle is connected in the sense
   that for any family of propositions parametrized by the circle, if the
   proposition at the base holds, then it holds for any x : circle. -}

{- Exercises -}

-- Exercise 11.1

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
