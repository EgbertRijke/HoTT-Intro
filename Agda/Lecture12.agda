{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture12 where

import Lecture11
open Lecture11 public

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

Eq-free-loops :
  { l1 : Level} {X : UU l1} (l l' : free-loops X) → UU l1
Eq-free-loops (dpair x l) l' =
  Σ (Id x (pr1 l')) (λ p → Id (l ∙ p) (p ∙ (pr2 l')))

reflexive-Eq-free-loops :
  { l1 : Level} {X : UU l1} (l : free-loops X) → Eq-free-loops l l
reflexive-Eq-free-loops (dpair x l) = dpair refl (right-unit l)

Eq-free-loops-eq :
  { l1 : Level} {X : UU l1} (l l' : free-loops X) →
  Id l l' → Eq-free-loops l l'
Eq-free-loops-eq l .l refl = reflexive-Eq-free-loops l

is-contr-total-Eq-free-loops :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  is-contr (Σ (free-loops X) (Eq-free-loops l))
is-contr-total-Eq-free-loops (dpair x l) =
  is-contr-total-Eq-structure
    ( λ x l' p → Id (l ∙ p) (p ∙ l'))
    ( is-contr-total-path _ x)
    ( dpair x refl)
    ( is-contr-is-equiv'
      ( Σ (Id x x) (λ l' → Id l l'))
      ( tot (λ l' α → (right-unit l) ∙ α))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ l' → is-equiv-concat (right-unit l) l'))
      ( is-contr-total-path _ l))

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
Eq-dependent-free-loops (dpair x l) P (dpair y p) p' =
  Σ ( Id y (pr1 p'))
    ( λ q → Id (p ∙ q) ((ap (tr P l) q) ∙ (pr2 p')))

reflexive-Eq-dependent-free-loops :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2) →
  ( p : dependent-free-loops l P) → Eq-dependent-free-loops l P p p
reflexive-Eq-dependent-free-loops (dpair x l) P (dpair y p) =
  dpair refl (right-unit p)

Eq-dependent-free-loops-eq :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2) →
  ( p p' : dependent-free-loops l P) →
  Id p p' → Eq-dependent-free-loops l P p p'
Eq-dependent-free-loops-eq l P p .p refl =
  reflexive-Eq-dependent-free-loops l P p

is-contr-total-Eq-dependent-free-loops :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : X → UU l2) →
  ( p : dependent-free-loops l P) →
  is-contr (Σ (dependent-free-loops l P) (Eq-dependent-free-loops l P p))
is-contr-total-Eq-dependent-free-loops (dpair x l) P (dpair y p) =
  is-contr-total-Eq-structure
    ( λ y' p' q → Id (p ∙ q) ((ap (tr P l) q) ∙ p'))
    ( is-contr-total-path _ y)
    ( dpair y refl)
    ( is-contr-is-equiv'
      ( Σ (Id (tr P l y) y) (λ p' → Id p p'))
      ( tot (λ p' α → (right-unit p) ∙ α))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ p' → is-equiv-concat (right-unit p) p'))
      ( is-contr-total-path _ p))

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
ev-free-loop' (dpair x₀ p) P f = dpair (f x₀) (apd f p)

induction-principle-circle :
  { l1 : Level} (l2 : Level) {X : UU l1} (l : free-loops X) →
  UU ((lsuc l2) ⊔ l1)
induction-principle-circle l2 {X} l = (P : X → UU l2) → sec (ev-free-loop' l P)

{- Section 11.2 The universal property of the circle -}

{- We first state the universal property of the circle -}

ev-free-loop :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (Y : UU l2) →
  ( X → Y) → free-loops Y
ev-free-loop (dpair x l) Y f = dpair (f x) (ap f l)

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
dependent-free-loops-htpy {l = (dpair x l)} (dpair p q) =
  dpair p (tr-Eq-subst _ _ l p p q)

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

comparison-free-loops :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (Y : UU l2) →
  free-loops Y → dependent-free-loops l (λ x → Y)
comparison-free-loops l Y =
  tot (λ y l' → (tr-triv (pr2 l) y) ∙ l')

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
triangle-comparison-free-loops (dpair x l) Y f =
  eq-Eq-dependent-free-loops
    ( dpair x l)
    ( λ x → Y)
    ( comparison-free-loops (dpair x l) Y (ev-free-loop (dpair x l) Y f))
    ( ev-free-loop' (dpair x l) (λ x → Y) f)
    ( dpair refl ((right-unit _) ∙ (inv (apd-triv f l))))

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

universal-property-induction-principle-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
  induction-principle-circle l2 l → universal-property-circle l2 l
universal-property-induction-principle-circle l =
  ( universal-property-dependent-universal-property-circle l) ∘
  ( dependent-universal-property-induction-principle-circle l)

{- Section 11.3 The fundamental cover of the circle -}

{- An elimination principle for ℤ -}

elim-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( k : ℤ) → P k
elim-ℤ P p0 pS (inl zero-ℕ) =
  inv-is-equiv (is-equiv-eqv-map (pS neg-one-ℤ)) p0
elim-ℤ P p0 pS (inl (succ-ℕ x)) =
  inv-is-equiv
    ( is-equiv-eqv-map (pS (inl (succ-ℕ x))))
    ( elim-ℤ P p0 pS (inl x))
elim-ℤ P p0 pS (inr (inl star)) = p0
elim-ℤ P p0 pS (inr (inr zero-ℕ)) = eqv-map (pS zero-ℤ) p0
elim-ℤ P p0 pS (inr (inr (succ-ℕ x))) =
  eqv-map
    ( pS (inr (inr x)))
    ( elim-ℤ P p0 pS (inr (inr x)))

comp-zero-elim-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  Id (elim-ℤ P p0 pS zero-ℤ) p0
comp-zero-elim-ℤ P p0 pS = refl

comp-succ-elim-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) (k : ℤ) →
  Id ( elim-ℤ P p0 pS (succ-ℤ k)) (eqv-map (pS k)
     ( elim-ℤ P p0 pS k))
comp-succ-elim-ℤ P p0 pS (inl zero-ℕ) =
  inv
    ( issec-inv-is-equiv
      ( is-equiv-eqv-map (pS (inl zero-ℕ)))
      ( elim-ℤ P p0 pS (succ-ℤ (inl zero-ℕ))))
comp-succ-elim-ℤ P p0 pS (inl (succ-ℕ x)) =
  inv
    ( issec-inv-is-equiv
      ( is-equiv-eqv-map (pS (inl (succ-ℕ x))))
      ( elim-ℤ P p0 pS (succ-ℤ (inl (succ-ℕ x)))))
comp-succ-elim-ℤ P p0 pS (inr (inl star)) = refl
comp-succ-elim-ℤ P p0 pS (inr (inr x)) = refl

