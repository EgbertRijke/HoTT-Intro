\begin{code}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture10 where

import Lecture09
open Lecture09 public

htpy-square : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (p : C → A) (q : C → B) → UU _
htpy-square f g p q = (f ∘ p) ~ (g ∘ q)

cospan : {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) → UU _
cospan {l3 = l3} A B = Σ (UU l3) (λ X → (A → X) × (B → X))

cone : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → UU l4 → UU _
cone {l4 = l4} {A = A} {B = B} f g C =
  Σ (C → A) (λ p → Σ (C → B) (λ q → htpy-square f g p q))

cone-map : {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} {C' : UU l5} →
  cone f g C → (C' → C) → cone f g C'
cone-map f g (dpair p (dpair q H)) h =
  dpair (p ∘ h) (dpair (q ∘ h) (htpy-right-whisk H h))

universal-property-pullback : {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (f : A → X) (g : B → X) (C : UU l4) → cone f g C → UU _
universal-property-pullback {l5 = l5} f g C cone-f-g-C =
  (C' : UU l5) → is-equiv (cone-map f g {C' = C'} cone-f-g-C)

Eq-cone : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} → cone f g C → cone f g C → UU _
Eq-cone f g c c' =
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
      p' = pr1 c'
      q' = pr1 (pr2 c')
      H' = pr2 (pr2 c') in
  Σ (p ~ p') (λ K → Σ (q ~ q') (λ L →
    ( htpy-concat (g ∘ q) H (htpy-left-whisk g L)) ~
      ( htpy-concat (f ∘ p') (htpy-left-whisk f K) H')))

Eq-cone-eq-cone : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (cone-f-g-C cone-f-g-C' : cone f g C) →
  Id cone-f-g-C cone-f-g-C' → Eq-cone f g cone-f-g-C cone-f-g-C'
Eq-cone-eq-cone f g (dpair p (dpair q H)) .(dpair p (dpair q H)) refl =
  dpair (htpy-refl p) (dpair (htpy-refl q) (htpy-right-unit H))

is-equiv-htpy-concat : {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h : (x : A) → B x} (H : f ~ g) → is-equiv (htpy-concat g {h = h} H)
is-equiv-htpy-concat {l1} {l2} {f = f} {g = g} {h = h} =
  ind-htpy {l3 = l1 ⊔ l2} f (λ g H → is-equiv (htpy-concat g {h = h} H))
    (is-equiv-id (f ~ h)) g

is-contr-total-Eq-cone : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C) →
  is-contr (Σ (cone f g C) (Eq-cone f g c))
is-contr-total-Eq-cone {A = A} {B} f g {C} (dpair p (dpair q H)) =
  is-contr-Σ-×-Σ-rearrange-is-contr
    ( C → A)
    ( λ p' → Σ (C → B) (λ q' → (f ∘ p') ~ (g ∘ q')))
    ( λ p' → p ~ p')
    ( λ t →
      let q' = pr1 (pr2 (pr1 t)) in
      let H' = pr2 (pr2 (pr1 t)) in
      let p' = pr1 (pr1 t) in
      let K = pr2 t in
      Σ ( q ~ q')
        ( λ L →
          ( htpy-concat (g ∘ q) H (htpy-left-whisk g L)) ~
            ( htpy-concat (f ∘ p') (htpy-left-whisk f K) H')))
    ( is-contr-total-htpy-nondep p)
    ( is-contr-Σ-×-Σ-rearrange-is-contr
      ( C → B)
      ( λ q' → (f ∘ p) ~ (g ∘ q'))
      ( λ q' → q ~ q')
      ( λ t →
        let L = pr2 t in
        let H' = pr2 (pr1 t) in
        ( htpy-concat (g ∘ q) H (htpy-left-whisk g L)) ~ H')
      ( is-contr-total-htpy-nondep q)
      ( let E = λ (H' : (f ∘ p) ~ (g ∘ q)) →
                is-equiv-htpy-concat {h = H'} (htpy-right-unit H) in
          is-contr-is-equiv
          ( Σ ((f ∘ p) ~ (g ∘ q)) (λ H' → H ~ H'))
          ( tot (λ H' → inv-is-equiv (E H')))
          ( is-equiv-tot-is-fiberwise-equiv (λ H' → inv-is-equiv (E H'))
            ( λ H' → is-equiv-inv-is-equiv (E H')))
          ( is-contr-total-htpy H)))

is-fiberwise-equiv-Eq-cone-eq-cone : {l1 l2 l3 l4 : Level} {A : UU l1}
  {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C) →
  is-fiberwise-equiv (Eq-cone-eq-cone f g c)
is-fiberwise-equiv-Eq-cone-eq-cone f g {C = C} c =
  id-fundamental-gen c
    ( Eq-cone-eq-cone f g c c refl)
    ( is-contr-total-Eq-cone f g c)
    ( Eq-cone-eq-cone f g c)

is-contr-universal-property-pullback : {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  {C : UU l3} {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C) →
  universal-property-pullback {l5 = l5} f g C c →
  (C' : UU l5) (c' : cone f g C') →
  is-contr (Σ (C' → C) (λ h → Eq-cone f g (cone-map f g c h) c'))
is-contr-universal-property-pullback {C = C} f g c up C' c' =
  is-contr-is-equiv'
    ( Σ (C' → C) (λ h → Id (cone-map f g c h) c'))
    ( tot (λ h → Eq-cone-eq-cone f g (cone-map f g c h) c'))
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ h → Eq-cone-eq-cone f g (cone-map f g c h) c')
      ( λ h → is-fiberwise-equiv-Eq-cone-eq-cone f g (cone-map f g c h) c'))
    (is-contr-map-is-equiv (up C')  c')

-- Section 10.2

canonical-pullback : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → UU ((l1 ⊔ l2) ⊔ l3)
canonical-pullback {A = A} {B = B} f g = Σ A (λ x → Σ B (λ y → Id (f x) (g y)))

π₁ : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {g : B → X} → canonical-pullback f g → A
π₁ = pr1

π₂ : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {g : B → X} → canonical-pullback f g → B
π₂ t = pr1 (pr2 t)

π₃ : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {f : A → X}
  {g : B → X} → (f ∘ (π₁ {f = f} {g = g})) ~ (g ∘ (π₂ {f = f} {g = g}))
π₃ t = pr2 (pr2 t)

cone-canonical-pullback : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → cone f g (canonical-pullback f g)
cone-canonical-pullback f g = dpair π₁ (dpair π₂ π₃)

universal-property-pullback-canonical-pullback : {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X) →
  universal-property-pullback {l5 = l4} f g (canonical-pullback f g)
    (cone-canonical-pullback f g)
universal-property-pullback-canonical-pullback f g C =
  is-equiv-comp
    ( cone-map f g (cone-canonical-pullback f g))
    ( tot (λ p → choice-∞))
    ( mapping-into-Σ)
    ( htpy-refl (cone-map f g (cone-canonical-pullback f g)))
    ( is-equiv-mapping-into-Σ)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ p → choice-∞)
      ( λ p → is-equiv-choice-∞))

\end{code}
