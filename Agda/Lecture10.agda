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
cone-map f g c h =
  dpair
    ( (pr1 c) ∘ h)
    ( dpair
      ( (pr1 (pr2 c)) ∘ h)
      ( htpy-right-whisk (pr2 (pr2 c)) h))

universal-property-pullback : {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (f : A → X) (g : B → X) {C : UU l4} → cone f g C → UU _
universal-property-pullback {l5 = l5} f g cone-f-g-C =
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

Eq-cone-eq-cone' : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c c' : cone f g C)
  (α : Id (pr1 c) (pr1 c')) →
  Id (tr (λ p → Σ (C → B) (λ q' → (f ∘ p) ~ (g ∘ q'))) α (pr2 c)) (pr2 c') →
  Σ ((pr1 (pr2 c)) ~ (pr1 (pr2 c')))
    (λ L → ((pr2 (pr2 c)) ∙h (htpy-left-whisk g L)) ~
      ((htpy-left-whisk f (htpy-eq α)) ∙h (pr2 (pr2 c'))))
Eq-cone-eq-cone' f g (dpair p qH) (dpair .p .qH) refl refl =
  dpair (htpy-refl (pr1 qH)) (htpy-right-unit (pr2 qH))

Eq-cone-eq-cone : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c c' : cone f g C) →
  Id c c' → Eq-cone f g c c'
Eq-cone-eq-cone f g c .c refl =
  dpair
    ( htpy-refl (pr1 c))
    ( dpair
      ( htpy-refl (pr1 (pr2 c)))
      ( htpy-right-unit (pr2 (pr2 c))))

is-contr-total-Eq-structure : {l1 l2 l3 l4 : Level}
  { A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( D : (t : Σ A B) → C (pr1 t) → UU l4) →
  ( is-contr-AC : is-contr (Σ A C)) → (t : Σ A C) →
  is-contr (Σ (B (pr1 t)) (λ y → D (dpair (pr1 t) y) (pr2 t))) →
  is-contr (Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D t)))
is-contr-total-Eq-structure {A = A} {B = B} {C = C} D is-contr-AC t is-contr-BD =
  is-contr-is-equiv
    ( Σ A (λ x → Σ (B x) (λ y → Σ (C x) (λ z → D (dpair x y) z))))
    ( Σ-assoc A B (λ t → Σ (C (pr1 t)) (D t)))
    ( is-equiv-Σ-assoc A B (λ t → Σ (C (pr1 t)) (D t)))
    ( is-contr-is-equiv
      ( Σ A (λ x → Σ (C x) (λ z → Σ (B x) (λ y → D (dpair x y) z))))
      ( tot (λ x → Σ-swap (B x) (C x) (λ y → D (dpair x y))))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ x → is-equiv-Σ-swap (B x) (C x) (λ y → D (dpair x y))))
      ( is-contr-is-equiv
        ( Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y →
          D (dpair (pr1 t) y) (pr2 t))))
        ( inv-is-equiv (is-equiv-Σ-assoc A C (λ t → Σ (B (pr1 t)) (λ y →
          D (dpair (pr1 t) y) (pr2 t)))))
        ( is-equiv-inv-is-equiv (is-equiv-Σ-assoc A C
          ( λ t → Σ (B (pr1 t)) (λ y →
            D (dpair (pr1 t) y) (pr2 t)))))
        ( is-contr-is-equiv
          ( Σ (B (pr1 t)) (λ y →
            D ( dpair (pr1 t) y)
              ( pr2 t)))
          ( left-unit-law-Σ-map-conv
            ( λ t → Σ (B (pr1 t)) (λ y → D (dpair (pr1 t) y) (pr2 t)))
            ( dpair t (λ t' →
              ( inv (contraction is-contr-AC t)) ∙
              ( contraction is-contr-AC t'))))
          ( is-equiv-left-unit-law-Σ-map-conv
            ( λ t → Σ (B (pr1 t)) (λ y → D (dpair (pr1 t) y) (pr2 t)))
            ( dpair t (λ t' →
              ( inv (contraction is-contr-AC t)) ∙
              ( contraction is-contr-AC t'))))
          ( is-contr-BD))))

is-contr-total-Eq-cone : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C) →
  is-contr (Σ (cone f g C) (Eq-cone f g c))
is-contr-total-Eq-cone {A = A} {B} f g {C} c =
  let p = (pr1 c)
      q = (pr1 (pr2 c))
      H = (pr2 (pr2 c))
  in
  is-contr-total-Eq-structure
    ( λ t (K : p ~ (pr1 t)) →
      Σ ( q ~ (pr1 (pr2 t)))
        ( λ L →
          ( H ∙h (htpy-left-whisk g L)) ~
            ( (htpy-left-whisk f K) ∙h (pr2 (pr2 t)))))
    ( is-contr-total-htpy-nondep p)
    ( dpair p (htpy-refl p))
    ( is-contr-total-Eq-structure
      ( λ t (L : q ~ (pr1 t)) → (H ∙h (htpy-left-whisk g L)) ~ (pr2 t))
      ( is-contr-total-htpy-nondep q)
      ( dpair q (htpy-refl q))
      ( is-contr-is-equiv'
          ( Σ ((f ∘ p) ~ (g ∘ q)) (λ H' → H ~ H'))
          ( tot (λ H' → htpy-concat H {h = H'} (htpy-right-unit H)))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ H' → is-equiv-htpy-concat (htpy-right-unit H) H'))
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
      
eq-cone-Eq-cone : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {g : B → X} {C : UU l4} (c c' : cone f g C) →
  Eq-cone f g c c' → Id c c'
eq-cone-Eq-cone {f = f} {g = g} c c' =
  inv-is-equiv (is-fiberwise-equiv-Eq-cone-eq-cone f g c c')
 
is-contr-universal-property-pullback : {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  {B : UU l2} {C : UU l3} {X : UU l4} (f : A → X) (g : B → X)
  (c : cone f g C) → universal-property-pullback {l5 = l5} f g c →
  (C' : UU l5) (c' : cone f g C') →
  is-contr (Σ (C' → C) (λ h → Eq-cone f g (cone-map f g c h) c'))
is-contr-universal-property-pullback {C = C} f g c up C' c' =
  is-contr-is-equiv'
    ( Σ (C' → C) (λ h → Id (cone-map f g c h) c'))
    ( tot (λ h → Eq-cone-eq-cone f g (cone-map f g c h) c'))
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ h → is-fiberwise-equiv-Eq-cone-eq-cone f g (cone-map f g c h) c'))
    ( is-contr-map-is-equiv (up C')  c')

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
  universal-property-pullback {l5 = l4} f g (cone-canonical-pullback f g)
universal-property-pullback-canonical-pullback f g C =
  is-equiv-comp
    ( cone-map f g (cone-canonical-pullback f g))
    ( tot (λ p → choice-∞))
    ( mapping-into-Σ)
    ( htpy-refl (cone-map f g (cone-canonical-pullback f g)))
    ( is-equiv-mapping-into-Σ)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ p → is-equiv-choice-∞))

triangle-cone-cone : {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
  {f : A → X} {g : B → X} (c : cone f g C) (c' : cone f g C')
  (h : C' → C) (KLM : Eq-cone f g (cone-map f g c h) c') (D : UU l6) →
  (cone-map f g {C' = D} c') ~ ((cone-map f g c) ∘ (λ (k : D → C') → h ∘ k))
triangle-cone-cone {C' = C'} {f = f} {g = g} c c' h KLM D k = 
  inv (ap
    ( λ t → cone-map f g {C' = D} t k)
    { x = (cone-map f g c h)}
    { y = c'}
    ( eq-cone-Eq-cone (cone-map f g c h) c' KLM))
 
is-equiv-up-pullback-up-pullback : {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
  (f : A → X) (g : B → X) (c : cone f g C) (c' : cone f g C')
  (h : C' → C) (KLM : Eq-cone f g (cone-map f g c h) c') →
  ({l6 : Level} → universal-property-pullback {l5 = l6} f g c) →
  ({l6 : Level} → universal-property-pullback {l5 = l6} f g c') →
  is-equiv h
is-equiv-up-pullback-up-pullback {C = C} {C' = C'} f g c c' h KLM up up' =
  is-equiv-is-equiv-postcomp h
    ( λ D → is-equiv-right-factor
      ( cone-map f g {C' = D} c')
      ( cone-map f g c)
      ( λ (k : D → C') → h ∘ k)
      ( triangle-cone-cone {C = C} {C' = C'} {f = f} {g = g} c c' h KLM D)
      ( up D) (up' D))

up-pullback-up-pullback-is-equiv : {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
  (f : A → X) (g : B → X) (c : cone f g C) (c' : cone f g C')
  (h : C' → C) (KLM : Eq-cone f g (cone-map f g c h) c') → is-equiv h →
  ({l6 : Level} → universal-property-pullback {l5 = l6} f g c) →
  ({l6 : Level} → universal-property-pullback {l5 = l6} f g c')
up-pullback-up-pullback-is-equiv f g c c' h KLM is-equiv-h up D =
  is-equiv-comp
    ( cone-map f g c')
    ( cone-map f g c)
    ( λ k → h ∘ k)
    ( triangle-cone-cone {f = f} {g = g} c c' h KLM D)
    ( is-equiv-postcomp-is-equiv h is-equiv-h D)
    ( up D)

up-pullback-is-equiv-up-pullback : {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
  (f : A → X) (g : B → X) (c : cone f g C) (c' : cone f g C')
  (h : C' → C) (KLM : Eq-cone f g (cone-map f g c h) c') →
  ({l6 : Level} → universal-property-pullback {l5 = l6} f g c') →
  is-equiv h →
  ({l6 : Level} → universal-property-pullback {l5 = l6} f g c)
up-pullback-is-equiv-up-pullback f g c c' h KLM up' is-equiv-h D =
  is-equiv-left-factor
    ( cone-map f g c')
    ( cone-map f g c)
    ( λ k → h ∘ k)
    ( triangle-cone-cone {f = f} {g = g} c c' h KLM D)
    ( up' D)
    ( is-equiv-postcomp-is-equiv h is-equiv-h D)

uniquely-unique-pullback : {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
  (f : A → X) (g : B → X) (c : cone f g C) (c' : cone f g C') →
  ({l6 : Level} → universal-property-pullback {l5 = l6} f g c') →
  ({l6 : Level} → universal-property-pullback {l5 = l6} f g c) →
  is-contr (Σ (C' ≃ C) (λ h → Eq-cone f g (cone-map f g c (eqv-map h)) c'))
uniquely-unique-pullback {C = C} {C' = C'} f g c c' up up' =
  is-contr-is-equiv
    ( Σ (C' → C) (λ h → (is-equiv h) × (Eq-cone f g (cone-map f g c h) c')))
    ( Σ-assoc
      ( C' → C)
      ( is-equiv)
      ( λ t → Eq-cone f g (cone-map f g c (eqv-map t)) c'))
    ( is-equiv-Σ-assoc
      ( C' → C)
      ( is-equiv)
      ( λ t → Eq-cone f g (cone-map f g c (eqv-map t)) c'))
    ( is-contr-is-equiv
      ( Σ (C' → C) (λ h → (Eq-cone f g (cone-map f g c h) c') × (is-equiv h)))
      ( tot
        ( λ h → swap-prod (is-equiv h) (Eq-cone f g (cone-map f g c h) c')))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h → is-equiv-swap-prod
          ( is-equiv h)
          ( Eq-cone f g (cone-map f g c h) c')))
      ( is-contr-is-equiv'
        ( Σ (Σ (C' → C) (λ h → Eq-cone f g (cone-map f g c h) c'))
          ( λ t → is-equiv (pr1 t)))
        ( Σ-assoc
          ( C' → C)
          ( λ h → Eq-cone f g (cone-map f g c h) c')
          ( λ t → is-equiv (pr1 t)))
        ( is-equiv-Σ-assoc _ _ _)
        ( is-contr-is-equiv
          ( Σ (C' → C) (λ h → Eq-cone f g (cone-map f g c h) c'))
          ( pr1)
          ( is-equiv-pr1-is-contr
            ( λ t → is-equiv (pr1 t))
            ( λ t → is-contr-is-equiv-is-equiv
              ( is-equiv-up-pullback-up-pullback f g c c'
                (pr1 t) (pr2 t) up' up)))
          ( is-contr-universal-property-pullback f g c up' C' c'))))

gap : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) → cone f g C → C → canonical-pullback f g
gap f g c z = dpair ((pr1 c) z) (dpair ((pr1 (pr2 c)) z) ((pr2 (pr2 c)) z))

is-pullback : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {C : UU l4} (f : A → X) (g : B → X) → cone f g C → UU _
is-pullback f g c = is-equiv (gap f g c)

Eq-cone-up-pullback-canonical-pullback : {l1 l2 l3 l4 : Level} {A : UU l1}
  {B : UU l2} {X : UU l3} {C : UU l4} (f : A → X) (g : B → X)
  (c : cone f g C) →
  Eq-cone f g (cone-map f g (cone-canonical-pullback f g) (gap f g c)) c
Eq-cone-up-pullback-canonical-pullback f g c =
  dpair
    ( htpy-refl (pr1 c))
    ( dpair
      ( htpy-refl (pr1 (pr2 c)))
      ( htpy-right-unit (pr2 (pr2 c))))
 
is-pullback-up-pullback : {l1 l2 l3 l4 : Level} {A : UU l1}
  {B : UU l2} {X : UU l3} {C : UU l4} (f : A → X) (g : B → X)
  (c : cone f g C) →
  ({l5 : Level} → universal-property-pullback {l5 = l5} f g c) →
  is-pullback f g c
is-pullback-up-pullback f g c up =
  is-equiv-up-pullback-up-pullback f g
    ( cone-canonical-pullback f g)
    ( c)
    ( gap f g c)
    ( Eq-cone-up-pullback-canonical-pullback f g c)
    ( universal-property-pullback-canonical-pullback f g)
    ( up)

up-pullback-is-pullback : {l1 l2 l3 l4 : Level} {A : UU l1}
  {B : UU l2} {X : UU l3} {C : UU l4} (f : A → X) (g : B → X)
  (c : cone f g C) →
  is-pullback f g c →
  ({l5 : Level} → universal-property-pullback {l5 = l5} f g c)
up-pullback-is-pullback f g c is-pullback-c =
  up-pullback-up-pullback-is-equiv f g
    ( cone-canonical-pullback f g)
    ( c)
    ( gap f g c)
    ( Eq-cone-up-pullback-canonical-pullback f g c)
    ( is-pullback-c)
    ( universal-property-pullback-canonical-pullback f g)

-- Section 10.3 Fiber products

cone-prod : {i j : Level} (A : UU i) (B : UU j) →
  cone (const A unit star) (const B unit star) (A × B)
cone-prod A B = dpair pr1 (dpair pr2 (htpy-refl (const (A × B) unit star)))

is-pullback-prod : {i j : Level} (A : UU i) (B : UU j) →
  is-pullback (const A unit star) (const B unit star) (cone-prod A B)
is-pullback-prod A B =
  is-equiv-has-inverse
    ( dpair
      ( λ t → dpair (pr1 t) (pr1 (pr2 t)))
      ( dpair
        ( λ t → eq-pair (dpair refl
          ( eq-pair (dpair refl
            ( center (is-prop-is-contr
              ( is-prop-is-contr is-contr-unit star star)
                refl (pr2 (pr2 t))))))))
        ( λ t → eq-pair (dpair refl refl))))

universal-property-pullback-prod : {i j : Level} (A : UU i) (B : UU j) →
  {k : Level} → universal-property-pullback {l5 = k}
    ( const A unit star)
    ( const B unit star)
    ( cone-prod A B)
universal-property-pullback-prod A B =
  up-pullback-is-pullback
    ( const A unit star)
    ( const B unit star)
    ( cone-prod A B)
    ( is-pullback-prod A B)

cone-fiberwise-prod : {l1 l2 l3 : Level} {X : UU l1} (P : X → UU l2)
  (Q : X → UU l3) →
  cone (pr1 {A = X} {B = P}) (pr1 {A = X} {B = Q}) (Σ X (λ x → (P x) × (Q x)))
cone-fiberwise-prod P Q =
  dpair
    ( tot (λ x → pr1))
    ( dpair
      ( tot (λ x → pr2))
      ( htpy-refl pr1))

inv-gap-fiberwise-prod : {l1 l2 l3 : Level} {X : UU l1} (P : X → UU l2)
  (Q : X → UU l3) → canonical-pullback (pr1 {B = P}) (pr1 {B = Q}) →
  Σ X (λ x → (P x) × (Q x))
inv-gap-fiberwise-prod P Q (dpair (dpair x p) (dpair (dpair .x q) refl)) =
  dpair x (dpair p q)

issec-inv-gap-fiberwise-prod : {l1 l2 l3 : Level} {X : UU l1} (P : X → UU l2)
  (Q : X → UU l3) →
  ((gap (pr1 {B = P}) (pr1 {B = Q}) (cone-fiberwise-prod P Q)) ∘
  (inv-gap-fiberwise-prod P Q)) ~ id
issec-inv-gap-fiberwise-prod P Q (dpair (dpair x p) (dpair (dpair .x q) refl)) =
  eq-pair (dpair refl (eq-pair (dpair refl refl)))

isretr-inv-gap-fiberwise-prod : {l1 l2 l3 : Level} {X : UU l1} (P : X → UU l2)
  (Q : X → UU l3) →
  ((inv-gap-fiberwise-prod P Q) ∘
  (gap (pr1 {B = P}) (pr1 {B = Q}) (cone-fiberwise-prod P Q))) ~ id
isretr-inv-gap-fiberwise-prod P Q (dpair x (dpair p q)) = refl

is-pullback-fiberwise-prod : {l1 l2 l3 : Level} {X : UU l1} (P : X → UU l2)
  (Q : X → UU l3) →
  is-pullback (pr1 {A = X} {B = P}) (pr1 {A = X} {B = Q})
    (cone-fiberwise-prod P Q)
is-pullback-fiberwise-prod P Q =
  is-equiv-has-inverse
    ( dpair
      ( inv-gap-fiberwise-prod P Q)
      ( dpair
        ( issec-inv-gap-fiberwise-prod P Q)
        ( isretr-inv-gap-fiberwise-prod P Q)))

universal-property-pullback-fiberwise-prod : {l1 l2 l3 l4 : Level}
  {X : UU l1} (P : X → UU l2) (Q : X → UU l3) →
  universal-property-pullback {l5 = l4} (pr1 {B = P}) (pr1 {B = Q})
    (cone-fiberwise-prod P Q)
universal-property-pullback-fiberwise-prod P Q =
  up-pullback-is-pullback pr1 pr1
    ( cone-fiberwise-prod P Q)
    ( is-pullback-fiberwise-prod P Q)

cone-total-prod-fibers : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → cone f g (Σ X (λ x → (fib f x) × (fib g x)))
cone-total-prod-fibers f g =
  dpair
    ( λ t → pr1 (pr1 (pr2 t)))
    ( dpair
      ( λ t → pr1 (pr2 (pr2 t)))
       λ t → concat (pr1 t) (pr2 (pr1 (pr2 t))) (inv (pr2 (pr2 (pr2 t)))))

cone-span : {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l4} {B' : UU l5} {C : A' → B' → UU l6}
  (i : A' → A) (j : B' → B)
  (k : (x : A') (y : B') → C x y → Id (f (i x)) (g (j y))) →
  cone f g (Σ A' (λ x → Σ B' (C x)))
cone-span f g i j k =
  dpair
    ( λ t → i (pr1 t))
    ( dpair
      ( λ t → j (pr1 (pr2 t)))
      ( λ t → k (pr1 t) (pr1 (pr2 t)) (pr2 (pr2 t))))

is-pullback-cone-span-is-equiv : {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l4} {B' : UU l5} {C : A' → B' → UU l6}
  (i : A' → A) (j : B' → B)
  (k : (x' : A') (y' : B') → C x' y' → Id (f (i x')) (g (j y'))) →
  is-equiv i → is-equiv j → ((x : A') (y : B') → is-equiv (k x y)) →
  is-pullback f g (cone-span f g i j k)
is-pullback-cone-span-is-equiv {B = B} f g i j k is-equiv-i is-equiv-j is-equiv-k =
  is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map
    ( λ x → Σ B (λ y → Id (f x) (g y)))
    ( i)
    ( λ x' → toto (λ y → Id (f (i x')) (g y)) j (k x'))
    ( is-equiv-i)
    ( λ x' → is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map
      ( λ y → Id (f (i x')) (g y))
      ( j)
      ( k x')
      ( is-equiv-j)
      ( is-equiv-k x'))

is-pullback-total-prod-fibers : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (f : A → X) (g : B → X) →
  is-pullback f g (cone-total-prod-fibers f g)
is-pullback-total-prod-fibers f g =
  is-equiv-comp
    ( gap f g (cone-total-prod-fibers f g))
    ( gap f g
      (cone-span f g
        ( Σ-fib-to-domain f)
        ( Σ-fib-to-domain g)
        ( λ s t α → (pr2 (pr2 s)) ∙ (α ∙ (inv (pr2 (pr2 t)))))))
    ( gap
      ( pr1 {B = fib f})
      ( pr1 {B = fib g})
      ( cone-fiberwise-prod (fib f) (fib g)))
    ( λ t → refl)
    ( is-pullback-fiberwise-prod (fib f) (fib g))
    ( is-pullback-cone-span-is-equiv f g
      ( Σ-fib-to-domain f)
      ( Σ-fib-to-domain g)
      ( λ s t α → (pr2 (pr2 s)) ∙ (α ∙ (inv (pr2 (pr2 t)))))
      ( is-equiv-Σ-fib-to-domain f)
      ( is-equiv-Σ-fib-to-domain g)
      ( λ s t → is-equiv-comp _
        ( concat (pr1 s) (pr2 (pr2 s)))
        ( concat' (pr1 t) (inv (pr2 (pr2 t))))
        ( htpy-refl _)
        ( is-equiv-concat' (pr1 s) (inv (pr2 (pr2 t))))
        ( is-equiv-concat (pr2 (pr2 s)) (g (pr1 (pr2 t))))))

-- Section 10.4 Fibers as pullbacks

square-fiber : {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B) →
  (f ∘ (pr1 {B = λ x → Id (f x) b})) ~
  ((const unit B b) ∘ (const (fib f b) unit star))
square-fiber f b = pr2

cone-fiber : {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B) →
  cone f (const unit B b) (fib f b)
cone-fiber f b =
  dpair pr1 (dpair (const (fib f b) unit star) (square-fiber f b))

is-pullback-cone-fiber : {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (b : B) → is-pullback f (const unit B b) (cone-fiber f b)
is-pullback-cone-fiber f b =
  is-equiv-tot-is-fiberwise-equiv
    ( λ a → is-equiv-left-unit-law-Σ-map (λ t → Id (f a) b) is-contr-unit)

universal-property-pullback-cone-fiber : {l1 l2 l3 : Level} {A : UU l1} →
  {B : UU l2} (f : A → B) (b : B) →
  universal-property-pullback {l5 = l3} f (const unit B b) (cone-fiber f b)
universal-property-pullback-cone-fiber {B = B} f b =
  up-pullback-is-pullback f (const unit B b)
    ( cone-fiber f b)
    ( is-pullback-cone-fiber f b)

cone-fiber-fam : {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A) →
  cone (pr1 {B = B}) (const unit A a) (B a)
cone-fiber-fam B a =
  dpair (λ b → dpair a b) (dpair (const (B a) unit star) (λ b → refl))

is-pullback-cone-fiber-fam : {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
 (a : A) → is-pullback (pr1 {B = B}) (const unit A a) (cone-fiber-fam B a)
is-pullback-cone-fiber-fam {A = A} B a =
  is-equiv-comp
    ( gap (pr1 {B = B}) (const unit A a) (cone-fiber-fam B a))
    ( gap (pr1 {B = B}) (const unit A a) (cone-fiber (pr1 {B = B}) a))
    ( fib-pr1-fib-fam B a)
    ( λ y → refl)
    ( is-equiv-fib-pr1-fib-fam B a)
    ( is-pullback-cone-fiber pr1 a)

-- Section 10.5 Fiberwise equivalences

cone-subst : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (Q : B → UU l3) → cone f (pr1 {B = Q}) (Σ A (λ x → Q (f x)))
cone-subst f Q = dpair pr1 (dpair (Σ-map-base-map f Q) (λ t → refl))

inv-gap-cone-subst : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (Q : B → UU l3) →
  canonical-pullback f (pr1 {B = Q}) → Σ A (λ x → Q (f x))
inv-gap-cone-subst f Q (dpair x (dpair (dpair .(f x) q) refl)) = dpair x q

issec-inv-gap-cone-subst : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (Q : B → UU l3) →
  ((gap f (pr1 {B = Q}) (cone-subst f Q)) ∘ (inv-gap-cone-subst f Q)) ~ id
issec-inv-gap-cone-subst f Q (dpair x (dpair (dpair .(f x) q) refl)) = refl

isretr-inv-gap-cone-subst : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (Q : B → UU l3) →
  ((inv-gap-cone-subst f Q) ∘ (gap f (pr1 {B = Q}) (cone-subst f Q))) ~ id
isretr-inv-gap-cone-subst f Q (dpair x q) = refl

is-pullback-cone-subst : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (Q : B → UU l3) → is-pullback f (pr1 {B = Q}) (cone-subst f Q)
is-pullback-cone-subst f Q =
  is-equiv-has-inverse
    ( dpair
      ( inv-gap-cone-subst f Q)
      ( dpair
        ( issec-inv-gap-cone-subst f Q)
        ( isretr-inv-gap-cone-subst f Q)))

cone-toto : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3}
  (Q : B → UU l4) (f : A → B) (g : (x : A) → (P x) → (Q (f x))) →
  cone f (pr1 {B = Q}) (Σ A P)
cone-toto Q f g = dpair pr1 (dpair (toto Q f g) (λ t → refl))

is-pullback-is-fiberwise-equiv : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {P : A → UU l3} (Q : B → UU l4) (f : A → B)
  (g : (x : A) → (P x) → (Q (f x))) →
  is-fiberwise-equiv g → is-pullback f (pr1 {B = Q}) (cone-toto Q f g)
is-pullback-is-fiberwise-equiv Q f g is-equiv-g =
  is-equiv-comp
    ( gap f pr1 (cone-toto Q f g))
    ( gap f pr1 (cone-subst f Q))
    ( tot g)
    ( λ t → refl)
    ( is-equiv-tot-is-fiberwise-equiv is-equiv-g)
    ( is-pullback-cone-subst f Q)

universal-property-pullback-is-fiberwise-equiv : {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {P : A → UU l3} (Q : B → UU l4) (f : A → B)
  (g : (x : A) → (P x) → (Q (f x))) →
  is-fiberwise-equiv g →
  universal-property-pullback {l5 = l5} f (pr1 {B = Q}) (cone-toto Q f g)
universal-property-pullback-is-fiberwise-equiv Q f g is-equiv-g =
  up-pullback-is-pullback f pr1 (cone-toto Q f g)
    ( is-pullback-is-fiberwise-equiv Q f g is-equiv-g)

is-fiberwise-equiv-is-pullback : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {P : A → UU l3} (Q : B → UU l4) (f : A → B)
  (g : (x : A) → (P x) → (Q (f x))) →
  is-pullback f (pr1 {B = Q}) (cone-toto Q f g) → is-fiberwise-equiv g
is-fiberwise-equiv-is-pullback Q f g is-pullback-cone-toto =
  is-fiberwise-equiv-is-equiv-tot g
    ( is-equiv-right-factor
      ( gap f pr1 (cone-toto Q f g))
      ( gap f pr1 (cone-subst f Q))
      ( tot g)
      ( λ t → refl)
      ( is-pullback-cone-subst f Q)
      ( is-pullback-cone-toto))

is-fiberwise-equiv-universal-property-pullback : {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {P : A → UU l3} (Q : B → UU l4) (f : A → B)
  (g : (x : A) → (P x) → (Q (f x))) →
  ( {l5 : Level} → universal-property-pullback {l5 = l5} f (pr1 {B = Q})
    (cone-toto Q f g)) →
  is-fiberwise-equiv g
is-fiberwise-equiv-universal-property-pullback Q f g up =
  is-fiberwise-equiv-is-pullback Q f g
    ( is-pullback-up-pullback f pr1 (cone-toto Q f g) up)

fib-square : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C) → (x : A) → fib (pr1 c) x → fib g (f x)
fib-square f g c x t =
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  dpair (q (pr1 t) ) (concat (f (p (pr1 t))) (inv (H (pr1 t))) (ap f (pr2 t)))

square-tot-fib-square : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {C : UU l3} {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C) →
  ((gap f g c) ∘ (Σ-fib-to-domain (pr1 c))) ~
  ((tot (λ a → tot (λ b → inv))) ∘ (tot (fib-square f g c)))
square-tot-fib-square f g c (dpair .((pr1 c) x) (dpair x refl)) =
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  eq-pair
    ( dpair refl
      ( eq-pair
        ( dpair refl
          ( inv
            ( concat
              ( inv (inv (H x)))
              ( ap inv (right-unit (inv (H x))))
              ( inv-inv (H x)))))))

is-fiberwise-equiv-fib-square-is-pullback : {l1 l2 l3 l4 : Level} {A : UU l1}
  {B : UU l2} {C : UU l3} {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C) →
  is-pullback f g c → is-fiberwise-equiv (fib-square f g c)
is-fiberwise-equiv-fib-square-is-pullback f g c pb =
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  is-fiberwise-equiv-is-equiv-tot
    ( fib-square f g c)
    ( is-equiv-top-is-equiv-bottom-square
      ( Σ-fib-to-domain p)
      ( tot (λ x → tot (λ y → inv)))
      ( tot (fib-square f g c))
      ( gap f g c)
      ( square-tot-fib-square f g c)
      ( is-equiv-Σ-fib-to-domain p)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ x → is-equiv-tot-is-fiberwise-equiv
          ( λ y → is-equiv-inv (g y) (f x))))
      ( pb))

is-pullback-is-fiberwise-equiv-fib-square : {l1 l2 l3 l4 : Level} {A : UU l1}
  {B : UU l2} {C : UU l3} {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C) →
  is-fiberwise-equiv (fib-square f g c) → is-pullback f g c
is-pullback-is-fiberwise-equiv-fib-square f g c is-equiv-fsq =
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  is-equiv-bottom-is-equiv-top-square
    ( Σ-fib-to-domain p)
    ( tot (λ x → tot (λ y → inv)))
    ( tot (fib-square f g c))
    ( gap f g c)
    ( square-tot-fib-square f g c)
    ( is-equiv-Σ-fib-to-domain p)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ x → is-equiv-tot-is-fiberwise-equiv
        ( λ y → is-equiv-inv (g y) (f x))))
    ( is-equiv-tot-is-fiberwise-equiv is-equiv-fsq)

is-trunc-is-pullback : {l1 l2 l3 l4 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  {C : UU l3} {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C) →
  is-pullback f g c → is-trunc-map k g → is-trunc-map k (pr1 c)
is-trunc-is-pullback k f g c pb is-trunc-g a =
  is-trunc-is-equiv k
    ( fib g (f a))
    ( fib-square f g c a)
    ( is-fiberwise-equiv-fib-square-is-pullback f g c pb a)
    (is-trunc-g (f a))

is-emb-is-pullback : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {C : UU l3} {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C) →
  is-pullback f g c → is-emb g → is-emb (pr1 c)
is-emb-is-pullback f g c pb is-emb-g =
  is-emb-is-prop-map
    ( pr1 c)
    ( is-trunc-is-pullback neg-one-𝕋 f g c pb (is-prop-map-is-emb g is-emb-g))

is-equiv-is-pullback : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {C : UU l3} {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C) →
  is-equiv g → is-pullback f g c → is-equiv (pr1 c)
is-equiv-is-pullback f g c is-equiv-g pb =
  is-equiv-is-contr-map
    ( is-trunc-is-pullback neg-two-𝕋 f g c pb
      ( is-contr-map-is-equiv is-equiv-g))

is-pullback-is-equiv : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {C : UU l3} {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C) →
  is-equiv g → is-equiv (pr1 c) → is-pullback f g c
is-pullback-is-equiv f g c is-equiv-g is-equiv-p =
  is-pullback-is-fiberwise-equiv-fib-square f g c
    ( λ a → is-equiv-is-contr
      ( fib-square f g c a)
      ( is-contr-map-is-equiv is-equiv-p a)
      ( is-contr-map-is-equiv is-equiv-g (f a)))

-- Section 10.6 The pullback pasting property

htpy-square-comp-horizontal : {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  {f : A → X} {g : B → Y} {h : C → Z} {i : X → Y} {j : Y → Z} {k : A → B}
  {l : B → C} → ((i ∘ f) ~ (g ∘ k)) → ((j ∘ g) ~ (h ∘ l)) →
  ((j ∘ (i ∘ f)) ~ (h ∘ (l ∘ k)))
htpy-square-comp-horizontal {g = g} {j = j} {k = k} H K =
  htpy-concat (j ∘ (g ∘ k)) (htpy-left-whisk j H) (htpy-right-whisk K k)

cone-comp-horizontal : {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z) →
  (c : cone j h B) → (cone i (pr1 c) A) → cone (j ∘ i) h A
cone-comp-horizontal i j h c d =
  dpair
   ( pr1 d)
   ( dpair
     ( (pr1 (pr2 c)) ∘ (pr1 (pr2 d)))
     ( htpy-square-comp-horizontal
       {f = pr1 d} {g = pr1 c} {h = h} {i = i} {j = j} {k = pr1 (pr2 d)}
       (pr2 (pr2 d)) (pr2 (pr2 c))))

triangle-fib-square : {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z) →
  (c : cone j h B) (d : cone i (pr1 c) A) → (x : X) →
  ((fib-square (j ∘ i) h (cone-comp-horizontal i j h c d) x) ~
    ((fib-square j h c (i x)) ∘ (fib-square i (pr1 c) d x)))
triangle-fib-square i j h c d .(pr1 d a) (dpair a refl) =
  let f = pr1 d
      k = pr1 (pr2 d)
      H = pr2 (pr2 d)
      g = pr1 c
      l = pr1 (pr2 c)
      K = pr2 (pr2 c)
  in
  eq-pair (dpair refl
    ( concat
      ( ((inv (K (k a))) ∙ (inv (ap j (H a)))) ∙ refl)
      ( ap (concat' _ refl) (inv-assoc (ap j (H a)) (K (k a))))
      ( concat ((inv (K (k a))) ∙ ((inv (ap j (H a))) ∙ refl))
        ( inv (assoc (inv (K (k a))) (inv (ap j (H a))) refl))
        ( ap (concat _ (inv (K (k a))))
          ( concat
            ( (ap j (inv (H a))) ∙ refl)
            ( ap (concat' _ refl) (inv (ap-inv j (H a))))
            ( inv (ap-concat j (inv (H a)) refl)))))))

is-pullback-rectangle-is-pullback-left-square : {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  (c : cone j h B) (d : cone i (pr1 c) A) →
  is-pullback j h c → is-pullback i (pr1 c) d →
  is-pullback (j ∘ i) h (cone-comp-horizontal i j h c d)
is-pullback-rectangle-is-pullback-left-square i j h c d is-pb-c is-pb-d =
  is-pullback-is-fiberwise-equiv-fib-square (j ∘ i) h
    ( cone-comp-horizontal i j h c d)
    ( λ x → is-equiv-comp
      ( fib-square (j ∘ i) h (cone-comp-horizontal i j h c d) x)
      ( fib-square j h c (i x))
      ( fib-square i (pr1 c) d x)
      ( triangle-fib-square i j h c d x)
      ( is-fiberwise-equiv-fib-square-is-pullback i (pr1 c) d is-pb-d x)
      ( is-fiberwise-equiv-fib-square-is-pullback j h c is-pb-c (i x)))

is-pullback-left-square-is-pullback-rectangle : {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  (c : cone j h B) (d : cone i (pr1 c) A) →
  is-pullback j h c → is-pullback (j ∘ i) h (cone-comp-horizontal i j h c d) →
  is-pullback i (pr1 c) d
is-pullback-left-square-is-pullback-rectangle i j h c d is-pb-c is-pb-rect =
  is-pullback-is-fiberwise-equiv-fib-square i (pr1 c) d
    ( λ x → is-equiv-right-factor
      ( fib-square (j ∘ i) h (cone-comp-horizontal i j h c d) x)
      ( fib-square j h c (i x))
      ( fib-square i (pr1 c) d x)
      ( triangle-fib-square i j h c d x)
      ( is-fiberwise-equiv-fib-square-is-pullback j h c is-pb-c (i x))
      ( is-fiberwise-equiv-fib-square-is-pullback (j ∘ i) h
        ( cone-comp-horizontal i j h c d) is-pb-rect x))

-- Section 10.7 Descent for coproducts and Σ-types

fib-functor-coprod-inl-fib : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (x : A) →
  fib f x → fib (functor-coprod f g) (inl x)
fib-functor-coprod-inl-fib f g x (dpair a' p) =
  dpair (inl a') (ap inl p)

fib-fib-functor-coprod-inl : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (x : A) →
  fib (functor-coprod f g) (inl x) → fib f x
fib-fib-functor-coprod-inl f g x (dpair (inl a') p) =
  dpair a' (map-compute-eq-coprod-inl-inl (f a') x p)
fib-fib-functor-coprod-inl f g x (dpair (inr b') p) =
  ind-empty {P = λ t → fib f x}
    ( map-compute-eq-coprod-inr-inl (g b') x p)

issec-fib-fib-functor-coprod-inl : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (x : A) →
  ( (fib-functor-coprod-inl-fib f g x) ∘
    ( fib-fib-functor-coprod-inl f g x)) ~ id
issec-fib-fib-functor-coprod-inl f g .(f a') (dpair (inl a') refl) =
  eq-pair (dpair refl
    ( ap (ap inl)
      ( isretr-inv-is-equiv
        ( is-equiv-map-raise _ (Id (f a') (f a'))) refl)))
issec-fib-fib-functor-coprod-inl f g x (dpair (inr b') p) =
  ind-empty
    { P = λ t → Id
      ( fib-functor-coprod-inl-fib f g x
        ( fib-fib-functor-coprod-inl f g x (dpair (inr b') p)))
      ( dpair (inr b') p)}
    ( map-compute-eq-coprod-inr-inl (g b') x p)

isretr-fib-fib-functor-coprod-inl : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (x : A) →
  ( (fib-fib-functor-coprod-inl f g x) ∘
    ( fib-functor-coprod-inl-fib f g x)) ~ id
isretr-fib-fib-functor-coprod-inl f g .(f a') (dpair a' refl) =
  eq-pair (dpair refl
    ( isretr-inv-is-equiv (is-equiv-map-raise _ (Id (f a') (f a'))) refl))

is-equiv-fib-functor-coprod-inl-fib : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (x : A) →
  is-equiv (fib-functor-coprod-inl-fib f g x)
is-equiv-fib-functor-coprod-inl-fib f g x =
  is-equiv-has-inverse (dpair
    ( fib-fib-functor-coprod-inl f g x)
    ( dpair
      ( issec-fib-fib-functor-coprod-inl f g x)
      ( isretr-fib-fib-functor-coprod-inl f g x)))

fib-functor-coprod-inr-fib : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (y : B) →
  fib g y → fib (functor-coprod f g) (inr y)
fib-functor-coprod-inr-fib f g y (dpair b' p) =
  dpair (inr b') (ap inr p)
  
fib-fib-functor-coprod-inr : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (y : B) →
  fib (functor-coprod f g) (inr y) → fib g y
fib-fib-functor-coprod-inr f g y (dpair (inl a') p) =
  ind-empty {P = λ t → fib g y}
    ( map-compute-eq-coprod-inl-inr (f a') y p)
fib-fib-functor-coprod-inr f g y (dpair (inr b') p) =
  dpair b' (map-compute-eq-coprod-inr-inr (g b') y p)

issec-fib-fib-functor-coprod-inr : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (y : B) →
  ( (fib-functor-coprod-inr-fib f g y) ∘
    ( fib-fib-functor-coprod-inr f g y)) ~ id
issec-fib-fib-functor-coprod-inr f g .(g b') (dpair (inr b') refl) =
  eq-pair (dpair refl
    ( ap (ap inr)
      ( isretr-inv-is-equiv
        ( is-equiv-map-raise _ (Id (g b') (g b'))) refl)))
issec-fib-fib-functor-coprod-inr f g y (dpair (inl a') p) =
  ind-empty
    { P = λ t → Id
      ( fib-functor-coprod-inr-fib f g y
        ( fib-fib-functor-coprod-inr f g y (dpair (inl a') p)))
      ( dpair (inl a') p)}
    ( map-compute-eq-coprod-inl-inr (f a') y p)

isretr-fib-fib-functor-coprod-inr : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (y : B) →
  ( (fib-fib-functor-coprod-inr f g y) ∘
    ( fib-functor-coprod-inr-fib f g y)) ~ id
isretr-fib-fib-functor-coprod-inr f g .(g b') (dpair b' refl) =
  eq-pair (dpair refl
    ( isretr-inv-is-equiv (is-equiv-map-raise _ (Id (g b') (g b'))) refl))

is-equiv-fib-functor-coprod-inr-fib : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (y : B) →
  is-equiv (fib-functor-coprod-inr-fib f g y)
is-equiv-fib-functor-coprod-inr-fib f g y =
  is-equiv-has-inverse (dpair
    ( fib-fib-functor-coprod-inr f g y)
    ( dpair
      ( issec-fib-fib-functor-coprod-inr f g y)
      ( isretr-fib-fib-functor-coprod-inr f g y)))

cone-descent-coprod : {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (i : X' → X)
  (cone-A' : cone f i A') (cone-B' : cone g i B') →
  cone (ind-coprod _ f g) i (coprod A' B')
cone-descent-coprod f g i (dpair h (dpair f' H)) (dpair k (dpair g' K)) =
   dpair
     ( functor-coprod h k)
     ( dpair
       ( ind-coprod _ f' g')
       ( ind-coprod _ H K))

triangle-descent-square-fib-functor-coprod-inl-fib :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A' → A) (g : B' → B) (h : X' → X)
  (αA : A → X) (αB : B → X) (αA' : A' → X') (αB' : B' → X')
  (HA : (αA ∘ f) ~ (h ∘ αA')) (HB : (αB ∘ g) ~ (h ∘ αB')) (x : A) →
  (fib-square αA h (dpair f (dpair αA' HA)) x) ~
    ( (fib-square (ind-coprod _ αA αB) h
      ( dpair
        ( functor-coprod f g)
        ( dpair (ind-coprod _ αA' αB') (ind-coprod _ HA HB))) (inl x)) ∘
    ( fib-functor-coprod-inl-fib f g x))
triangle-descent-square-fib-functor-coprod-inl-fib {X = X} {X' = X'} f g h αA αB αA' αB' HA HB x
  ( dpair a' p) = eq-pair (dpair refl
    ( ap (concat (αA (f a')) (inv (HA a')))
      ( ap-comp (ind-coprod _ αA αB) inl p)))

triangle-descent-square-fib-functor-coprod-inr-fib :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A' → A) (g : B' → B) (h : X' → X)
  (αA : A → X) (αB : B → X) (αA' : A' → X') (αB' : B' → X')
  (HA : (αA ∘ f) ~ (h ∘ αA')) (HB : (αB ∘ g) ~ (h ∘ αB')) (y : B) →
  (fib-square αB h (dpair g (dpair αB' HB)) y) ~
    ( (fib-square (ind-coprod _ αA αB) h
      ( dpair
        ( functor-coprod f g)
        ( dpair (ind-coprod _ αA' αB') (ind-coprod _ HA HB))) (inr y)) ∘
    ( fib-functor-coprod-inr-fib f g y))
triangle-descent-square-fib-functor-coprod-inr-fib
  {X = X} {X' = X'} f g h αA αB αA' αB' HA HB y ( dpair b' p) =
  eq-pair (dpair refl
    ( ap (concat (αB (g b')) (inv (HB b')))
      ( ap-comp (ind-coprod _ αA αB) inr p)))
      
descent-coprod : {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (i : X' → X)
  (cone-A' : cone f i A') (cone-B' : cone g i B') →
  is-pullback f i cone-A' →
  is-pullback g i cone-B' →
  is-pullback (ind-coprod _ f g) i (cone-descent-coprod f g i cone-A' cone-B')
descent-coprod f g i (dpair h (dpair f' H)) (dpair k (dpair g' K))
  is-pb-cone-A' is-pb-cone-B' =
  is-pullback-is-fiberwise-equiv-fib-square
    ( ind-coprod _ f g)
    ( i)
    ( cone-descent-coprod f g i (dpair h (dpair f' H)) (dpair k (dpair g' K)))
    ( ind-coprod _
      ( λ x → is-equiv-left-factor
        ( fib-square f i (dpair h (dpair f' H)) x)
        ( fib-square (ind-coprod _ f g) i
          ( dpair (functor-coprod h k)
            ( dpair (ind-coprod _ f' g') (ind-coprod _ H K)))
          ( inl x))
        ( fib-functor-coprod-inl-fib h k x)
        ( triangle-descent-square-fib-functor-coprod-inl-fib
          h k i f g f' g' H K x)
        ( is-fiberwise-equiv-fib-square-is-pullback f i
          ( dpair h (dpair f' H)) is-pb-cone-A' x)
        ( is-equiv-fib-functor-coprod-inl-fib h k x))
      ( λ y →  is-equiv-left-factor
        ( fib-square g i (dpair k (dpair g' K)) y)
        ( fib-square
          ( ind-coprod _ f g) i
          ( dpair
            ( functor-coprod h k)
            ( dpair (ind-coprod _ f' g') (ind-coprod _ H K))) (inr y))
          ( fib-functor-coprod-inr-fib h k y)
          ( triangle-descent-square-fib-functor-coprod-inr-fib
            h k i f g f' g' H K y)
          ( is-fiberwise-equiv-fib-square-is-pullback g i
            ( dpair k (dpair g' K)) is-pb-cone-B' y)
          ( is-equiv-fib-functor-coprod-inr-fib h k y)))

descent-coprod-inl : {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (i : X' → X)
  (cone-A' : cone f i A') (cone-B' : cone g i B') →
  is-pullback (ind-coprod _ f g) i (cone-descent-coprod f g i cone-A' cone-B') →
  is-pullback f i cone-A'
descent-coprod-inl f g i (dpair h (dpair f' H)) (dpair k (dpair g' K))
  is-pb-dsq =
    is-pullback-is-fiberwise-equiv-fib-square f i (dpair h (dpair f' H))
      ( λ a → is-equiv-comp
        ( fib-square f i (dpair h (dpair f' H)) a)
        ( fib-square (ind-coprod _ f g) i
          ( cone-descent-coprod f g i
            ( dpair h (dpair f' H)) (dpair k (dpair g' K))) (inl a))
        ( fib-functor-coprod-inl-fib h k a)
        ( triangle-descent-square-fib-functor-coprod-inl-fib
          h k i f g f' g' H K a)
        ( is-equiv-fib-functor-coprod-inl-fib h k a)
        ( is-fiberwise-equiv-fib-square-is-pullback (ind-coprod _ f g) i
          ( cone-descent-coprod f g i
            ( dpair h (dpair f' H)) (dpair k (dpair g' K))) is-pb-dsq (inl a)))

descent-coprod-inr : {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (i : X' → X)
  (cone-A' : cone f i A') (cone-B' : cone g i B') →
  is-pullback (ind-coprod _ f g) i (cone-descent-coprod f g i cone-A' cone-B') →
  is-pullback g i cone-B'
descent-coprod-inr f g i (dpair h (dpair f' H)) (dpair k (dpair g' K))
  is-pb-dsq =
    is-pullback-is-fiberwise-equiv-fib-square g i (dpair k (dpair g' K))
      ( λ b → is-equiv-comp
        ( fib-square g i (dpair k (dpair g' K)) b)
        ( fib-square (ind-coprod _ f g) i
          ( cone-descent-coprod f g i
            ( dpair h (dpair f' H)) (dpair k (dpair g' K))) (inr b))
        ( fib-functor-coprod-inr-fib h k b)
        ( triangle-descent-square-fib-functor-coprod-inr-fib
          h k i f g f' g' H K b)
        ( is-equiv-fib-functor-coprod-inr-fib h k b)
        ( is-fiberwise-equiv-fib-square-is-pullback (ind-coprod _ f g) i
          ( cone-descent-coprod f g i
            ( dpair h (dpair f' H)) (dpair k (dpair g' K))) is-pb-dsq (inr b)))

-- Descent for Σ-types

cone-descent-Σ : {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : I → UU l2} {A' : I → UU l3} {X : UU l4} {X' : UU l5}
  (f : (i : I) → A i → X) (h : X' → X)
  (c : (i : I) → cone (f i) h (A' i)) →
  cone (ind-Σ f) h (Σ I A')
cone-descent-Σ f h c =
  dpair
    ( tot (λ i → (pr1 (c i))))
    ( dpair
      ( ind-Σ (λ i → (pr1 (pr2 (c i)))))
      ( ind-Σ (λ i → (pr2 (pr2 (c i))))))

triangle-descent-Σ : {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : I → UU l2} {A' : I → UU l3} {X : UU l4} {X' : UU l5}
  (f : (i : I) → A i → X) (h : X' → X)
  (c : (i : I) → cone (f i) h (A' i)) →
  (i : I) (a : A i) →
  ( fib-square (f i) h (c i) a) ~
  ((fib-square (ind-Σ f) h (cone-descent-Σ f h c) (dpair i a)) ∘ (fib-tot-fib-ftr (λ i → (pr1 (c i))) (dpair i a)))
triangle-descent-Σ f h c i .(pr1 (c i) a') (dpair a' refl) = refl

descent-Σ : {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : I → UU l2} {A' : I → UU l3} {X : UU l4} {X' : UU l5}
  (f : (i : I) → A i → X) (h : X' → X)
  (c : (i : I) → cone (f i) h (A' i)) →
  ((i : I) → is-pullback (f i) h (c i)) →
  is-pullback (ind-Σ f) h (cone-descent-Σ f h c)
descent-Σ f h c is-pb-c =
  is-pullback-is-fiberwise-equiv-fib-square
    ( ind-Σ f)
    ( h)
    ( cone-descent-Σ f h c)
    ( ind-Σ
      ( λ i a → is-equiv-left-factor
        ( fib-square (f i) h (c i) a)
        ( fib-square (ind-Σ f) h (cone-descent-Σ f h c) (dpair i a))
        ( fib-tot-fib-ftr (λ i → pr1 (c i)) (dpair i a))
        ( triangle-descent-Σ f h c i a)
        ( is-fiberwise-equiv-fib-square-is-pullback (f i) h (c i) (is-pb-c i) a)
        ( is-equiv-fib-tot-fib-ftr (λ i → pr1 (c i)) (dpair i a))))

descent-Σ' : {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : I → UU l2} {A' : I → UU l3} {X : UU l4} {X' : UU l5}
  (f : (i : I) → A i → X) (h : X' → X)
  (c : (i : I) → cone (f i) h (A' i)) →
  is-pullback (ind-Σ f) h (cone-descent-Σ f h c) →
  ((i : I) → is-pullback (f i) h (c i))
descent-Σ' f h c is-pb-dsq i =
  is-pullback-is-fiberwise-equiv-fib-square (f i) h (c i)
    ( λ a → is-equiv-comp
      ( fib-square (f i) h (c i) a)
      ( fib-square (ind-Σ f) h (cone-descent-Σ f h c) (dpair i a))
      ( fib-tot-fib-ftr (λ i → pr1 (c i)) (dpair i a))
      ( triangle-descent-Σ f h c i a)
      ( is-equiv-fib-tot-fib-ftr (λ i → pr1 (c i)) (dpair i a))
      ( is-fiberwise-equiv-fib-square-is-pullback (ind-Σ f) h
        ( cone-descent-Σ f h c) is-pb-dsq (dpair i a)))

-- Extra material

coherence-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) (c' : cone f' g' C)
  (Hp : pr1 c ~ pr1 c') (Hq : pr1 (pr2 c) ~ pr1 (pr2 c')) → UU _
coherence-htpy-cone {f = f} {f'} Hf {g} {g'} Hg c c' Hp Hq =
  let p  = pr1 c
      q  = pr1 (pr2 c)
      H  = pr2 (pr2 c)
      p' = pr1 c'
      q' = pr1 (pr2 c')
      H' = pr2 (pr2 c')
  in
  ( H ∙h ((g ·l Hq) ∙h (Hg ·r q'))) ~ (((f ·l Hp) ∙h (Hf ·r p')) ∙h H')

fam-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) → (c' : cone f' g' C) →
  (pr1 c ~ pr1 c') → UU _
fam-htpy-cone {f = f} {f'} Hf {g} {g'} Hg c c' Hp =
  Σ ((pr1 (pr2 c)) ~ (pr1 (pr2 c'))) (coherence-htpy-cone Hf Hg c c' Hp)
  
htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  cone f g C → cone f' g' C → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
htpy-cone
  {f = f} {f'} Hf {g} {g'} Hg c c' =
  Σ ((pr1 c) ~ (pr1 c')) (fam-htpy-cone Hf Hg c c')

is-contr-total-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) →
  is-contr (Σ (cone f' g' C) (htpy-cone Hf Hg c))
is-contr-total-htpy-cone {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg =
  ind-htpy
    { A = A}
    { B = λ t → X}
    f
    ( λ f'' Hf' → (g g' : B → X) (Hg : g ~ g') (c : cone f g C) →
      is-contr (Σ (cone f'' g' C) (htpy-cone Hf' Hg c)))
    ( λ g → ind-htpy {A = B} {B = λ t → X} g
      ( λ g'' Hg' →
        ( c : cone f g C) →
        is-contr (Σ (cone f g'' C) (htpy-cone (htpy-refl f) Hg' c)))
      ( λ (c : cone f g C) → 
        let p = pr1 c
            q = pr1 (pr2 c)
            H = pr2 (pr2 c)
        in
        is-contr-total-Eq-structure
          ( fam-htpy-cone (htpy-refl f) (htpy-refl g) c)
          ( is-contr-total-htpy p)
          ( dpair p (htpy-refl p))
          ( is-contr-total-Eq-structure
            ( λ t Hq →
              coherence-htpy-cone (htpy-refl f) (htpy-refl g) c
              ( dpair p t)
              ( htpy-refl p)
              ( Hq))
            ( is-contr-total-htpy q)
            ( dpair q (htpy-refl q))
            ( is-contr-is-equiv'
              ( Σ ((f ∘ p) ~ (g ∘ q)) (λ H' → H ~ H'))
              ( tot (λ H' → htpy-concat _ {h = H'} (htpy-right-unit H)))
              ( is-equiv-tot-is-fiberwise-equiv
                ( λ H' → is-equiv-htpy-concat (htpy-right-unit H) H'))
              ( is-contr-total-htpy H)))))
    f' Hf g g' Hg

reflexive-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  htpy-cone (htpy-refl f) (htpy-refl g) c c
reflexive-htpy-cone f g c =
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  dpair (htpy-refl p) (dpair (htpy-refl q) (htpy-right-unit H))

htpy-cone-eq-htpy-refl :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  Id c c' → htpy-cone (htpy-refl f) (htpy-refl g) c c'
htpy-cone-eq-htpy-refl f g c .c refl =
  dpair (htpy-refl _) (dpair (htpy-refl _) (htpy-right-unit _))

tr-tr-htpy-refl-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy (htpy-refl f)) c
      tr-tr-c = tr (λ y → cone f y C) (eq-htpy (htpy-refl g)) tr-c
  in
  Id tr-tr-c c
tr-tr-htpy-refl-cone {C = C} f g c =
  let tr-c = tr (λ f''' → cone f''' g C) (eq-htpy (htpy-refl f)) c
      tr-tr-c = tr (λ g'' → cone f g'' C) (eq-htpy (htpy-refl g)) tr-c
      α : Id tr-tr-c tr-c
      α = ap (λ t → tr (λ g'' → cone f g'' C) t tr-c) (eq-htpy-htpy-refl g)
      β : Id tr-c c
      β = ap (λ t → tr (λ f''' → cone f''' g C) t c) (eq-htpy-htpy-refl f)
  in
  α ∙ β

htpy-cone-eq-htpy-refl-htpy-refl :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy (htpy-refl f)) c
      tr-tr-c = tr (λ y → cone f y C) (eq-htpy (htpy-refl g)) tr-c
  in
  Id tr-tr-c c' → htpy-cone (htpy-refl f) (htpy-refl g) c c'
htpy-cone-eq-htpy-refl-htpy-refl f g c c' =
  ind-is-equiv
    ( λ p → htpy-cone (htpy-refl f) (htpy-refl g) c c')
    ( λ (p : Id c c') → (tr-tr-htpy-refl-cone f g c) ∙ p)
    ( is-equiv-concat (tr-tr-htpy-refl-cone f g c) c')
    ( htpy-cone-eq-htpy-refl f g c c')

comp-htpy-cone-eq-htpy-refl-htpy-refl :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  ( (htpy-cone-eq-htpy-refl-htpy-refl f g c c') ∘
    (concat c {z = c'} (tr-tr-htpy-refl-cone f g c))) ~
  ( htpy-cone-eq-htpy-refl f g c c')
comp-htpy-cone-eq-htpy-refl-htpy-refl f g c c' =
  htpy-comp-is-equiv
    ( λ p → htpy-cone (htpy-refl f) (htpy-refl g) c c')
    ( λ (p : Id c c') → (tr-tr-htpy-refl-cone f g c) ∙ p)
    ( is-equiv-concat (tr-tr-htpy-refl-cone f g c) c')
    ( htpy-cone-eq-htpy-refl f g c c')

htpy-cone-eq' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) (c' : cone f g' C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy (htpy-refl f)) c
      tr-tr-c = tr (λ y → cone f y C) (eq-htpy Hg) tr-c
  in
  Id tr-tr-c c' → htpy-cone (htpy-refl f) Hg c c'
htpy-cone-eq' {C = C} f {g} {g'} =
  ind-htpy g
    ( λ g'' Hg' →
      ( c : cone f g C) (c' : cone f g'' C) →
      Id (tr (λ g'' → cone f g'' C) (eq-htpy Hg')
        ( tr (λ f''' → cone f''' g C) (eq-htpy (htpy-refl f)) c)) c' →
      htpy-cone (htpy-refl f) Hg' c c')
    ( htpy-cone-eq-htpy-refl-htpy-refl f g)
    g'

comp-htpy-cone-eq' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  ( ( htpy-cone-eq' f (htpy-refl g) c c') ∘
    ( concat c {z = c'} (tr-tr-htpy-refl-cone f g c))) ~
  ( htpy-cone-eq-htpy-refl f g c c')
comp-htpy-cone-eq' {A = A} {B} {X} {C} f g c c' =
  htpy-right-whisk
    ( htpy-eq (htpy-eq (htpy-eq (comp-htpy g
      ( λ g'' Hg' →
        ( c : cone f g C) (c' : cone f g'' C) →
          Id (tr (λ g'' → cone f g'' C) (eq-htpy Hg')
            ( tr (λ f''' → cone f''' g C) (eq-htpy (htpy-refl f)) c)) c' →
      htpy-cone (htpy-refl f) Hg' c c')
    ( htpy-cone-eq-htpy-refl-htpy-refl f g)) c) c'))
    ( concat c {z = c'} (tr-tr-htpy-refl-cone f g c)) ∙h
  ( comp-htpy-cone-eq-htpy-refl-htpy-refl f g c c')

htpy-cone-eq :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) (c' : cone f' g' C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy Hf) c
      tr-tr-c = tr (λ y → cone f' y C) (eq-htpy Hg) tr-c
  in
  Id tr-tr-c c' → htpy-cone Hf Hg c c'
htpy-cone-eq {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg c c' p =
  ind-htpy f
  ( λ f'' Hf' →
    ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f'' g' C) →
    ( Id (tr (λ g'' → cone f'' g'' C) (eq-htpy Hg)
      ( tr (λ f''' → cone f''' g C) (eq-htpy Hf') c)) c') →
    htpy-cone Hf' Hg c c')
  ( λ g g' → htpy-cone-eq' f {g = g} {g' = g'})
  f' Hf g g' Hg c c' p

comp-htpy-cone-eq : 
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  ( ( htpy-cone-eq (htpy-refl f) (htpy-refl g) c c') ∘
    ( concat c {z = c'} (tr-tr-htpy-refl-cone f g c))) ~
  ( htpy-cone-eq-htpy-refl f g c c')
comp-htpy-cone-eq {A = A} {B} {X} {C} f g c c' =
  htpy-right-whisk
    (htpy-eq (htpy-eq (htpy-eq (htpy-eq (htpy-eq (htpy-eq (comp-htpy f
  ( λ f'' Hf' →
    ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f'' g' C) →
    ( Id (tr (λ g'' → cone f'' g'' C) (eq-htpy Hg)
      ( tr (λ f''' → cone f''' g C) (eq-htpy Hf') c)) c') →
    htpy-cone Hf' Hg c c')
  ( λ g g' → htpy-cone-eq' f {g = g} {g' = g'})) g) g) (htpy-refl g)) c) c'))
    ( concat c {z = c'} (tr-tr-htpy-refl-cone f g c)) ∙h
  ( comp-htpy-cone-eq' f g c c')
  
is-fiberwise-equiv-htpy-cone-eq :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) (c' : cone f' g' C) →
  is-equiv (htpy-cone-eq Hf Hg c c')
is-fiberwise-equiv-htpy-cone-eq
  {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg c c' =
  ind-htpy f
    ( λ f' Hf →
      ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f' g' C) →
        is-equiv (htpy-cone-eq Hf Hg c c'))
    ( λ g g' Hg c c' →
      ind-htpy g
        ( λ g' Hg →
          ( c : cone f g C) (c' : cone f g' C) →
            is-equiv (htpy-cone-eq (htpy-refl f) Hg c c'))
        ( λ c c' →
          is-equiv-left-factor
            ( htpy-cone-eq-htpy-refl f g c c')
            ( htpy-cone-eq (htpy-refl f) (htpy-refl g) c c')
            ( concat c {z = c'} (tr-tr-htpy-refl-cone f g c))
            ( htpy-inv (comp-htpy-cone-eq f g c c'))
            ( id-fundamental-gen c
              ( reflexive-htpy-cone f g c)
              ( is-contr-total-htpy-cone (htpy-refl f) (htpy-refl g) c)
              ( htpy-cone-eq-htpy-refl f g c) c')
            ( is-equiv-concat (tr-tr-htpy-refl-cone f g c) c'))
        g' Hg c c')
    f' Hf g g' Hg c c'

eq-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) (c' : cone f' g' C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy Hf) c
      tr-tr-c = tr (λ y → cone f' y C) (eq-htpy Hg) tr-c
  in
  htpy-cone Hf Hg c c' → Id tr-tr-c c'
eq-htpy-cone Hf Hg c c' =
  inv-is-equiv
    { f = htpy-cone-eq Hf Hg c c'}
    ( is-fiberwise-equiv-htpy-cone-eq Hf Hg c c')

map-is-pullback-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {f' : A → X} (Hf : f ~ f')
  {g : B → X} {g' : B → X} (Hg : g ~ g') →
  canonical-pullback f' g' → canonical-pullback f g
map-is-pullback-htpy {f = f} {f'} Hf {g} {g'} Hg =
  tot (λ a → tot (λ b →
    ( concat' (g' b) (inv (Hg b))) ∘ (concat (f' a) {z = g' b} (Hf a))))

is-equiv-map-is-pullback-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {f' : A → X} (Hf : f ~ f')
  {g : B → X} {g' : B → X} (Hg : g ~ g') →
  is-equiv (map-is-pullback-htpy Hf Hg)
is-equiv-map-is-pullback-htpy {f = f} {f'} Hf {g} {g'} Hg =
  is-equiv-tot-is-fiberwise-equiv (λ a →
    is-equiv-tot-is-fiberwise-equiv (λ b →
      is-equiv-comp
        ( (concat' (g' b) (inv (Hg b))) ∘ (concat (f' a) {z = g' b} (Hf a)))
        ( concat' (g' b) (inv (Hg b)))
        ( concat (f' a) {z = g' b} (Hf a))
        ( htpy-refl _)
        ( is-equiv-concat (Hf a) (g' b))
        ( is-equiv-concat' (f a) (inv (Hg b)))))

tot-pullback-rel : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (x : A) → UU _
tot-pullback-rel {B = B} f g x = Σ B (λ y → Id (f x) (g y))

tr-tot-pullback-rel : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {x x' : A} (p : Id x x')
  (t : tot-pullback-rel f g x) →
  Id
    ( tr (tot-pullback-rel f g) p t)
    ( dpair (pr1 t) ((inv (ap f p)) ∙ (pr2 t)))
tr-tot-pullback-rel f g refl (dpair y α) = refl

square-eq-inv-vertical : {l : Level} {A : UU l}
  {top-left top-right bottom-left bottom-right : A}
  (left : Id top-left bottom-left) (bottom : Id bottom-left bottom-right)
  (top : Id top-left top-right) (right : Id top-right bottom-right) →
  Id (left ∙ bottom) (top ∙ right) →
  Id ((inv left) ∙ top) (bottom ∙ (inv right))
square-eq-inv-vertical refl bottom refl refl refl = refl

triangle-is-pullback-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f : A → X} {f' : A → X} (Hf : f ~ f')
  {g : B → X} {g' : B → X} (Hg : g ~ g')
  {c : cone f g C} {c' : cone f' g' C} (Hc : htpy-cone Hf Hg c c') →
  (gap f g c) ~ ((map-is-pullback-htpy Hf Hg) ∘ (gap f' g' c'))
triangle-is-pullback-htpy {A = A} {B} {X} {C} {f = f} {f'} Hf {g} {g'} Hg
  {dpair p (dpair q H)} {dpair p' (dpair q' H')} (dpair Hp (dpair Hq HH)) z =
  eq-pair
    ( dpair
      ( Hp z)
      ( ( tr-tot-pullback-rel f g (Hp z) (dpair (q z) (H z))) ∙
        ( eq-pair
          ( dpair
            ( Hq z)
            ( ( tr-id-right-subst
                ( Hq z)
                ( f (p' z))
                ( (inv (ap f (Hp z))) ∙ (H z))) ∙
              ( inv (assoc (inv (ap f (Hp z))) (H z) (ap g (Hq z))) ∙
                 square-eq-inv-vertical
                   ( ap f (Hp z))
                   ( (Hf (p' z)) ∙ (H' z))
                   ( (H z) ∙ (ap g (Hq z)))
                   ( Hg (q' z))
                   ( ( assoc (ap f (Hp z)) (Hf (p' z)) (H' z)) ∙
                     ( ( inv (HH z)) ∙
                       ( assoc (H z) (ap g (Hq z)) (Hg (q' z)))))))))))

is-pullback-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f : A → X} (f' : A → X) (Hf : f ~ f')
  {g : B → X} (g' : B → X) (Hg : g ~ g')
  {c : cone f g C} (c' : cone f' g' C) (Hc : htpy-cone Hf Hg c c') →
  is-pullback f' g' c' → is-pullback f g c
is-pullback-htpy
  {f = f} f' Hf {g} g' Hg
  {c = dpair p (dpair q H)} (dpair p' (dpair q' H'))
  (dpair Hp (dpair Hq HH)) is-pb-c' =
  is-equiv-comp
    ( gap f g (dpair p (dpair q H)))
    ( map-is-pullback-htpy Hf Hg)
    ( gap f' g' (dpair p' (dpair q' H')))
    ( triangle-is-pullback-htpy Hf Hg
      {dpair p (dpair q H)} {dpair p' (dpair q' H')} (dpair Hp (dpair Hq HH)))
    ( is-pb-c')
    ( is-equiv-map-is-pullback-htpy Hf Hg)

is-pullback-htpy' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) {f' : A → X} (Hf : f ~ f')
  (g : B → X) {g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) {c' : cone f' g' C} (Hc : htpy-cone Hf Hg c c') →
  is-pullback f g c → is-pullback f' g' c'
is-pullback-htpy'
  f {f'} Hf g {g'} Hg
  (dpair p (dpair q H)) {dpair p' (dpair q' H')}
  (dpair Hp (dpair Hq HH)) is-pb-c =
  is-equiv-right-factor
    ( gap f g (dpair p (dpair q H)))
    ( map-is-pullback-htpy Hf Hg)
    ( gap f' g' (dpair p' (dpair q' H')))
    ( triangle-is-pullback-htpy Hf Hg
      {dpair p (dpair q H)} {dpair p' (dpair q' H')} (dpair Hp (dpair Hq HH)))
    ( is-equiv-map-is-pullback-htpy Hf Hg)
    ( is-pb-c)
