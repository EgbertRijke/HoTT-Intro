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

abstract
  -- The following definition is very slow to type-check.
  is-contr-total-Eq-cone : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C) →
    is-contr (Σ (cone f g C) (Eq-cone f g c))
  is-contr-total-Eq-cone {A = A} {B} f g {C} (dpair p (dpair q H)) =
    is-contr-total-Eq-structure
      ( C → A)
      ( λ (p' : C → A) → Σ (C → B) (λ q' → (f ∘ p') ~ (g ∘ q')))
      ( λ (p' : C → A) → p ~ p')
      ( λ t (K : p ~ (pr1 t)) →
        Σ ( q ~ (pr1 (pr2 t)))
          ( λ L →
            ( H ∙h (htpy-left-whisk g L)) ~
              ( (htpy-left-whisk f K) ∙h (pr2 (pr2 t)))))
      ( is-contr-total-htpy-nondep p)
      ( is-contr-total-Eq-structure
        ( C → B)
        ( λ (q' : C → B) → (f ∘ p) ~ (g ∘ q'))
        ( λ (q' : C → B) → q ~ q')
        ( λ t (L : q ~ (pr1 t)) → (H ∙h (htpy-left-whisk g L)) ~ (pr2 t))
        ( is-contr-total-htpy-nondep q)
        ( is-contr-is-equiv
            ( Σ ((f ∘ p) ~ (g ∘ q)) (λ H' → H ~ H'))
            ( tot (λ H' → inv-is-equiv
              ( is-equiv-htpy-concat (htpy-right-unit H) H')))
            ( is-equiv-tot-is-fiberwise-equiv
              ( λ H' → is-equiv-inv-is-equiv
                ( is-equiv-htpy-concat (htpy-right-unit H) H')))
            ( is-contr-total-htpy {B = λ z → Id (f (p z)) (g (q z))} H)))

abstract 
  is-fiberwise-equiv-Eq-cone-eq-cone : {l1 l2 l3 l4 : Level} {A : UU l1}
    {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C) →
    is-fiberwise-equiv (Eq-cone-eq-cone f g c)
  is-fiberwise-equiv-Eq-cone-eq-cone f g {C = C} c =
    id-fundamental-gen c
      ( Eq-cone-eq-cone f g c c refl)
      ( is-contr-total-Eq-cone f g c)
      ( Eq-cone-eq-cone f g c)
      
{-
    is-fiberwise-equiv-id-to-Eq-structure c
      ( λ t → Σ ((pr1 (pr2 c)) ~ (pr1 (pr2 (pr1 t)))) (λ L →
        ( (pr2 (pr2 c)) ∙h (htpy-left-whisk g L)) ~
        ( (htpy-left-whisk f (pr2 t)) ∙h (pr2 (pr2 (pr1 t))))))
      ( Eq-cone-eq-cone f g c)
      ( λ p' → htpy-eq)
      ( Eq-cone-eq-cone' f g c)
      ( eq-pair (dpair refl (eq-pair (dpair (eq-htpy (λ z → {!!})) {!!}))))
      ( funext (pr1 c))
      ( is-fiberwise-equiv-id-to-Eq-structure (pr2 c)
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!})
-}


eq-cone-Eq-cone : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {g : B → X} {C : UU l4} (c c' : cone f g C) →
  Eq-cone f g c c' → Id c c'
eq-cone-Eq-cone {f = f} {g = g} c c' =
  inv-is-equiv (is-fiberwise-equiv-Eq-cone-eq-cone f g c c')

abstract 
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

abstract 
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

abstract
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

abstract 
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

-- Functoriality of pullbacks

htpy-cube : {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  {A' : UU l5} {B' : UU l6} {C' : UU l7} {X' : UU l8}
  {f : A → X} {g : B → X} {p : C → A} {q : C → B} (H : (f ∘ p) ~ (g ∘ q))
  {f' : A' → X'} {g' : B' → X'} {p' : C' → A'} {q' : C' → B'}
  (H' : (f' ∘ p') ~ (g' ∘ q'))
  {iA : A' → A} {iB : B' → B} {iC : C' → C} {iX : X' → X}
  (F : (f ∘ iA) ~ (iX ∘ f')) (G : (g ∘ iB) ~ (iX ∘ g'))
  (P : (p ∘ iC) ~ (iA ∘ p')) (Q : (q ∘ iC) ~ (iB ∘ q')) → UU _
htpy-cube {f = f} {g = g} H {p' = p'} {q' = q'} H' {iA} {iB} {iC} {iX} F G P Q =
  ((H ·r iC) ∙h ((g ·l Q) ∙h (G ·r q'))) ~
    (((f ·l P) ∙h (F ·r p')) ∙h (iX ·l H'))

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
    ( λ x → Sigma B (λ y → Id (f x) (g y)))
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

-- Section 10.7 Disjointness of coproducts

map-coprod : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} →
  (A → X) → (B → X) → (coprod A B → X)
map-coprod f g (inl x) = f x
map-coprod f g (inr y) = g y

coprod-functor : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {Y : UU l4} → (A → X) → (B → Y) → (coprod A B → coprod X Y)
coprod-functor f g (inl x) = inl (f x)
coprod-functor f g (inr y) = inr (g y)

cone-const-true-true : {l : Level} (X : UU l) →
  cone (const X bool true) (const unit bool true) X
cone-const-true-true X = dpair id (dpair (const X unit star) (λ x → refl))

is-pullback-cone-const-true-true : {l : Level} (X : UU l) →
  is-pullback (const X bool true) (const unit bool true)
    (cone-const-true-true X)
is-pullback-cone-const-true-true X = {!!}

\end{code}
