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

abstract 
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

eq-cone-Eq-cone : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {g : B → X} {C : UU l4} (c c' : cone f g C) →
  Eq-cone f g c c' → Id c c'
eq-cone-Eq-cone {f = f} {g = g} c c' =
  inv-is-equiv (is-fiberwise-equiv-Eq-cone-eq-cone f g c c')

abstract 
  is-contr-universal-property-pullback : {l1 l2 l3 l4 l5 : Level} {A : UU l1}
    {B : UU l2} {C : UU l3} {X : UU l4} (f : A → X) (g : B → X)
    (c : cone f g C) → universal-property-pullback {l5 = l5} f g C c →
    (C' : UU l5) (c' : cone f g C') →
    is-contr (Σ (C' → C) (λ h → Eq-cone f g (cone-map f g c h) c'))
  is-contr-universal-property-pullback {C = C} f g c up C' c' =
    is-contr-is-equiv'
      ( Σ (C' → C) (λ h → Id (cone-map f g c h) c'))
      ( tot (λ h → Eq-cone-eq-cone f g (cone-map f g c h) c'))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h → Eq-cone-eq-cone f g (cone-map f g c h) c')
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
    ({l6 : Level} → universal-property-pullback {l5 = l6} f g C c) →
    ({l6 : Level} → universal-property-pullback {l5 = l6} f g C' c') →
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
  ({l6 : Level} → universal-property-pullback {l5 = l6} f g C c) →
  ({l6 : Level} → universal-property-pullback {l5 = l6} f g C' c')
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
  ({l6 : Level} → universal-property-pullback {l5 = l6} f g C' c') →
  is-equiv h →
  ({l6 : Level} → universal-property-pullback {l5 = l6} f g C c)
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
    ({l6 : Level} → universal-property-pullback {l5 = l6} f g C' c') →
    ({l6 : Level} → universal-property-pullback {l5 = l6} f g C c) →
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
        ( is-equiv-tot-is-fiberwise-equiv _
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
    ({l5 : Level} → universal-property-pullback {l5 = l5} f g C c) →
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
  ({l5 : Level} → universal-property-pullback {l5 = l5} f g C c)
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
    ( A × B)
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
    (Σ X (λ x → (P x) × (Q x))) (cone-fiberwise-prod P Q)
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
    ( λ a p → dpair star p)
    ( λ a → is-equiv-left-unit-law-Σ-map (λ t → Id (f a) b) is-contr-unit)

universal-property-pullback-cone-fiber : {l1 l2 l3 : Level} {A : UU l1} →
  {B : UU l2} (f : A → B) (b : B) →
  universal-property-pullback {l5 = l3} f
    ( const unit B b) (fib f b) (cone-fiber f b)
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

\end{code}
