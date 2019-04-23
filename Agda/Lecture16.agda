{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture16 where

import Lecture15
open Lecture15 public

-- Section 16.1 The dependent pullback property of pushouts

{- Our goal in this section is to show that the pullback property of pushouts 
   implies the dependent pullback property of pushouts. -}

{- We first define the family of lifts, which is indexed by maps Y → X. -}

fam-lifts :
  {l1 l2 l3 : Level} (Y : UU l1) {X : UU l2} (P : X → UU l3) →
  (Y → X) → UU (l1 ⊔ l3)
fam-lifts Y P h = (y : Y) → P (h y)

tr-fam-lifts' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
  (h : B → X) {f g : A → B} (H : f ~ g) →
  fam-lifts A P (h ∘ f) → fam-lifts A P (h ∘ g)
tr-fam-lifts' P h {f} {g} H k s = tr (P ∘ h) (H s) (k s)

TR-EQ-HTPY-FAM-LIFTS :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
  (h : B → X) {f g : A → B} (H : f ~ g) → UU (l1 ⊔ l4)
TR-EQ-HTPY-FAM-LIFTS {A = A} P h H =
  tr (fam-lifts A P) (eq-htpy (h ·l H)) ~ (tr-fam-lifts' P h H)

tr-eq-htpy-fam-lifts-htpy-refl :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
  (h : B → X) (f : A → B) → TR-EQ-HTPY-FAM-LIFTS P h (htpy-refl f)
tr-eq-htpy-fam-lifts-htpy-refl P h f k =
  ap (λ t → tr (fam-lifts _ P) t k) (eq-htpy-htpy-refl (h ∘ f))

tr-eq-htpy-fam-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
  (h : B → X) {f g : A → B} (H : f ~ g) →
  TR-EQ-HTPY-FAM-LIFTS P h H
tr-eq-htpy-fam-lifts P h {f} =
  ind-htpy f
    ( λ g H → TR-EQ-HTPY-FAM-LIFTS P h H)
    ( tr-eq-htpy-fam-lifts-htpy-refl P h f)

compute-tr-eq-htpy-fam-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4) →
  (h : B → X) (f : A → B) →
  Id  ( tr-eq-htpy-fam-lifts P h (htpy-refl f))
      ( tr-eq-htpy-fam-lifts-htpy-refl P h f)
compute-tr-eq-htpy-fam-lifts P h f =
  comp-htpy f
    ( λ g H → TR-EQ-HTPY-FAM-LIFTS P h H)
    ( tr-eq-htpy-fam-lifts-htpy-refl P h f) 

{- One of the basic operations on lifts is precomposition by an ordinary 
   function. -}

precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) → (f : A → B) → (h : B → X) →
  (fam-lifts B P h) → (fam-lifts A P (h ∘ f))
precompose-lifts P f h h' a = h' (f a)

{- Given two homotopic maps, their precomposition functions have different 
   codomains. However, there is a commuting triangle. We obtain this triangle
   by homotopy induction. -}

TRIANGLE-PRECOMPOSE-LIFTS :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  ( P : X → UU l4) {f g : A → B} (H : f ~ g) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
TRIANGLE-PRECOMPOSE-LIFTS {A = A} {B} {X} P {f} {g} H =
  (h : B → X) →
    ( (tr (fam-lifts A P) (eq-htpy (h ·l H))) ∘ (precompose-lifts P f h)) ~
    ( precompose-lifts P g h)

triangle-precompose-lifts-htpy-refl :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) → TRIANGLE-PRECOMPOSE-LIFTS P (htpy-refl f)
triangle-precompose-lifts-htpy-refl {A = A} P f h h' =
  tr-eq-htpy-fam-lifts-htpy-refl P h f (λ a → h' (f a))

triangle-precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) {f g : A → B} (H : f ~ g) →
  TRIANGLE-PRECOMPOSE-LIFTS P H
triangle-precompose-lifts {A = A} P {f} =
  ind-htpy f
    ( λ g H → TRIANGLE-PRECOMPOSE-LIFTS P H)
    ( triangle-precompose-lifts-htpy-refl P f)

compute-triangle-precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) →
  Id
    ( triangle-precompose-lifts P (htpy-refl f))
    ( triangle-precompose-lifts-htpy-refl P f)
compute-triangle-precompose-lifts P f =
  comp-htpy f
    ( λ g H → TRIANGLE-PRECOMPOSE-LIFTS P H)
    ( triangle-precompose-lifts-htpy-refl P f)

{- There is a similar commuting triangle with the computed transport function.
   This time we don't use homotopy induction to construct the homotopy. We
   give an explicit definition instead. -}

triangle-precompose-lifts' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) {f g : A → B} (H : f ~ g) → (h : B → X) →
  ( (tr-fam-lifts' P h H) ∘ (precompose-lifts P f h)) ~
  ( precompose-lifts P g h)
triangle-precompose-lifts' P H h k = eq-htpy (λ a → apd k (H a))

compute-triangle-precompose-lifts' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) → (h : B → X) →
  ( triangle-precompose-lifts' P (htpy-refl f) h) ~
  ( htpy-refl ( precompose-lifts P f h))
compute-triangle-precompose-lifts' P f h k = eq-htpy-htpy-refl _

{- There is a coherence between the two commuting triangles. This coherence
   is again constructed by homotopy induction. -}

COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS {A = A} {B} {X} P {f} {g} H =
  (h : B → X) →
    ( triangle-precompose-lifts P H h) ~
    ( ( ( tr-eq-htpy-fam-lifts P h H) ·r (precompose-lifts P f h)) ∙h
      ( triangle-precompose-lifts' P H h))

coherence-triangle-precompose-lifts-htpy-refl :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  (f : A → B) → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P (htpy-refl f)
coherence-triangle-precompose-lifts-htpy-refl P f h =
  ( htpy-eq (htpy-eq (compute-triangle-precompose-lifts P f) h)) ∙h
  ( ( ( htpy-inv (htpy-right-unit _)) ∙h
      ( htpy-ap-concat
        ( λ h' → tr-eq-htpy-fam-lifts-htpy-refl P h f (λ a → h' (f a)))
        ( htpy-refl _)
        ( triangle-precompose-lifts' P (htpy-refl f) h)
        ( htpy-inv (compute-triangle-precompose-lifts' P f h)))) ∙h
    ( htpy-eq
      ( ap
        ( λ t →
          ( t ·r (precompose-lifts P f h)) ∙h
          ( triangle-precompose-lifts' P (htpy-refl f) h))
        ( inv (compute-tr-eq-htpy-fam-lifts P h f)))))

coherence-triangle-precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P H
coherence-triangle-precompose-lifts P {f} =
  ind-htpy f
    ( λ g H → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P H)
    ( coherence-triangle-precompose-lifts-htpy-refl P f)

compute-coherence-triangle-precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  (f : A → B) →
  Id  ( coherence-triangle-precompose-lifts P (htpy-refl f))
      ( coherence-triangle-precompose-lifts-htpy-refl P f)
compute-coherence-triangle-precompose-lifts P f =
  comp-htpy f
    ( λ g H → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P H)
    ( coherence-triangle-precompose-lifts-htpy-refl P f)

total-lifts :
  {l1 l2 l3 : Level} (A : UU l1) {X : UU l2} (P : X → UU l3) →
  UU _
total-lifts A {X} P = type-choice-∞ {A = A} {B = λ a → X} (λ a → P)

precompose-total-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) → (A → B) →
  total-lifts B P → total-lifts A P
precompose-total-lifts {A = A} P f =
  toto
    ( λ h → (a : A) → P (h a))
    ( λ h → h ∘ f)
    ( precompose-lifts P f)

coherence-square-inv-choice-∞ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) →
  coherence-square
    ( precompose-total-lifts P f)
    ( inv-choice-∞ {A = B} {B = λ x → X} {C = λ x y → P y})
    ( inv-choice-∞)
    ( λ h → h ∘ f)
coherence-square-inv-choice-∞ P f = htpy-refl _

{- Our goal is now to produce a homotopy between (precompose-total-lifts P f) 
   and (precompose-total-lifts P g) for homotopic maps f and g, and a coherence
   filling a cilinder. -}

HTPY-PRECOMPOSE-TOTAL-LIFTS :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) {f g : A → B} (H : f ~ g) →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
HTPY-PRECOMPOSE-TOTAL-LIFTS P {f} {g} H =
  (precompose-total-lifts P f) ~ (precompose-total-lifts P g)

htpy-precompose-total-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → HTPY-PRECOMPOSE-TOTAL-LIFTS P H
htpy-precompose-total-lifts {A = A} {B} P {f} {g} H =
  htpy-toto
    { P = fam-lifts B P}
    ( fam-lifts A P)
    ( λ h → eq-htpy (h ·l H))
    ( precompose-lifts P f)
    ( triangle-precompose-lifts P H)

{- We show that when htpy-precompose-total-lifts is applied to htpy-refl, it
   computes to htpy-refl. -}

compute-htpy-precompose-total-lifts :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  ( f : A → B) →
  ( htpy-precompose-total-lifts P (htpy-refl f)) ~
  ( htpy-refl (toto (fam-lifts A P) (λ h → h ∘ f) (precompose-lifts P f)))
compute-htpy-precompose-total-lifts {A = A} P f (pair h h') =
  let α = λ (t : Id (h ∘ f) (h ∘ f)) → tr (fam-lifts A P) t (λ a → h' (f a))
  in
  ap eq-pair
    ( eq-pair
      ( pair
        ( eq-htpy-htpy-refl (h ∘ f))
        ( ( tr-id-left-subst
            { f = α}
            ( eq-htpy-htpy-refl (h ∘ f))
            ( λ a → h' (f a))
            ( triangle-precompose-lifts P (htpy-refl f) h h')) ∙
          ( ( ap
              ( λ t → inv (ap α (eq-htpy-htpy-refl (λ a → h (f a)))) ∙ t)
              ( htpy-eq
                ( htpy-eq (compute-triangle-precompose-lifts P f) h) h')) ∙
            ( left-inv (triangle-precompose-lifts-htpy-refl P f h h'))))))

COHERENCE-HTPY-INV-CHOICE-∞ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → UU _
COHERENCE-HTPY-INV-CHOICE-∞ P {f} {g} H =
  ( ( coherence-square-inv-choice-∞ P f) ∙h
    ( inv-choice-∞ ·l ( htpy-precompose-total-lifts P H))) ~
  ( ( ( λ h → eq-htpy (h ·l H)) ·r inv-choice-∞) ∙h
    ( coherence-square-inv-choice-∞ P g))

coherence-htpy-inv-choice-∞-htpy-refl :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  (f : A → B) → COHERENCE-HTPY-INV-CHOICE-∞ P (htpy-refl f)
coherence-htpy-inv-choice-∞-htpy-refl P f =
  ( htpy-ap-concat
    ( coherence-square-inv-choice-∞ P f)
    ( inv-choice-∞ ·l ( htpy-precompose-total-lifts P (htpy-refl f)))
    ( htpy-refl _)
    ( λ h →
      ap (ap inv-choice-∞) (compute-htpy-precompose-total-lifts P f h))) ∙h
  ( htpy-inv
    ( htpy-ap-concat'
      ( ( htpy-precompose _ (htpy-refl f)) ·r inv-choice-∞)
      ( htpy-refl _)
      ( htpy-refl _)
      ( λ h → compute-htpy-precompose _ f (inv-choice-∞ h))))

coherence-htpy-inv-choice-∞ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → COHERENCE-HTPY-INV-CHOICE-∞ P H
coherence-htpy-inv-choice-∞ P {f} =
  ind-htpy f
    ( λ g H → COHERENCE-HTPY-INV-CHOICE-∞ P H)
    ( coherence-htpy-inv-choice-∞-htpy-refl P f)
    
cone-family-dependent-pullback-property :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) (P : X → UU l) →
  cone-family
    ( fam-lifts S P)
    ( precompose-lifts P f)
    ( precompose-lifts P g)
    ( cone-pullback-property-pushout f g c X)
    ( fam-lifts X P)
cone-family-dependent-pullback-property f g c P γ =
  pair
    ( precompose-lifts P (pr1 c) γ)
    ( pair
      ( precompose-lifts P (pr1 (pr2 c)) γ)
      ( triangle-precompose-lifts P (pr2 (pr2 c)) γ))

is-pullback-cone-family-dependent-pullback-property :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ((l : Level) → pullback-property-pushout l f g c) →
  {l : Level} (P : X → UU l) (γ : X → X) →
  is-pullback
    ( ( tr (fam-lifts S P) (eq-htpy (γ ·l (pr2 (pr2 c))))) ∘
      ( precompose-lifts P f (γ ∘ (pr1 c))))
    ( precompose-lifts P g (γ ∘ (pr1 (pr2 c))))
    ( cone-family-dependent-pullback-property f g c P γ)
is-pullback-cone-family-dependent-pullback-property {S = S} {A} {B} {X}
  f g (pair i (pair j H)) pb-c P =
  let c = pair i (pair j H) in
  is-pullback-family-is-pullback-tot
    ( fam-lifts S P)
    ( precompose-lifts P f)
    ( precompose-lifts P g)
    ( cone-pullback-property-pushout f g c X)
    ( cone-family-dependent-pullback-property f g c P)
    ( pb-c _ X)
    ( is-pullback-top-is-pullback-bottom-cube-is-equiv
      ( precompose (Σ X P) i)
      ( precompose (Σ X P) j)
      ( precompose (Σ X P) f)
      ( precompose (Σ X P) g)
      ( toto (fam-lifts A P) (precompose X i) (precompose-lifts P i))
      ( toto (fam-lifts B P) (precompose X j) (precompose-lifts P j))
      ( toto (fam-lifts S P) (precompose X f) (precompose-lifts P f))
      ( toto (fam-lifts S P) (precompose X g) (precompose-lifts P g))
      ( inv-choice-∞) 
      ( inv-choice-∞)
      ( inv-choice-∞)
      ( inv-choice-∞)
      ( htpy-precompose-total-lifts P H)
      ( htpy-refl _)
      ( htpy-refl _)
      ( htpy-refl _)
      ( htpy-refl _)
      ( htpy-precompose _ H)
      ( coherence-htpy-inv-choice-∞ P H)
      ( is-equiv-inv-choice-∞)
      ( is-equiv-inv-choice-∞)
      ( is-equiv-inv-choice-∞)
      ( is-equiv-inv-choice-∞)
      ( pb-c _ (Σ X P)))
    
dependent-pullback-property-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ((l : Level) → pullback-property-pushout l f g c) →
  ((l : Level) → dependent-pullback-property-pushout l f g c)
dependent-pullback-property-pullback-property-pushout
  {S = S} {A} {B} {X}
  f g (pair i (pair j H)) pullback-c l P =
  let c = pair i (pair j H) in
  is-pullback-htpy'
    ( (tr (fam-lifts S P) (eq-htpy (id ·l H))) ∘ (precompose-lifts P f i))
    ( (tr-eq-htpy-fam-lifts P id H) ·r (precompose-lifts P f i))
    ( precompose-lifts P g j)
    ( htpy-refl _)
    ( cone-family-dependent-pullback-property f g c P id)
    { c' = cone-dependent-pullback-property-pushout f g c P}
    ( pair (htpy-refl _)
      ( pair
        ( htpy-refl _)
        ( ( htpy-right-unit _) ∙h
          ( coherence-triangle-precompose-lifts P H id))))
    ( is-pullback-cone-family-dependent-pullback-property f g c pullback-c P id)

-- Section 16.2 Families over pushouts

Fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ lsuc l)))
Fam-pushout l {S} {A} {B} f g =
  Σ ( A → UU l)
    ( λ PA → Σ (B → UU l)
      ( λ PB → (s : S) → PA (f s) ≃ PB (g s)))

Fam-pushout-cocone-UU :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  cocone f g (UU l) → Fam-pushout l f g
Fam-pushout-cocone-UU l f g =
  tot (λ PA → (tot (λ PB H s → equiv-eq (H s))))

is-equiv-Fam-pushout-cocone-UU :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  is-equiv (Fam-pushout-cocone-UU l f g)
is-equiv-Fam-pushout-cocone-UU l f g =
  is-equiv-tot-is-fiberwise-equiv
    ( λ PA → is-equiv-tot-is-fiberwise-equiv
      ( λ PB → is-equiv-postcomp-Π
        ( λ s → equiv-eq)
        ( λ s → univalence (PA (f s)) (PB (g s)))))

gen-fam-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  (P : X → UU l) → Fam-pushout l f g
gen-fam-pushout f g (pair i (pair j H)) P =
  pair
    ( P ∘ i)
    ( pair
      ( P ∘ j)
      ( λ s → (pair (tr P (H s)) (is-equiv-tr P (H s)))))

equiv-eq-ap-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A} (p : Id x y) →
  Id (equiv-tr B p) (equiv-eq (ap B p))
equiv-eq-ap-fam B refl = refl

triangle-gen-fam-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ( gen-fam-pushout {l = l} f g c) ~
  ( ( Fam-pushout-cocone-UU l f g) ∘
    ( cocone-map f g {Y = UU l} c))
triangle-gen-fam-pushout {l = l} {S} {A} {B} {X} f g (pair i (pair j H)) P =
  eq-pair
    ( pair refl
      ( eq-pair
        ( pair refl
          ( eq-htpy (λ s → equiv-eq-ap-fam P (H s))))))

coherence-Eq-Fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  (PA : A → UU l) (PB : B → UU l) (PS : (s : S) → (PA (f s)) ≃ (PB (g s))) →
  (PA' : A → UU l) (PB' : B → UU l)
  (PS' : (s : S) → (PA' (f s)) ≃ (PB' (g s))) →
  (eA : (a : A) → (PA a) ≃ (PA' a)) (eB : (b : B) → (PB b) ≃ (PB' b)) →
  UU (l1 ⊔ l)
coherence-Eq-Fam-pushout {S = S}
  f g PA PB PS PA' PB' PS' eA eB =
  ( s : S) →
    ( (map-equiv (eB (g s))) ∘ (map-equiv (PS s))) ~
    ( (map-equiv (PS' s)) ∘ (map-equiv (eA (f s))))

is-contr-total-coherence-Eq-Fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  (PA : A → UU l) (PB : B → UU l)
  (PS : (s : S) → (PA (f s)) ≃ (PB (g s))) →
  is-contr (Σ ((s : S) → (PA (f s)) ≃ (PB (g s)))
    ( λ PS' → coherence-Eq-Fam-pushout
      f g PA PB PS PA PB PS' (λ a → equiv-id (PA a)) (λ b → equiv-id (PB b))))
is-contr-total-coherence-Eq-Fam-pushout {S = S} f g PA PB PS =
  is-contr-is-equiv'
    ( (s : S) →
      Σ ( (PA (f s)) ≃ (PB (g s)))
        ( λ PS's → ((map-equiv (PS s))) ~ (map-equiv (PS's))))
    ( choice-∞)
    ( is-equiv-choice-∞)
    ( is-contr-Π
      ( λ s → is-contr-total-htpy-equiv (PS s)))

Eq-Fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  (s t : Fam-pushout l f g) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l)))
Eq-Fam-pushout l {S} {A} {B} f g
  (pair PA (pair PB PS)) t =
  let PA' = pr1 t
      PB' = pr1 (pr2 t)
      PS' = pr2 (pr2 t)
  in
  Σ ( (a : A) → (PA a) ≃ (PA' a))
    ( λ eA → Σ ( (b : B) → (PB b) ≃ (PB' b))
      ( λ eB →
        coherence-Eq-Fam-pushout
          f g PA PB PS PA' PB' PS' eA eB))

is-contr-total-fam-equiv :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  is-contr (Σ (A → UU l2) (λ B' → (a : A) → (B a) ≃ (B' a)))
is-contr-total-fam-equiv {l2 = l2} {A} B =
  is-contr-is-equiv'
    ( (a : A) → Σ (UU l2) (λ B' → B a ≃ B'))
    ( choice-∞)
    ( is-equiv-choice-∞)
    ( is-contr-Π (λ a → is-contr-total-equiv (B a)))

is-contr-total-Eq-Fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s : Fam-pushout l f g) →
  is-contr
    ( Σ ( Fam-pushout l f g)
      ( Eq-Fam-pushout l f g s))
is-contr-total-Eq-Fam-pushout l {S} {A} {B} f g
  ( pair PA (pair PB PS)) =
  is-contr-total-Eq-structure
    ( λ PA' t eA →
      let PB' = pr1 t
          PS' = pr2 t
      in
      Σ ( (b : B) → (PB b) ≃ (PB' b))
        ( λ eB →
          coherence-Eq-Fam-pushout
            f g PA PB PS PA' PB' PS' eA eB))
    ( is-contr-total-fam-equiv PA)
    ( pair PA (λ a → equiv-id (PA a)))
    ( is-contr-total-Eq-structure
      ( λ PB' PS' eB →
        coherence-Eq-Fam-pushout
        f g PA PB PS PA PB' PS' (λ a → equiv-id (PA a)) eB)
      ( is-contr-total-fam-equiv PB)
      ( pair PB (λ b → equiv-id (PB b)))
      ( is-contr-total-coherence-Eq-Fam-pushout f g PA PB PS))

reflexive-Eq-Fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s : Fam-pushout l f g) →
  Eq-Fam-pushout l f g s s
reflexive-Eq-Fam-pushout l f g (pair PA (pair PB PS)) =
  pair (λ a → equiv-id (PA a))
    ( pair
      ( λ b → equiv-id (PB b))
      ( λ s → htpy-refl _))

Eq-Fam-pushout-eq :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s t : Fam-pushout l f g) →
  Id s t → Eq-Fam-pushout l f g s t
Eq-Fam-pushout-eq l f g s .s refl =
  reflexive-Eq-Fam-pushout l f g s

is-equiv-Eq-Fam-pushout-eq :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s t : Fam-pushout l f g) →
  is-equiv (Eq-Fam-pushout-eq l f g s t)
is-equiv-Eq-Fam-pushout-eq l f g s =
  id-fundamental-gen s
    ( reflexive-Eq-Fam-pushout l f g s)
    ( is-contr-total-Eq-Fam-pushout l f g s)
    ( Eq-Fam-pushout-eq l f g s)

eq-Eq-Fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s t : Fam-pushout l f g) →
  (Eq-Fam-pushout l f g s t) → Id s t
eq-Eq-Fam-pushout l f g s t =
  inv-is-equiv
    ( is-equiv-Eq-Fam-pushout-eq l f g s t)

issec-eq-Eq-Fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s t : Fam-pushout l f g) →
  ( ( Eq-Fam-pushout-eq l f g s t) ∘
    ( eq-Eq-Fam-pushout l f g s t)) ~ id
issec-eq-Eq-Fam-pushout l f g s t =
  issec-inv-is-equiv
    ( is-equiv-Eq-Fam-pushout-eq l f g s t)

isretr-eq-Eq-Fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s t : Fam-pushout l f g) →
  ( ( eq-Eq-Fam-pushout l f g s t) ∘
    ( Eq-Fam-pushout-eq l f g s t)) ~ id
isretr-eq-Eq-Fam-pushout l f g s t =
  isretr-inv-is-equiv
    ( is-equiv-Eq-Fam-pushout-eq l f g s t)

{- Next we compute the identity type of products of total spaces. Note again
   that the identity type of a product of total spaces is again a product of
   total spaces. -}

Eq-ΠΣ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → UU (l1 ⊔ (l2 ⊔ l3))
Eq-ΠΣ {A = A} C t t' =
  (a : A) →
    Σ (Id (pr1 (t a)) (pr1 (t' a))) (λ p →
      Id (tr (C a) p (pr2 (t a))) (pr2 (t' a)))

reflexive-Eq-ΠΣ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : (a : A) → Σ (B a) (C a)) → Eq-ΠΣ C t t
reflexive-Eq-ΠΣ C t a = pair refl refl

Eq-ΠΣ-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → Id t t' → Eq-ΠΣ C t t'
Eq-ΠΣ-eq C t .t refl = reflexive-Eq-ΠΣ C t

is-contr-total-Eq-ΠΣ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : (a : A) → Σ (B a) (C a)) →
  is-contr (Σ ((a : A) → Σ (B a) (C a)) (Eq-ΠΣ C t))
is-contr-total-Eq-ΠΣ {A = A} {B} C t =
  is-contr-is-equiv
    ( (a : A) →
      Σ (Σ (B a) (C a)) (λ t' →
        Σ (Id (pr1 (t a)) (pr1 t')) (λ p →
          Id (tr (C a) p (pr2 (t a))) (pr2 t'))))
    ( inv-choice-∞)
    ( is-equiv-inv-choice-∞)
    ( is-contr-Π
      ( λ a →
        is-contr-total-Eq-structure
        ( λ b c p → Id (tr (C a) p (pr2 (t a))) c)
        ( is-contr-total-path (B a) (pr1 (t a)))
        ( pair (pr1 (t a)) refl)
        ( is-contr-total-path (C a (pr1 (t a))) (pr2 (t a)))))

is-equiv-Eq-ΠΣ-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → is-equiv (Eq-ΠΣ-eq C t t')
is-equiv-Eq-ΠΣ-eq C t =
  id-fundamental-gen t
    ( reflexive-Eq-ΠΣ C t)
    ( is-contr-total-Eq-ΠΣ C t)
    ( Eq-ΠΣ-eq C t)

eq-Eq-ΠΣ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → Eq-ΠΣ C t t' → Id t t'
eq-Eq-ΠΣ C t t' = inv-is-equiv (is-equiv-Eq-ΠΣ-eq C t t')


{- Since the identity types of type-choice-∞ and of products of total spaces
   are again of the same form, it follows that the action on paths of
   inv-choice-∞ is again of the form inv-choice-∞.
-}

square-ap-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : type-choice-∞ C) →
  coherence-square
    ( Eq-type-choice-∞-eq C t t')
    ( ap inv-choice-∞ {x = t} {y = t'})
    ( inv-choice-∞)
    ( Eq-ΠΣ-eq C (inv-choice-∞ t) (inv-choice-∞ t'))
square-ap-inv-choice-∞ C (pair f g) .(pair f g) refl = refl

coherence-square-inv-is-equiv-horizontal :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D) (H : (h ∘ f) ~ (k ∘ g)) →
  (is-equiv-h : is-equiv h) → (is-equiv-g : is-equiv g) →
  coherence-square (inv-is-equiv is-equiv-g) k f (inv-is-equiv is-equiv-h)
coherence-square-inv-is-equiv-horizontal f g h k H is-equiv-h is-equiv-g c =
  ( ap
    ( (inv-is-equiv is-equiv-h) ∘ k)
    ( inv (issec-inv-is-equiv is-equiv-g c))) ∙
  ( ( ap
      ( inv-is-equiv is-equiv-h)
      ( inv (H (inv-is-equiv is-equiv-g c)))) ∙
    ( isretr-inv-is-equiv is-equiv-h (f (inv-is-equiv is-equiv-g c))))
-}
