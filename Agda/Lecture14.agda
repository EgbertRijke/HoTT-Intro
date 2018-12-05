{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture14 where

import Cubical-diagrams
open Cubical-diagrams public

-- Section 14.1 Families over pushouts

generating-data-fam-pushout :
  {l1 l2 l3 : Level} (l : Level)
  {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ lsuc l)))
generating-data-fam-pushout l {S} {A} {B} f g =
  Σ ( A → UU l)
    ( λ PA → Σ (B → UU l)
      ( λ PB → (s : S) → PA (f s) ≃ PB (g s)))

generating-data-fam-pushout-cocone-UU :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  cocone f g (UU l) → generating-data-fam-pushout l f g
generating-data-fam-pushout-cocone-UU l f g =
  tot (λ PA → (tot (λ PB H s → equiv-eq (H s))))

is-equiv-generating-data-fam-pushout-cocone-UU :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  is-equiv (generating-data-fam-pushout-cocone-UU l f g)
is-equiv-generating-data-fam-pushout-cocone-UU l f g =
  is-equiv-tot-is-fiberwise-equiv
    ( λ PA → is-equiv-tot-is-fiberwise-equiv
      ( λ PB → is-equiv-postcomp-Π
        ( λ s → equiv-eq)
        ( λ s → univalence (PA (f s)) (PB (g s)))))

gen-fam-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  (P : X → UU l) → generating-data-fam-pushout l f g
gen-fam-pushout f g (dpair i (dpair j H)) P =
  dpair
    ( P ∘ i)
    ( dpair
      ( P ∘ j)
      ( λ s → (dpair (tr P (H s)) (is-equiv-tr P (H s)))))

equiv-eq-ap-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A} (p : Id x y) →
  Id (equiv-tr B p) (equiv-eq (ap B p))
equiv-eq-ap-fam B refl = refl

triangle-gen-fam-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ( gen-fam-pushout {l = l} f g c) ~
  ( ( generating-data-fam-pushout-cocone-UU l f g) ∘
    ( cocone-map f g {Y = UU l} c))
triangle-gen-fam-pushout {l = l} {S} {A} {B} {X} f g (dpair i (dpair j H)) P =
  eq-pair
    ( dpair refl
      ( eq-pair
        ( dpair refl
          ( eq-htpy (λ s → equiv-eq-ap-fam P (H s))))))

coherence-htpy-generating-data-fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  (PA : A → UU l) (PB : B → UU l) (PS : (s : S) → (PA (f s)) ≃ (PB (g s))) →
  (PA' : A → UU l) (PB' : B → UU l)
  (PS' : (s : S) → (PA' (f s)) ≃ (PB' (g s))) →
  (eA : (a : A) → (PA a) ≃ (PA' a)) (eB : (b : B) → (PB b) ≃ (PB' b)) →
  UU (l1 ⊔ l)
coherence-htpy-generating-data-fam-pushout {S = S}
  f g PA PB PS PA' PB' PS' eA eB =
  ( s : S) →
    ( (eqv-map (eB (g s))) ∘ (eqv-map (PS s))) ~
    ( (eqv-map (PS' s)) ∘ (eqv-map (eA (f s))))

is-contr-total-Eq-substructure :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {P : A → UU l3} →
  is-contr (Σ A B) → (is-subtype P) → (a : A) (b : B a) (p : P a) →
  is-contr (Σ (Σ A P) (λ t → B (pr1 t)))
is-contr-total-Eq-substructure {A = A} {B} {P} is-contr-AB is-subtype-P a b p =
  is-contr-is-equiv
    ( Σ (Σ A B) (λ t → P (pr1 t)))
    ( double-structure-swap A P B)
    ( is-equiv-double-structure-swap A P B)
    ( is-contr-is-equiv'
      ( P a)
      ( left-unit-law-Σ-map-gen (λ t → P (pr1 t)) is-contr-AB (dpair a b))
      ( is-equiv-left-unit-law-Σ-map-gen _ is-contr-AB (dpair a b))
      ( is-contr-is-prop-inh (is-subtype-P a) p))

htpy-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A ≃ B → A ≃ B → UU (l1 ⊔ l2)
htpy-equiv e e' = (eqv-map e) ~ (eqv-map e')

is-contr-total-htpy-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-contr (Σ (A ≃ B) (λ e' → htpy-equiv e e'))
is-contr-total-htpy-equiv (dpair f is-equiv-f) =
  is-contr-total-Eq-substructure
    ( is-contr-total-htpy f)
    ( is-subtype-is-equiv)
    ( f)
    ( htpy-refl f)
    ( is-equiv-f)

is-contr-total-coherence-htpy-generating-data-fam-pushout :
  {l1 l2 l3 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  (PA : A → UU l) (PB : B → UU l)
  (PS : (s : S) → (PA (f s)) ≃ (PB (g s))) →
  is-contr (Σ ((s : S) → (PA (f s)) ≃ (PB (g s)))
    ( λ PS' → coherence-htpy-generating-data-fam-pushout
      f g PA PB PS PA PB PS' (λ a → equiv-id (PA a)) (λ b → equiv-id (PB b))))
is-contr-total-coherence-htpy-generating-data-fam-pushout {S = S} f g PA PB PS =
  is-contr-is-equiv'
    ( (s : S) →
      Σ ( (PA (f s)) ≃ (PB (g s)))
        ( λ PS's → ((eqv-map (PS s))) ~ (eqv-map (PS's))))
    ( choice-∞)
    ( is-equiv-choice-∞)
    ( is-contr-Π
      ( λ s → is-contr-total-htpy-equiv (PS s)))

htpy-generating-data-fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  (s t : generating-data-fam-pushout l f g) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l)))
htpy-generating-data-fam-pushout l {S} {A} {B} f g
  (dpair PA (dpair PB PS)) t =
  let PA' = pr1 t
      PB' = pr1 (pr2 t)
      PS' = pr2 (pr2 t)
  in
  Σ ( (a : A) → (PA a) ≃ (PA' a))
    ( λ eA → Σ ( (b : B) → (PB b) ≃ (PB' b))
      ( λ eB →
        coherence-htpy-generating-data-fam-pushout
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

is-contr-total-htpy-generating-data-fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s : generating-data-fam-pushout l f g) →
  is-contr
    ( Σ ( generating-data-fam-pushout l f g)
      ( htpy-generating-data-fam-pushout l f g s))
is-contr-total-htpy-generating-data-fam-pushout l {S} {A} {B} f g
  ( dpair PA (dpair PB PS)) =
  is-contr-total-Eq-structure
    ( λ PA' t eA →
      let PB' = pr1 t
          PS' = pr2 t
      in
      Σ ( (b : B) → (PB b) ≃ (PB' b))
        ( λ eB →
          coherence-htpy-generating-data-fam-pushout
            f g PA PB PS PA' PB' PS' eA eB))
    ( is-contr-total-fam-equiv PA)
    ( dpair PA (λ a → equiv-id (PA a)))
    ( is-contr-total-Eq-structure
      ( λ PB' PS' eB →
        coherence-htpy-generating-data-fam-pushout
        f g PA PB PS PA PB' PS' (λ a → equiv-id (PA a)) eB)
      ( is-contr-total-fam-equiv PB)
      ( dpair PB (λ b → equiv-id (PB b)))
      ( is-contr-total-coherence-htpy-generating-data-fam-pushout f g PA PB PS))
