{-# OPTIONS --without-K --allow-unsolved-metas #-}

module subuniverses where

import Lecture15
open Lecture15 public

is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU ((lsuc l1) ⊔ l2)
is-subuniverse P = is-subtype P

is-local :
  {l1 l2 l3 l4 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3} (f : (i : I) → A i → B i)
  (X : UU l4) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
is-local {I = I} {B = B} f X =
  (i : I) → is-equiv (λ (h : B i → X) → h ∘ (f i))

is-subuniverse-is-local :
  {l1 l2 l3 l4 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3} (f : (i : I) → A i → B i) →
  is-subuniverse (is-local {l4 = l4} f)
is-subuniverse-is-local f X = is-prop-Π (λ i → is-subtype-is-equiv _)

subuniverse :
  (l1 l2 : Level) → UU ((lsuc l1) ⊔ (lsuc l2))
subuniverse l1 l2 = Σ (UU l1 → UU l2) is-subuniverse

total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU ((lsuc l1) ⊔ l2)
total-subuniverse {l1} P = Σ (UU l1) (pr1 P)

Eq-total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → UU l1
Eq-total-subuniverse (dpair P H) (dpair X p) t = X ≃ (pr1 t)

Eq-total-subuniverse-eq :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → Id s t → Eq-total-subuniverse P s t
Eq-total-subuniverse-eq (dpair P H) (dpair X p) .(dpair X p) refl = equiv-id X

is-contr-total-Eq-total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (s : total-subuniverse P) →
  is-contr (Σ (total-subuniverse P) (λ t → Eq-total-subuniverse P s t))
is-contr-total-Eq-total-subuniverse (dpair P H) (dpair X p) =
  is-contr-total-Eq-substructure (is-contr-total-equiv X) H X (equiv-id X) p

is-equiv-Eq-total-subuniverse-eq :
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (s t : total-subuniverse P) → is-equiv (Eq-total-subuniverse-eq P s t)
is-equiv-Eq-total-subuniverse-eq (dpair P H) (dpair X p) =
  id-fundamental-gen
    ( dpair X p)
    ( equiv-id X)
    ( is-contr-total-Eq-total-subuniverse (dpair P H) (dpair X p))
    ( Eq-total-subuniverse-eq (dpair P H) (dpair X p))

universal-property-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2)
  (X : UU l1) (Y : total-subuniverse P) (l : X → pr1 Y) →
  UU ((lsuc l1) ⊔ l2)
universal-property-localization {l1} (dpair P H) X (dpair Y p) l =
  (Z : UU l1) (q : P Z) → is-equiv (λ (h : Y → Z) → h ∘ l)

is-prop-universal-property-localization :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1)
  (Y : total-subuniverse P) (l : X → pr1 Y) →
  is-prop (universal-property-localization P X Y l)
is-prop-universal-property-localization (dpair P H) X (dpair Y p) l =
  is-prop-Π (λ Z → is-prop-Π (λ q → is-subtype-is-equiv _))

localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  UU ((lsuc l1) ⊔ l2)
localizations {l1} P X =
  Σ ( total-subuniverse P)
    ( λ Y → Σ (X → pr1 Y) (universal-property-localization P X Y))

Eq-localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  ( s t : localizations P X) → UU l1
Eq-localizations (dpair P H) X
  (dpair (dpair Y p) (dpair l up)) t =
  let Y' = pr1 (pr1 t)
      p' = pr1 (pr1 t)
      l' = pr1 (pr2 t)
      up' = pr2 (pr2 t)
  in
  Σ ( Y ≃ Y')
    ( λ e → ((eqv-map e) ∘ l) ~ l' )

reflexive-Eq-localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  (s : localizations P X) → Eq-localizations P X s s
reflexive-Eq-localizations (dpair P H) X (dpair (dpair Y p) (dpair l up)) =
  dpair (equiv-id Y) (htpy-refl l)

Eq-localizations-eq :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  ( s t : localizations P X) → Id s t → Eq-localizations P X s t
Eq-localizations-eq P X s s refl = reflexive-Eq-localizations P X s

is-contr-total-Eq-localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) (s : localizations P X) →
  is-contr (Σ (localizations P X) (Eq-localizations P X s))
is-contr-total-Eq-localizations
  (dpair P H) X (dpair (dpair Y p) (dpair l up)) =
  is-contr-total-Eq-structure
    ( λ Y' l' e → ((eqv-map e) ∘ l) ~ (pr1 l'))
    ( is-contr-total-Eq-total-subuniverse (dpair P H) (dpair Y p))
    ( dpair (dpair Y p) (equiv-id Y))
    ( is-contr-total-Eq-substructure
      ( is-contr-total-htpy l)
      ( is-prop-universal-property-localization (dpair P H) X (dpair Y p))
      ( l)
      ( htpy-refl _)
      ( up))

is-equiv-Eq-localizations-eq :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  ( s t : localizations P X) → is-equiv (Eq-localizations-eq P X s t)
is-equiv-Eq-localizations-eq P X s =
  id-fundamental-gen s
  ( reflexive-Eq-localizations P X s)
  ( is-contr-total-Eq-localizations P X s)
  ( Eq-localizations-eq P X s)

eq-Eq-localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1)
  ( s t : localizations P X) → (Eq-localizations P X s t) → Id s t
eq-Eq-localizations P X s t =
  inv-is-equiv (is-equiv-Eq-localizations-eq P X s t)

uniqueness-localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  ( s t : localizations P X) → Eq-localizations P X s t
uniqueness-localizations (dpair P H) X
  (dpair (dpair Y p) (dpair l up)) (dpair (dpair Y' p') (dpair l' up')) =
  dpair
    ( dpair
      ( inv-is-equiv (up Y' p') l')
      ( is-equiv-has-inverse
        ( dpair
          ( inv-is-equiv (up' Y p) l)
          ( dpair
            ( htpy-eq
              ( ap
                ( pr1 {B = λ h → Id (h ∘ l') l'})
                ( center
                  ( is-prop-is-contr
                    ( is-contr-map-is-equiv (up' Y' p') l')
                    ( dpair
                      ( ( inv-is-equiv (up Y' p') l') ∘
                        ( inv-is-equiv (up' Y p) l))
                      ( ( ap
                          ( λ t → (inv-is-equiv (up Y' p') l') ∘ t)
                          ( issec-inv-is-equiv (up' Y p) l)) ∙
                        ( issec-inv-is-equiv (up Y' p') l')))
                    ( dpair id refl)))))
            ( htpy-eq
              ( ap
                ( pr1 {B = λ h → Id (h ∘ l) l})
                ( center
                  ( is-prop-is-contr
                    ( is-contr-map-is-equiv (up Y p) l)
                    ( dpair
                      ( ( inv-is-equiv (up' Y p) l) ∘
                        ( inv-is-equiv (up Y' p') l'))
                      ( ( ap
                          ( λ t → (inv-is-equiv (up' Y p) l) ∘ t)
                          ( issec-inv-is-equiv (up Y' p') l')) ∙
                         issec-inv-is-equiv (up' Y p) l))
                    ( dpair id refl)))))))))
    ( htpy-eq (issec-inv-is-equiv (up Y' p') l'))

is-prop-localizations :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  is-prop (localizations P X)
is-prop-localizations P X =
  is-prop-is-prop'
    ( λ Y Y' → eq-Eq-localizations P X Y Y'
      ( uniqueness-localizations P X Y Y'))
