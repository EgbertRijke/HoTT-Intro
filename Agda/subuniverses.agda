{-# OPTIONS --without-K --allow-unsolved-metas #-}

module subuniverses where

import Lecture15
open Lecture15 public

is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU ((lsuc l1) ⊔ l2)
is-subuniverse P = is-subtype P

subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU ((lsuc l1) ⊔ l2)
subuniverse {l1} P = Σ (UU l1) P

Eq-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) (H : is-subuniverse P) →
  (s t : subuniverse P) → UU l1
Eq-subuniverse P H (dpair X p) t = X ≃ (pr1 t)

Eq-subuniverse-eq :
  {l1 l2 : Level} (P : UU l1 → UU l2) (H : is-subuniverse P) →
  (s t : subuniverse P) → Id s t → Eq-subuniverse P H s t
Eq-subuniverse-eq P H (dpair X p) .(dpair X p) refl = equiv-id X

is-contr-total-Eq-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) (H : is-subuniverse P)
  (s : subuniverse P) →
  is-contr (Σ (subuniverse P) (λ t → Eq-subuniverse P H s t))
is-contr-total-Eq-subuniverse P H (dpair X p) =
  is-contr-total-Eq-substructure (is-contr-total-equiv X) H X (equiv-id X) p

is-equiv-Eq-subuniverse-eq :
  {l1 l2 : Level} (P : UU l1 → UU l2) (H : is-subuniverse P)
  (s t : subuniverse P) → is-equiv (Eq-subuniverse-eq P H s t)
is-equiv-Eq-subuniverse-eq P H (dpair X p) = {!id-fundamental-gen (dpair X p) (equiv-id X) (is-contr-total-Eq-subuniverse P H (dpair X p)) (Eq-subuniverse-eq P H (dpair X p))!}

is-localization-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) (H : is-subuniverse P)
  (X : UU l1) (Y : subuniverse P) (l : X → pr1 Y) →
  UU ((lsuc l1) ⊔ l2)
is-localization-subuniverse {l1} P H X (dpair Y p) l =
  (Z : UU l1) (q : P Z) → is-equiv (λ (h : Y → Z) → h ∘ l)

Localizations-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) (H : is-subuniverse P) (X : UU l1) →
  UU ((lsuc l1) ⊔ l2)
Localizations-subuniverse {l1} P H X =
  Σ ( subuniverse P)
    ( λ Y → Σ (X → pr1 Y)
      ( λ l → is-localization-subuniverse P H X Y l))

Eq-total-is-localization-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) (H : is-subuniverse P) (X : UU l1) →
  ( s t : Localizations-subuniverse P H X) → UU l1
Eq-total-is-localization-subuniverse P H X
  (dpair (dpair Y p) (dpair l up)) (dpair (dpair Y' p') (dpair l' up')) =
  Σ ( Y ≃ Y')
    ( λ e → ((eqv-map e) ∘ l) ~ l' )

is-prop-total-is-localization-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) (H : is-subuniverse P) (X : UU l1) →
  is-prop (Localizations-subuniverse P H X)
is-prop-total-is-localization-subuniverse P H X = {!!}
