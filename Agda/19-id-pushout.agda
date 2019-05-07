{-# OPTIONS --without-K --exact-split #-}

module 19-id-pushout where

import 18-descent
open 18-descent public

-- Section 19.1 Characterizing the identity types of pushouts

hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) (P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l4 ⊔ l5))))
hom-Fam-pushout {S = S} {A} {B}
  f g P Q =
  Σ ( (x : A) → ((pr1 P) x) → ((pr1 Q) x)) (λ hA →
    Σ ( (y : B) → ((pr1 (pr2 P)) y) → ((pr1 (pr2 Q)) y)) (λ hB →
      ( s : S) → ((hB (g s)) ∘ (map-equiv (pr2 (pr2 P) s))) ~
      ( (map-equiv (pr2 (pr2 Q) s)) ∘ (hA (f s)))))

{- We characterize the identity type of hom-Fam-pushout. -}

Eq-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  ( h k : hom-Fam-pushout f g P Q) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l4 ⊔ l5))))
Eq-hom-Fam-pushout {S = S} {A} {B} f g P Q h k =
  Σ ( (x : A) → (pr1 h x) ~ (pr1 k x)) (λ HA →
    Σ ( (y : B) → (pr1 (pr2 h) y) ~ (pr1 (pr2 k) y)) (λ HB →
      ( s : S) →
      ( ((HB (g s)) ·r (map-equiv (pr2 (pr2 P) s))) ∙h (pr2 (pr2 k) s)) ~
      ((pr2 (pr2 h) s) ∙h ((map-equiv (pr2 (pr2 Q) s)) ·l (HA (f s))))))

reflexive-Eq-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  ( h : hom-Fam-pushout f g P Q) → Eq-hom-Fam-pushout f g P Q h h
reflexive-Eq-hom-Fam-pushout f g P Q h =
  pair
    ( λ x → htpy-refl)
    ( pair
      ( λ y → htpy-refl)
      ( λ s → htpy-inv htpy-right-unit))

Eq-hom-Fam-pushout-eq :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  ( h k : hom-Fam-pushout f g P Q) → Id h k → Eq-hom-Fam-pushout f g P Q h k
Eq-hom-Fam-pushout-eq f g P Q h .h refl =
  reflexive-Eq-hom-Fam-pushout f g P Q h

is-contr-total-Eq-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  ( h : hom-Fam-pushout f g P Q) →
  is-contr (Σ (hom-Fam-pushout f g P Q) (Eq-hom-Fam-pushout f g P Q h))
is-contr-total-Eq-hom-Fam-pushout {S = S} {A} {B} f g P Q h =
  is-contr-total-Eq-structure
    ( λ kA kB-ke (HA : (x : A) → (pr1 h x) ~ (kA x)) →
        Σ ( (y : B) → (pr1 (pr2 h) y) ~ (pr1 kB-ke y)) (λ HB →
          ( s : S) →
            ( ((HB (g s)) ·r (map-equiv (pr2 (pr2 P) s))) ∙h (pr2 kB-ke s)) ~
            ( (pr2 (pr2 h) s) ∙h ((map-equiv (pr2 (pr2 Q) s)) ·l (HA (f s))))))
    ( is-contr-total-Eq-Π
      ( λ x τ → (pr1 h x) ~ τ)
      ( λ x → is-contr-total-htpy (pr1 h x))
      ( pr1 h))
    ( pair (pr1 h) (λ x → htpy-refl))
    ( is-contr-total-Eq-structure
      ( λ kB ke (HB : (y : B) → (pr1 (pr2 h) y) ~ kB y) →
        (s : S) →
          ( ((HB (g s)) ·r (map-equiv (pr2 (pr2 P) s))) ∙h (ke s)) ~
          ( (pr2 (pr2 h) s) ∙h ((map-equiv (pr2 (pr2 Q) s)) ·l htpy-refl)))
      ( is-contr-total-Eq-Π
        ( λ y τ → (pr1 (pr2 h) y) ~ τ)
        ( λ y → is-contr-total-htpy (pr1 (pr2 h) y))
        ( pr1 (pr2 h)))
      ( pair (pr1 (pr2 h)) (λ y → htpy-refl))
      ( is-contr-total-Eq-Π
        ( λ (s : S) he →
          (he ~ (pr2 (pr2 h) s ∙h (pr1 (pr2 (pr2 Q) s) ·l htpy-refl))))
        ( λ s → is-contr-total-htpy'
          ((pr2 (pr2 h) s) ∙h ((map-equiv (pr2 (pr2 Q) s)) ·l htpy-refl)))
        ( λ s →
          ((pr2 (pr2 h) s) ∙h ((map-equiv (pr2 (pr2 Q) s)) ·l htpy-refl)))))

is-equiv-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} {P : Fam-pushout l4 f g} {Q : Fam-pushout l5 f g} →
  hom-Fam-pushout f g P Q → UU _
is-equiv-hom-Fam-pushout {A = A} {B} {f} {g} {P} {Q} h =
  ((a : A) → is-equiv (pr1 h a)) × ((b : B) → is-equiv (pr1 (pr2 h) b)) 

is-Eq-pushout :
  { l1 l2 l3 l4 : Level} (l5 : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) (a : A) →
  ( P : Fam-pushout l4 f g) (p₀ : pr1 P a) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
is-Eq-pushout l5 f g a P p₀ =
  ( Q : Fam-pushout l5 f g) (q : (pr1 Q) a) →
  is-contr (Σ (hom-Fam-pushout f g P Q) (λ h → Id ((pr1 h) a p₀) q))

is-identity-is-Eq-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l5}
  ( f : S → A) (g : S → B) (c : cocone f g X) →
  ( up-X : (l : Level) → universal-property-pushout l f g c) →
  ( a : A) (P : Fam-pushout l4 f g) (p₀ : pr1 P a) →
  is-Eq-pushout _ f g a P p₀ →
  Eq-Fam-pushout _ f g P (Fam-pushout-fam f g c (Id (pr1 c a)))
is-identity-is-Eq-pushout f g c up-X a P p₀ is-eq-P = ?
