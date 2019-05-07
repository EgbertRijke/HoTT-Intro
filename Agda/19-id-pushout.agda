{-# OPTIONS --without-K --exact-split #-}

module 19-id-pushout where

import 18-descent
open 18-descent public

-- Section 19.1 Characterizing the identity types of pushouts

hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} (P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
hom-Fam-pushout {S = S} {A} {B} {f = f} {g} P Q =
  Σ ( (x : A) → ((pr1 P) x) → ((pr1 Q) x)) (λ hA →
    Σ ( (y : B) → ((pr1 (pr2 P)) y) → ((pr1 (pr2 Q)) y)) (λ hB →
      ( s : S) → ((hB (g s)) ∘ (map-equiv (pr2 (pr2 P) s))) ~
      ( (map-equiv (pr2 (pr2 Q) s)) ∘ (hA (f s)))))

{- We characterize the identity type of hom-Fam-pushout. -}

htpy-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  ( h k : hom-Fam-pushout P Q) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l4 ⊔ l5))))
htpy-hom-Fam-pushout {S = S} {A} {B} {f} {g} P Q h k =
  Σ ( (x : A) → (pr1 h x) ~ (pr1 k x)) (λ HA →
    Σ ( (y : B) → (pr1 (pr2 h) y) ~ (pr1 (pr2 k) y)) (λ HB →
      ( s : S) →
      ( ((HB (g s)) ·r (map-equiv (pr2 (pr2 P) s))) ∙h (pr2 (pr2 k) s)) ~
      ((pr2 (pr2 h) s) ∙h ((map-equiv (pr2 (pr2 Q) s)) ·l (HA (f s))))))

reflexive-htpy-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  ( h : hom-Fam-pushout P Q) → htpy-hom-Fam-pushout P Q h h
reflexive-htpy-hom-Fam-pushout P Q h =
  pair
    ( λ x → htpy-refl)
    ( pair
      ( λ y → htpy-refl)
      ( λ s → htpy-inv htpy-right-unit))

htpy-hom-Fam-pushout-eq :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  ( h k : hom-Fam-pushout P Q) → Id h k → htpy-hom-Fam-pushout P Q h k
htpy-hom-Fam-pushout-eq P Q h .h refl =
  reflexive-htpy-hom-Fam-pushout P Q h

is-contr-total-htpy-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  ( h : hom-Fam-pushout P Q) →
  is-contr (Σ (hom-Fam-pushout P Q) (htpy-hom-Fam-pushout P Q h))
is-contr-total-htpy-hom-Fam-pushout {S = S} {A} {B} {f} {g} P Q h =
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

is-equiv-htpy-hom-Fam-pushout-eq :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  ( h k : hom-Fam-pushout P Q) →
  is-equiv (htpy-hom-Fam-pushout-eq P Q h k)
is-equiv-htpy-hom-Fam-pushout-eq P Q h =
  fundamental-theorem-id h
    ( reflexive-htpy-hom-Fam-pushout P Q h)
    ( is-contr-total-htpy-hom-Fam-pushout P Q h)
    ( htpy-hom-Fam-pushout-eq P Q h)

eq-htpy-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g)
  ( h k : hom-Fam-pushout P Q) → htpy-hom-Fam-pushout P Q h k → Id h k
eq-htpy-hom-Fam-pushout P Q h k =
  inv-is-equiv (is-equiv-htpy-hom-Fam-pushout-eq P Q h k)

{- We construct the identity morphism and composition. -}

id-hom-Fam-pushout :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) → hom-Fam-pushout P P
id-hom-Fam-pushout P =
  pair
    ( λ a → id)
    ( pair
      ( λ b → id)
      ( λ s → htpy-refl))

comp-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) (R : Fam-pushout l6 f g) →
  hom-Fam-pushout Q R → hom-Fam-pushout P Q → hom-Fam-pushout P R
comp-hom-Fam-pushout {f = f} {g} P Q R (pair kA (pair kB kS)) (pair hA (pair hB hS)) =
  pair
    ( λ a → (kA a) ∘ (hA a))
    ( pair
      ( λ b → (kB b) ∘ (hB b))
      ( λ s → coherence-square-comp-horizontal
        ( hA (f s))
        ( kA (f s))
        ( map-equiv (pr2 (pr2 P) s))
        ( map-equiv (pr2 (pr2 Q) s))
        ( map-equiv (pr2 (pr2 R) s))
        ( hB (g s))
        ( kB (g s))
        ( hS s)
        ( kS s)))

has-inverse-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) (h : hom-Fam-pushout P Q) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
has-inverse-hom-Fam-pushout P Q h =
  Σ ( hom-Fam-pushout Q P) (λ k →
    ( htpy-hom-Fam-pushout Q Q
      ( comp-hom-Fam-pushout Q P Q h k)
      ( id-hom-Fam-pushout Q)) ×
    ( htpy-hom-Fam-pushout P P
      ( comp-hom-Fam-pushout P Q P k h)
      ( id-hom-Fam-pushout P)))

is-equiv-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} (P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  hom-Fam-pushout P Q → UU (l2 ⊔ l3 ⊔ l4 ⊔ l5)
is-equiv-hom-Fam-pushout {A = A} {B} {f} {g} P Q h =
  ((a : A) → is-equiv (pr1 h a)) × ((b : B) → is-equiv (pr1 (pr2 h) b))
  
{- Definition 19.1.2. Universal families over spans -}

is-universal-Fam-pushout :
  { l1 l2 l3 l4 : Level} (l5 : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} (P : Fam-pushout l4 f g) (a : A) (p : pr1 P a) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
is-universal-Fam-pushout l5 {f = f} {g} P a p =
  ( Q : Fam-pushout l5 f g) (q : (pr1 Q) a) →
  is-contr (Σ (hom-Fam-pushout P Q) (λ h → Id ((pr1 h) a p) q))

{- Theorem 19.1.3. Characterization of identity types of pushouts. -}

hom-identity-is-universal-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l5}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : (l : Level) → universal-property-pushout l f g c) →
  ( P : Fam-pushout l4 f g) (a : A) (p : pr1 P a) →
  is-universal-Fam-pushout l5 P a p →
  Σ ( hom-Fam-pushout P (Fam-pushout-fam f g c (Id (pr1 c a))))
    ( λ h → Id (pr1 h a p) refl)
hom-identity-is-universal-Fam-pushout {f = f} {g} c up-X P a p is-univ-P =
  center
    ( is-univ-P
      ( Fam-pushout-fam f g c (Id (pr1 c a)))
      ( refl))

is-identity-is-universal-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l5}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : (l : Level) → universal-property-pushout l f g c) →
  ( P : Fam-pushout l4 f g) (a : A) (p : pr1 P a) →
  is-universal-Fam-pushout l5 P a p →
  Σ ( equiv-Fam-pushout P (Fam-pushout-fam f g c (Id (pr1 c a))))
    ( λ e → Id (map-equiv (pr1 e a) p) refl)
is-identity-is-universal-Fam-pushout {f = f} {g} c up-X a P p₀ is-eq-P = {!!}
