{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module 19-id-pushout where

import 18-descent
open 18-descent public

-- Section 19.1 Characterizing families of maps over pushouts

module hom-Fam-pushout
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1}
  { A : UU l2}
  { B : UU l3}
  { f : S → A}
  { g : S → B}
  ( P : Fam-pushout l4 f g)
  ( Q : Fam-pushout l5 f g)
  where

  private
    PA = pr1 P
    PB = pr1 (pr2 P)
    PS = pr2 (pr2 P)
    QA = pr1 Q
    QB = pr1 (pr2 Q)
    QS = pr2 (pr2 Q)

  {- Definition 19.1.1 -}
  
  hom-Fam-pushout :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  hom-Fam-pushout =
    Σ ( (x : A) → (PA x) → (QA x)) (λ hA →
      Σ ( (y : B) → (PB y) → (QB y)) (λ hB →
        ( s : S) →
          ( (hB (g s)) ∘ (map-equiv (PS s))) ~ ((map-equiv (QS s)) ∘ (hA (f s)))))

  {- Remark 19.1.2. We characterize the identity type of hom-Fam-pushout. -}
  
  htpy-hom-Fam-pushout :
    ( h k : hom-Fam-pushout) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  htpy-hom-Fam-pushout h k =
    Σ ( (x : A) → (pr1 h x) ~ (pr1 k x)) (λ HA →
      Σ ( (y : B) → (pr1 (pr2 h) y) ~ (pr1 (pr2 k) y)) (λ HB →
        ( s : S) →
        ( ((HB (g s)) ·r (map-equiv (PS s))) ∙h (pr2 (pr2 k) s)) ~
        ( (pr2 (pr2 h) s) ∙h ((map-equiv (QS s)) ·l (HA (f s))))))

  reflexive-htpy-hom-Fam-pushout :
    ( h : hom-Fam-pushout) → htpy-hom-Fam-pushout h h
  reflexive-htpy-hom-Fam-pushout h =
    pair
      ( λ x → htpy-refl)
      ( pair
        ( λ y → htpy-refl)
        ( λ s → htpy-inv htpy-right-unit))

  htpy-hom-Fam-pushout-eq :
    ( h k : hom-Fam-pushout) → Id h k → htpy-hom-Fam-pushout h k
  htpy-hom-Fam-pushout-eq h .h refl =
    reflexive-htpy-hom-Fam-pushout h

  is-contr-total-htpy-hom-Fam-pushout :
    ( h : hom-Fam-pushout) →
    is-contr (Σ (hom-Fam-pushout) (htpy-hom-Fam-pushout h))
  is-contr-total-htpy-hom-Fam-pushout h =
    is-contr-total-Eq-structure
      ( λ kA kB-ke (HA : (x : A) → (pr1 h x) ~ (kA x)) →
          Σ ( (y : B) → (pr1 (pr2 h) y) ~ (pr1 kB-ke y)) (λ HB →
            ( s : S) →
              ( ((HB (g s)) ·r (map-equiv (PS s))) ∙h (pr2 kB-ke s)) ~
              ( (pr2 (pr2 h) s) ∙h ((map-equiv (QS s)) ·l (HA (f s))))))
      ( is-contr-total-Eq-Π
        ( λ x τ → (pr1 h x) ~ τ)
        ( λ x → is-contr-total-htpy (pr1 h x))
        ( pr1 h))
      ( pair (pr1 h) (λ x → htpy-refl))
      ( is-contr-total-Eq-structure
        ( λ kB ke (HB : (y : B) → (pr1 (pr2 h) y) ~ kB y) →
          (s : S) →
            ( ((HB (g s)) ·r (map-equiv (PS s))) ∙h (ke s)) ~
            ( (pr2 (pr2 h) s) ∙h ((map-equiv (QS s)) ·l htpy-refl)))
        ( is-contr-total-Eq-Π
          ( λ y τ → (pr1 (pr2 h) y) ~ τ)
          ( λ y → is-contr-total-htpy (pr1 (pr2 h) y))
          ( pr1 (pr2 h)))
        ( pair (pr1 (pr2 h)) (λ y → htpy-refl))
        ( is-contr-total-Eq-Π
          ( λ (s : S) he →
            (he ~ (pr2 (pr2 h) s ∙h (map-equiv (QS s) ·l htpy-refl))))
          ( λ s → is-contr-total-htpy'
            ((pr2 (pr2 h) s) ∙h ((map-equiv (QS s)) ·l htpy-refl)))
          ( λ s →
            ((pr2 (pr2 h) s) ∙h ((map-equiv (QS s)) ·l htpy-refl)))))

  is-equiv-htpy-hom-Fam-pushout-eq :
    ( h k : hom-Fam-pushout) → is-equiv (htpy-hom-Fam-pushout-eq h k)
  is-equiv-htpy-hom-Fam-pushout-eq h =
    fundamental-theorem-id h
      ( reflexive-htpy-hom-Fam-pushout h)
      ( is-contr-total-htpy-hom-Fam-pushout h)
      ( htpy-hom-Fam-pushout-eq h)

  eq-htpy-hom-Fam-pushout :
    ( h k : hom-Fam-pushout) → htpy-hom-Fam-pushout h k → Id h k
  eq-htpy-hom-Fam-pushout h k =
    inv-is-equiv (is-equiv-htpy-hom-Fam-pushout-eq h k)
  
open hom-Fam-pushout public

{- Definition 19.1.3. Given a cocone structure on X and a family of maps indexed
   by X, we obtain a morphism of descent data. -}

Naturality-fam-maps :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( f : (a : A) → B a → C a) {x x' : A} (p : Id x x') → UU _
Naturality-fam-maps {B = B} {C} f {x} {x'} p =
  (y : B x) → Id (f x' (tr B p y)) (tr C p (f x y))

naturality-fam-maps :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( f : (a : A) → B a → C a) {x x' : A} (p : Id x x') →
  Naturality-fam-maps f p
naturality-fam-maps f refl y = refl

hom-Fam-pushout-map :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( P : X → UU l5) (Q : X → UU l6) → ((x : X) → P x → Q x) →
  hom-Fam-pushout (desc-fam c P) (desc-fam c Q)
hom-Fam-pushout-map {f = f} {g} c P Q h =
  pair
    ( precomp-Π (pr1 c) (λ x → P x → Q x) h)
    ( pair
      ( precomp-Π (pr1 (pr2 c)) (λ x → P x → Q x) h)
      ( λ s → naturality-fam-maps h (pr2 (pr2 c) s)))

{- Theorem 19.1.4. The function hom-Fam-pushout-map is an equivalence. -}

square-path-over-fam-maps :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  { x x' : A} (p : Id x x') (f : B x → C x) (f' : B x' → C x') →
  Id (tr (λ a → B a → C a) p f) f' →
  ( y : B x) → Id (f' (tr B p y)) (tr C p (f y))
square-path-over-fam-maps refl f f' = htpy-eq ∘ inv

hom-Fam-pushout-dep-cocone :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( P : X → UU l5) (Q : X → UU l6) →
  dep-cocone f g c (λ x → P x → Q x) →
  hom-Fam-pushout (desc-fam c P) (desc-fam c Q)
hom-Fam-pushout-dep-cocone {f = f} {g} c P Q =
  tot (λ hA → tot (λ hB →
    postcomp-Π (λ s →
      square-path-over-fam-maps (pr2 (pr2 c) s) (hA (f s)) (hB (g s)))))

is-equiv-square-path-over-fam-maps :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  { x x' : A} (p : Id x x') (f : B x → C x) (f' : B x' → C x') →
  is-equiv (square-path-over-fam-maps p f f')
is-equiv-square-path-over-fam-maps refl f f' =
  is-equiv-comp' htpy-eq inv (is-equiv-inv f f') (funext f' f)
  
is-equiv-hom-Fam-pushout-dep-cocone :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( P : X → UU l5) (Q : X → UU l6) →
  is-equiv (hom-Fam-pushout-dep-cocone c P Q)
is-equiv-hom-Fam-pushout-dep-cocone {f = f} {g} c P Q =
  is-equiv-tot-is-fiberwise-equiv (λ hA →
    is-equiv-tot-is-fiberwise-equiv (λ hB →
      is-equiv-postcomp-Π _
        ( λ s → is-equiv-square-path-over-fam-maps
          ( pr2 (pr2 c) s)
          ( hA (f s))
          ( hB (g s)))))

coherence-naturality-fam-maps :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (P : B → UU l3) (Q : B → UU l4) →
  { f f' : A → B} (H : f ~ f') (h : (b : B) → P b → Q b) (a : A) →
  Id ( square-path-over-fam-maps (H a) (h (f a)) (h (f' a)) (apd h (H a)))
     ( naturality-fam-maps h (H a))
coherence-naturality-fam-maps {A = A} {B} P Q {f} {f'} H =
  ind-htpy f
    ( λ f' H →
      ( h : (b : B) → P b → Q b) (a : A) →
      Id ( square-path-over-fam-maps (H a) (h (f a)) (h (f' a)) (apd h (H a)))
         ( naturality-fam-maps h (H a)))
    ( λ h a → refl)
    ( H)

triangle-hom-Fam-pushout-dep-cocone :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( P : X → UU l5) (Q : X → UU l6) →
  ( hom-Fam-pushout-map c P Q) ~
  ( ( hom-Fam-pushout-dep-cocone c P Q) ∘
    ( dep-cocone-map f g c (λ x → P x → Q x)))
triangle-hom-Fam-pushout-dep-cocone {f = f} {g} c P Q h =
  eq-htpy-hom-Fam-pushout
    ( desc-fam c P)
    ( desc-fam c Q)
    ( hom-Fam-pushout-map c P Q h)
    ( hom-Fam-pushout-dep-cocone c P Q
      ( dep-cocone-map f g c (λ x → P x → Q x) h))
    ( pair
      ( λ a → htpy-refl)
      ( pair
        ( λ b → htpy-refl)
        ( λ s →
          ( htpy-eq
            ( coherence-naturality-fam-maps P Q (pr2 (pr2 c)) h s)) ∙h
          ( htpy-inv htpy-right-unit))))

is-equiv-hom-Fam-pushout-map :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : (l : Level) → universal-property-pushout l f g c)
  ( P : X → UU l5) (Q : X → UU l6) →
  is-equiv (hom-Fam-pushout-map c P Q)
is-equiv-hom-Fam-pushout-map {l5 = l5} {l6} {f = f} {g} c up-X P Q =
  is-equiv-comp
    ( hom-Fam-pushout-map c P Q)
    ( hom-Fam-pushout-dep-cocone c P Q)
    ( dep-cocone-map f g c (λ x → P x → Q x))
    ( triangle-hom-Fam-pushout-dep-cocone c P Q)
    ( dependent-universal-property-universal-property-pushout
      f g c up-X (l5 ⊔ l6) (λ x → P x → Q x))
    ( is-equiv-hom-Fam-pushout-dep-cocone c P Q)

equiv-hom-Fam-pushout-map :
  { l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : (l : Level) → universal-property-pushout l f g c)
  ( P : X → UU l5) (Q : X → UU l6) →
  ( (x : X) → P x → Q x) ≃
  hom-Fam-pushout (desc-fam c P) (desc-fam c Q)
equiv-hom-Fam-pushout-map c up-X P Q =
  pair
    ( hom-Fam-pushout-map c P Q)
    ( is-equiv-hom-Fam-pushout-map c up-X P Q)

{- Definition 19.2.1. Universal families over spans -}

ev-pt-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} (P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g)
  {a : A} → (pr1 P a) → (hom-Fam-pushout P Q) → pr1 Q a
ev-pt-hom-Fam-pushout P Q {a} p h = pr1 h a p 

is-universal-Fam-pushout :
  { l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} (P : Fam-pushout l4 f g) (a : A) (p : pr1 P a) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
is-universal-Fam-pushout l {f = f} {g} P a p =
  ( Q : Fam-pushout l f g) → is-equiv (ev-pt-hom-Fam-pushout P Q p)

{- Lemma 19.2.2. The descent data of the identity type is a universal family. -}

triangle-is-universal-id-Fam-pushout' :
  { l l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X)
  (a : A) ( Q : (x : X) → UU l) →
  ( ev-refl (pr1 c a) {B = λ x p → Q x}) ~
  ( ( ev-pt-hom-Fam-pushout
      ( desc-fam c (Id (pr1 c a)))
      ( desc-fam c Q)
      ( refl)) ∘
    ( hom-Fam-pushout-map c (Id (pr1 c a)) Q))
triangle-is-universal-id-Fam-pushout' c a Q = htpy-refl

is-universal-id-Fam-pushout' :
  { l l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X)
  ( up-X : (l' : Level) → universal-property-pushout l' f g c) (a : A) →
  ( Q : (x : X) → UU l) →
  is-equiv
    ( ev-pt-hom-Fam-pushout
      ( desc-fam c (Id (pr1 c a)))
      ( desc-fam c Q)
      ( refl))
is-universal-id-Fam-pushout' c up-X a Q =
  is-equiv-left-factor
    ( ev-refl (pr1 c a) {B = λ x p → Q x})
    ( ev-pt-hom-Fam-pushout
      ( desc-fam c (Id (pr1 c a)))
      ( desc-fam c Q)
      ( refl))
    ( hom-Fam-pushout-map c (Id (pr1 c a)) Q)
    ( triangle-is-universal-id-Fam-pushout' c a Q)
    ( is-equiv-ev-refl (pr1 c a))
    ( is-equiv-hom-Fam-pushout-map c up-X (Id (pr1 c a)) Q)

is-universal-id-Fam-pushout :
  { l1 l2 l3 l4 : Level} (l : Level)
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { f : S → A} {g : S → B} (c : cocone f g X)
  ( up-X : (l' : Level) → universal-property-pushout l' f g c) (a : A) →
  is-universal-Fam-pushout l (desc-fam c (Id (pr1 c a))) a refl
is-universal-id-Fam-pushout l {S = S} {A} {B} {X} {f} {g} c up-X a Q =
  inv-map-equiv
    ( precomp-Π-equiv
      ( equiv-desc-fam c up-X)
      ( λ (Q : Fam-pushout l f g) →
        is-equiv (ev-pt-hom-Fam-pushout
          ( desc-fam c (Id (pr1 c a))) Q refl)))
    ( is-universal-id-Fam-pushout' c up-X a)
    ( Q)

{- We construct the identity morphism and composition, and we show that 
   morphisms equipped with two-sided inverses are equivalences. -}

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
comp-hom-Fam-pushout {f = f} {g} P Q R k h =
  pair
    ( λ a → (pr1 k a) ∘ (pr1 h a))
    ( pair
      ( λ b → (pr1 (pr2 k) b) ∘ (pr1 (pr2 h) b))
      ( λ s → coherence-square-comp-horizontal
        ( pr1 h (f s))
        ( pr1 k (f s))
        ( map-equiv (pr2 (pr2 P) s))
        ( map-equiv (pr2 (pr2 Q) s))
        ( map-equiv (pr2 (pr2 R) s))
        ( pr1 (pr2 h) (g s))
        ( pr1 (pr2 k) (g s))
        ( pr2 (pr2 h) s)
        ( pr2 (pr2 k) s)))

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

is-equiv-has-inverse-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} →
  ( P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) (h : hom-Fam-pushout P Q) →
  has-inverse-hom-Fam-pushout P Q h → is-equiv-hom-Fam-pushout P Q h
is-equiv-has-inverse-hom-Fam-pushout P Q h has-inv-h =
  pair
    ( λ a →
      is-equiv-has-inverse
        ( pr1 (pr1 has-inv-h) a)
        ( pr1 (pr1 (pr2 has-inv-h)) a)
        ( pr1 (pr2 (pr2 has-inv-h)) a))
    ( λ b →
      is-equiv-has-inverse
        ( pr1 (pr2 (pr1 has-inv-h)) b)
        ( pr1 (pr2 (pr1 (pr2 has-inv-h))) b)
        ( pr1 (pr2 (pr2 (pr2 has-inv-h))) b))

equiv-is-equiv-hom-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { f : S → A} {g : S → B} (P : Fam-pushout l4 f g) (Q : Fam-pushout l5 f g) →
  ( h : hom-Fam-pushout P Q) →
  is-equiv-hom-Fam-pushout P Q h → equiv-Fam-pushout P Q
equiv-is-equiv-hom-Fam-pushout P Q h is-equiv-h =
  pair
    ( λ a → pair (pr1 h a) (pr1 is-equiv-h a))
    ( pair
      ( λ b → pair (pr1 (pr2 h) b) (pr2 is-equiv-h b))
      ( pr2 (pr2 h)))

{- Theorem 19.1.3. Characterization of identity types of pushouts. -}

hom-identity-is-universal-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l5}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : (l : Level) → universal-property-pushout l f g c) →
  ( P : Fam-pushout l4 f g) (a : A) (p : pr1 P a) →
  is-universal-Fam-pushout l5 P a p →
  Σ ( hom-Fam-pushout P (desc-fam c (Id (pr1 c a))))
    ( λ h → Id (pr1 h a p) refl)
hom-identity-is-universal-Fam-pushout {f = f} {g} c up-X P a p is-univ-P =
  {!!}

is-identity-is-universal-Fam-pushout :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l5}
  { f : S → A} {g : S → B} (c : cocone f g X) →
  ( up-X : (l : Level) → universal-property-pushout l f g c) →
  ( P : Fam-pushout l4 f g) (a : A) (p : pr1 P a) →
  is-universal-Fam-pushout l5 P a p →
  Σ ( equiv-Fam-pushout P (desc-fam c (Id (pr1 c a))))
    ( λ e → Id (map-equiv (pr1 e a) p) refl)
is-identity-is-universal-Fam-pushout {f = f} {g} c up-X a P p₀ is-eq-P = {!!}
