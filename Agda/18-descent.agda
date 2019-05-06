{-# OPTIONS --without-K --allow-unsolved-metas --exact-split #-}

module 18-descent where

import 17-cubical-diagrams
open 17-cubical-diagrams public

-- Section 18.1 Five equivalent characterizations of pushouts

dep-cocone :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X) (P : X → UU l5) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
dep-cocone {S = S} {A} {B} f g c P =
  Σ ((a : A) → P ((pr1 c) a)) (λ hA →
    Σ ((b : B) → P (pr1 (pr2 c) b)) (λ hB →
      (s : S) → Id (tr P (pr2 (pr2 c) s) (hA (f s))) (hB (g s))))

dep-cocone-map :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X) (P : X → UU l5) →
  ( (x : X) → P x) → dep-cocone f g c P
dep-cocone-map f g c P h =
  pair (λ a → h (pr1 c a)) (pair (λ b → h (pr1 (pr2 c) b)) (λ s → apd h (pr2 (pr2 c) s)))

{- Definition 18.1.1 The induction principle of pushouts -}

Ind-pushout :
  { l1 l2 l3 l4 : Level} (l : Level) →
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} →
  ( f : S → A) (g : S → B) (c : cocone f g X) → UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
Ind-pushout l {X = X} f g c =
  (P : X → UU l) → sec (dep-cocone-map f g c P)

{- Definition 18.1.2 The dependent universal property of pushouts -}

dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) → UU _
dependent-universal-property-pushout l f g {X} c =
  (P : X → UU l) → is-equiv (dep-cocone-map f g c P)

{- Remark 18.1.3. We compute the identity type of dep-cocone in order to 
   express the computation rules of the induction principle for pushouts. -}

coherence-htpy-dep-cocone :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  (P : X → UU l5) (c' c'' : dep-cocone f g c P)
  (K : (pr1 c') ~ (pr1 c'')) (L : (pr1 (pr2 c')) ~ (pr1 (pr2 c''))) →
  UU (l1 ⊔ l5)
coherence-htpy-dep-cocone {S = S} f g (pair i (pair j H)) P
  c' c'' K L =
  (s : S) → 
  Id ( ((pr2 (pr2 c')) s) ∙ (L (g s)))
     ( (ap (tr P (H s)) (K (f s))) ∙ ((pr2 (pr2 c'')) s))

htpy-dep-cocone :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s t : dep-cocone f g c P) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l5)))
htpy-dep-cocone {S = S} f g c P h h' =
  Σ ( (pr1 h) ~ (pr1 h')) (λ K →
    Σ ( (pr1 (pr2 h)) ~ (pr1 (pr2 h')))
      ( coherence-htpy-dep-cocone f g c P h h' K))

reflexive-htpy-dep-cocone :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s : dep-cocone f g c P) →
  htpy-dep-cocone f g c P s s
reflexive-htpy-dep-cocone f g (pair i (pair j H)) P
  (pair hA (pair hB hS)) =
  pair htpy-refl (pair htpy-refl htpy-right-unit)

htpy-dep-cocone-eq :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  {s t : dep-cocone f g c P} →
  Id s t → htpy-dep-cocone f g c P s t
htpy-dep-cocone-eq f g c P {s} {.s} refl =
  reflexive-htpy-dep-cocone f g c P s

abstract
  is-contr-total-htpy-dep-cocone :
    {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
    (s : dep-cocone f g c P) →
    is-contr
      ( Σ (dep-cocone f g c P)
        ( htpy-dep-cocone f g c P s))
  is-contr-total-htpy-dep-cocone
    {S = S} {A} {B} f g {X} (pair i (pair j H)) P (pair hA (pair hB hS)) =
    is-contr-total-Eq-structure
      ( λ α βγ K →
          Σ (hB ~ (pr1 βγ)) (λ L →
          coherence-htpy-dep-cocone f g
            ( pair i (pair j H)) P (pair hA (pair hB hS)) (pair α βγ) K L))
      ( is-contr-total-htpy hA)
      ( pair hA htpy-refl)
      ( is-contr-total-Eq-structure
        ( λ β γ L →
          coherence-htpy-dep-cocone f g
            ( pair i (pair j H))
            ( P)
            ( pair hA (pair hB hS))
            ( pair hA (pair β γ))
            ( htpy-refl)
            ( L))
        ( is-contr-total-htpy hB)
        ( pair hB htpy-refl)
        ( is-contr-is-equiv
          ( Σ ((s : S) → Id (tr P (H s) (hA (f s))) (hB (g s))) (λ γ → hS ~ γ))
          ( tot (htpy-concat (htpy-inv htpy-right-unit)))
          ( is-equiv-tot-is-fiberwise-equiv
            ( is-equiv-htpy-concat (htpy-inv htpy-right-unit)))
          ( is-contr-total-htpy hS)))

abstract
  is-equiv-htpy-dep-cocone-eq :
    {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
    (s t : dep-cocone f g c P) → is-equiv (htpy-dep-cocone-eq f g c P {s} {t})
  is-equiv-htpy-dep-cocone-eq f g c P s =
    fundamental-theorem-id s
      ( reflexive-htpy-dep-cocone f g c P s)
      ( is-contr-total-htpy-dep-cocone f g c P s)
      ( λ t → htpy-dep-cocone-eq f g c P {s} {t})

  eq-htpy-dep-cocone :
    {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
    (s t : dep-cocone f g c P) →
      htpy-dep-cocone f g c P s t → Id s t
  eq-htpy-dep-cocone f g c P s t =
    inv-is-equiv (is-equiv-htpy-dep-cocone-eq f g c P s t)

  issec-eq-htpy-dep-cocone :
    {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
      (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
    (s t : dep-cocone f g c P) →
    ( ( htpy-dep-cocone-eq f g c P {s} {t}) ∘
      ( eq-htpy-dep-cocone f g c P s t)) ~ id
  issec-eq-htpy-dep-cocone f g c P s t =
    issec-inv-is-equiv
    ( is-equiv-htpy-dep-cocone-eq f g c P s t)

  isretr-eq-htpy-dep-cocone :
    {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
    (s t : dep-cocone f g c P) →
    ( ( eq-htpy-dep-cocone f g c P s t) ∘
      ( htpy-dep-cocone-eq f g c P {s} {t})) ~ id
  isretr-eq-htpy-dep-cocone f g c P s t =
    isretr-inv-is-equiv
      ( is-equiv-htpy-dep-cocone-eq f g c P s t)

ind-pushout :
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} →
  ( f : S → A) (g : S → B) (c : cocone f g X) →
  Ind-pushout l f g c → (P : X → UU l) →
  dep-cocone f g c P → (x : X) → P x
ind-pushout f g c ind-c P =
  pr1 (ind-c P)

comp-pushout :
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} →
  ( f : S → A) (g : S → B) (c : cocone f g X) →
  ( ind-c : Ind-pushout l f g c) (P : X → UU l) (h : dep-cocone f g c P) →
  htpy-dep-cocone f g c P
    ( dep-cocone-map f g c P (ind-pushout f g c ind-c P h))
    ( h)
comp-pushout f g c ind-c P h =
  htpy-dep-cocone-eq f g c P (pr2 (ind-c P) h)

left-comp-pushout :
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} →
  ( f : S → A) (g : S → B) (c : cocone f g X) →
  ( ind-c : Ind-pushout l f g c) (P : X → UU l) (h : dep-cocone f g c P) →
  ( a : A) → Id (ind-pushout f g c ind-c P h (pr1 c a)) (pr1 h a)
left-comp-pushout f g c ind-c P h =
  pr1 (comp-pushout f g c ind-c P h)

right-comp-pushout :
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} →
  ( f : S → A) (g : S → B) (c : cocone f g X) →
  ( ind-c : Ind-pushout l f g c) (P : X → UU l) (h : dep-cocone f g c P) →
  ( b : B) → Id (ind-pushout f g c ind-c P h (pr1 (pr2 c) b)) (pr1 (pr2 h) b)
right-comp-pushout f g c ind-c P h =
  pr1 (pr2 (comp-pushout f g c ind-c P h))

path-comp-pushout :
  { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} →
  ( f : S → A) (g : S → B) (c : cocone f g X) →
  ( ind-c : Ind-pushout l f g c) (P : X → UU l) (h : dep-cocone f g c P) →
  coherence-htpy-dep-cocone f g c P
    ( dep-cocone-map f g c P (ind-pushout f g c ind-c P h))
    ( h)
    ( left-comp-pushout f g c ind-c P h)
    ( right-comp-pushout f g c ind-c P h)
path-comp-pushout f g c ind-c P h =
  pr2 (pr2 (comp-pushout f g c ind-c P h))

abstract
  uniqueness-dependent-universal-property-pushout :
    { l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} →
    ( f : S → A) (g : S → B) (c : cocone f g X)
    ( dup-c : dependent-universal-property-pushout l f g c) →
    ( P : X → UU l) ( h : dep-cocone f g c P) →
    is-contr
      ( Σ ((x : X) → P x) (λ k →
          htpy-dep-cocone f g c P (dep-cocone-map f g c P k) h))
  uniqueness-dependent-universal-property-pushout f g c dup-c P h =
    is-contr-is-equiv'
      ( fib (dep-cocone-map f g c P) h)
      ( tot (λ k → htpy-dep-cocone-eq f g c P))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ k → is-equiv-htpy-dep-cocone-eq f g c P
          ( dep-cocone-map f g c P k) h))
      ( is-contr-map-is-equiv (dup-c P) h)

{- This finishes the formalization of remark 18.1.3. -}

{- Before we state the main theorem of this section, we also state a dependent
   version of the pullback property of pushouts. -}

cone-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  let i = pr1 c
      j = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  cone
    ( λ (h : (a : A) → P (i a)) → λ (s : S) → tr P (H s) (h (f s)))
    ( λ (h : (b : B) → P (j b)) → λ s → h (g s))
    ( (x : X) → P x)
cone-dependent-pullback-property-pushout f g (pair i (pair j H)) P =
  pair
    ( λ h → λ a → h (i a))
    ( pair
      ( λ h → λ b → h (j b))
      ( λ h → eq-htpy (λ s → apd h (H s))))

dependent-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l4 ⊔ lsuc l))))
dependent-pullback-property-pushout l {S} {A} {B} f g {X}
  (pair i (pair j H)) =
  (P : X → UU l) →
  is-pullback
    ( λ (h : (a : A) → P (i a)) → λ s → tr P (H s) (h (f s)))
    ( λ (h : (b : B) → P (j b)) → λ s → h (g s))
    ( cone-dependent-pullback-property-pushout f g (pair i (pair j H)) P)

{- Theorem 18.1.4 The following properties are all equivalent:
 
   1. universal-property-pushout
   2. pullback-property-pushout
   3. dependent-pullback-property-pushout
   4. dependent-universal-property-pushout
   5. Ind-pushout

   We have already shown that 1 ↔ 2. Therefore we will first show that 
   3 ↔ 4 ↔ 5. Finally, we will show that 2 ↔ 3. Here are the precise references
   to the proofs of those parts:

   Proof of 1 → 2.
   pullback-property-pushout-universal-property-pushout

   Proof of 2 → 1
   universal-property-pushout-pullback-property-pushout

   Proof of 2 → 3
   dependent-pullback-property-pullback-property-pushout

   Proof of 3 → 2
   pullback-property-dependent-pullback-property-pushout

   Proof of 3 → 4
   dependent-universal-property-dependent-pullback-property-pushout

   Proof of 4 → 3
   dependent-pullback-property-dependent-universal-property-pushout

   Proof of 4 → 5
   Ind-pushout-dependent-universal-property-pushout

   Proof of 5 → 4
   dependent-universal-property-pushout-Ind-pushout
   -}

{- Proof of Theorem 18.1.4, (v) implies (iv). -}

dependent-naturality-square :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f f' : (x : A) → B x)
  {x x' : A} (p : Id x x') (q : Id (f x) (f' x)) (q' : Id (f x') (f' x')) →
  Id ((apd f p) ∙ q') ((ap (tr B p) q) ∙ (apd f' p)) →
  Id (tr (λ y → Id (f y) (f' y)) p q) q' 
dependent-naturality-square f f' refl q q' s =
  inv (s ∙ (right-unit ∙ (ap-id q)))

htpy-eq-dep-cocone-map :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ( H : (l : Level) → Ind-pushout l f g c) →
  {l : Level} {P : X → UU l} (h h' : (x : X) → P x) →
  Id (dep-cocone-map f g c P h) (dep-cocone-map f g c P h') → h ~ h'
htpy-eq-dep-cocone-map f g (pair i (pair j H)) I {l} {P} h h' p =
  let c = (pair i (pair j H))
      K = pr1 (htpy-dep-cocone-eq f g c P p)
      L = pr1 (pr2 (htpy-dep-cocone-eq f g c P p))
      M = pr2 (pr2 (htpy-dep-cocone-eq f g c P p))
  in
  pr1
    ( I _ (λ x → Id (h x) (h' x)))
    ( pair
      ( K)
      ( pair
        ( L)
        ( λ s →
          dependent-naturality-square h h' (H s) (K (f s)) (L (g s)) (M s))))

dependent-universal-property-pushout-Ind-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) → Ind-pushout l f g c) →
  ((l : Level) → dependent-universal-property-pushout l f g c)
dependent-universal-property-pushout-Ind-pushout f g c H l P =
  let ind-pushout  = pr1 (H l P)
      comp-pushout = pr2 (H l P)
  in
  is-equiv-has-inverse
    ( ind-pushout)
    ( comp-pushout)
    ( λ h → eq-htpy (htpy-eq-dep-cocone-map f g c H
      ( ind-pushout (dep-cocone-map f g c P h))
      ( h)
      ( pr2 (H l P) (dep-cocone-map f g c P h))))

{- Proof of Theorem 18.1.4, (iv) implies (v). -}
   
Ind-pushout-dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) → dependent-universal-property-pushout l f g c) →
  ((l : Level) → Ind-pushout l f g c)
Ind-pushout-dependent-universal-property-pushout f g c dup-c l P =
  pr1 (dup-c l P)

{- Proof of Theorem 18.1.4, (iv) implies (iii). -}

triangle-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  let i = pr1 c
      j = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  ( dep-cocone-map f g c P) ~
  ( ( tot (λ h → tot (λ h' → htpy-eq))) ∘
    ( gap
      ( λ (h : (a : A) → P (i a)) → λ s → tr P (H s) (h (f s)))
      ( λ (h : (b : B) → P (j b)) → λ s → h (g s))
      ( cone-dependent-pullback-property-pushout f g c P)))
triangle-dependent-pullback-property-pushout f g (pair i (pair j H)) P h =
  eq-pair refl (eq-pair refl (inv (issec-eq-htpy (λ x → apd h (H x)))))

dependent-pullback-property-dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) → dependent-universal-property-pushout l f g c) →
  ((l : Level) → dependent-pullback-property-pushout l f g c)
dependent-pullback-property-dependent-universal-property-pushout
  f g (pair i (pair j H)) I l P =
  let c = (pair i (pair j H)) in
  is-equiv-right-factor
    ( dep-cocone-map f g c P)
    ( tot (λ h → tot λ h' → htpy-eq))
    ( gap
      ( λ h x → tr P (H x) (h (f x)))
      ( λ h x → h (g x))
      ( cone-dependent-pullback-property-pushout f g c P))
    ( triangle-dependent-pullback-property-pushout f g c P)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ h → is-equiv-tot-is-fiberwise-equiv
        ( λ h' → funext (λ x → tr P (H x) (h (f x))) (λ x → h' (g x)))))
    ( I l P)

{- Proof of Theorem 18.1.4, (iv) implies (iii). -}

dependent-universal-property-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) → dependent-pullback-property-pushout l f g c) →
  ((l : Level) → dependent-universal-property-pushout l f g c)
dependent-universal-property-dependent-pullback-property-pushout
  f g (pair i (pair j H)) dpullback-c l P =
  let c = (pair i (pair j H)) in
  is-equiv-comp
    ( dep-cocone-map f g c P)
    ( tot (λ h → tot λ h' → htpy-eq))
    ( gap
      ( λ h x → tr P (H x) (h (f x)))
      ( λ h x → h (g x))
      ( cone-dependent-pullback-property-pushout f g c P))
    ( triangle-dependent-pullback-property-pushout f g c P)
    ( dpullback-c l P)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ h → is-equiv-tot-is-fiberwise-equiv
        ( λ h' → funext (λ x → tr P (H x) (h (f x))) (λ x → h' (g x)))))

{- Proof of Theorem 18.1.4, (iii) implies (ii). -}

concat-eq-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) → Id (eq-htpy (H ∙h K)) ((eq-htpy H) ∙ (eq-htpy K))
concat-eq-htpy {A = A} {B} {f} H K =
  ind-htpy f
    ( λ g H →
      ( h : (x : A) → B x) (K : g ~ h) →
      Id (eq-htpy (H ∙h K)) ((eq-htpy H) ∙ (eq-htpy K)))
    ( λ h K → ap (concat' f (eq-htpy K)) (inv (eq-htpy-htpy-refl _))) H _ K

pullback-property-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  dependent-pullback-property-pushout l f g c →
  pullback-property-pushout l f g c
pullback-property-dependent-pullback-property-pushout
  l f g (pair i (pair j H)) dpb Y =
  is-pullback-htpy
    ( λ h s → tr (λ x → Y) (H s) (h (f s)))
    ( λ h → eq-htpy (λ s → inv (tr-triv (H s) (h (f s)))))
    ( λ h s → h (g s))
    ( htpy-refl)
    { c = pair
      ( λ h a → h (i a))
      ( pair (λ h b → h (j b)) (λ h → eq-htpy (h ·l H)))}
    ( cone-dependent-pullback-property-pushout
      f g (pair i (pair j H)) (λ x → Y))
    ( pair
      ( λ h → refl)
      ( pair
        ( λ h → refl)
        ( λ h → right-unit ∙
          ( ( ap eq-htpy
              ( eq-htpy (λ s →
                inv-con
                  ( tr-triv (H s) (h (i (f s))))
                  ( ap h (H s))
                  ( apd h (H s))
                  ( inv (apd-triv h (H s)))))) ∙
            ( concat-eq-htpy
              ( λ s → inv (tr-triv (H s) (h (i (f s)))))
              ( λ s → apd h (H s)))))))
    ( dpb (λ x → Y))

{- Proof of Theorem 18.1.4, (ii) implies (iii). -}

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
  (h : B → X) (f : A → B) → TR-EQ-HTPY-FAM-LIFTS P h (htpy-refl' f)
tr-eq-htpy-fam-lifts-htpy-refl P h f k =
  ap (λ t → tr (fam-lifts _ P) t k) (eq-htpy-htpy-refl (h ∘ f))

abstract
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
    Id  ( tr-eq-htpy-fam-lifts P h (htpy-refl' f))
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
  (P : X → UU l4) (f : A → B) → TRIANGLE-PRECOMPOSE-LIFTS P (htpy-refl' f)
triangle-precompose-lifts-htpy-refl {A = A} P f h h' =
  tr-eq-htpy-fam-lifts-htpy-refl P h f (λ a → h' (f a))

abstract
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
      ( triangle-precompose-lifts P (htpy-refl' f))
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
  ( triangle-precompose-lifts' P (htpy-refl' f) h) ~
  ( htpy-refl' ( precompose-lifts P f h))
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
  (f : A → B) → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P (htpy-refl' f)
coherence-triangle-precompose-lifts-htpy-refl P f h =
  ( htpy-eq (htpy-eq (compute-triangle-precompose-lifts P f) h)) ∙h
  ( ( ( htpy-inv htpy-right-unit) ∙h
      ( htpy-ap-concat
        ( λ h' → tr-eq-htpy-fam-lifts-htpy-refl P h f (λ a → h' (f a)))
        ( htpy-refl)
        ( triangle-precompose-lifts' P htpy-refl h)
        ( htpy-inv (compute-triangle-precompose-lifts' P f h)))) ∙h
    ( htpy-eq
      ( ap
        ( λ t →
          ( t ·r (precompose-lifts P f h)) ∙h
          ( triangle-precompose-lifts' P htpy-refl h))
        ( inv (compute-tr-eq-htpy-fam-lifts P h f)))))

abstract
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
      Id  ( coherence-triangle-precompose-lifts P (htpy-refl' f))
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
coherence-square-inv-choice-∞ P f = htpy-refl

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

tr-id-left-subst :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} {x y : A}
  (p : Id x y) (b : B) → (q : Id (f x) b) →
  Id (tr (λ (a : A) → Id (f a) b) p q) ((inv (ap f p)) ∙ q)
tr-id-left-subst refl b q = refl

compute-htpy-precompose-total-lifts :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  ( f : A → B) →
  ( htpy-precompose-total-lifts P (htpy-refl' f)) ~
  ( htpy-refl' (toto (fam-lifts A P) (λ h → h ∘ f) (precompose-lifts P f)))
compute-htpy-precompose-total-lifts {A = A} P f (pair h h') =
  let α = λ (t : Id (h ∘ f) (h ∘ f)) → tr (fam-lifts A P) t (λ a → h' (f a))
  in
  ap eq-pair'
    ( eq-pair
      ( eq-htpy-htpy-refl (h ∘ f))
      ( ( tr-id-left-subst
          { f = α}
          ( eq-htpy-htpy-refl (h ∘ f))
          ( λ a → h' (f a))
          ( triangle-precompose-lifts P htpy-refl h h')) ∙
        ( ( ap
            ( λ t → inv (ap α (eq-htpy-htpy-refl (λ a → h (f a)))) ∙ t)
            ( htpy-eq
              ( htpy-eq (compute-triangle-precompose-lifts P f) h) h')) ∙
          ( left-inv (triangle-precompose-lifts-htpy-refl P f h h')))))

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
  (f : A → B) → COHERENCE-HTPY-INV-CHOICE-∞ P (htpy-refl' f)
coherence-htpy-inv-choice-∞-htpy-refl P f =
  ( htpy-ap-concat
    ( coherence-square-inv-choice-∞ P f)
    ( inv-choice-∞ ·l ( htpy-precompose-total-lifts P htpy-refl))
    ( htpy-refl)
    ( λ h →
      ap (ap inv-choice-∞) (compute-htpy-precompose-total-lifts P f h))) ∙h
  ( htpy-inv
    ( htpy-ap-concat'
      ( ( htpy-precompose _ htpy-refl) ·r inv-choice-∞)
      ( htpy-refl)
      ( htpy-refl)
      ( λ h → compute-htpy-precompose _ f (inv-choice-∞ h))))

abstract
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
      ( htpy-refl)
      ( htpy-refl)
      ( htpy-refl)
      ( htpy-refl)
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
    ( htpy-refl)
    ( cone-family-dependent-pullback-property f g c P id)
    { c' = cone-dependent-pullback-property-pushout f g c P}
    ( pair htpy-refl
      ( pair htpy-refl
        ( htpy-right-unit ∙h (coherence-triangle-precompose-lifts P H id))))
    ( is-pullback-cone-family-dependent-pullback-property f g c pullback-c P id)

{- This concludes the proof of Theorem 18.1.4. -}

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

Fam-pushout-fam :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  (P : X → UU l) → Fam-pushout l f g
Fam-pushout-fam f g (pair i (pair j H)) P =
  pair
    ( P ∘ i)
    ( pair
      ( P ∘ j)
      ( λ s → (pair (tr P (H s)) (is-equiv-tr P (H s)))))

equiv-eq-ap-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A} (p : Id x y) →
  Id (equiv-tr B p) (equiv-eq (ap B p))
equiv-eq-ap-fam B refl = eq-htpy-equiv htpy-refl

triangle-Fam-pushout-fam :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ( Fam-pushout-fam {l = l} f g c) ~
  ( ( Fam-pushout-cocone-UU l f g) ∘
    ( cocone-map f g {Y = UU l} c))
triangle-Fam-pushout-fam {l = l} {S} {A} {B} {X} f g (pair i (pair j H)) P =
  eq-pair refl (eq-pair refl (eq-htpy (λ s → equiv-eq-ap-fam P (H s))))

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
      ( λ s → htpy-refl))

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
  fundamental-theorem-id s
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
    ( Eq-Π-total-fam-eq C (inv-choice-∞ t) (inv-choice-∞ t'))
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

{- The type of pushouts on a span S is now defined to be the type of types
   equipped with the structure of a cocone on S, that satisfies the induction
   principle for pushouts. 

   In order to ensure that PUSHOUT is a small type, we only require that
   pushouts eliminate into universe level lsuc (l1 ⊔ l2 ⊔ l3). This is strong
   enough to define families over the pushouts using types that have size
   similar to the size of the original span. -}

PUSHOUT :
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  UU (lsuc (lsuc l1) ⊔ (lsuc (lsuc l2) ⊔ (lsuc (lsuc l3))))
PUSHOUT {l1} {l2} {l3} f g =
  Σ ( UU (l1 ⊔ (l2 ⊔ l3)))
    ( λ X → Σ (cocone f g X)
      ( λ c → Ind-pushout (lsuc (l1 ⊔ (l2 ⊔ l3))) f g c)) 
