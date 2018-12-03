{-# OPTIONS --without-K --allow-unsolved-metas --cubical #-}

module Lecture13 where

import Lecture12
open Lecture12 public

-- Section 13.1

cocone : {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → UU l4 → UU _
cocone {A = A} {B = B} f g X =
  Σ (A → X) (λ i → Σ (B → X) (λ j → (i ∘ f) ~ (j ∘ g)))

generating-data-pushout : 
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l5)))
generating-data-pushout {S = S} {A} {B} f g c P =
  Σ ( (a : A) → P (pr1 c a))
    ( λ φ → Σ ( (b : B) → P (pr1 (pr2 c) b))
      ( λ ψ → (s : S) → Id (tr P (pr2 (pr2 c) s) (φ (f s))) (ψ (g s))))

dgen-pushout : {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) {P : X → UU l5} →
  ((x : X) → P x) → generating-data-pushout f g c P
dgen-pushout f g (dpair i (dpair j H)) h =
  dpair
    ( λ a → h (i a))
    ( dpair
      ( λ b → h (j b))
      ( λ s → apd h (H s)))

Ind-pushout : {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (l5 : Level) → UU _
Ind-pushout f g {X} c l5 = (P : X → UU l5) → sec (dgen-pushout f g c {P})

PUSHOUT : {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → UU _
PUSHOUT {l1} {l2} {l3} f g =
  Σ ( UU (l1 ⊔ (l2 ⊔ l3)))
    ( λ X → Σ (cocone f g X)
      ( λ c → Ind-pushout f g c (lsuc (l1 ⊔ (l2 ⊔ l3)))))

-- Section 13.3

-- We first give several different conditions that are equivalent to the
-- universal property of pushouts.

cocone-map : {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} {Y : UU l5} →
  cocone f g X → (X → Y) → cocone f g Y
cocone-map f g (dpair i (dpair j H)) h =
  dpair (h ∘ i) (dpair (h ∘ j) (h ·l H))

universal-property-pushout : {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} →
  cocone f g X → {l5 : Level} (Y : UU l5) → UU _
universal-property-pushout f g c Y = is-equiv (cocone-map f g {Y = Y} c)

cone-pullback-property-pushout : {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  {l : Level} (Y : UU l) →
  cone (λ (h : A → Y) → h ∘ f) (λ (h : B → Y) → h ∘ g) (X → Y)
cone-pullback-property-pushout f g {X} (dpair i (dpair j H)) Y =
  dpair
    ( λ (h : X → Y) → h ∘ i)
    ( dpair
      ( λ (h : X → Y) → h ∘ j)
      ( λ h → eq-htpy (h ·l H)))

pullback-property-pushout : {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  {l : Level} (Y : UU l) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l4 ⊔ l))))
pullback-property-pushout {l1} {l2} {l3} {l4} {S} {A} {B} f g {X} c {l} Y =
  is-pullback
    ( λ (h : A → Y) → h ∘ f)
    ( λ (h : B → Y) → h ∘ g)
    ( cone-pullback-property-pushout f g c Y)

dependent-universal-property-pushout : {l1 l2 l3 l4 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  (l : Level) → UU _
dependent-universal-property-pushout f g {X} c l =
  (P : X → UU l) → is-equiv (dgen-pushout f g c {P})

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
cone-dependent-pullback-property-pushout f g (dpair i (dpair j H)) P =
  dpair
    ( λ h → λ a → h (i a))
    ( dpair
      ( λ h → λ b → h (j b))
       λ h → eq-htpy (λ s → apd h (H s)))

dependent-pullback-property-pushout : {l1 l2 l3 l4 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} (f : S → A) (g : S → B)
  {X : UU l4} (c : cocone f g X) {l : Level} (P : X → UU l) →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l4 ⊔ l))))
dependent-pullback-property-pushout {l1} {l2} {l3} {l4} {S} {A} {B} f g {X}
  (dpair i (dpair j H)) {l} P =
  is-pullback
    ( λ (h : (a : A) → P (i a)) → λ s → tr P (H s) (h (f s)))
    ( λ (h : (b : B) → P (j b)) → λ s → h (g s))
    ( cone-dependent-pullback-property-pushout f g (dpair i (dpair j H)) P)

-- We will now start proving that the following properties are all equivalent:
-- 
-- universal-property-pushout
-- pullback-property-pushout
-- Ind-pushout
-- dependent-universal-property-pushout
-- dependent-pullback-property-pushout

triangle-pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  {l : Level} (Y : UU l) →
  ( cocone-map f g c) ~
  ( ( tot (λ i' → tot (λ j' p → htpy-eq p))) ∘
    ( gap (λ h → h ∘ f) (λ h → h ∘ g) (cone-pullback-property-pushout f g c Y)))
triangle-pullback-property-pushout-universal-property-pushout
  {S = S} {A = A} {B = B} f g (dpair i (dpair j H)) Y h =
    eq-pair
      ( dpair refl (eq-pair (dpair refl (inv (issec-eq-htpy (h ·l H))))))

pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  {l : Level} (Y : UU l) →
  universal-property-pushout f g c Y → pullback-property-pushout f g c Y
pullback-property-pushout-universal-property-pushout
  f g (dpair i (dpair j H)) Y up-c =
  let c = (dpair i (dpair j H)) in
  is-equiv-right-factor
    ( cocone-map f g c)
    ( tot (λ i' → tot (λ j' p → htpy-eq p)))
    ( gap (λ h → h ∘ f) (λ h → h ∘ g) (cone-pullback-property-pushout f g c Y))
    ( triangle-pullback-property-pushout-universal-property-pushout f g c Y)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ i' → is-equiv-tot-is-fiberwise-equiv
        ( λ j' → funext (i' ∘ f) (j' ∘ g))))
    ( up-c)

universal-property-pushout-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  {l : Level} (Y : UU l) →
  pullback-property-pushout f g c Y → universal-property-pushout f g c Y
universal-property-pushout-pullback-property-pushout
  f g (dpair i (dpair j H)) Y pb-c =
  let c = (dpair i (dpair j H)) in
  is-equiv-comp
    ( cocone-map f g c)
    ( tot (λ i' → tot (λ j' p → htpy-eq p)))
    ( gap (λ h → h ∘ f) (λ h → h ∘ g) (cone-pullback-property-pushout f g c Y))
    ( triangle-pullback-property-pushout-universal-property-pushout f g c Y)
    ( pb-c)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ i' → is-equiv-tot-is-fiberwise-equiv
        ( λ j' → funext (i' ∘ f) (j' ∘ g))))

Eq-generating-data-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s t : generating-data-pushout f g c P) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l5)))
Eq-generating-data-pushout {S = S} f g (dpair i (dpair j H)) P
  (dpair hA (dpair hB hS)) t =
  let kA = pr1 t
      kB = pr1 (pr2 t)
      kS = pr2 (pr2 t)
  in
  Σ ( hA ~ kA)
    ( λ K →
    Σ ( hB ~ kB)
      ( λ L →
      (s : S) → Id ((hS s) ∙ (L (g s))) ((ap (tr P (H s)) (K (f s))) ∙ (kS s))))

reflexive-Eq-generating-data-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s : generating-data-pushout f g c P) →
  Eq-generating-data-pushout f g c P s s
reflexive-Eq-generating-data-pushout f g (dpair i (dpair j H)) P
  (dpair hA (dpair hB hS)) =
  dpair
    ( htpy-refl hA)
    ( dpair
      ( htpy-refl hB)
      ( htpy-right-unit hS))

is-contr-total-Eq-generating-data-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s : generating-data-pushout f g c P) →
  is-contr
    ( Σ (generating-data-pushout f g c P)
      ( Eq-generating-data-pushout f g c P s))
is-contr-total-Eq-generating-data-pushout
  {S = S} {A} {B} f g {X} (dpair i (dpair j H)) P (dpair hA (dpair hB hS)) =
  is-contr-total-Eq-structure
    {A = (a : A) → P (i a)}
    {B = λ α →
             Σ ((x : B) → P (j x))
             (λ β → (s : S) → Id (tr P (H s) (α (f s))) (β (g s)))}
    {C = λ α → hA ~ α}
    ( λ t K →
      let α = pr1 t
          β = pr1 (pr2 t)
          γ = pr2 (pr2 t)
      in
      Σ (hB ~ β) (λ L →
        (s : S) →
          Id ((hS s) ∙ (L (g s))) ((ap (tr P (H s)) (K (f s))) ∙ (γ s))))
    ( is-contr-total-htpy hA)
    ( dpair hA (htpy-refl _))
    ( is-contr-total-Eq-structure
      {A = (b : B) → P (j b)}
      {B = λ β → (s : S) → Id (tr P (H s) (hA (f s))) (β (g s))}
      {C = λ β → hB ~ β}
      ( λ t L →
        let β = pr1 t
            γ = pr2 t
        in
        (s : S) → Id ((hS s) ∙ (L (g s))) (γ s))
      ( is-contr-total-htpy hB)
      ( dpair hB (htpy-refl _))
      ( is-contr-is-equiv
        ( Σ ((s : S) → Id (tr P (H s) (hA (f s))) (hB (g s))) (λ γ → hS ~ γ))
        ( tot (λ γ → htpy-concat _ (htpy-inv (htpy-right-unit hS))))
        ( is-equiv-tot-is-fiberwise-equiv
          ( is-equiv-htpy-concat (htpy-inv (htpy-right-unit hS))))
        ( is-contr-total-htpy hS)))

Eq-generating-data-pushout-eq :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s t : generating-data-pushout f g c P) →
  Id s t → Eq-generating-data-pushout f g c P s t
Eq-generating-data-pushout-eq f g c P s .s refl =
  reflexive-Eq-generating-data-pushout f g c P s

is-fiberwise-equiv-Eq-generating-data-pushout-eq :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s : generating-data-pushout f g c P) →
  is-fiberwise-equiv (Eq-generating-data-pushout-eq f g c P s)
is-fiberwise-equiv-Eq-generating-data-pushout-eq f g c P s =
  id-fundamental-gen s
    ( reflexive-Eq-generating-data-pushout f g c P s)
    ( is-contr-total-Eq-generating-data-pushout f g c P s)
    ( Eq-generating-data-pushout-eq f g c P s)

dependent-naturality-square : {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f f' : (x : A) → B x)
  {x x' : A} (p : Id x x') (q : Id (f x) (f' x)) (q' : Id (f x') (f' x')) →
  Id ((apd f p) ∙ q') ((ap (tr B p) q) ∙ (apd f' p)) →
  Id (tr (λ y → Id (f y) (f' y)) p q) q' 
dependent-naturality-square f f' refl q q' s =
  inv (s ∙ ((right-unit (ap id q)) ∙ (ap-id q)))

htpy-eq-dgen-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ( H : (l : Level) → Ind-pushout f g c l) →
  {l : Level} {P : X → UU l} (h h' : (x : X) → P x) →
  Id (dgen-pushout f g c h) (dgen-pushout f g c h') → h ~ h'
htpy-eq-dgen-pushout f g (dpair i (dpair j H)) I {l} {P} h h' p =
  let c = (dpair i (dpair j H))
      K = pr1 (Eq-generating-data-pushout-eq f g c P _ _ p)
      L = pr1 (pr2 (Eq-generating-data-pushout-eq f g c P _ _ p))
      M = pr2 (pr2 (Eq-generating-data-pushout-eq f g c P _ _ p))
  in
  pr1 (I _ (λ x → Id (h x) (h' x)))
    ( dpair
      ( K)
      ( dpair
        ( L)
        ( λ s →
          dependent-naturality-square h h' (H s) (K (f s)) (L (g s)) (M s))))

dependent-universal-property-pushout-Ind-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) → Ind-pushout f g c l) →
  ((l : Level) → dependent-universal-property-pushout f g c l)
dependent-universal-property-pushout-Ind-pushout f g c H l P =
  let ind-pushout  = pr1 (H l P)
      comp-pushout = pr2 (H l P)
  in
  is-equiv-has-inverse
    ( dpair
      ( ind-pushout)
      ( dpair
        ( comp-pushout)
        ( λ h → eq-htpy (htpy-eq-dgen-pushout f g c H
          ( ind-pushout (dgen-pushout f g c h))
          ( h)
          ( pr2 (H l P) (dgen-pushout f g c h))))))

triangle-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  let i = pr1 c
      j = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  ( dgen-pushout f g c) ~
  ( ( tot (λ h → tot (λ h' → htpy-eq))) ∘
    ( gap
      ( λ (h : (a : A) → P (i a)) → λ s → tr P (H s) (h (f s)))
      ( λ (h : (b : B) → P (j b)) → λ s → h (g s))
      ( cone-dependent-pullback-property-pushout f g c P)))
triangle-dependent-pullback-property-pushout f g (dpair i (dpair j H)) P h =
  eq-pair (dpair refl (eq-pair (dpair refl
    ( inv (issec-eq-htpy (λ x → apd h (H x)))))))

dependent-pullback-property-dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) → dependent-universal-property-pushout f g c l) →
  (l : Level) (P : X → UU l) → 
  let i = pr1 c
      j = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  is-pullback
    ( λ (h : (a : A) → P (i a)) → λ s → tr P (H s) (h (f s)))
    ( λ (h : (b : B) → P (j b)) → λ s → h (g s))
    ( cone-dependent-pullback-property-pushout f g c P)
dependent-pullback-property-dependent-universal-property-pushout
  f g (dpair i (dpair j H)) I l P =
  let c = (dpair i (dpair j H)) in
  is-equiv-right-factor
    ( dgen-pushout f g c)
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

concat-eq-htpy : {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h : (x : A) → B x} (H : f ~ g) (K : g ~ h) →
  Id (eq-htpy (H ∙h K)) ((eq-htpy H) ∙ (eq-htpy K))
concat-eq-htpy {A = A} {B} {f} H K =
  ind-htpy f
    ( λ g H →
      ( h : (x : A) → B x) (K : g ~ h) →
      Id (eq-htpy (H ∙h K)) ((eq-htpy H) ∙ (eq-htpy K)))
    ( λ h K → ap (concat' _ (eq-htpy K)) (inv (eq-htpy-htpy-refl _))) _ H _ K

pullback-property-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) (P : X → UU l) → dependent-pullback-property-pushout f g c P) →
  ((l : Level) (Y : UU l) → pullback-property-pushout f g c Y)
pullback-property-dependent-pullback-property-pushout
  f g (dpair i (dpair j H)) dpb l Y =
  is-pullback-htpy
    ( λ h s → tr (λ x → Y) (H s) (h (f s)))
    ( λ h → eq-htpy (λ s → inv (tr-triv (H s) (h (f s)))))
    ( λ h s → h (g s))
    ( htpy-refl _)
    { c = dpair
      ( λ h a → h (i a))
      ( dpair (λ h b → h (j b)) (λ h → eq-htpy (h ·l H)))}
    ( cone-dependent-pullback-property-pushout
      f g (dpair i (dpair j H)) (λ x → Y))
    ( dpair
      ( λ h → refl)
      ( dpair
        ( λ h → refl)
        ( λ h → (right-unit _) ∙
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
    ( dpb l (λ x → Y))

cocone-generating-data-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  (l : Level) (P : X → UU l) →
  generating-data-pushout f g c P → cocone f g (Σ X P)
cocone-generating-data-pushout
  f g (dpair i (dpair j H)) l P (dpair i' (dpair j' H')) =
  dpair
    ( λ a → dpair (i a) (i' a))
    ( dpair
      ( λ b → dpair (j b) (j' b))
      ( λ s → eq-pair (dpair (H s) (H' s))))

cocone-map-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  {Y : UU l5} (h : X → Y) {Z : UU l6} (k : Y → Z) →
  Id (cocone-map f g c (k ∘ h)) ((cocone-map f g (cocone-map f g c h) k))
cocone-map-comp f g (dpair i (dpair j H)) h k =
  eq-pair (dpair refl
    ( eq-pair (dpair refl
      ( eq-htpy (λ s → ap-comp k h (H s))))))

ap-pr1-eq-pair : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (s t : Σ A B)
  (p : Id (pr1 s) (pr1 t)) (q : Id (tr B p (pr2 s)) (pr2 t)) →
  Id (ap pr1 (eq-pair' s t (dpair p q))) p
ap-pr1-eq-pair (dpair x x₁) (dpair .x .x₁) refl refl = refl

sec-pr1-generating-data-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) (Y : UU l) → universal-property-pushout f g c Y) →
  (l : Level) (P : X → UU l) →
  generating-data-pushout f g c P → sec (pr1 {A = X} {B = P})
sec-pr1-generating-data-pushout
  f g {X} (dpair i (dpair j H)) up l P (dpair i' (dpair j' H')) =
  let c = dpair i (dpair j H)
      c' = dpair i' (dpair j' H')
      u = inv-is-equiv (up _ (Σ X P))
          ( cocone-generating-data-pushout f g c l P c')
      α = issec-inv-is-equiv (up _ (Σ X P))
          ( cocone-generating-data-pushout f g c l P c')
  in
  dpair
    ( u)
    ( htpy-eq (ap pr1 (center (is-prop-is-contr
      ( is-contr-map-is-equiv (up _ X)
        ( dpair i (dpair j H)))
      ( dpair (pr1 ∘ u)
        ( ( cocone-map-comp f g c u pr1) ∙
          ( ( ap (λ t → cocone-map f g t pr1) α) ∙
           eq-pair (dpair refl (eq-pair (dpair refl (eq-htpy
             ( λ s → ap-pr1-eq-pair
               ( dpair (i (f s)) (i' (f s)))
               ( dpair (j (g s)) (j' (g s)))
               ( H s)
               ( H' s)))))))))
      ( dpair id
        ( eq-pair (dpair refl
          ( eq-pair (dpair refl (eq-htpy (λ s → ap-id (H s))))))))))))

Π-sec-pr1 : {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  sec (pr1 {A = A} {B = B}) → (x : A) → B x
Π-sec-pr1 B (dpair f H) x = tr B (H x) (pr2 (f x))

ind-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) (Y : UU l) → universal-property-pushout f g c Y) →
  (l : Level) (P : X → UU l) →
  generating-data-pushout f g c P → (x : X) → P x
ind-pushout-universal-property-pushout {S = S} {A} {B} f g {X} c up l P c' =
  Π-sec-pr1 P (sec-pr1-generating-data-pushout f g c up l P c')

comp-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  (up : (l : Level) (Y : UU l) → universal-property-pushout f g c Y) →
  (l : Level) (P : X → UU l) →
  ( ( dgen-pushout f g c) ∘
    ( ind-pushout-universal-property-pushout f g c up l P)) ~ id
comp-pushout-universal-property-pushout
  f g (dpair i (dpair j H)) up l P (dpair i' (dpair j' H')) = {!!}
