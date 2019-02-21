{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture15 where

import Lecture14
open Lecture14 public
open Lecture14.Cubes public

-- Section 15.1 The dependent pullback property of pushouts

{- Our goal in this section is to show that the pullback property of pushouts 
   implies the dependent pullback property of pushouts. -}

coherence-square-inv-choice-∞ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {P : X → UU l4}
  (h : A → B) →
  coherence-square
    ( inv-choice-∞ {A = B} {B = λ x → X} {C = λ x y → P y})
    ( λ fg → dpair ((pr1 fg) ∘ h) (λ x → (pr2 fg) (h x)))
    ( λ f → f ∘ h)
    ( inv-choice-∞)
coherence-square-inv-choice-∞ h (dpair f g) = refl

{-
htpy-dependent-precomposition :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {P : C → UU l4}
  (γ : B → C) {f g : A → B} (H : f ~ g) →
  ( ( tr (λ (α : A → C) → (a : A) → P (α a)) (eq-htpy (γ ·l H))) ∘
    ( λ (h : (b : B) → P (γ b)) a → h (f a))) ~
  ( λ (h : (b : B) → P (γ b)) a → (h (g a)))
htpy-dependent-precomposition {A = A} {B} {C} {P} γ {f} {g} =
  ind-htpy f
    ( λ g H →
      ( ( tr (λ (α : A → C) → (a : A) → P (α a)) (eq-htpy (γ ·l H))) ∘
        ( λ (h : (b : B) → P (γ b)) a → h (f a))) ~
      ( λ h a → h (g a)))
    ( tr ( λ t →
           ( λ a → tr (λ α → (a₁ : A) → P (α a₁)) t (λ a₁ → a (f a₁))) ~
           ( λ h a → h (f a)))
         ( eq-htpy-htpy-refl (γ ∘ f))
         ( htpy-refl (λ h a → h (f a))))
    g
-}

compute-transport-cone-family-dependent-pullback-property :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  {f g : A → B} (H : f ~ g) (f' : (a : A) → C (f a)) → 
  ( tr (λ (h : A → B) → (a : A) → C (h a)) (eq-htpy H) f') ~
  ( λ a → tr C (H a) (f' a))
compute-transport-cone-family-dependent-pullback-property
  {A = A} {B} C {f} {g} H f' =
  ind-htpy f
    ( λ g H →
      ( tr (λ (h : A → B) → (a : A) → C (h a)) (eq-htpy H) f') ~
      ( λ a → tr C (H a) (f' a)))
    ( λ a → ap
      ( λ t → (tr (λ h → (a' : A) → C (h a')) t f' a))
      ( eq-htpy-htpy-refl f))
    g H

fiberwise-square-dependent-pullback-property :
  {l1 l2 l3 l4 l5 l6 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5} (P : Y → UU l6)
  (f : S → A) (g : S → B) (i : A → X) (j : B → X) (H : (i ∘ f) ~ (j ∘ g)) →
  (γ : X → Y) →
  coherence-square
    ( λ (γ' : (x : X) → P (γ x)) b → γ' (j b))
    ( λ (γ' : (x : X) → P (γ x)) a → γ' (i a))
    ( λ (β' : (b : B) → P (γ (j b))) s → β' (g s))
    ( λ (α' : (a : A) → P (γ (i a))) →
      tr
        ( λ (σ : S → Y) → (s : S) → P (σ s))
        ( eq-htpy (γ ·l H))
        ( λ s → α' (f s)))
fiberwise-square-dependent-pullback-property P f g i j H γ γ' =
  eq-htpy
    ( λ s →
      ( compute-transport-cone-family-dependent-pullback-property
        ( P)
        ( γ ·l H)
        ( λ s → γ' (i (f s)))
        ( s)) ∙
      ( ( tr-precompose-fam P γ (H s) (γ' (i (f s)))) ∙
        ( apd γ' (H s))))

cone-family-dependent-pullback-property :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) (P : X → UU l) →
  cone-family
    ( λ (σ : S → X) → (s : S) → P (σ s))
    ( λ (α : A → X) (α' : (a : A) → P (α a)) (s : S) → α' (f s))
    ( λ (β : B → X) (β' : (b : B) → P (β b)) (s : S) → β' (g s))
    ( cone-pullback-property-pushout f g c X)
    ( λ (γ : X → X) → (x : X) → P (γ x))
cone-family-dependent-pullback-property f g (dpair i (dpair j H)) P γ =
  dpair
    ( λ γ' a → γ' (i a))
    ( dpair
      ( λ γ' b → γ' (j b))
      ( fiberwise-square-dependent-pullback-property P f g i j H γ))

coherence-square-tot-cone-family-dependent-pullback-property :
  {l1 l2 l3 l4 l5 l6 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5} (P : Y → UU l6)
  (f : S → A) (g : S → B) (i : A → X) (j : B → X) (H : (i ∘ f) ~ (j ∘ g)) →
  coherence-square
    ( toto
      ( λ (β : B → Y) → (b : B) → P (β b))
      ( λ (γ : X → Y) → γ ∘ j)
      ( λ (γ : X → Y) (γ' : (x : X) → P (γ x)) (b : B) → γ' (j b)))
    ( toto
      ( λ (α : A → Y) → (a : A) → P (α a))
      ( λ (γ : X → Y) → γ ∘ i)
      ( λ (γ : X → Y) (γ' : (x : X) → P (γ x)) (a : A) → γ' (i a)))
    ( toto
      ( λ (σ : S → Y) → (s : S) → P (σ s))
      ( λ (β : B → Y) → β ∘ g)
      ( λ (β : B → Y) (β' : (b : B) → P (β b)) (s : S) → β' (g s)))
    ( toto
      ( λ (σ : S → Y) → (s : S) → P (σ s))
      ( λ (α : A → Y) → α ∘ f)
      ( λ (α : A → Y) (α' : (a : A) → P (α a)) (s : S) → α' (f s)))
coherence-square-tot-cone-family-dependent-pullback-property
  P f g i j H (dpair γ γ') =
  eq-pair (dpair
    ( eq-htpy (γ ·l H))
    ( fiberwise-square-dependent-pullback-property P f g i j H γ γ'))

coherence-cube-inv-choice-∞ :
  {l1 l2 l3 l4 l5 l6 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5} (P : Y → UU l6)
  (f : S → A) (g : S → B) (i : A → X) (j : B → X) (H : (i ∘ f) ~ (j ∘ g)) →
  coherence-cube
    ( λ φ → φ ∘ i)
    ( λ φ → φ ∘ j)
    ( λ φ → φ ∘ f)
    ( λ φ → φ ∘ g)
    ( toto
      ( λ (α : A → Y) → (a : A) → P (α a))
      ( λ (γ : X → Y) → γ ∘ i)
      ( λ (γ : X → Y) (γ' : (x : X) → P (γ x)) (a : A) → γ' (i a)))
    ( toto
      ( λ (β : B → Y) → (b : B) → P (β b))
      ( λ (γ : X → Y) → γ ∘ j)
      ( λ (γ : X → Y) (γ' : (x : X) → P (γ x)) (b : B) → γ' (j b)))
    ( toto
      ( λ (σ : S → Y) → (s : S) → P (σ s))
      ( λ (α : A → Y) → α ∘ f)
      ( λ (α : A → Y) (α' : (a : A) → P (α a)) (s : S) → α' (f s)))
    ( toto
      ( λ (σ : S → Y) → (s : S) → P (σ s))
      ( λ (β : B → Y) → β ∘ g)
      ( λ (β : B → Y) (β' : (b : B) → P (β b)) (s : S) → β' (g s)))
    ( inv-choice-∞ {A = X} {B = λ x → Y} {C = λ x y → P y}) 
    ( inv-choice-∞)
    ( inv-choice-∞)
    ( inv-choice-∞)
    ( coherence-square-tot-cone-family-dependent-pullback-property P f g i j H)
    ( coherence-square-inv-choice-∞ i)
    ( coherence-square-inv-choice-∞ j)
    ( coherence-square-inv-choice-∞ f)
    ( coherence-square-inv-choice-∞ g)
    ( λ φ → eq-htpy (φ ·l H))
coherence-cube-inv-choice-∞ P f g i j H (dpair γ γ') =
  concat
    ( ( inv-choice-∞ ·l
        coherence-square-tot-cone-family-dependent-pullback-property P f g
        i j H)
      (dpair γ γ'))
    ( refl)
    ( concat (eq-htpy ((λ x → dpair (γ x) (γ' x)) ·l H))
      ( concat
        ( eq-htpy
          ( λ s → eq-pair
            ( dpair
              ( ap γ (H s))
              ( ( tr-precompose-fam P γ (H s) (γ' (i (f s)))) ∙
                ( apd γ' (H s))))))
        {!!}
        {!!})
      ( inv (right-unit _)))

ap-inv-choice-∞-eq-pair-eq-htpy-eq-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3} (f : A → B)
  (f' : (x : A) → C (f x)) (g' : (x : A) → C (f x))
  (H' : f' ~ g') →
  Id
    ( ap
      ( inv-choice-∞ {A = A} {B = λ a → B} {C = λ a → C})
      { x = dpair f f'}
      { y = dpair f g'}
      ( eq-pair (dpair refl (eq-htpy H'))))
    ( eq-htpy (λ s → eq-pair (dpair refl (H' s))))
ap-inv-choice-∞-eq-pair-eq-htpy-eq-htpy {A = A} {B} {C} f f' g' H' =
  ind-htpy f'
  ( λ g' H' → Id
    ( ap inv-choice-∞
      { x = dpair f f'}
      { y = dpair f g'}
      ( eq-pair (dpair refl (eq-htpy H'))))
    ( eq-htpy (λ s → eq-pair (dpair refl (H' s)))))
  ( ap
    ( λ t → ap (inv-choice-∞ {A = A} {B = λ a → B} {C = λ a → C})
      { x = dpair f f'}
      { y = choice-∞ (λ x → dpair (f x) (f' x))}
      ( eq-pair (dpair refl t)))
    ( eq-htpy-htpy-refl f'))
  ( g')
  ( H') 

ap-inv-choice-∞-eq-pair-eq-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3}
  {f g : A → B} (H : f ~ g) (f' : (x : A) → C (f x)) (g' : (x : A) → C (g x))
  (H' : (tr (λ t → (x : A) → C (t x)) (eq-htpy H) f') ~ g') →
  Id
    ( ap inv-choice-∞
      { x = dpair f f'}
      { y = dpair g g'}
      ( eq-pair (dpair (eq-htpy H) (eq-htpy H'))))
    ( eq-htpy (λ s → eq-pair (dpair (H s) ({!compute-transport-cone-family-dependent-pullback-property!} ∙ (H' s)))))
ap-inv-choice-∞-eq-pair-eq-htpy {A = A} {B} {C} {f} {g} H f' g' H' =
 ind-htpy f
   ( λ g H →
     ( g' : (x : A) → (C (g x)))
     ( H' : (tr (λ t → (x : A) → C (t x)) (eq-htpy H) f') ~ g') →
     Id
       ( ap inv-choice-∞ {x = dpair f f'} {y = dpair g g'} (eq-pair (dpair (eq-htpy H) (eq-htpy H'))))
       ( eq-htpy (λ s → eq-pair (dpair (H s) ({!!} ∙ (H' s))))))
   {!!}
   g H g' H'

{-
{-
coherence-cone-family-dependent-pullback-property :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) (P : X → UU l) (γ : X → X) →
  coherence-square
    ( λ (γ' : (x : X) → P (γ x)) (a : A) → γ' ((pr1 c) a))
    ( λ (γ' : (x : X) → P (γ x)) (b : B) → γ' ((pr1 (pr2 c)) b))
    ( λ (α' : (a : A) → P (γ ((pr1 c) a))) (s : S) →
      tr (λ σ → (s : S) → P (σ s)) (eq-htpy (γ ·l (pr2 (pr2 c)))) ?)
    ( λ (β' : (b : B) → P (γ ((pr1 (pr2 c)) b))) → λ s → β' (g s))
coherence-cone-family-dependent-pullback-property f g c P γ = ?
-}

is-pullback-tot-cone-family-dependent-pullback-property :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ((l : Level) → pullback-property-pushout l f g c) →
  {l : Level} (P : X → UU l) →
  is-pullback
    ( toto
      ( λ σ → (s : S) → P (σ s))
      ( λ (α : A → X) → α ∘ f)
      ( λ α (α' : (a : A) → P (α a)) s → α' (f s)))
    ( toto
      ( λ σ → (s : S) → P (σ s))
      ( λ (β : B → X) → β ∘ g)
      ( λ β (β' : (b : B) → P (β b)) s → β' (g s)))
    ( tot-cone-cone-family
      ( λ σ → (s : S) → P (σ s))
      ( λ α α' s → α' (f s))
      ( λ β β' s → β' (g s))
      ( cone-pullback-property-pushout f g c X)
      ( cone-family-dependent-pullback-property f g c P))
is-pullback-tot-cone-family-dependent-pullback-property
  {S = S} {A} {B} {X} f g (dpair i (dpair j H)) pb-c P =
  is-pullback-top-is-pullback-bottom-cube-is-equiv
    ( λ (φ : X → Σ X P) → φ ∘ i)
    ( λ (φ : X → Σ X P) → φ ∘ j)
    ( λ (φ : A → Σ X P) → φ ∘ f)
    ( λ (φ : B → Σ X P) → φ ∘ g)
    ( toto
      ( λ (α : A → X) → (a : A) → P (α a))
      ( λ (γ : X → X) → γ ∘ i)
      ( λ (γ : X → X) (γ' : (x : X) → P (γ x)) (a : A) → γ' (i a)))
    ( toto
      ( λ (β : B → X) → (b : B) → P (β b))
      ( λ (γ : X → X) → γ ∘ j)
      ( λ (γ : X → X) (γ' : (x : X) → P (γ x)) (b : B) → γ' (j b)))
    ( toto
      ( λ (σ : S → X) → (s : S) → P (σ s))
      ( λ (α : A → X) → α ∘ f)
      ( λ (α : A → X) (α' : (a : A) → P (α a)) (s : S) → α' (f s)))
    ( toto
      ( λ (σ : S → X) → (s : S) → P (σ s))
      ( λ (β : B → X) → β ∘ g)
      ( λ (β : B → X) (β' : (b : B) → P (β b)) (s : S) → β' (g s)))
    ( inv-choice-∞) 
    ( inv-choice-∞)
    ( inv-choice-∞)
    ( inv-choice-∞)
    ( λ t → eq-pair
      ( dpair
        ( eq-htpy ((pr1 t) ·l H))
        ( eq-htpy
          ( λ s →
            ( compute-transport-cone-family-dependent-pullback-property
              ( P) ((pr1 t) ·l H) (λ a → (pr2 t) (i (f a))) s) ∙
            ( ( tr-precompose-fam P (pr1 t) (H s) ((pr2 t) (i (f s)))) ∙
              ( apd (pr2 t) (H s)))))))
    ( coherence-square-inv-choice-∞ i)
    ( coherence-square-inv-choice-∞ j)
    ( coherence-square-inv-choice-∞ f)
    ( coherence-square-inv-choice-∞ g)
    ( λ φ → eq-htpy (φ ·l H))
    {! coherence-cube-inv-choice-∞ P f g i j H!}
    ( is-equiv-inv-choice-∞)
    ( is-equiv-inv-choice-∞)
    ( is-equiv-inv-choice-∞)
    ( is-equiv-inv-choice-∞)
    ( pb-c _ (Σ X P))

dependent-pullback-property-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X) →
  ((l : Level) → pullback-property-pushout l f g c) →
  ((l : Level) → dependent-pullback-property-pushout l f g c)
dependent-pullback-property-pullback-property-pushout
  {S = S} {A} {B} {X}
  f g (dpair i (dpair j H)) pullback-c l P = {!!}
{-
  is-pullback-family-is-pullback-tot
    { X = S → X}
    { A = A → X}
    { B = B → X}
    { C = X → X}
    ( λ (σ : S → X) → (s : S) → P (σ s))
    { PA = λ α → (a : A) → P (α a)}
    { PB = λ β → (b : B) → P (β b)}
    { PC = λ γ → (x : X) → P x}
    { f = λ (α : A → X) → α ∘ f}
    { g = λ (β : B → X) → β ∘ g}
    ( λ (α : A → X) (α' : (a : A) → P (α a)) (s : S) → α' (f s))
    ( λ (β : B → X) (β' : (b : B) → P (β b)) (s : S) → β' (g s))
    {! cone-pullback-property-pushout f g (dpair i (dpair j H)) X!}
    {!!}
    {!!}
    {!!}
    {!!}
    ?
-}

{-
tot-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  {l : Level} {P : X → UU l} →
  generating-data-pushout f g c P → cocone f g (Σ X P)
tot-cocone f g (dpair i (dpair j H)) (dpair i' (dpair j' H')) =
  dpair
    ( λ a → dpair (i a) (i' a))
    ( dpair
      ( λ b → dpair (j b) (j' b))
      ( λ s → eq-pair (dpair (H s) (H' s))))

map-tot-cocone :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) 
  (up : (l' : Level) → universal-property-pushout l' f g c) →
  (P : X → UU l) → generating-data-pushout f g c P → X → Σ X P
map-tot-cocone f g c up P c' =
  inv-is-equiv (up _ (Σ _ P)) (tot-cocone f g c c')

eq-map-tot-cocone :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) 
  (up : (l' : Level) → universal-property-pushout l' f g c) →
  (P : X → UU l) (c' : generating-data-pushout f g c P) →
  Id ( cocone-map f g c (map-tot-cocone f g c up P c'))
    ( tot-cocone f g c c')
eq-map-tot-cocone f g c up P c' =
  issec-inv-is-equiv (up _ (Σ _ P)) (tot-cocone f g c c')

ap-pr1-eq-pair :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (s t : Σ A B)
  (p : Id (pr1 s) (pr1 t)) (q : Id (tr B p (pr2 s)) (pr2 t)) →
  Id (ap pr1 (eq-pair' s t (dpair p q))) p
ap-pr1-eq-pair (dpair x x₁) (dpair .x .x₁) refl refl = refl

htpy-cocone-cocone-map-pr1-tot-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  {l : Level} (P : X → UU l) (c' : generating-data-pushout f g c P) →
  (up : (l' : Level) → universal-property-pushout l' f g c) →
  htpy-cocone f g (cocone-map f g (tot-cocone f g c c') pr1) c
htpy-cocone-cocone-map-pr1-tot-cocone
  f g {X} (dpair i (dpair j H)) P (dpair i' (dpair j' H')) up =
  ( dpair
    ( htpy-refl i)
    ( dpair
      ( htpy-refl j)
      ( (htpy-right-unit _) ∙h (λ s → ap-pr1-eq-pair _ _ (H s) (H' s)))))

htpy-whisk-swap :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f f' : A → B} {g g' : B → C} (H : f ~ f') (K : g ~ g') →
  ((g ·l H) ∙h (K ·r f')) ~ ((K ·r f) ∙h (g' ·l H))
htpy-whisk-swap H K x = inv (htpy-nat K (H x))

{-

coherence-htpy-fib-cocone-map :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  {Y : UU l5} (c' : cocone f g Y) →
  (s t : fib (cocone-map f g c) c')
  (α : (pr1 s) ~ (pr1 t))
  (β : {!(pr1 (htpy-cocone-eq f g (cocone-map f g c (pr1 s)) c' (pr2 s))) ~ ((α ·r (pr1 c)) ∙h (pr1 (htpy-cocone-eq f g (cocone-map f g c (pr1 t)) c' (pr2 t))))!}) (γ : {!!}) → UU _
coherence-htpy-fib-cocone-map f g (dpair i (dpair j H)) (dpair i' (dpair j' H')) (dpair h KLM) (dpair h' KLM') α β γ =
  let E = htpy-cocone-eq f g
          ( cocone-map f g (dpair i (dpair j H)) h)
          ( dpair i' (dpair j' H')) KLM
      K = pr1 E
      L = pr1 (pr2 E)
      M = pr2 (pr2 E)
      E' = htpy-cocone-eq f g
          ( cocone-map f g (dpair i (dpair j H)) h')
          ( dpair i' (dpair j' H')) KLM'
      K' = pr1 E'
      L' = pr1 (pr2 E')
      M' = pr2 (pr2 E')
  in
  (htpy-ap-concat _ _ (h ·l H) {!!} ∙h {!!}) ~ {!!}

htpy-fib-cocone-map :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  {Y : UU l5} (c' : cocone f g Y) →
  fib (cocone-map f g c) c' → fib (cocone-map f g c) c' → UU _
htpy-fib-cocone-map f g (dpair i (dpair j H)) (dpair i' (dpair j' H'))
  (dpair h KLM) (dpair h' KLM') =
  let E = htpy-cocone-eq f g
          ( cocone-map f g (dpair i (dpair j H)) h)
          ( dpair i' (dpair j' H')) KLM
      K = pr1 E
      L = pr1 (pr2 E)
      M = pr2 (pr2 E)
      E' = htpy-cocone-eq f g
          ( cocone-map f g (dpair i (dpair j H)) h')
          ( dpair i' (dpair j' H')) KLM'
      K' = pr1 E'
      L' = pr1 (pr2 E')
      M' = pr2 (pr2 E')
  in
  Σ ( h ~ h')
    ( λ α → Σ (K ~ ((α ·r i) ∙h K'))
      ( λ β → Σ (L ~ ((α ·r j) ∙h L'))
        ( coherence-htpy-fib-cocone-map f g
          ( dpair i (dpair j H))
          ( dpair i' (dpair j' H'))
          ( dpair h KLM)

          ( dpair h' KLM') α β )))

sec-pr1-generating-data-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l' : Level) → universal-property-pushout l' f g c) →
  (P : X → UU l) →
  generating-data-pushout f g c P → sec (pr1 {A = X} {B = P})
sec-pr1-generating-data-pushout
  f g {X} (dpair i (dpair j H)) up P (dpair i' (dpair j' H')) =
  let c = dpair i (dpair j H)
      c' = dpair i' (dpair j' H')
      u = inv-is-equiv (up _ (Σ X P))
          ( tot-cocone f g c c')
      α = issec-inv-is-equiv (up _ (Σ X P))
          ( tot-cocone f g c c')
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
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) → universal-property-pushout l f g c) →
  (P : X → UU l) →
  generating-data-pushout f g c P → (x : X) → P x
ind-pushout-universal-property-pushout {S = S} {A} {B} f g {X} c up P c' =
  Π-sec-pr1 P (sec-pr1-generating-data-pushout f g c up P c')

comp-pushout-universal-property-pushout-A :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4}
  (i : A → X) (j : B → X) (H : (i ∘ f) ~ (j ∘ g)) →
  (up : (l' : Level) → universal-property-pushout l' f g (dpair i (dpair j H)))
  (P : X → UU l)
  (i' : (a : A) → P (i a)) (j' : (b : B) → P (j b))
  (H' : (s : S) → Id (tr P (H s) (i' (f s))) (j' (g s))) →
  ( ( pr1 ( dgen-pushout f g (dpair i (dpair j H))
      ( ind-pushout-universal-property-pushout
        f g (dpair i (dpair j H)) up P (dpair i' (dpair j' H'))))) ~ i')
comp-pushout-universal-property-pushout-A f g i j H up i' j' H' = {!!}

comp-pushout-universal-property-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  (up : (l' : Level) → universal-property-pushout l' f g c) →
  (P : X → UU l) →
  ( ( dgen-pushout f g c) ∘
    ( ind-pushout-universal-property-pushout f g c up P)) ~ id
comp-pushout-universal-property-pushout
  f g (dpair i (dpair j H)) up P (dpair i' (dpair j' H')) =
  eq-htpy-generating-data-pushout f g
    ( dpair i (dpair j H)) P
    ( dgen-pushout f g
      ( dpair i (dpair j H))
      ( ind-pushout-universal-property-pushout f g
        ( dpair i (dpair j H)) up P
        ( dpair i' (dpair j' H'))))
    ( dpair i' (dpair j' H'))
    ( dpair
      ( comp-pushout-universal-property-pushout-A f g i j H up P i' j' H')
      ( dpair
        {!!}
        {!!}))
-}
-}

-- Section 15.2 Families over pushouts

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

reflexive-htpy-generating-data-fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s : generating-data-fam-pushout l f g) →
  htpy-generating-data-fam-pushout l f g s s
reflexive-htpy-generating-data-fam-pushout l f g (dpair PA (dpair PB PS)) =
  dpair (λ a → equiv-id (PA a))
    ( dpair
      ( λ b → equiv-id (PB b))
      ( λ s → htpy-refl _))

htpy-generating-data-fam-pushout-eq :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s t : generating-data-fam-pushout l f g) →
  Id s t → htpy-generating-data-fam-pushout l f g s t
htpy-generating-data-fam-pushout-eq l f g s .s refl =
  reflexive-htpy-generating-data-fam-pushout l f g s

is-equiv-htpy-generating-data-fam-pushout-eq :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s t : generating-data-fam-pushout l f g) →
  is-equiv (htpy-generating-data-fam-pushout-eq l f g s t)
is-equiv-htpy-generating-data-fam-pushout-eq l f g s =
  id-fundamental-gen s
    ( reflexive-htpy-generating-data-fam-pushout l f g s)
    ( is-contr-total-htpy-generating-data-fam-pushout l f g s)
    ( htpy-generating-data-fam-pushout-eq l f g s)

eq-htpy-generating-data-fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s t : generating-data-fam-pushout l f g) →
  (htpy-generating-data-fam-pushout l f g s t) → Id s t
eq-htpy-generating-data-fam-pushout l f g s t =
  inv-is-equiv
    ( is-equiv-htpy-generating-data-fam-pushout-eq l f g s t)

issec-eq-htpy-generating-data-fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s t : generating-data-fam-pushout l f g) →
  ( ( htpy-generating-data-fam-pushout-eq l f g s t) ∘
    ( eq-htpy-generating-data-fam-pushout l f g s t)) ~ id
issec-eq-htpy-generating-data-fam-pushout l f g s t =
  issec-inv-is-equiv
    ( is-equiv-htpy-generating-data-fam-pushout-eq l f g s t)

isretr-eq-htpy-generating-data-fam-pushout :
  {l1 l2 l3 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (s t : generating-data-fam-pushout l f g) →
  ( ( eq-htpy-generating-data-fam-pushout l f g s t) ∘
    ( htpy-generating-data-fam-pushout-eq l f g s t)) ~ id
isretr-eq-htpy-generating-data-fam-pushout l f g s t =
  isretr-inv-is-equiv
    ( is-equiv-htpy-generating-data-fam-pushout-eq l f g s t)
-}
