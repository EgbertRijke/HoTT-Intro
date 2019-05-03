{-# OPTIONS --without-K --exact-split #-}

module 15-pullbacks where

import 14-fundamental-cover
open 14-fundamental-cover public

-- Section 13.1 Cartesian squares

{- We introduce the basic concepts of this chapter: commuting squares, cospans,
   cones, and pullback squares. Pullback squares are also called cartesian
   squares. -}

{- Commutativity of squares is expressed with a homotopy. -}

coherence-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (top : C → B) (left : C → A) (right : B → X) (bottom : A → X) →
  UU (l3 ⊔ l4)
coherence-square top left right bottom =
  (bottom ∘ left) ~ (right ∘ top)

{- A cospan is a pair of functions with a common codomain. -}

cospan :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) →
  UU (l1 ⊔ (l2 ⊔ (lsuc l)))
cospan l A B =
  Σ (UU l) (λ X → (A → X) × (B → X))

{- A cone on a cospan with a vertex C is a pair of functions from C into the
   domains of the maps in the cospan, equipped with a homotopy witnessing that
   the resulting square commutes. -}
   
cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → UU l4 → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
cone {A = A} {B = B} f g C =
  Σ (C → A) (λ p → Σ (C → B) (λ q → coherence-square q p g f))

{- A map into the vertex of a cone induces a new cone. -}

cone-map :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} {C' : UU l5} →
  cone f g C → (C' → C) → cone f g C'
cone-map f g c h =
  pair
    ( (pr1 c) ∘ h)
    ( pair
      ( (pr1 (pr2 c)) ∘ h)
      ( (pr2 (pr2 c)) ·r h))

{- We introduce the universal property of pullbacks. -}

universal-property-pullback :
  {l1 l2 l3 l4 : Level} (l : Level) {A : UU l1} {B : UU l2}
  {X : UU l3} (f : A → X) (g : B → X) {C : UU l4} → cone f g C →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l4 ⊔ (lsuc l)))))
universal-property-pullback l f g c =
  (C' : UU l) → is-equiv (cone-map f g {C' = C'} c)

map-universal-property-pullback :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C) →
  ({l : Level} → universal-property-pullback l f g c) →
  {C' : UU l5} (c' : cone f g C') → C' → C
map-universal-property-pullback f g c up-c {C'} c' =
  inv-is-equiv (up-c C') c'

eq-map-universal-property-pullback :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C) →
  (up-c : {l : Level} → universal-property-pullback l f g c) →
  {C' : UU l5} (c' : cone f g C') →
  Id (cone-map f g c (map-universal-property-pullback f g c up-c c')) c'
eq-map-universal-property-pullback f g c up-c {C'} c' =
  issec-inv-is-equiv (up-c C') c'

{- Next we characterize the identity type of the type of cones with a given
   vertex C. Note that in the definition of htpy-cone we do not use pattern 
   matching on the cones c and c'. This is to ensure that the type
   htpy-cone f g c c' is a Σ-type for any c and c', not just for c and c' of the
   form (pair p (pair q H)) and (pair p' (pair q' H')) respectively. -}

coherence-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c c' : cone f g C) →
  (K : (pr1 c) ~ (pr1 c')) (L : (pr1 (pr2 c)) ~ (pr1 (pr2 c'))) → UU (l4 ⊔ l3)
coherence-htpy-cone f g c c' K L =
  ( (pr2 (pr2 c)) ∙h (htpy-left-whisk g L)) ~
  ( (htpy-left-whisk f K) ∙h (pr2 (pr2 c')))

htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} → cone f g C → cone f g C →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
htpy-cone f g c c' =
  Σ ( (pr1 c) ~ (pr1 c'))
    ( λ K → Σ ((pr1 (pr2 c)) ~ (pr1 (pr2 c')))
      ( λ L → coherence-htpy-cone f g c c' K L))

reflexive-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C) →
  htpy-cone f g c c
reflexive-htpy-cone f g c = 
  pair htpy-refl (pair htpy-refl htpy-right-unit)
      
htpy-cone-eq :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c c' : cone f g C) →
  Id c c' → htpy-cone f g c c'
htpy-cone-eq f g c .c refl =
  reflexive-htpy-cone f g c

abstract
  is-contr-total-htpy-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C) →
    is-contr (Σ (cone f g C) (htpy-cone f g c))
  is-contr-total-htpy-cone {A = A} {B} f g {C} (pair p (pair q H)) =
    is-contr-total-Eq-structure
      ( λ p' qH' K →
        Σ ( q ~ (pr1 qH'))
          ( coherence-htpy-cone f g (pair p (pair q H)) (pair p' qH') K))
      ( is-contr-total-htpy p)
      ( pair p htpy-refl)
      ( is-contr-total-Eq-structure
        ( λ q' H' →
            coherence-htpy-cone f g
            ( pair p (pair q H))
            ( pair p (pair q' H'))
            ( htpy-refl))
        ( is-contr-total-htpy q)
        ( pair q htpy-refl)
        ( is-contr-equiv'
          ( Σ ((f ∘ p) ~ (g ∘ q)) (λ H' → H ~ H'))
          ( equiv-tot-fam-equiv
            ( λ H' → equiv-htpy-concat htpy-right-unit H'))
            ( is-contr-total-htpy H)))
  
abstract
  is-fiberwise-equiv-htpy-cone-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C) →
    is-fiberwise-equiv (htpy-cone-eq f g c)
  is-fiberwise-equiv-htpy-cone-eq f g {C = C} c =
    fundamental-theorem-id c
      ( htpy-cone-eq f g c c refl)
      ( is-contr-total-htpy-cone f g c)
      ( htpy-cone-eq f g c)

equiv-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c c' : cone f g C) →
  Id c c' ≃ htpy-cone f g c c'
equiv-htpy-cone f g c c' =
  pair (htpy-cone-eq f g c c') (is-fiberwise-equiv-htpy-cone-eq f g c c')

{- The inverse of htpy-cone-eq is the map eq-htpy-cone. -}
      
eq-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {g : B → X} {C : UU l4} (c c' : cone f g C) →
  htpy-cone f g c c' → Id c c'
eq-htpy-cone {f = f} {g = g} c c' =
  inv-is-equiv (is-fiberwise-equiv-htpy-cone-eq f g c c')

{- This completes our characterization of the identity type of the type of
   cones with a fixed vertex C. -}

{- We now conclude the universal property of pullbacks as the following
   statement of contractibility. -}

abstract
  is-contr-universal-property-pullback :
    {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    universal-property-pullback l5 f g c →
    (C' : UU l5) (c' : cone f g C') →
    is-contr (Σ (C' → C) (λ h → htpy-cone f g (cone-map f g c h) c'))
  is-contr-universal-property-pullback {C = C} f g c up C' c' =
    is-contr-equiv'
      ( Σ (C' → C) (λ h → Id (cone-map f g c h) c'))
      ( equiv-tot-fam-equiv
        (λ h → equiv-htpy-cone f g (cone-map f g c h) c'))
      ( is-contr-map-is-equiv (up C')  c')

-- Section 13.2

{- The canonical pullback is a type which can be equipped with a cone that
   satisfies the universal property of a pullback. -}

canonical-pullback : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → UU ((l1 ⊔ l2) ⊔ l3)
canonical-pullback {A = A} {B = B} f g = Σ A (λ x → Σ B (λ y → Id (f x) (g y)))

{- We construct the maps and homotopies that are part of the cone structure of
   the canonical pullback. -}
   
π₁ : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {g : B → X} → canonical-pullback f g → A
π₁ = pr1

π₂ : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {g : B → X} → canonical-pullback f g → B
π₂ t = pr1 (pr2 t)

π₃ : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {f : A → X}
  {g : B → X} → (f ∘ (π₁ {f = f} {g = g})) ~ (g ∘ (π₂ {f = f} {g = g}))
π₃ t = pr2 (pr2 t)

cone-canonical-pullback : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → cone f g (canonical-pullback f g)
cone-canonical-pullback f g = pair π₁ (pair π₂ π₃)

{- We show now that the canonical pullback satisfies the universal property of
   a pullback. -}

abstract
  universal-property-pullback-canonical-pullback : {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X) →
    universal-property-pullback l4 f g (cone-canonical-pullback f g)
  universal-property-pullback-canonical-pullback f g C =
    is-equiv-comp
      ( cone-map f g (cone-canonical-pullback f g))
      ( tot (λ p → choice-∞))
      ( mapping-into-Σ)
      ( htpy-refl)
      ( is-equiv-mapping-into-Σ)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ p → is-equiv-choice-∞))

{- Next we establish a '3-for-2' property for pullbacks. -}

triangle-cone-cone : {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
  {f : A → X} {g : B → X} (c : cone f g C) (c' : cone f g C')
  (h : C' → C) (KLM : htpy-cone f g (cone-map f g c h) c') (D : UU l6) →
  (cone-map f g {C' = D} c') ~ ((cone-map f g c) ∘ (λ (k : D → C') → h ∘ k))
triangle-cone-cone {C' = C'} {f = f} {g = g} c c' h KLM D k = 
  inv (ap
    ( λ t → cone-map f g {C' = D} t k)
    { x = (cone-map f g c h)}
    { y = c'}
    ( eq-htpy-cone (cone-map f g c h) c' KLM))

abstract
  is-equiv-up-pullback-up-pullback : {l1 l2 l3 l4 l5 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
    (f : A → X) (g : B → X) (c : cone f g C) (c' : cone f g C')
    (h : C' → C) (KLM : htpy-cone f g (cone-map f g c h) c') →
    ({l : Level} → universal-property-pullback l f g c) →
    ({l : Level} → universal-property-pullback l f g c') →
    is-equiv h
  is-equiv-up-pullback-up-pullback {C = C} {C' = C'} f g c c' h KLM up up' =
    is-equiv-is-equiv-postcomp h
      ( λ D → is-equiv-right-factor
        ( cone-map f g {C' = D} c')
        ( cone-map f g c)
        ( λ (k : D → C') → h ∘ k)
        ( triangle-cone-cone {C = C} {C' = C'} {f = f} {g = g} c c' h KLM D)
        ( up D) (up' D))

abstract
  up-pullback-up-pullback-is-equiv : {l1 l2 l3 l4 l5 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
    (f : A → X) (g : B → X) (c : cone f g C) (c' : cone f g C')
    (h : C' → C) (KLM : htpy-cone f g (cone-map f g c h) c') → is-equiv h →
    ({l : Level} → universal-property-pullback l f g c) →
    ({l : Level} → universal-property-pullback l f g c')
  up-pullback-up-pullback-is-equiv f g c c' h KLM is-equiv-h up D =
    is-equiv-comp
      ( cone-map f g c')
      ( cone-map f g c)
      ( λ k → h ∘ k)
      ( triangle-cone-cone {f = f} {g = g} c c' h KLM D)
      ( is-equiv-postcomp-is-equiv h is-equiv-h D)
      ( up D)

abstract
  up-pullback-is-equiv-up-pullback : {l1 l2 l3 l4 l5 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
    (f : A → X) (g : B → X) (c : cone f g C) (c' : cone f g C')
    (h : C' → C) (KLM : htpy-cone f g (cone-map f g c h) c') →
    ({l : Level} → universal-property-pullback l f g c') →
    is-equiv h →
    ({l : Level} → universal-property-pullback l f g c)
  up-pullback-is-equiv-up-pullback f g c c' h KLM up' is-equiv-h D =
    is-equiv-left-factor
      ( cone-map f g c')
      ( cone-map f g c)
      ( λ k → h ∘ k)
      ( triangle-cone-cone {f = f} {g = g} c c' h KLM D)
      ( up' D)
      ( is-equiv-postcomp-is-equiv h is-equiv-h D)

{- This concludes the '3-for-2-property' of pullbacks. -}

{- We characterize the identity type of the canonical pullback. -}

Eq-canonical-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (t t' : canonical-pullback f g) → UU (l1 ⊔ (l2 ⊔ l3))
Eq-canonical-pullback f g (pair a bp) t' =
  let b = pr1 bp
      p = pr2 bp
      a' = pr1 t'
      b' = pr1 (pr2 t')
      p' = pr2 (pr2 t')
  in
  Σ (Id a a') (λ α → Σ (Id b b') (λ β → Id ((ap f α) ∙ p') (p ∙ (ap g β))))

reflexive-Eq-canonical-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (t : canonical-pullback f g) →
  Eq-canonical-pullback f g t t
reflexive-Eq-canonical-pullback f g (pair a (pair b p)) =
  pair refl (pair refl (inv right-unit))

Eq-canonical-pullback-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (t t' : canonical-pullback f g) →
  Id t t' → Eq-canonical-pullback f g t t'
Eq-canonical-pullback-eq f g t .t refl =
  reflexive-Eq-canonical-pullback f g t

abstract
  is-contr-total-Eq-canonical-pullback :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) (t : canonical-pullback f g) →
    is-contr (Σ (canonical-pullback f g) (Eq-canonical-pullback f g t))
  is-contr-total-Eq-canonical-pullback f g (pair a (pair b p)) =
    is-contr-total-Eq-structure
      ( λ a' bp' α →
        Σ (Id b (pr1 bp')) (λ β → Id ((ap f α) ∙ (pr2 bp')) (p ∙ (ap g β))))
      ( is-contr-total-path a)
      ( pair a refl)
      ( is-contr-total-Eq-structure
        ( λ b' p' β → Id ((ap f refl) ∙ p') (p ∙ (ap g β)))
        ( is-contr-total-path b)
        ( pair b refl)
        ( is-contr-equiv'
          ( Σ (Id (f a) (g b)) (λ p' → Id p p'))
          ( equiv-tot-fam-equiv
            ( λ p' → (equiv-concat' p' (inv right-unit)) ∘e (equiv-inv p p')))
          ( is-contr-total-path p)))

abstract
  is-equiv-Eq-canonical-pullback-eq :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) (t t' : canonical-pullback f g) →
    is-equiv (Eq-canonical-pullback-eq f g t t')
  is-equiv-Eq-canonical-pullback-eq f g t =
    fundamental-theorem-id t
      ( reflexive-Eq-canonical-pullback f g t)
      ( is-contr-total-Eq-canonical-pullback f g t)
      ( Eq-canonical-pullback-eq f g t)

eq-Eq-canonical-pullback :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  ( f : A → X) (g : B → X) {t t' : canonical-pullback f g} →
  ( α : Id (pr1 t) (pr1 t')) (β : Id (pr1 (pr2 t)) (pr1 (pr2 t'))) →
  ( Id ((ap f α) ∙ (pr2 (pr2 t'))) ((pr2 (pr2 t)) ∙ (ap g β))) → Id t t'
eq-Eq-canonical-pullback f g {pair a (pair b p)} {pair a' (pair b' p')} α β γ =
  inv-is-equiv
    ( is-equiv-Eq-canonical-pullback-eq f g
      ( pair a (pair b p))
      ( pair a' (pair b' p')))
    ( pair α (pair β γ))

{- We establish the uniquely uniqueness of pullbacks. -}

htpy-cone-map-universal-property-pullback :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C) →
  (up-c : {l : Level} → universal-property-pullback l f g c) →
  {C' : UU l5} (c' : cone f g C') →
  htpy-cone f g
    ( cone-map f g c (map-universal-property-pullback f g c up-c c'))
    ( c')
htpy-cone-map-universal-property-pullback f g c up-c c' =
  htpy-cone-eq f g
    ( cone-map f g c (map-universal-property-pullback f g c up-c c'))
    ( c')
    ( eq-map-universal-property-pullback f g c up-c c')

abstract
  uniquely-unique-pullback :
    { l1 l2 l3 l4 l5 : Level}
    { A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
    ( f : A → X) (g : B → X) (c : cone f g C) (c' : cone f g C') →
    ( {l : Level} → universal-property-pullback l f g c') →
    ( {l : Level} → universal-property-pullback l f g c) →
    is-contr
      ( Σ (C' ≃ C) (λ h → htpy-cone f g (cone-map f g c (map-equiv h)) c'))
  uniquely-unique-pullback {C = C} {C' = C'} f g c c' up-c' up-c =
    is-contr-total-Eq-substructure
      ( is-contr-universal-property-pullback f g c up-c C' c')
      ( is-subtype-is-equiv)
      ( map-universal-property-pullback f g c up-c c')
      ( htpy-cone-map-universal-property-pullback f g c up-c c')
      ( is-equiv-up-pullback-up-pullback f g c c'
        ( map-universal-property-pullback f g c up-c c')
        ( htpy-cone-map-universal-property-pullback f g c up-c c')
        up-c up-c')

{- The gap map of a square is the map fron the vertex of the cone into the
   canonical pullback. -}

gap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) → cone f g C → C → canonical-pullback f g
gap f g c z = pair ((pr1 c) z) (pair ((pr1 (pr2 c)) z) ((pr2 (pr2 c)) z))

{- The proposition is-pullback is the assertion that the gap map is an 
   equivalence. Note that this proposition is small, whereas the universal 
   property is a large proposition. Of course, we will show below that the
   proposition is-pullback is equivalent to the universal property of
   pullbacks. -}

is-pullback :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) → cone f g C → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
is-pullback f g c = is-equiv (gap f g c)

{- We first establish that a cone is equal to the value of cone-map at
   its own gap map. -}

htpy-cone-up-pullback-canonical-pullback :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  htpy-cone f g (cone-map f g (cone-canonical-pullback f g) (gap f g c)) c
htpy-cone-up-pullback-canonical-pullback f g c =
  pair htpy-refl ( pair htpy-refl htpy-right-unit)

{- We show that the universal property of the pullback implies that the gap
   map is an equivalence. -}

abstract
  is-pullback-up-pullback :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    ({l : Level} → universal-property-pullback l f g c) → is-pullback f g c
  is-pullback-up-pullback f g c up =
    is-equiv-up-pullback-up-pullback f g
      ( cone-canonical-pullback f g)
      ( c)
      ( gap f g c)
      ( htpy-cone-up-pullback-canonical-pullback f g c)
      ( universal-property-pullback-canonical-pullback f g)
      ( up)

{- We show that the universal property follows from the assumption that the
   the gap map is an equivalence. -}

abstract
  up-pullback-is-pullback :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → ({l : Level} → universal-property-pullback l f g c)
  up-pullback-is-pullback f g c is-pullback-c =
    up-pullback-up-pullback-is-equiv f g
      ( cone-canonical-pullback f g)
      ( c)
      ( gap f g c)
      ( htpy-cone-up-pullback-canonical-pullback f g c)
      ( is-pullback-c)
      ( universal-property-pullback-canonical-pullback f g)

-- Section 13.3 Fiber products

{- We construct the cone for two maps into the unit type. -}

cone-prod :
  {i j : Level} (A : UU i) (B : UU j) →
  cone (const A unit star) (const B unit star) (A × B)
cone-prod A B = pair pr1 (pair pr2 htpy-refl)

{- Cartesian products are a special case of pullbacks. -}

inv-gap-prod :
  {i j : Level} (A : UU i) (B : UU j) →
  canonical-pullback (const A unit star) (const B unit star) → A × B
inv-gap-prod A B (pair a (pair b p)) = pair a b

issec-inv-gap-prod :
  {i j : Level} (A : UU i) (B : UU j) →
  ( ( gap (const A unit star) (const B unit star) (cone-prod A B)) ∘
    ( inv-gap-prod A B)) ~ id
issec-inv-gap-prod A B (pair a (pair b p)) =
  eq-Eq-canonical-pullback
    ( const A unit star)
    ( const B unit star)
    refl
    refl
    ( is-prop-is-contr' (is-prop-is-contr is-contr-unit star star) p refl)

isretr-inv-gap-prod :
  {i j : Level} (A : UU i) (B : UU j) →
  ( ( inv-gap-prod A B) ∘
    ( gap (const A unit star) (const B unit star) (cone-prod A B))) ~ id
isretr-inv-gap-prod A B (pair a b) =
  eq-pair refl refl

abstract
  is-pullback-prod :
    {i j : Level} (A : UU i) (B : UU j) →
    is-pullback (const A unit star) (const B unit star) (cone-prod A B)
  is-pullback-prod A B =
    is-equiv-has-inverse
      ( inv-gap-prod A B)
      ( issec-inv-gap-prod A B)
      ( isretr-inv-gap-prod A B)

{- We conclude that cartesian products satisfy the universal property of 
   pullbacks. -}

abstract
  universal-property-pullback-prod :
    {i j : Level} (A : UU i) (B : UU j) →
    {l : Level} → universal-property-pullback l
      ( const A unit star)
      ( const B unit star)
      ( cone-prod A B)
  universal-property-pullback-prod A B =
    up-pullback-is-pullback
      ( const A unit star)
      ( const B unit star)
      ( cone-prod A B)
      ( is-pullback-prod A B)

{- Similar as the above, but now for families of products. -}

cone-fiberwise-prod :
  {l1 l2 l3 : Level} {X : UU l1} (P : X → UU l2) (Q : X → UU l3) →
  cone (pr1 {A = X} {B = P}) (pr1 {A = X} {B = Q}) (Σ X (λ x → (P x) × (Q x)))
cone-fiberwise-prod P Q =
  pair
    ( tot (λ x → pr1))
    ( pair
      ( tot (λ x → pr2))
      ( htpy-refl))

{- We will show that the fiberwise product is a pullback by showing that the
   gap map is an equivalence. We do this by directly construct an inverse to
   the gap map. -}

inv-gap-fiberwise-prod :
  {l1 l2 l3 : Level} {X : UU l1} (P : X → UU l2) (Q : X → UU l3) →
  canonical-pullback (pr1 {B = P}) (pr1 {B = Q}) → Σ X (λ x → (P x) × (Q x))
inv-gap-fiberwise-prod P Q (pair (pair x p) (pair (pair .x q) refl)) =
  pair x (pair p q)

issec-inv-gap-fiberwise-prod :
  {l1 l2 l3 : Level} {X : UU l1} (P : X → UU l2) (Q : X → UU l3) →
  ((gap (pr1 {B = P}) (pr1 {B = Q}) (cone-fiberwise-prod P Q)) ∘
  (inv-gap-fiberwise-prod P Q)) ~ id
issec-inv-gap-fiberwise-prod P Q (pair (pair x p) (pair (pair .x q) refl)) =
  eq-pair refl (eq-pair refl refl)

isretr-inv-gap-fiberwise-prod :
  {l1 l2 l3 : Level} {X : UU l1} (P : X → UU l2) (Q : X → UU l3) →
  ( ( inv-gap-fiberwise-prod P Q) ∘
    ( gap (pr1 {B = P}) (pr1 {B = Q}) (cone-fiberwise-prod P Q))) ~ id
isretr-inv-gap-fiberwise-prod P Q (pair x (pair p q)) = refl

{- With all the pieces in place we conclude that the fiberwise product is a
   pullback. -}

abstract
  is-pullback-fiberwise-prod :
    {l1 l2 l3 : Level} {X : UU l1} (P : X → UU l2) (Q : X → UU l3) →
    is-pullback (pr1 {A = X} {B = P}) (pr1 {A = X} {B = Q})
      (cone-fiberwise-prod P Q)
  is-pullback-fiberwise-prod P Q =
    is-equiv-has-inverse
      ( inv-gap-fiberwise-prod P Q)
      ( issec-inv-gap-fiberwise-prod P Q)
      ( isretr-inv-gap-fiberwise-prod P Q)
  
{- Furthermore we conclude that the fiberwise product satisfies the universal
   property of pullbacks. -}

abstract
  universal-property-pullback-fiberwise-prod :
    {l1 l2 l3 l4 : Level} {X : UU l1} (P : X → UU l2) (Q : X → UU l3) →
    universal-property-pullback l4 (pr1 {B = P}) (pr1 {B = Q})
      (cone-fiberwise-prod P Q)
  universal-property-pullback-fiberwise-prod P Q =
    up-pullback-is-pullback pr1 pr1
      ( cone-fiberwise-prod P Q)
      ( is-pullback-fiberwise-prod P Q)

{- We now generalize the above to arbitrary maps and their fibers. -}

cone-total-prod-fibers :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → cone f g (Σ X (λ x → (fib f x) × (fib g x)))
cone-total-prod-fibers f g =
  pair
    ( λ t → pr1 (pr1 (pr2 t)))
    ( pair
      ( λ t → pr1 (pr2 (pr2 t)))
      ( λ t → (pr2 (pr1 (pr2 t))) ∙ (inv (pr2 (pr2 (pr2 t))))))

cone-span :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l4} {B' : UU l5} {C : A' → B' → UU l6}
  (i : A' → A) (j : B' → B)
  (k : (x : A') (y : B') → C x y → Id (f (i x)) (g (j y))) →
  cone f g (Σ A' (λ x → Σ B' (C x)))
cone-span f g i j k =
  pair
    ( λ t → i (pr1 t))
    ( pair
      ( λ t → j (pr1 (pr2 t)))
      ( λ t → k (pr1 t) (pr1 (pr2 t)) (pr2 (pr2 t))))

abstract
  is-pullback-cone-span-is-equiv :
    {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X)
    {A' : UU l4} {B' : UU l5} {C : A' → B' → UU l6}
    (i : A' → A) (j : B' → B)
    (k : (x' : A') (y' : B') → C x' y' → Id (f (i x')) (g (j y'))) →
    is-equiv i → is-equiv j → ((x : A') (y : B') → is-equiv (k x y)) →
    is-pullback f g (cone-span f g i j k)
  is-pullback-cone-span-is-equiv {B = B} f g i j k
    is-equiv-i is-equiv-j is-equiv-k =
    is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map
      ( λ x → Σ B (λ y → Id (f x) (g y)))
      ( i)
      ( λ x' → toto (λ y → Id (f (i x')) (g y)) j (k x'))
      ( is-equiv-i)
      ( λ x' → is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map
        ( λ y → Id (f (i x')) (g y))
        ( j)
        ( k x')
        ( is-equiv-j)
        ( is-equiv-k x'))

abstract
  is-pullback-total-prod-fibers :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) →
    is-pullback f g (cone-total-prod-fibers f g)
  is-pullback-total-prod-fibers f g =
    is-equiv-comp
      ( gap f g (cone-total-prod-fibers f g))
      ( gap f g
        (cone-span f g
          ( Σ-fib-to-domain f)
          ( Σ-fib-to-domain g)
          ( λ s t α → (pr2 (pr2 s)) ∙ (α ∙ (inv (pr2 (pr2 t)))))))
      ( gap
        ( pr1 {B = fib f})
        ( pr1 {B = fib g})
        ( cone-fiberwise-prod (fib f) (fib g)))
      ( λ t → refl)
      ( is-pullback-fiberwise-prod (fib f) (fib g))
      ( is-pullback-cone-span-is-equiv f g
        ( Σ-fib-to-domain f)
        ( Σ-fib-to-domain g)
        ( λ s t α → (pr2 (pr2 s)) ∙ (α ∙ (inv (pr2 (pr2 t)))))
        ( is-equiv-Σ-fib-to-domain f)
        ( is-equiv-Σ-fib-to-domain g)
        ( λ s t → is-equiv-comp _
          ( concat (pr2 (pr2 s)) (g (pr1 (pr2 t))))
          ( concat' (pr1 s) (inv (pr2 (pr2 t))))
          ( htpy-refl)
          ( is-equiv-concat' (pr1 s) (inv (pr2 (pr2 t))))
          ( is-equiv-concat (pr2 (pr2 s)) (g (pr1 (pr2 t))))))

-- Section 13.4 Fibers as pullbacks

square-fiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B) →
  ( f ∘ (pr1 {B = λ x → Id (f x) b})) ~
  ( (const unit B b) ∘ (const (fib f b) unit star))
square-fiber f b = pr2

cone-fiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B) →
  cone f (const unit B b) (fib f b)
cone-fiber f b =
  pair pr1 (pair (const (fib f b) unit star) (square-fiber f b))

abstract
  is-pullback-cone-fiber :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    (b : B) → is-pullback f (const unit B b) (cone-fiber f b)
  is-pullback-cone-fiber f b =
    is-equiv-tot-is-fiberwise-equiv ( λ a →
      is-equiv-left-unit-law-Σ-map-gen (λ t → Id (f a) b) is-contr-unit star)

abstract
  universal-property-pullback-cone-fiber :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B) →
    universal-property-pullback l3 f (const unit B b) (cone-fiber f b)
  universal-property-pullback-cone-fiber {B = B} f b =
    up-pullback-is-pullback f (const unit B b)
      ( cone-fiber f b)
      ( is-pullback-cone-fiber f b)

cone-fiber-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  (a : A) → cone (pr1 {B = B}) (const unit A a) (B a)
cone-fiber-fam B a =
  pair (λ b → pair a b) (pair (const (B a) unit star) (λ b → refl))

abstract
  is-pullback-cone-fiber-fam :
    {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
    (a : A) → is-pullback (pr1 {B = B}) (const unit A a) (cone-fiber-fam B a)
  is-pullback-cone-fiber-fam {A = A} B a =
    is-equiv-comp
      ( gap (pr1 {B = B}) (const unit A a) (cone-fiber-fam B a))
      ( gap (pr1 {B = B}) (const unit A a) (cone-fiber (pr1 {B = B}) a))
      ( fib-pr1-fib-fam B a)
      ( λ y → refl)
      ( is-equiv-fib-pr1-fib-fam B a)
      ( is-pullback-cone-fiber pr1 a)

-- Section 13.5 Fiberwise equivalences

cone-subst :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3) →
  cone f (pr1 {B = Q}) (Σ A (λ x → Q (f x)))
cone-subst f Q =
  pair pr1 (pair (Σ-map-base-map f Q) (λ t → refl))

inv-gap-cone-subst :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3) →
  canonical-pullback f (pr1 {B = Q}) → Σ A (λ x → Q (f x))
inv-gap-cone-subst f Q (pair x (pair (pair .(f x) q) refl)) =
  pair x q

issec-inv-gap-cone-subst :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3) →
  ((gap f (pr1 {B = Q}) (cone-subst f Q)) ∘ (inv-gap-cone-subst f Q)) ~ id
issec-inv-gap-cone-subst f Q (pair x (pair (pair .(f x) q) refl)) =
  refl

isretr-inv-gap-cone-subst :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3) →
  ((inv-gap-cone-subst f Q) ∘ (gap f (pr1 {B = Q}) (cone-subst f Q))) ~ id
isretr-inv-gap-cone-subst f Q (pair x q) =
  refl

abstract
  is-pullback-cone-subst :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3) →
    is-pullback f (pr1 {B = Q}) (cone-subst f Q)
  is-pullback-cone-subst f Q =
    is-equiv-has-inverse
      ( inv-gap-cone-subst f Q)
      ( issec-inv-gap-cone-subst f Q)
      ( isretr-inv-gap-cone-subst f Q)

cone-toto :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3}
  (Q : B → UU l4) (f : A → B) (g : (x : A) → (P x) → (Q (f x))) →
  cone f (pr1 {B = Q}) (Σ A P)
cone-toto Q f g = pair pr1 (pair (toto Q f g) (λ t → refl))

abstract
  is-pullback-is-fiberwise-equiv :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3}
    (Q : B → UU l4) (f : A → B) (g : (x : A) → (P x) → (Q (f x))) →
    is-fiberwise-equiv g → is-pullback f (pr1 {B = Q}) (cone-toto Q f g)
  is-pullback-is-fiberwise-equiv Q f g is-equiv-g =
    is-equiv-comp
      ( gap f pr1 (cone-toto Q f g))
      ( gap f pr1 (cone-subst f Q))
      ( tot g)
      ( λ t → refl)
      ( is-equiv-tot-is-fiberwise-equiv is-equiv-g)
      ( is-pullback-cone-subst f Q)

abstract
  universal-property-pullback-is-fiberwise-equiv :
    {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3}
    (Q : B → UU l4) (f : A → B) (g : (x : A) → (P x) → (Q (f x))) →
    is-fiberwise-equiv g →
    universal-property-pullback l5 f (pr1 {B = Q}) (cone-toto Q f g)
  universal-property-pullback-is-fiberwise-equiv Q f g is-equiv-g =
    up-pullback-is-pullback f pr1 (cone-toto Q f g)
      ( is-pullback-is-fiberwise-equiv Q f g is-equiv-g)

abstract
  is-fiberwise-equiv-is-pullback :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3}
    (Q : B → UU l4) (f : A → B) (g : (x : A) → (P x) → (Q (f x))) →
    is-pullback f (pr1 {B = Q}) (cone-toto Q f g) → is-fiberwise-equiv g
  is-fiberwise-equiv-is-pullback Q f g is-pullback-cone-toto =
    is-fiberwise-equiv-is-equiv-tot g
      ( is-equiv-right-factor
        ( gap f pr1 (cone-toto Q f g))
        ( gap f pr1 (cone-subst f Q))
        ( tot g)
        ( λ t → refl)
        ( is-pullback-cone-subst f Q)
        ( is-pullback-cone-toto))

abstract
  is-fiberwise-equiv-universal-property-pullback :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3}
    (Q : B → UU l4) (f : A → B) (g : (x : A) → (P x) → (Q (f x))) →
    ( {l : Level} → universal-property-pullback l f (pr1 {B = Q})
      (cone-toto Q f g)) →
    is-fiberwise-equiv g
  is-fiberwise-equiv-universal-property-pullback Q f g up =
    is-fiberwise-equiv-is-pullback Q f g
      ( is-pullback-up-pullback f pr1 (cone-toto Q f g) up)

fib-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  (x : A) → fib (pr1 c) x → fib g (f x)
fib-square f g c x t =
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  pair (q (pr1 t) ) ((inv (H (pr1 t))) ∙ (ap f (pr2 t)))

fib-square-id :
  {l1 l2 : Level} {B : UU l1} {X : UU l2} (g : B → X) (x : X) →
  fib-square id g (pair g (pair id htpy-refl)) x ~ id
fib-square-id g .(g b) (pair b refl) =
  refl

square-tot-fib-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  ( (gap f g c) ∘ (Σ-fib-to-domain (pr1 c))) ~
  ( (tot (λ a → tot (λ b → inv))) ∘ (tot (fib-square f g c)))
square-tot-fib-square f g c (pair .((pr1 c) x) (pair x refl)) =
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  eq-pair refl
    ( eq-pair refl
      ( inv ((ap inv right-unit) ∙ (inv-inv (H x)))))

abstract
  is-fiberwise-equiv-fib-square-is-pullback :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-fiberwise-equiv (fib-square f g c)
  is-fiberwise-equiv-fib-square-is-pullback f g c pb =
    let p = pr1 c
        q = pr1 (pr2 c)
        H = pr2 (pr2 c)
    in
    is-fiberwise-equiv-is-equiv-tot
      ( fib-square f g c)
      ( is-equiv-top-is-equiv-bottom-square
        ( Σ-fib-to-domain p)
        ( tot (λ x → tot (λ y → inv)))
        ( tot (fib-square f g c))
        ( gap f g c)
        ( square-tot-fib-square f g c)
        ( is-equiv-Σ-fib-to-domain p)
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ x → is-equiv-tot-is-fiberwise-equiv
            ( λ y → is-equiv-inv (g y) (f x))))
        ( pb))

abstract
  is-pullback-is-fiberwise-equiv-fib-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-fiberwise-equiv (fib-square f g c) → is-pullback f g c
  is-pullback-is-fiberwise-equiv-fib-square f g c is-equiv-fsq =
    let p = pr1 c
        q = pr1 (pr2 c)
        H = pr2 (pr2 c)
    in
    is-equiv-bottom-is-equiv-top-square
      ( Σ-fib-to-domain p)
      ( tot (λ x → tot (λ y → inv)))
      ( tot (fib-square f g c))
      ( gap f g c)
      ( square-tot-fib-square f g c)
      ( is-equiv-Σ-fib-to-domain p)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ x → is-equiv-tot-is-fiberwise-equiv
          ( λ y → is-equiv-inv (g y) (f x))))
      ( is-equiv-tot-is-fiberwise-equiv is-equiv-fsq)

abstract
  is-trunc-is-pullback :
    {l1 l2 l3 l4 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {C : UU l3}
    {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-trunc-map k g → is-trunc-map k (pr1 c)
  is-trunc-is-pullback k f g c pb is-trunc-g a =
    is-trunc-is-equiv k
      ( fib g (f a))
      ( fib-square f g c a)
      ( is-fiberwise-equiv-fib-square-is-pullback f g c pb a)
      (is-trunc-g (f a))

abstract
  is-emb-is-pullback :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-emb g → is-emb (pr1 c)
  is-emb-is-pullback f g c pb is-emb-g =
    is-emb-is-prop-map
      ( pr1 c)
      ( is-trunc-is-pullback neg-one-𝕋 f g c pb (is-prop-map-is-emb g is-emb-g))

abstract
  is-equiv-is-pullback :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-equiv g → is-pullback f g c → is-equiv (pr1 c)
  is-equiv-is-pullback f g c is-equiv-g pb =
    is-equiv-is-contr-map
      ( is-trunc-is-pullback neg-two-𝕋 f g c pb
        ( is-contr-map-is-equiv is-equiv-g))

abstract
  is-pullback-is-equiv :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-equiv g → is-equiv (pr1 c) → is-pullback f g c
  is-pullback-is-equiv f g c is-equiv-g is-equiv-p =
    is-pullback-is-fiberwise-equiv-fib-square f g c
      ( λ a → is-equiv-is-contr
        ( fib-square f g c a)
        ( is-contr-map-is-equiv is-equiv-p a)
        ( is-contr-map-is-equiv is-equiv-g (f a)))

-- Section 13.6 The pullback pasting property

coherence-square-comp-horizontal :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (top-left : A → B) (top-right : B → C)
  (left : A → X) (mid : B → Y) (right : C → Z)
  (bottom-left : X → Y) (bottom-right : Y → Z) →
  coherence-square top-left left mid bottom-left →
  coherence-square top-right mid right bottom-right →
  coherence-square
    (top-right ∘ top-left) left right (bottom-right ∘ bottom-left)
coherence-square-comp-horizontal
  top-left top-right left mid right bottom-left bottom-right sq-left sq-right =
  (bottom-right ·l sq-left) ∙h (sq-right ·r top-left)

coherence-square-comp-vertical :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (top : A → X)
  (left-top : A → B) (right-top : X → Y)
  (mid : B → Y)
  (left-bottom : B → C) (right-bottom : Y → Z)
  (bottom : C → Z) →
  coherence-square top left-top right-top mid →
  coherence-square mid left-bottom right-bottom bottom →
  coherence-square
    top (left-bottom ∘ left-top) (right-bottom ∘ right-top) bottom
coherence-square-comp-vertical
  top left-top right-top mid left-bottom right-bottom bottom sq-top sq-bottom =
  (sq-bottom ·r left-top) ∙h (right-bottom ·l sq-top)

cone-comp-horizontal :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z) →
  (c : cone j h B) → (cone i (pr1 c) A) → cone (j ∘ i) h A
cone-comp-horizontal i j h c d =
  pair
   ( pr1 d)
   ( pair
     ( (pr1 (pr2 c)) ∘ (pr1 (pr2 d)))
     ( coherence-square-comp-horizontal
       (pr1 (pr2 d)) (pr1 (pr2 c)) (pr1 d) (pr1 c) h i j
       (pr2 (pr2 d)) (pr2 (pr2 c))))

cone-comp-vertical :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y) →
  (c : cone f g B) → cone (pr1 (pr2 c)) h A → cone f (g ∘ h) A
cone-comp-vertical f g h c d =
  pair
    ( (pr1 c) ∘ (pr1 d))
    ( pair
      ( pr1 (pr2 d))
      ( coherence-square-comp-vertical
        ( pr1 (pr2 d)) (pr1 d) h (pr1 (pr2 c)) (pr1 c) g f
        ( pr2 (pr2 d)) (pr2 (pr2 c))))
  
fib-square-comp-horizontal :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z) →
  (c : cone j h B) (d : cone i (pr1 c) A) → (x : X) →
  ( fib-square (j ∘ i) h (cone-comp-horizontal i j h c d) x) ~
  ( (fib-square j h c (i x)) ∘ (fib-square i (pr1 c) d x))
fib-square-comp-horizontal i j h c d .(pr1 d a) (pair a refl) =
  let f = pr1 d
      k = pr1 (pr2 d)
      H = pr2 (pr2 d)
      g = pr1 c
      l = pr1 (pr2 c)
      K = pr2 (pr2 c)
  in
  eq-pair refl
    ( ( ap
        ( concat' (h (l (k a))) refl)
        ( distributive-inv-concat (ap j (H a)) (K (k a)))) ∙
      ( ( assoc (inv (K (k a))) (inv (ap j (H a))) refl) ∙
        ( ap
          ( concat (inv (K (k a))) (j (i (f a))))
          ( ( ap (concat' (j (g (k a))) refl) (inv (ap-inv j (H a)))) ∙
            ( inv (ap-concat j (inv (H a)) refl))))))

fib-square-comp-vertical : 
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y) →
  (c : cone f g B) (d : cone (pr1 (pr2 c)) h A) (x : C) →
  ( ( fib-square f (g ∘ h) (cone-comp-vertical f g h c d) x) ∘
    ( inv-map-fib-comp (pr1 c) (pr1 d) x)) ~
  ( ( inv-map-fib-comp g h (f x)) ∘
    ( toto
      ( λ t → fib h (pr1 t))
      ( fib-square f g c x)
      ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t))))
fib-square-comp-vertical f g h
  (pair p (pair q H)) (pair p' (pair q' H')) .(p (p' a))
  (pair (pair .(p' a) refl) (pair a refl)) =
  eq-pair refl
    ( ( right-unit) ∙
      ( ( distributive-inv-concat (H (p' a)) (ap g (H' a))) ∙
        ( ( ap
            ( concat (inv (ap g (H' a))) (f (p (p' a))))
            ( inv right-unit)) ∙
          ( ap
            ( concat' (g (h (q' a)))
              ( pr2
                ( fib-square f g
                  ( pair p (pair q H))
                  ( p (p' a))
                  ( pair (p' a) refl))))
            ( ( inv (ap-inv g (H' a))) ∙
              ( ap (ap g) (inv right-unit)))))))

abstract
  is-pullback-rectangle-is-pullback-left-square :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
    (i : X → Y) (j : Y → Z) (h : C → Z)
    (c : cone j h B) (d : cone i (pr1 c) A) →
    is-pullback j h c → is-pullback i (pr1 c) d →
    is-pullback (j ∘ i) h (cone-comp-horizontal i j h c d)
  is-pullback-rectangle-is-pullback-left-square i j h c d is-pb-c is-pb-d =
    is-pullback-is-fiberwise-equiv-fib-square (j ∘ i) h
      ( cone-comp-horizontal i j h c d)
      ( λ x → is-equiv-comp
        ( fib-square (j ∘ i) h (cone-comp-horizontal i j h c d) x)
        ( fib-square j h c (i x))
        ( fib-square i (pr1 c) d x)
        ( fib-square-comp-horizontal i j h c d x)
        ( is-fiberwise-equiv-fib-square-is-pullback i (pr1 c) d is-pb-d x)
        ( is-fiberwise-equiv-fib-square-is-pullback j h c is-pb-c (i x)))

abstract
  is-pullback-left-square-is-pullback-rectangle :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
    (i : X → Y) (j : Y → Z) (h : C → Z)
    (c : cone j h B) (d : cone i (pr1 c) A) →
    is-pullback j h c → is-pullback (j ∘ i) h (cone-comp-horizontal i j h c d) →
    is-pullback i (pr1 c) d
  is-pullback-left-square-is-pullback-rectangle i j h c d is-pb-c is-pb-rect =
    is-pullback-is-fiberwise-equiv-fib-square i (pr1 c) d
      ( λ x → is-equiv-right-factor
        ( fib-square (j ∘ i) h (cone-comp-horizontal i j h c d) x)
        ( fib-square j h c (i x))
        ( fib-square i (pr1 c) d x)
        ( fib-square-comp-horizontal i j h c d x)
        ( is-fiberwise-equiv-fib-square-is-pullback j h c is-pb-c (i x))
        ( is-fiberwise-equiv-fib-square-is-pullback (j ∘ i) h
          ( cone-comp-horizontal i j h c d) is-pb-rect x))

abstract
  is-pullback-top-is-pullback-rectangle :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
    (f : C → Z) (g : Y → Z) (h : X → Y) →
    (c : cone f g B) (d : cone (pr1 (pr2 c)) h A) →
    is-pullback f g c →
    is-pullback f (g ∘ h) (cone-comp-vertical f g h c d) →
    is-pullback (pr1 (pr2 c)) h d
  is-pullback-top-is-pullback-rectangle f g h c d is-pb-c is-pb-dc =
    is-pullback-is-fiberwise-equiv-fib-square (pr1 (pr2 c)) h d
      ( λ x → is-fiberwise-equiv-is-equiv-toto-is-equiv-base-map
        ( λ t → fib h (pr1 t))
        ( fib-square f g c ((pr1 c) x))
        ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t))
        ( is-fiberwise-equiv-fib-square-is-pullback f g c is-pb-c ((pr1 c) x))
        ( is-equiv-top-is-equiv-bottom-square
          ( inv-map-fib-comp (pr1 c) (pr1 d) ((pr1 c) x))
          ( inv-map-fib-comp g h (f ((pr1 c) x)))
          ( toto
            ( λ t → fib h (pr1 t))
            ( fib-square f g c ((pr1 c) x))
            ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t)))
          ( fib-square f (g ∘ h) (cone-comp-vertical f g h c d) ((pr1 c) x))
          ( fib-square-comp-vertical f g h c d ((pr1 c) x))
          ( is-equiv-inv-map-fib-comp (pr1 c) (pr1 d) ((pr1 c) x))
          ( is-equiv-inv-map-fib-comp g h (f ((pr1 c) x)))
          ( is-fiberwise-equiv-fib-square-is-pullback f (g ∘ h)
            ( cone-comp-vertical f g h c d) is-pb-dc ((pr1 c) x)))
        ( pair x refl))

abstract
  is-pullback-rectangle-is-pullback-top :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
    (f : C → Z) (g : Y → Z) (h : X → Y) →
    (c : cone f g B) (d : cone (pr1 (pr2 c)) h A) →
    is-pullback f g c →
    is-pullback (pr1 (pr2 c)) h d →
    is-pullback f (g ∘ h) (cone-comp-vertical f g h c d)
  is-pullback-rectangle-is-pullback-top f g h c d is-pb-c is-pb-d =
    is-pullback-is-fiberwise-equiv-fib-square f (g ∘ h)
      ( cone-comp-vertical f g h c d)
      ( λ x → is-equiv-bottom-is-equiv-top-square
        ( inv-map-fib-comp (pr1 c) (pr1 d) x)
        ( inv-map-fib-comp g h (f x))
        ( toto
          ( λ t → fib h (pr1 t))
          ( fib-square f g c x)
          ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t)))
        ( fib-square f (g ∘ h) (cone-comp-vertical f g h c d) x)
        ( fib-square-comp-vertical f g h c d x)
        ( is-equiv-inv-map-fib-comp (pr1 c) (pr1 d) x)
        ( is-equiv-inv-map-fib-comp g h (f x))
        ( is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map
          ( λ t → fib h (pr1 t))
          ( fib-square f g c x)
          ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t))
          ( is-fiberwise-equiv-fib-square-is-pullback f g c is-pb-c x)
          ( λ t → is-fiberwise-equiv-fib-square-is-pullback
            (pr1 (pr2 c)) h d is-pb-d (pr1 t)))) 

-- Section 13.7 Descent for coproducts and Σ-types

fib-functor-coprod-inl-fib : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (x : A) →
  fib f x → fib (functor-coprod f g) (inl x)
fib-functor-coprod-inl-fib f g x (pair a' p) =
  pair (inl a') (ap inl p)

fib-fib-functor-coprod-inl : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (x : A) →
  fib (functor-coprod f g) (inl x) → fib f x
fib-fib-functor-coprod-inl f g x (pair (inl a') p) =
  pair a' (map-compute-eq-coprod-inl-inl (f a') x p)
fib-fib-functor-coprod-inl f g x (pair (inr b') p) =
  ind-empty {P = λ t → fib f x}
    ( map-compute-eq-coprod-inr-inl (g b') x p)

issec-fib-fib-functor-coprod-inl : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (x : A) →
  ( (fib-functor-coprod-inl-fib f g x) ∘
    ( fib-fib-functor-coprod-inl f g x)) ~ id
issec-fib-fib-functor-coprod-inl f g .(f a') (pair (inl a') refl) =
  eq-pair refl
    ( ap (ap inl)
      ( isretr-inv-is-equiv
        ( is-equiv-map-raise _ (Id (f a') (f a'))) refl))
issec-fib-fib-functor-coprod-inl f g x (pair (inr b') p) =
  ind-empty
    { P = λ t → Id
      ( fib-functor-coprod-inl-fib f g x
        ( fib-fib-functor-coprod-inl f g x (pair (inr b') p)))
      ( pair (inr b') p)}
    ( map-compute-eq-coprod-inr-inl (g b') x p)

isretr-fib-fib-functor-coprod-inl : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (x : A) →
  ( (fib-fib-functor-coprod-inl f g x) ∘
    ( fib-functor-coprod-inl-fib f g x)) ~ id
isretr-fib-fib-functor-coprod-inl f g .(f a') (pair a' refl) =
  eq-pair refl
    ( isretr-inv-is-equiv (is-equiv-map-raise _ (Id (f a') (f a'))) refl)

abstract
  is-equiv-fib-functor-coprod-inl-fib : {l1 l2 l1' l2' : Level}
    {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
    (f : A' → A) (g : B' → B) (x : A) →
    is-equiv (fib-functor-coprod-inl-fib f g x)
  is-equiv-fib-functor-coprod-inl-fib f g x =
    is-equiv-has-inverse
      ( fib-fib-functor-coprod-inl f g x)
      ( issec-fib-fib-functor-coprod-inl f g x)
      ( isretr-fib-fib-functor-coprod-inl f g x)

fib-functor-coprod-inr-fib : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (y : B) →
  fib g y → fib (functor-coprod f g) (inr y)
fib-functor-coprod-inr-fib f g y (pair b' p) =
  pair (inr b') (ap inr p)
  
fib-fib-functor-coprod-inr : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (y : B) →
  fib (functor-coprod f g) (inr y) → fib g y
fib-fib-functor-coprod-inr f g y (pair (inl a') p) =
  ind-empty {P = λ t → fib g y}
    ( map-compute-eq-coprod-inl-inr (f a') y p)
fib-fib-functor-coprod-inr f g y (pair (inr b') p) =
  pair b' (map-compute-eq-coprod-inr-inr (g b') y p)

issec-fib-fib-functor-coprod-inr : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (y : B) →
  ( (fib-functor-coprod-inr-fib f g y) ∘
    ( fib-fib-functor-coprod-inr f g y)) ~ id
issec-fib-fib-functor-coprod-inr f g .(g b') (pair (inr b') refl) =
  eq-pair refl
    ( ap (ap inr)
      ( isretr-inv-is-equiv
        ( is-equiv-map-raise _ (Id (g b') (g b'))) refl))
issec-fib-fib-functor-coprod-inr f g y (pair (inl a') p) =
  ind-empty
    { P = λ t → Id
      ( fib-functor-coprod-inr-fib f g y
        ( fib-fib-functor-coprod-inr f g y (pair (inl a') p)))
      ( pair (inl a') p)}
    ( map-compute-eq-coprod-inl-inr (f a') y p)

isretr-fib-fib-functor-coprod-inr : {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B) (y : B) →
  ( (fib-fib-functor-coprod-inr f g y) ∘
    ( fib-functor-coprod-inr-fib f g y)) ~ id
isretr-fib-fib-functor-coprod-inr f g .(g b') (pair b' refl) =
  eq-pair refl
    ( isretr-inv-is-equiv (is-equiv-map-raise _ (Id (g b') (g b'))) refl)

abstract
  is-equiv-fib-functor-coprod-inr-fib : {l1 l2 l1' l2' : Level}
    {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
    (f : A' → A) (g : B' → B) (y : B) →
    is-equiv (fib-functor-coprod-inr-fib f g y)
  is-equiv-fib-functor-coprod-inr-fib f g y =
    is-equiv-has-inverse
      ( fib-fib-functor-coprod-inr f g y)
      ( issec-fib-fib-functor-coprod-inr f g y)
      ( isretr-fib-fib-functor-coprod-inr f g y)

cone-descent-coprod : {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (i : X' → X)
  (cone-A' : cone f i A') (cone-B' : cone g i B') →
  cone (ind-coprod _ f g) i (coprod A' B')
cone-descent-coprod f g i (pair h (pair f' H)) (pair k (pair g' K)) =
   pair
     ( functor-coprod h k)
     ( pair
       ( ind-coprod _ f' g')
       ( ind-coprod _ H K))

triangle-descent-square-fib-functor-coprod-inl-fib :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A' → A) (g : B' → B) (h : X' → X)
  (αA : A → X) (αB : B → X) (αA' : A' → X') (αB' : B' → X')
  (HA : (αA ∘ f) ~ (h ∘ αA')) (HB : (αB ∘ g) ~ (h ∘ αB')) (x : A) →
  (fib-square αA h (pair f (pair αA' HA)) x) ~
    ( (fib-square (ind-coprod _ αA αB) h
      ( pair
        ( functor-coprod f g)
        ( pair (ind-coprod _ αA' αB') (ind-coprod _ HA HB))) (inl x)) ∘
    ( fib-functor-coprod-inl-fib f g x))
triangle-descent-square-fib-functor-coprod-inl-fib
  {X = X} {X' = X'} f g h αA αB αA' αB' HA HB x (pair a' p) =
  eq-pair refl
    ( ap (concat (inv (HA a')) (αA x))
      ( ap-comp (ind-coprod _ αA αB) inl p))

triangle-descent-square-fib-functor-coprod-inr-fib :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A' → A) (g : B' → B) (h : X' → X)
  (αA : A → X) (αB : B → X) (αA' : A' → X') (αB' : B' → X')
  (HA : (αA ∘ f) ~ (h ∘ αA')) (HB : (αB ∘ g) ~ (h ∘ αB')) (y : B) →
  (fib-square αB h (pair g (pair αB' HB)) y) ~
    ( (fib-square (ind-coprod _ αA αB) h
      ( pair
        ( functor-coprod f g)
        ( pair (ind-coprod _ αA' αB') (ind-coprod _ HA HB))) (inr y)) ∘
    ( fib-functor-coprod-inr-fib f g y))
triangle-descent-square-fib-functor-coprod-inr-fib
  {X = X} {X' = X'} f g h αA αB αA' αB' HA HB y ( pair b' p) =
  eq-pair refl
    ( ap (concat (inv (HB b')) (αB y))
      ( ap-comp (ind-coprod _ αA αB) inr p))

abstract
  descent-coprod : {l1 l2 l3 l1' l2' l3' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
    (f : A → X) (g : B → X) (i : X' → X)
    (cone-A' : cone f i A') (cone-B' : cone g i B') →
    is-pullback f i cone-A' →
    is-pullback g i cone-B' →
    is-pullback (ind-coprod _ f g) i (cone-descent-coprod f g i cone-A' cone-B')
  descent-coprod f g i (pair h (pair f' H)) (pair k (pair g' K))
    is-pb-cone-A' is-pb-cone-B' =
    is-pullback-is-fiberwise-equiv-fib-square
      ( ind-coprod _ f g)
      ( i)
      ( cone-descent-coprod f g i (pair h (pair f' H)) (pair k (pair g' K)))
      ( ind-coprod _
        ( λ x → is-equiv-left-factor
          ( fib-square f i (pair h (pair f' H)) x)
          ( fib-square (ind-coprod _ f g) i
            ( pair (functor-coprod h k)
              ( pair (ind-coprod _ f' g') (ind-coprod _ H K)))
            ( inl x))
          ( fib-functor-coprod-inl-fib h k x)
          ( triangle-descent-square-fib-functor-coprod-inl-fib
            h k i f g f' g' H K x)
          ( is-fiberwise-equiv-fib-square-is-pullback f i
            ( pair h (pair f' H)) is-pb-cone-A' x)
          ( is-equiv-fib-functor-coprod-inl-fib h k x))
        ( λ y →  is-equiv-left-factor
          ( fib-square g i (pair k (pair g' K)) y)
          ( fib-square
            ( ind-coprod _ f g) i
            ( pair
              ( functor-coprod h k)
              ( pair (ind-coprod _ f' g') (ind-coprod _ H K))) (inr y))
            ( fib-functor-coprod-inr-fib h k y)
            ( triangle-descent-square-fib-functor-coprod-inr-fib
              h k i f g f' g' H K y)
            ( is-fiberwise-equiv-fib-square-is-pullback g i
              ( pair k (pair g' K)) is-pb-cone-B' y)
            ( is-equiv-fib-functor-coprod-inr-fib h k y)))

abstract
  descent-coprod-inl : {l1 l2 l3 l1' l2' l3' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
    (f : A → X) (g : B → X) (i : X' → X)
    (cone-A' : cone f i A') (cone-B' : cone g i B') →
    is-pullback
      ( ind-coprod _ f g)
      ( i)
      ( cone-descent-coprod f g i cone-A' cone-B') →
    is-pullback f i cone-A'
  descent-coprod-inl f g i (pair h (pair f' H)) (pair k (pair g' K))
    is-pb-dsq =
      is-pullback-is-fiberwise-equiv-fib-square f i (pair h (pair f' H))
        ( λ a → is-equiv-comp
          ( fib-square f i (pair h (pair f' H)) a)
          ( fib-square (ind-coprod _ f g) i
            ( cone-descent-coprod f g i
              ( pair h (pair f' H)) (pair k (pair g' K))) (inl a))
          ( fib-functor-coprod-inl-fib h k a)
          ( triangle-descent-square-fib-functor-coprod-inl-fib
            h k i f g f' g' H K a)
          ( is-equiv-fib-functor-coprod-inl-fib h k a)
          ( is-fiberwise-equiv-fib-square-is-pullback (ind-coprod _ f g) i
            ( cone-descent-coprod f g i
              ( pair h (pair f' H)) (pair k (pair g' K))) is-pb-dsq (inl a)))

abstract
  descent-coprod-inr : {l1 l2 l3 l1' l2' l3' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
    (f : A → X) (g : B → X) (i : X' → X)
    (cone-A' : cone f i A') (cone-B' : cone g i B') →
    is-pullback
      ( ind-coprod _ f g)
      ( i)
      ( cone-descent-coprod f g i cone-A' cone-B') →
    is-pullback g i cone-B'
  descent-coprod-inr f g i (pair h (pair f' H)) (pair k (pair g' K))
    is-pb-dsq =
      is-pullback-is-fiberwise-equiv-fib-square g i (pair k (pair g' K))
        ( λ b → is-equiv-comp
          ( fib-square g i (pair k (pair g' K)) b)
          ( fib-square (ind-coprod _ f g) i
            ( cone-descent-coprod f g i
              ( pair h (pair f' H)) (pair k (pair g' K))) (inr b))
          ( fib-functor-coprod-inr-fib h k b)
          ( triangle-descent-square-fib-functor-coprod-inr-fib
            h k i f g f' g' H K b)
          ( is-equiv-fib-functor-coprod-inr-fib h k b)
          ( is-fiberwise-equiv-fib-square-is-pullback (ind-coprod _ f g) i
            ( cone-descent-coprod f g i
              ( pair h (pair f' H)) (pair k (pair g' K))) is-pb-dsq (inr b)))

-- Descent for Σ-types

cone-descent-Σ : {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : I → UU l2} {A' : I → UU l3} {X : UU l4} {X' : UU l5}
  (f : (i : I) → A i → X) (h : X' → X)
  (c : (i : I) → cone (f i) h (A' i)) →
  cone (ind-Σ f) h (Σ I A')
cone-descent-Σ f h c =
  pair
    ( tot (λ i → (pr1 (c i))))
    ( pair
      ( ind-Σ (λ i → (pr1 (pr2 (c i)))))
      ( ind-Σ (λ i → (pr2 (pr2 (c i))))))

triangle-descent-Σ : {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : I → UU l2} {A' : I → UU l3} {X : UU l4} {X' : UU l5}
  (f : (i : I) → A i → X) (h : X' → X)
  (c : (i : I) → cone (f i) h (A' i)) →
  (i : I) (a : A i) →
  ( fib-square (f i) h (c i) a) ~
  ((fib-square (ind-Σ f) h (cone-descent-Σ f h c) (pair i a)) ∘ (fib-tot-fib-ftr (λ i → (pr1 (c i))) (pair i a)))
triangle-descent-Σ f h c i .(pr1 (c i) a') (pair a' refl) = refl

abstract
  descent-Σ : {l1 l2 l3 l4 l5 : Level}
    {I : UU l1} {A : I → UU l2} {A' : I → UU l3} {X : UU l4} {X' : UU l5}
    (f : (i : I) → A i → X) (h : X' → X)
    (c : (i : I) → cone (f i) h (A' i)) →
    ((i : I) → is-pullback (f i) h (c i)) →
    is-pullback (ind-Σ f) h (cone-descent-Σ f h c)
  descent-Σ f h c is-pb-c =
    is-pullback-is-fiberwise-equiv-fib-square
      ( ind-Σ f)
      ( h)
      ( cone-descent-Σ f h c)
      ( ind-Σ
        ( λ i a → is-equiv-left-factor
          ( fib-square (f i) h (c i) a)
          ( fib-square (ind-Σ f) h (cone-descent-Σ f h c) (pair i a))
          ( fib-tot-fib-ftr (λ i → pr1 (c i)) (pair i a))
          ( triangle-descent-Σ f h c i a)
          ( is-fiberwise-equiv-fib-square-is-pullback
            (f i) h (c i) (is-pb-c i) a)
          ( is-equiv-fib-tot-fib-ftr (λ i → pr1 (c i)) (pair i a))))

abstract
  descent-Σ' : {l1 l2 l3 l4 l5 : Level}
    {I : UU l1} {A : I → UU l2} {A' : I → UU l3} {X : UU l4} {X' : UU l5}
    (f : (i : I) → A i → X) (h : X' → X)
    (c : (i : I) → cone (f i) h (A' i)) →
    is-pullback (ind-Σ f) h (cone-descent-Σ f h c) →
    ((i : I) → is-pullback (f i) h (c i))
  descent-Σ' f h c is-pb-dsq i =
    is-pullback-is-fiberwise-equiv-fib-square (f i) h (c i)
      ( λ a → is-equiv-comp
        ( fib-square (f i) h (c i) a)
        ( fib-square (ind-Σ f) h (cone-descent-Σ f h c) (pair i a))
        ( fib-tot-fib-ftr (λ i → pr1 (c i)) (pair i a))
        ( triangle-descent-Σ f h c i a)
        ( is-equiv-fib-tot-fib-ftr (λ i → pr1 (c i)) (pair i a))
        ( is-fiberwise-equiv-fib-square-is-pullback (ind-Σ f) h
          ( cone-descent-Σ f h c) is-pb-dsq (pair i a)))

-- Extra material

-- Homotopical squares

{- We consider the situation where we have two 'parallel squares', i.e. a
   diagram of the form

      --------->
    C ---------> B
   | |          | |
   | |          | |
   V V          V V
    A ---------> X.
      --------->

   Suppose that between each parallel pair of maps there is a homotopy, and
   that there is a homotopy between the homotopies that fill the two squares,
   as expessed by the type coherence-htpy-square below. Our goal is to show
   that if one of the squares is a pullback square, then so is the other.

   We do so without using function extensionality. -}

coherence-htpy-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) (c' : cone f' g' C)
  (Hp : pr1 c ~ pr1 c') (Hq : pr1 (pr2 c) ~ pr1 (pr2 c')) → UU _
coherence-htpy-square {f = f} {f'} Hf {g} {g'} Hg c c' Hp Hq =
  let p  = pr1 c
      q  = pr1 (pr2 c)
      H  = pr2 (pr2 c)
      p' = pr1 c'
      q' = pr1 (pr2 c')
      H' = pr2 (pr2 c')
  in
  ( H ∙h ((g ·l Hq) ∙h (Hg ·r q'))) ~ (((f ·l Hp) ∙h (Hf ·r p')) ∙h H')

fam-htpy-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) → (c' : cone f' g' C) →
  (pr1 c ~ pr1 c') → UU _
fam-htpy-square {f = f} {f'} Hf {g} {g'} Hg c c' Hp =
  Σ ((pr1 (pr2 c)) ~ (pr1 (pr2 c'))) (coherence-htpy-square Hf Hg c c' Hp)
  
htpy-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  cone f g C → cone f' g' C → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
htpy-square
  {f = f} {f'} Hf {g} {g'} Hg c c' =
  Σ ((pr1 c) ~ (pr1 c')) (fam-htpy-square Hf Hg c c')

map-is-pullback-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {f' : A → X} (Hf : f ~ f')
  {g : B → X} {g' : B → X} (Hg : g ~ g') →
  canonical-pullback f' g' → canonical-pullback f g
map-is-pullback-htpy {f = f} {f'} Hf {g} {g'} Hg =
  tot (λ a → tot (λ b →
    ( concat' (f a) (inv (Hg b))) ∘ (concat (Hf a) (g' b))))

abstract
  is-equiv-map-is-pullback-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    {f : A → X} {f' : A → X} (Hf : f ~ f')
    {g : B → X} {g' : B → X} (Hg : g ~ g') →
    is-equiv (map-is-pullback-htpy Hf Hg)
  is-equiv-map-is-pullback-htpy {f = f} {f'} Hf {g} {g'} Hg =
    is-equiv-tot-is-fiberwise-equiv (λ a →
      is-equiv-tot-is-fiberwise-equiv (λ b →
        is-equiv-comp
          ( (concat' (f a) (inv (Hg b))) ∘ (concat (Hf a) (g' b)))
          ( concat' (f a) (inv (Hg b)))
          ( concat (Hf a) (g' b))
          ( htpy-refl)
          ( is-equiv-concat (Hf a) (g' b))
          ( is-equiv-concat' (f a) (inv (Hg b)))))

tot-pullback-rel : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (x : A) → UU _
tot-pullback-rel {B = B} f g x = Σ B (λ y → Id (f x) (g y))

triangle-is-pullback-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f : A → X} {f' : A → X} (Hf : f ~ f')
  {g : B → X} {g' : B → X} (Hg : g ~ g')
  {c : cone f g C} {c' : cone f' g' C} (Hc : htpy-square Hf Hg c c') →
  (gap f g c) ~ ((map-is-pullback-htpy Hf Hg) ∘ (gap f' g' c'))
triangle-is-pullback-htpy {A = A} {B} {X} {C} {f = f} {f'} Hf {g} {g'} Hg
  {pair p (pair q H)} {pair p' (pair q' H')} (pair Hp (pair Hq HH)) z =
  eq-Eq-canonical-pullback f g
    ( Hp z)
    ( Hq z)
    ( ( inv
        ( assoc (ap f (Hp z)) ((Hf (p' z)) ∙ (H' z)) (inv (Hg (q' z))))) ∙
      ( inv
        ( con-inv
          ( (H z) ∙ (ap g (Hq z)))
          ( Hg (q' z))
          ( ( ap f (Hp z)) ∙ ((Hf (p' z)) ∙ (H' z)))
          ( ( assoc (H z) (ap g (Hq z)) (Hg (q' z))) ∙
            ( ( HH z) ∙
              ( assoc (ap f (Hp z)) (Hf (p' z)) (H' z)))))))

abstract
  is-pullback-htpy :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f : A → X} (f' : A → X) (Hf : f ~ f')
    {g : B → X} (g' : B → X) (Hg : g ~ g')
    {c : cone f g C} (c' : cone f' g' C) (Hc : htpy-square Hf Hg c c') →
    is-pullback f' g' c' → is-pullback f g c
  is-pullback-htpy
    {f = f} f' Hf {g} g' Hg
    {c = pair p (pair q H)} (pair p' (pair q' H'))
    (pair Hp (pair Hq HH)) is-pb-c' =
    is-equiv-comp
      ( gap f g (pair p (pair q H)))
      ( map-is-pullback-htpy Hf Hg)
      ( gap f' g' (pair p' (pair q' H')))
      ( triangle-is-pullback-htpy Hf Hg
        {pair p (pair q H)} {pair p' (pair q' H')} (pair Hp (pair Hq HH)))
      ( is-pb-c')
      ( is-equiv-map-is-pullback-htpy Hf Hg)

abstract
  is-pullback-htpy' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) {f' : A → X} (Hf : f ~ f')
    (g : B → X) {g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) {c' : cone f' g' C} (Hc : htpy-square Hf Hg c c') →
    is-pullback f g c → is-pullback f' g' c'
  is-pullback-htpy'
    f {f'} Hf g {g'} Hg
    (pair p (pair q H)) {pair p' (pair q' H')}
    (pair Hp (pair Hq HH)) is-pb-c =
    is-equiv-right-factor
      ( gap f g (pair p (pair q H)))
      ( map-is-pullback-htpy Hf Hg)
      ( gap f' g' (pair p' (pair q' H')))
      ( triangle-is-pullback-htpy Hf Hg
        {pair p (pair q H)} {pair p' (pair q' H')} (pair Hp (pair Hq HH)))
      ( is-equiv-map-is-pullback-htpy Hf Hg)
      ( is-pb-c)

{- In the following part we will relate the type htpy-square to the Identity
   type of cones. Here we will rely on function extensionality. -}

reflexive-htpy-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  htpy-square (htpy-refl {f = f}) (htpy-refl {f = g}) c c
reflexive-htpy-square f g c =
  pair htpy-refl (pair htpy-refl htpy-right-unit)

htpy-square-eq-htpy-refl :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  Id c c' → htpy-square (htpy-refl {f = f}) (htpy-refl {f = g}) c c'
htpy-square-eq-htpy-refl f g c .c refl =
  pair htpy-refl (pair htpy-refl htpy-right-unit)

htpy-square-htpy-refl-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) →
  (c c' : cone f g C) →
  htpy-cone f g c c' → htpy-square (htpy-refl {f = f}) (htpy-refl {f = g}) c c'
htpy-square-htpy-refl-htpy-cone f g
  (pair p (pair q H)) (pair p' (pair q' H')) =
  tot
    ( λ K → tot
      ( λ L M → ( htpy-ap-concat H _ _ htpy-right-unit) ∙h
        ( M ∙h htpy-ap-concat' _ _ H' (htpy-inv htpy-right-unit))))

abstract
  is-equiv-htpy-square-htpy-refl-htpy-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) →
    (c c' : cone f g C) →
    is-equiv (htpy-square-htpy-refl-htpy-cone f g c c')
  is-equiv-htpy-square-htpy-refl-htpy-cone f g
    (pair p (pair q H)) (pair p' (pair q' H')) =
    is-equiv-tot-is-fiberwise-equiv
      ( λ K → is-equiv-tot-is-fiberwise-equiv
        ( λ L → is-equiv-comp
          ( λ M → ( htpy-ap-concat H _ _ htpy-right-unit) ∙h
            ( M ∙h
              ( htpy-ap-concat' _ _ H' (htpy-inv htpy-right-unit))))
          ( htpy-concat
            ( htpy-ap-concat H _ _ htpy-right-unit)
            ( ((f ·l K) ∙h htpy-refl) ∙h H'))
          ( htpy-concat'
            ( H ∙h (g ·l L))
            ( htpy-ap-concat' _ _ H' (htpy-inv htpy-right-unit)))
          ( htpy-refl)
          ( is-equiv-htpy-concat'
            ( H ∙h (g ·l L))
            ( λ x → ap (λ z → z ∙ H' x) (inv right-unit)))
          ( is-equiv-htpy-concat
            ( λ x → ap (_∙_ (H x)) right-unit)
            ( ((f ·l K) ∙h htpy-refl) ∙h H'))))

abstract
  is-contr-total-htpy-square-htpy-refl-htpy-refl :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) →
    (c : cone f g C) →
    is-contr (Σ (cone f g C) (htpy-square (htpy-refl' f) (htpy-refl' g) c))
  is-contr-total-htpy-square-htpy-refl-htpy-refl {A = A} {B} {X} {C}
    f g (pair p (pair q H)) =
    let c = pair p (pair q H) in
    is-contr-is-equiv'
      ( Σ (cone f g C) (htpy-cone f g c))
      ( tot (htpy-square-htpy-refl-htpy-cone f g c))
      ( is-equiv-tot-is-fiberwise-equiv
        ( is-equiv-htpy-square-htpy-refl-htpy-cone f g c))
      ( is-contr-total-htpy-cone f g c)

abstract
  is-contr-total-htpy-square-htpy-refl :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) →
    is-contr (Σ (cone f g' C) (htpy-square (htpy-refl' f) Hg c))
  is-contr-total-htpy-square-htpy-refl {C = C} f {g} =
    ind-htpy g
      ( λ g'' Hg' → ( c : cone f g C) →
        is-contr (Σ (cone f g'' C) (htpy-square (htpy-refl' f) Hg' c)))
      ( is-contr-total-htpy-square-htpy-refl-htpy-refl f g)

abstract
  is-contr-total-htpy-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) →
    is-contr (Σ (cone f' g' C) (htpy-square Hf Hg c))
  is-contr-total-htpy-square {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg =
    ind-htpy
      { A = A}
      { B = λ t → X}
      ( f)
      ( λ f'' Hf' → (g g' : B → X) (Hg : g ~ g') (c : cone f g C) →
        is-contr (Σ (cone f'' g' C) (htpy-square Hf' Hg c)))
      ( λ g g' Hg → is-contr-total-htpy-square-htpy-refl f Hg)
      Hf g g' Hg

tr-tr-htpy-refl-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy (htpy-refl {f = f})) c
      tr-tr-c = tr (λ y → cone f y C) (eq-htpy (htpy-refl {f = g})) tr-c
  in
  Id tr-tr-c c
tr-tr-htpy-refl-cone {C = C} f g c =
  let tr-c = tr (λ f''' → cone f''' g C) (eq-htpy htpy-refl) c
      tr-tr-c = tr (λ g'' → cone f g'' C) (eq-htpy htpy-refl) tr-c
      α : Id tr-tr-c tr-c
      α = ap (λ t → tr (λ g'' → cone f g'' C) t tr-c) (eq-htpy-htpy-refl g)
      β : Id tr-c c
      β = ap (λ t → tr (λ f''' → cone f''' g C) t c) (eq-htpy-htpy-refl f)
  in
  α ∙ β

htpy-square-eq-htpy-refl-htpy-refl :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy (htpy-refl {f = f})) c
      tr-tr-c = tr (λ y → cone f y C) (eq-htpy (htpy-refl {f = g})) tr-c
  in
  Id tr-tr-c c' → htpy-square (htpy-refl' f) (htpy-refl' g) c c'
htpy-square-eq-htpy-refl-htpy-refl f g c c' =
  ind-is-equiv
    ( λ p → htpy-square (htpy-refl' f) (htpy-refl' g) c c')
    ( λ (p : Id c c') → (tr-tr-htpy-refl-cone f g c) ∙ p)
    ( is-equiv-concat (tr-tr-htpy-refl-cone f g c) c')
    ( htpy-square-eq-htpy-refl f g c c')

comp-htpy-square-eq-htpy-refl-htpy-refl :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  ( (htpy-square-eq-htpy-refl-htpy-refl f g c c') ∘
    (concat (tr-tr-htpy-refl-cone f g c) c')) ~
  ( htpy-square-eq-htpy-refl f g c c')
comp-htpy-square-eq-htpy-refl-htpy-refl f g c c' =
  htpy-comp-is-equiv
    ( λ p → htpy-square (htpy-refl' f) (htpy-refl' g) c c')
    ( λ (p : Id c c') → (tr-tr-htpy-refl-cone f g c) ∙ p)
    ( is-equiv-concat (tr-tr-htpy-refl-cone f g c) c')
    ( htpy-square-eq-htpy-refl f g c c')

abstract
  htpy-square-eq' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f g' C) →
    let tr-c    = tr (λ x → cone x g C) (eq-htpy (htpy-refl {f = f})) c
        tr-tr-c = tr (λ y → cone f y C) (eq-htpy Hg) tr-c
    in
    Id tr-tr-c c' → htpy-square (htpy-refl' f) Hg c c'
  htpy-square-eq' {C = C} f {g} =
    ind-htpy g
      ( λ g'' Hg' →
        ( c : cone f g C) (c' : cone f g'' C) →
        Id (tr (λ g'' → cone f g'' C) (eq-htpy Hg')
          ( tr (λ f''' → cone f''' g C) (eq-htpy (htpy-refl' f)) c)) c' →
        htpy-square htpy-refl Hg' c c')
      ( htpy-square-eq-htpy-refl-htpy-refl f g)

  comp-htpy-square-eq' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c c' : cone f g C) →
    ( ( htpy-square-eq' f htpy-refl c c') ∘
      ( concat (tr-tr-htpy-refl-cone f g c) c')) ~
    ( htpy-square-eq-htpy-refl f g c c')
  comp-htpy-square-eq' {A = A} {B} {X} {C} f g c c' =
    htpy-right-whisk
      ( htpy-eq (htpy-eq (htpy-eq (comp-htpy g
        ( λ g'' Hg' →
          ( c : cone f g C) (c' : cone f g'' C) →
            Id (tr (λ g'' → cone f g'' C) (eq-htpy Hg')
              ( tr (λ f''' → cone f''' g C) (eq-htpy (htpy-refl' f)) c)) c' →
          htpy-square htpy-refl Hg' c c')
      ( htpy-square-eq-htpy-refl-htpy-refl f g)) c) c'))
      ( concat (tr-tr-htpy-refl-cone f g c) c') ∙h
    ( comp-htpy-square-eq-htpy-refl-htpy-refl f g c c')

abstract
  htpy-square-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f' g' C) →
    let tr-c    = tr (λ x → cone x g C) (eq-htpy Hf) c
        tr-tr-c = tr (λ y → cone f' y C) (eq-htpy Hg) tr-c
    in
    Id tr-tr-c c' → htpy-square Hf Hg c c'
  htpy-square-eq {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg c c' p =
    ind-htpy f
    ( λ f'' Hf' →
      ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f'' g' C) →
      ( Id (tr (λ g'' → cone f'' g'' C) (eq-htpy Hg)
        ( tr (λ f''' → cone f''' g C) (eq-htpy Hf') c)) c') →
      htpy-square Hf' Hg c c')
    ( λ g g' → htpy-square-eq' f {g = g} {g' = g'})
    Hf g g' Hg c c' p
  
  comp-htpy-square-eq : 
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c c' : cone f g C) →
    ( ( htpy-square-eq htpy-refl htpy-refl c c') ∘
      ( concat (tr-tr-htpy-refl-cone f g c) c')) ~
    ( htpy-square-eq-htpy-refl f g c c')
  comp-htpy-square-eq {A = A} {B} {X} {C} f g c c' =
    htpy-right-whisk
      ( htpy-eq (htpy-eq (htpy-eq (htpy-eq (htpy-eq (htpy-eq (comp-htpy f
        ( λ f'' Hf' →
          ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f'' g' C) →
            ( Id ( tr (λ g'' → cone f'' g'' C) (eq-htpy Hg)
                 ( tr (λ f''' → cone f''' g C) (eq-htpy Hf') c)) c') →
            htpy-square Hf' Hg c c')
        ( λ g g' → htpy-square-eq' f {g = g} {g' = g'})) g) g)
        htpy-refl) c) c'))
      ( concat (tr-tr-htpy-refl-cone f g c) c') ∙h
      ( comp-htpy-square-eq' f g c c')

abstract
  is-fiberwise-equiv-htpy-square-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f' g' C) →
    is-equiv (htpy-square-eq Hf Hg c c')
  is-fiberwise-equiv-htpy-square-eq
    {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg c c' =
    ind-htpy f
      ( λ f' Hf →
        ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f' g' C) →
          is-equiv (htpy-square-eq Hf Hg c c'))
      ( λ g g' Hg c c' →
        ind-htpy g
          ( λ g' Hg →
            ( c : cone f g C) (c' : cone f g' C) →
              is-equiv (htpy-square-eq htpy-refl Hg c c'))
          ( λ c c' →
            is-equiv-left-factor
              ( htpy-square-eq-htpy-refl f g c c')
              ( htpy-square-eq htpy-refl htpy-refl c c')
              ( concat (tr-tr-htpy-refl-cone f g c) c')
              ( htpy-inv (comp-htpy-square-eq f g c c'))
              ( fundamental-theorem-id c
                ( reflexive-htpy-square f g c)
                ( is-contr-total-htpy-square (htpy-refl' f) (htpy-refl' g) c)
                ( htpy-square-eq-htpy-refl f g c) c')
              ( is-equiv-concat (tr-tr-htpy-refl-cone f g c) c'))
          Hg c c')
      Hf g g' Hg c c'

eq-htpy-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) (c' : cone f' g' C) →
  let tr-c    = tr (λ x → cone x g C) (eq-htpy Hf) c
      tr-tr-c = tr (λ y → cone f' y C) (eq-htpy Hg) tr-c
  in
  htpy-square Hf Hg c c' → Id tr-tr-c c'
eq-htpy-square Hf Hg c c' =
  inv-is-equiv
    { f = htpy-square-eq Hf Hg c c'}
    ( is-fiberwise-equiv-htpy-square-eq Hf Hg c c')

-- Exercises

-- Exercise 10.1

cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  cone (const unit A x) (const unit A y) (Id x y)
cone-Id x y =
  pair
    ( const (Id x y) unit star)
    ( pair
      ( const (Id x y) unit star)
      ( id))

inv-gap-cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  canonical-pullback (const unit A x) (const unit A y) → Id x y
inv-gap-cone-Id x y (pair star (pair star p)) = p

issec-inv-gap-cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  ( ( gap (const unit A x) (const unit A y) (cone-Id x y)) ∘
    ( inv-gap-cone-Id x y)) ~ id
issec-inv-gap-cone-Id x y (pair star (pair star p)) = refl

isretr-inv-gap-cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  ( ( inv-gap-cone-Id x y) ∘
    ( gap (const unit A x) (const unit A y) (cone-Id x y))) ~ id
isretr-inv-gap-cone-Id x y p = refl

abstract
  is-pullback-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    is-pullback (const unit A x) (const unit A y) (cone-Id x y)
  is-pullback-cone-Id x y =
    is-equiv-has-inverse
      ( inv-gap-cone-Id x y)
      ( issec-inv-gap-cone-Id x y)
      ( isretr-inv-gap-cone-Id x y)

{- One way to solve this exercise is to show that Id (pr1 t) (pr2 t) is a
   pullback for every t : A × A. This allows one to use path induction to
   show that the inverse of the gap map is a section.
-}

cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  cone (const unit (A × A) t) (diagonal A) (Id (pr1 t) (pr2 t))
cone-Id' {A = A} (pair x y) =
  pair
    ( const (Id x y) unit star)
    ( pair
      ( const (Id x y) A x)
      ( λ p → eq-pair refl (inv p)))

inv-gap-cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  canonical-pullback (const unit (A × A) t) (diagonal A) → Id (pr1 t) (pr2 t)
inv-gap-cone-Id' t (pair star (pair z p)) =
  (ap pr1 p) ∙ (inv (ap pr2 p))

issec-inv-gap-cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  ( ( gap (const unit (A × A) t) (diagonal A) (cone-Id' t)) ∘
    ( inv-gap-cone-Id' t)) ~ id
issec-inv-gap-cone-Id' .(pair z z) (pair star (pair z refl)) = refl

isretr-inv-gap-cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  ( ( inv-gap-cone-Id' t) ∘
    ( gap (const unit (A × A) t) (diagonal A) (cone-Id' t))) ~ id
isretr-inv-gap-cone-Id' (pair x .x) refl = refl

abstract
  is-pullback-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    is-pullback (const unit (A × A) t) (diagonal A) (cone-Id' t)
  is-pullback-cone-Id' t =
    is-equiv-has-inverse
      ( inv-gap-cone-Id' t)
      ( issec-inv-gap-cone-Id' t)
      ( isretr-inv-gap-cone-Id' t)

-- Exercise 10.2

diagonal-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  A → canonical-pullback f f
diagonal-map f x = pair x (pair x refl)

fib-ap-fib-diagonal-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (t : canonical-pullback f f) →
  (fib (diagonal-map f) t) → (fib (ap f) (pr2 (pr2 t)))
fib-ap-fib-diagonal-map f .(pair z (pair z refl)) (pair z refl) =
  pair refl refl

fib-diagonal-map-fib-ap :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (t : canonical-pullback f f) →
  (fib (ap f) (pr2 (pr2 t))) → (fib (diagonal-map f) t)
fib-diagonal-map-fib-ap f (pair x (pair .x .refl)) (pair refl refl) =
  pair x refl

issec-fib-diagonal-map-fib-ap :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (t : canonical-pullback f f) →
  ((fib-ap-fib-diagonal-map f t) ∘ (fib-diagonal-map-fib-ap f t)) ~ id
issec-fib-diagonal-map-fib-ap f (pair x (pair .x .refl)) (pair refl refl) =
  refl

isretr-fib-diagonal-map-fib-ap :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (t : canonical-pullback f f) →
  ((fib-diagonal-map-fib-ap f t) ∘ (fib-ap-fib-diagonal-map f t)) ~ id
isretr-fib-diagonal-map-fib-ap f .(pair x (pair x refl)) (pair x refl) =
  refl

abstract
  is-equiv-fib-ap-fib-diagonal-map :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : canonical-pullback f f) →
    is-equiv (fib-ap-fib-diagonal-map f t)
  is-equiv-fib-ap-fib-diagonal-map f t =
    is-equiv-has-inverse
      ( fib-diagonal-map-fib-ap f t)
      ( issec-fib-diagonal-map-fib-ap f t)
      ( isretr-fib-diagonal-map-fib-ap f t)

abstract
  is-trunc-diagonal-map-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-trunc-map (succ-𝕋 k) f → is-trunc-map k (diagonal-map f)
  is-trunc-diagonal-map-is-trunc-map k f is-trunc-f (pair x (pair y p)) =
    is-trunc-is-equiv k (fib (ap f) p)
      ( fib-ap-fib-diagonal-map f (pair x (pair y p)))
      ( is-equiv-fib-ap-fib-diagonal-map f (pair x (pair y p)))
      ( is-trunc-ap-is-trunc-map k f is-trunc-f x y p)

abstract
  is-trunc-map-is-trunc-diagonal-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-trunc-map k (diagonal-map f) → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-is-trunc-diagonal-map
    k f is-trunc-δ b (pair x p) (pair x' p') =
    is-trunc-is-equiv k
      ( fib (ap f) (p ∙ (inv p')))
      ( fib-ap-eq-fib f (pair x p) (pair x' p'))
      ( is-equiv-fib-ap-eq-fib f (pair x p) (pair x' p'))
      ( is-trunc-is-equiv' k
        ( fib (diagonal-map f) (pair x (pair x' (p ∙ (inv p')))))
        ( fib-ap-fib-diagonal-map f (pair x (pair x' (p ∙ (inv p')))))
        ( is-equiv-fib-ap-fib-diagonal-map f (pair x (pair x' (p ∙ (inv p')))))
        ( is-trunc-δ (pair x (pair x' (p ∙ (inv p'))))))

abstract
  is-equiv-diagonal-map-is-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-emb f → is-equiv (diagonal-map f)
  is-equiv-diagonal-map-is-emb f is-emb-f =
    is-equiv-is-contr-map
      ( is-trunc-diagonal-map-is-trunc-map neg-two-𝕋 f
        ( is-prop-map-is-emb f is-emb-f))

abstract
  is-emb-is-equiv-diagonal-map :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (diagonal-map f) → is-emb f
  is-emb-is-equiv-diagonal-map f is-equiv-δ =
    is-emb-is-prop-map f
      ( is-trunc-map-is-trunc-diagonal-map neg-two-𝕋 f
        ( is-contr-map-is-equiv is-equiv-δ))

-- Exercise 10.3

cone-swap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) → cone f g C → cone g f C
cone-swap f g (pair p (pair q H)) = pair q (pair p (htpy-inv H))

map-canonical-pullback-swap :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → canonical-pullback f g → canonical-pullback g f
map-canonical-pullback-swap f g (pair a (pair b p)) =
  pair b (pair a (inv p))

inv-inv-map-canonical-pullback-swap :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  (map-canonical-pullback-swap f g ∘ map-canonical-pullback-swap g f) ~ id
inv-inv-map-canonical-pullback-swap f g (pair b (pair a q)) =
  eq-pair refl (eq-pair refl (inv-inv q))

abstract
  is-equiv-map-canonical-pullback-swap :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-canonical-pullback-swap f g)
  is-equiv-map-canonical-pullback-swap f g =
    is-equiv-has-inverse
      ( map-canonical-pullback-swap g f)
      ( inv-inv-map-canonical-pullback-swap f g)
      ( inv-inv-map-canonical-pullback-swap g f)

triangle-map-canonical-pullback-swap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  ( gap g f (cone-swap f g c)) ~
  ( ( map-canonical-pullback-swap f g) ∘ ( gap f g c))
triangle-map-canonical-pullback-swap f g (pair p (pair q H)) x = refl

abstract
  is-pullback-cone-swap :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-pullback g f (cone-swap f g c)
  is-pullback-cone-swap f g c is-pb-c =
    is-equiv-comp
      ( gap g f (cone-swap f g c))
      ( map-canonical-pullback-swap f g)
      ( gap f g c)
      ( triangle-map-canonical-pullback-swap f g c)
      ( is-pb-c)
      ( is-equiv-map-canonical-pullback-swap f g)

abstract
  is-pullback-cone-swap' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback g f (cone-swap f g c) → is-pullback f g c
  is-pullback-cone-swap' f g c is-pb-c' =
    is-equiv-right-factor
      ( gap g f (cone-swap f g c))
      ( map-canonical-pullback-swap f g)
      ( gap f g c)
      ( triangle-map-canonical-pullback-swap f g c)
      ( is-equiv-map-canonical-pullback-swap f g)
      ( is-pb-c')

{- We conclude the swapped versions of some properties derived above, for 
   future convenience -}

abstract
  is-trunc-is-pullback' :
    {l1 l2 l3 l4 : Level} (k : 𝕋)
    {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-trunc-map k f → is-trunc-map k (pr1 (pr2 c))
  is-trunc-is-pullback' k f g (pair p (pair q H)) pb is-trunc-f =
    is-trunc-is-pullback k g f
      ( cone-swap f g (pair p (pair q H)))
      ( is-pullback-cone-swap f g (pair p (pair q H)) pb)
      is-trunc-f

abstract
  is-emb-is-pullback' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-emb f → is-emb (pr1 (pr2 c))
  is-emb-is-pullback' f g c pb is-emb-f =
    is-emb-is-prop-map
      ( pr1 (pr2 c))
      ( is-trunc-is-pullback' neg-one-𝕋 f g c pb
        ( is-prop-map-is-emb f is-emb-f))

abstract
  is-equiv-is-pullback' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-equiv f → is-pullback f g c → is-equiv (pr1 (pr2 c))
  is-equiv-is-pullback' f g c is-equiv-f pb =
    is-equiv-is-contr-map
      ( is-trunc-is-pullback' neg-two-𝕋 f g c pb
        ( is-contr-map-is-equiv is-equiv-f))

abstract
  is-pullback-is-equiv' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-equiv f → is-equiv (pr1 (pr2 c)) → is-pullback f g c
  is-pullback-is-equiv' f g (pair p (pair q H)) is-equiv-f is-equiv-q =
    is-pullback-cone-swap' f g (pair p (pair q H))
      ( is-pullback-is-equiv g f
        ( cone-swap f g (pair p (pair q H)))
        is-equiv-f
        is-equiv-q)

-- Exercise 10.4

cone-empty :
  {l1 l2 l3 : Level} {B : UU l1} {X : UU l2} {C : UU l3} →
  (g : B → X) (p : C → empty) (q : C → B) →
  cone (ind-empty {P = λ t → X}) g C
cone-empty g p q =
  pair p
    ( pair q
      ( λ c → ind-empty {P = λ t → Id (ind-empty (p c)) (g (q c))} (p c)))

abstract
  descent-empty :
    {l1 l2 l3 : Level} {B : UU l1} {X : UU l2} {C : UU l3} →
    let f = ind-empty {P = λ t → X} in
    (g : B → X) (c : cone f g C) → is-pullback f g c
  descent-empty g c =
    is-pullback-is-fiberwise-equiv-fib-square _ g c ind-empty

abstract
  descent-empty' :
    {l1 l2 l3 : Level} {B : UU l1} {X : UU l2} {C : UU l3} →
    (g : B → X) (p : C → empty) (q : C → B) →
    is-pullback (ind-empty {P = λ t → X}) g (cone-empty g p q)
  descent-empty' g p q = descent-empty g (cone-empty g p q)

-- Exercise 10.5

{- We show that a square is a pullback square if and only if every exponent of 
  it is a pullback square. -}

cone-exponent :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} (T : UU l5)
  (f : A → X) (g : B → X) (c : cone f g C) →
  cone (λ (h : T → A) → f ∘ h) (λ (h : T → B) → g ∘ h) (T → C)
cone-exponent T f g (pair p (pair q H)) =
  pair
    ( λ h → p ∘ h)
    ( pair
      ( λ h → q ∘ h)
      ( λ h → eq-htpy (H ·r h)))

map-canonical-pullback-exponent :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  (T : UU l4) →
  canonical-pullback (λ (h : T → A) → f ∘ h) (λ (h : T → B) → g ∘ h) →
  cone f g T
map-canonical-pullback-exponent f g T =
  tot (λ p → tot (λ q → htpy-eq))

abstract
  is-equiv-map-canonical-pullback-exponent :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
    (T : UU l4) → is-equiv (map-canonical-pullback-exponent f g T)
  is-equiv-map-canonical-pullback-exponent f g T =
    is-equiv-tot-is-fiberwise-equiv
      ( λ p → is-equiv-tot-is-fiberwise-equiv
        ( λ q → funext (f ∘ p) (g ∘ q)))

triangle-map-canonical-pullback-exponent :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (T : UU l5) (f : A → X) (g : B → X) (c : cone f g C) →
  ( cone-map f g {C' = T} c) ~
  ( ( map-canonical-pullback-exponent f g T) ∘
    ( gap
      ( λ (h : T → A) → f ∘ h)
      ( λ (h : T → B) → g ∘ h)
      ( cone-exponent T f g c)))
triangle-map-canonical-pullback-exponent
  {A = A} {B} T f g (pair p (pair q H)) h =
  eq-pair refl (eq-pair refl (inv (issec-eq-htpy (H ·r h))))

abstract
  is-pullback-exponent-is-pullback :
    {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) → is-pullback f g c →
    (T : UU l5) →
    is-pullback
      ( λ (h : T → A) → f ∘ h)
      ( λ (h : T → B) → g ∘ h)
      ( cone-exponent T f g c)
  is-pullback-exponent-is-pullback f g c is-pb-c T =
    is-equiv-right-factor
      ( cone-map f g c)
      ( map-canonical-pullback-exponent f g T)
      ( gap (_∘_ f) (_∘_ g) (cone-exponent T f g c))
      ( triangle-map-canonical-pullback-exponent T f g c)
      ( is-equiv-map-canonical-pullback-exponent f g T)
      ( up-pullback-is-pullback f g c is-pb-c T)

abstract
  is-pullback-is-pullback-exponent :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    ((l5 : Level) (T : UU l5) → is-pullback
      ( λ (h : T → A) → f ∘ h)
      ( λ (h : T → B) → g ∘ h)
      ( cone-exponent T f g c)) →
    is-pullback f g c
  is-pullback-is-pullback-exponent f g c is-pb-exp =
    is-pullback-up-pullback f g c
      ( λ T → is-equiv-comp
        ( cone-map f g c)
        ( map-canonical-pullback-exponent f g T)
        ( gap (_∘_ f) (_∘_ g) (cone-exponent T f g c))
        ( triangle-map-canonical-pullback-exponent T f g c)
        ( is-pb-exp _ T)
        ( is-equiv-map-canonical-pullback-exponent f g T))

-- Exercise 10.6

{- We construct the functoriality of cartesian products. -}

functor-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (A × B) → (C × D)
functor-prod f g (pair a b) = pair (f a) (g b)

functor-prod-pr1 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (pr1 ∘ (functor-prod f g)) ~ (f ∘ pr1)
functor-prod-pr1 f g (pair a b) = refl

functor-prod-pr2 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (pr2 ∘ (functor-prod f g)) ~ (g ∘ pr2)
functor-prod-pr2 f g (pair a b) = refl

{- For our convenience we show that the functorial action of cartesian products
   preserves identity maps, compositions, homotopies, and equivalences. -}

functor-prod-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (functor-prod (id {A = A}) (id {A = B})) ~ id
functor-prod-id (pair a b) = refl

functor-prod-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : UU l5} {F : UU l6} (f : A → C) (g : B → D) (h : C → E) (k : D → F) →
  functor-prod (h ∘ f) (k ∘ g) ~ ((functor-prod h k) ∘ (functor-prod f g))
functor-prod-comp f g h k (pair a b) = refl

functor-prod-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f f' : A → C} (H : f ~ f') {g g' : B → D} (K : g ~ g') →
  functor-prod f g ~ functor-prod f' g'
functor-prod-htpy {f = f} {f'} H {g} {g'} K (pair a b) =
  eq-pair-triv (pair (H a) (K b))

abstract
  is-equiv-functor-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) →
    is-equiv f → is-equiv g → is-equiv (functor-prod f g)
  is-equiv-functor-prod f g
    ( pair (pair sf issec-sf) (pair rf isretr-rf))
    ( pair (pair sg issec-sg) (pair rg isretr-rg)) =
    pair
      ( pair
        ( functor-prod sf sg)
        ( ( htpy-inv (functor-prod-comp sf sg f g)) ∙h
          ( (functor-prod-htpy issec-sf issec-sg) ∙h functor-prod-id)))
      ( pair
        ( functor-prod rf rg)
        ( ( htpy-inv (functor-prod-comp f g rf rg)) ∙h
          ( (functor-prod-htpy isretr-rf isretr-rg) ∙h functor-prod-id)))

{- Now we return to the solution of the exercise. 
   
  Note: the solution below involves a substantial amount of path algebra. It
  would be nice to find a simpler solution.
  -}

cone-fold :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) →
  cone f g C → cone (functor-prod f g) (diagonal X) C
cone-fold f g (pair p (pair q H)) =
  pair
    ( λ z → pair (p z) (q z))
    ( pair
      ( g ∘ q)
      ( λ z → eq-pair-triv (pair (H z) refl)))

map-cone-fold :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} 
  (f : A → X) → (g : B → X) →
  canonical-pullback f g → canonical-pullback (functor-prod f g) (diagonal X)
map-cone-fold f g (pair a (pair b p)) =
  pair
    ( pair a b)
    ( pair
      ( g b)
      ( eq-pair-triv (pair p refl)))

inv-map-cone-fold :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} 
  (f : A → X) → (g : B → X) →
  canonical-pullback (functor-prod f g) (diagonal X) → canonical-pullback f g
inv-map-cone-fold f g (pair (pair a b) (pair x α)) =
  pair a (pair b ((ap pr1 α) ∙ (inv (ap pr2 α))))

ap-diagonal :
  {l : Level} {A : UU l} {x y : A} (p : Id x y) →
  Id (ap (diagonal A) p) (eq-pair-triv (pair p p))
ap-diagonal refl = refl

eq-pair-triv-concat :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x x' x'' : A} {y y' y'' : B}
  (p : Id x x') (p' : Id x' x'') (q : Id y y') (q' : Id y' y'') →
  Id ( eq-pair-triv {s = pair x y} {t = pair x'' y''} (pair (p ∙ p') (q ∙ q')))
    ( ( eq-pair-triv {s = pair x y} {t = pair x' y'} (pair p q)) ∙
      ( eq-pair-triv (pair p' q')))
eq-pair-triv-concat refl p' refl q' = refl

issec-inv-map-cone-fold :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  ((map-cone-fold f g) ∘ (inv-map-cone-fold f g)) ~ id
issec-inv-map-cone-fold {A = A} {B} {X} f g (pair (pair a b) (pair x α)) =
  eq-Eq-canonical-pullback
    ( functor-prod f g)
    ( diagonal X)
    refl
    ( ap pr2 α)
    ( ( ( ( inv (issec-pair-eq-triv' (pair (f a) (g b)) (pair x x) α)) ∙
          ( ap
            ( λ t → (eq-pair-triv ( pair t (ap pr2 α))))
            ( ( ( inv right-unit) ∙
                ( inv (ap (concat (ap pr1 α) x) (left-inv (ap pr2 α))))) ∙
              ( inv (assoc (ap pr1 α) (inv (ap pr2 α)) (ap pr2 α)))))) ∙
        ( eq-pair-triv-concat
          ( (ap pr1 α) ∙ (inv (ap pr2 α)))
          ( ap pr2 α)
          ( refl)
          ( ap pr2 α))) ∙
      ( ap
        ( concat
          ( eq-pair-triv
            ( pair ((ap pr1 α) ∙ (inv (ap pr2 α))) refl))
          ( pair x x))
        ( inv (ap-diagonal (ap pr2 α)))))

ap-pr1-eq-pair-triv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') →
  Id (ap pr1 (eq-pair-triv' (pair x y) (pair x' y') (pair p q))) p
ap-pr1-eq-pair-triv refl refl = refl

ap-pr2-eq-pair-triv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') →
  Id (ap pr2 (eq-pair-triv' (pair x y) (pair x' y') (pair p q))) q
ap-pr2-eq-pair-triv refl refl = refl

isretr-inv-map-cone-fold :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  ((inv-map-cone-fold f g) ∘ (map-cone-fold f g)) ~ id
isretr-inv-map-cone-fold { A = A} { B = B} { X = X} f g (pair a (pair b p)) =
  eq-Eq-canonical-pullback {A = A} {B = B} {X = X} f g
    refl
    refl
    ( inv
      ( ( ap
          ( concat' (f a) refl)
          ( ( ( ap
                ( λ t → t ∙
                  ( inv (ap pr2 (eq-pair-triv'
                    ( pair (f a) (g b))
                    ( pair (g b) (g b))
                    ( pair p refl)))))
                  ( ap-pr1-eq-pair-triv p refl)) ∙
              ( ap (λ t → p ∙ (inv t)) (ap-pr2-eq-pair-triv p refl))) ∙
            ( right-unit))) ∙
        ( right-unit)))

abstract
  is-equiv-map-cone-fold :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-cone-fold f g)
  is-equiv-map-cone-fold f g =
    is-equiv-has-inverse
      ( inv-map-cone-fold f g)
      ( issec-inv-map-cone-fold f g)
      ( isretr-inv-map-cone-fold f g)

triangle-map-cone-fold :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  ( gap (functor-prod f g) (diagonal X) (cone-fold f g c)) ~
  ( (map-cone-fold f g) ∘ (gap f g c))
triangle-map-cone-fold f g (pair p (pair q H)) z = refl

abstract
  is-pullback-cone-fold-is-pullback :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c →
    is-pullback (functor-prod f g) (diagonal X) (cone-fold f g c)
  is-pullback-cone-fold-is-pullback f g c is-pb-c =
    is-equiv-comp
      ( gap (functor-prod f g) (diagonal _) (cone-fold f g c))
      ( map-cone-fold f g)
      ( gap f g c)
      ( triangle-map-cone-fold f g c)
      ( is-pb-c)
      ( is-equiv-map-cone-fold f g)

abstract
  is-pullback-is-pullback-cone-fold :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback (functor-prod f g) (diagonal X) (cone-fold f g c) →
    is-pullback f g c
  is-pullback-is-pullback-cone-fold f g c is-pb-fold =
    is-equiv-right-factor
      ( gap (functor-prod f g) (diagonal _) (cone-fold f g c))
      ( map-cone-fold f g)
      ( gap f g c)
      ( triangle-map-cone-fold f g c)
      ( is-equiv-map-cone-fold f g)
      ( is-pb-fold)

-- Exercise 10.7

cone-pair :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  cone f g C → cone f' g' C' →
  cone (functor-prod f f') (functor-prod g g') (C × C')
cone-pair f g f' g' (pair p (pair q H)) (pair p' (pair q' H')) =
  pair
    ( functor-prod p p')
    ( pair
      ( functor-prod q q')
      ( ( htpy-inv (functor-prod-comp p p' f f')) ∙h
        ( ( functor-prod-htpy H H') ∙h
          ( functor-prod-comp q q' g g'))))

map-cone-pair' :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  (t : A × A') (s : B × B') →
  (Id (f (pr1 t)) (g (pr1 s))) × (Id (f' (pr2 t)) (g' (pr2 s))) →
  (Id (pr1 (functor-prod f f' t)) (pr1 (functor-prod g g' s))) ×
  (Id (pr2 (functor-prod f f' t)) (pr2 (functor-prod g g' s)))
map-cone-pair' f g f' g' (pair a a') (pair b b') = id

abstract
  is-equiv-map-cone-pair' :
    {l1 l2 l3 l1' l2' l3' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
    (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
    (t : A × A') (s : B × B') →
    is-equiv (map-cone-pair' f g f' g' t s)
  is-equiv-map-cone-pair' f g f' g' (pair a a') (pair b b') =
    is-equiv-id _

map-cone-pair :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  (canonical-pullback f g) × (canonical-pullback f' g') →
  canonical-pullback (functor-prod f f') (functor-prod g g')
map-cone-pair {A' = A'} {B'} f g f' g' =
  ( tot
    ( λ t →
      ( tot
        ( λ s →
          ( eq-pair-triv ∘ (map-cone-pair' f g f' g' t s)))) ∘
      ( swap-total-Eq-structure
        ( λ y → Id (f (pr1 t)) (g y))
        ( λ y → B')
        ( λ y p y' → Id (f' (pr2 t)) (g' y'))))) ∘
  ( swap-total-Eq-structure
    ( λ x → Σ _ (λ y → Id (f x) (g y)))
    ( λ x → A')
    ( λ x t x' → Σ _ (λ y' → Id (f' x') (g' y'))))

triangle-map-cone-pair :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (c : cone f g C)
  (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
  (gap (functor-prod f f') (functor-prod g g') (cone-pair f g f' g' c c')) ~
  ((map-cone-pair f g f' g') ∘ (functor-prod (gap f g c) (gap f' g' c')))
triangle-map-cone-pair
  f g (pair p (pair q H)) f' g' (pair p' (pair q' H')) (pair z z') =
  eq-pair refl (eq-pair refl right-unit)

abstract
  is-equiv-map-cone-pair :
    {l1 l2 l3 l1' l2' l3' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
    (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
    is-equiv (map-cone-pair f g f' g')
  is-equiv-map-cone-pair f g f' g' =
    is-equiv-comp
      ( map-cone-pair f g f' g')
      ( tot ( λ t →
        ( tot
          ( λ s →
            ( eq-pair-triv ∘ (map-cone-pair' f g f' g' t s)))) ∘
        ( swap-total-Eq-structure _ _ _)))
      ( swap-total-Eq-structure _ _ _)
      ( htpy-refl)
      ( is-equiv-swap-total-Eq-structure _ _ _)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ t → is-equiv-comp
          ( ( tot
              ( λ s →
                ( eq-pair-triv ∘ (map-cone-pair' f g f' g' t s)))) ∘
            ( swap-total-Eq-structure
              ( λ y → Id (f (pr1 t)) (g y))
              ( λ y → _)
              ( λ y p y' → Id (f' (pr2 t)) (g' y'))))
          ( tot
            ( λ s →
              ( eq-pair-triv ∘ (map-cone-pair' f g f' g' t s))))
          ( swap-total-Eq-structure
            ( λ y → Id (f (pr1 t)) (g y))
            ( λ y → _)
            ( λ y p y' → Id (f' (pr2 t)) (g' y')))
          ( htpy-refl)
          ( is-equiv-swap-total-Eq-structure _ _ _)
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ s → is-equiv-comp
              ( eq-pair-triv ∘ (map-cone-pair' f g f' g' t s))
              ( eq-pair-triv)
              ( map-cone-pair' f g f' g' t s)
              ( htpy-refl)
              ( is-equiv-map-cone-pair' f g f' g' t s)
              ( is-equiv-eq-pair-triv'
                ( functor-prod f f' t)
                ( functor-prod g g' s))))))

abstract
  is-pullback-prod-is-pullback-pair :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback f g c → is-pullback f' g' c' →
    is-pullback
      ( functor-prod f f') (functor-prod g g') (cone-pair f g f' g' c c')
  is-pullback-prod-is-pullback-pair f g c f' g' c' is-pb-c is-pb-c' =
    is-equiv-comp
      ( gap (functor-prod f f') (functor-prod g g') (cone-pair f g f' g' c c'))
      ( map-cone-pair f g f' g')
      ( functor-prod (gap f g c) (gap f' g' c'))
      ( triangle-map-cone-pair f g c f' g' c')
      ( is-equiv-functor-prod _ _ is-pb-c is-pb-c')
      ( is-equiv-map-cone-pair f g f' g')
  
map-fib-functor-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) (t : C × D) →
  fib (functor-prod f g) t → (fib f (pr1 t)) × (fib g (pr2 t))
map-fib-functor-prod f g .(functor-prod f g (pair a b))
  (pair (pair a b) refl) = pair (pair a refl) (pair b refl)

inv-map-fib-functor-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) (t : C × D) →
  (fib f (pr1 t)) × (fib g (pr2 t)) → fib (functor-prod f g) t
inv-map-fib-functor-prod f g (pair .(f x) .(g y))
  (pair (pair x refl) (pair y refl)) = pair (pair x y) refl

issec-inv-map-fib-functor-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) (t : C × D) →
  ((map-fib-functor-prod f g t) ∘ (inv-map-fib-functor-prod f g t)) ~ id
issec-inv-map-fib-functor-prod f g (pair .(f x) .(g y))
  (pair (pair x refl) (pair y refl)) = refl

isretr-inv-map-fib-functor-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) (t : C × D) →
  ((inv-map-fib-functor-prod f g t) ∘ (map-fib-functor-prod f g t)) ~ id
isretr-inv-map-fib-functor-prod f g .(functor-prod f g (pair a b))
  (pair (pair a b) refl) = refl

abstract
  is-equiv-map-fib-functor-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) (t : C × D) →
    is-equiv (map-fib-functor-prod f g t)
  is-equiv-map-fib-functor-prod f g t =
    is-equiv-has-inverse
      ( inv-map-fib-functor-prod f g t)
      ( issec-inv-map-fib-functor-prod f g t)
      ( isretr-inv-map-fib-functor-prod f g t)

abstract
  is-equiv-left-factor-is-equiv-functor-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) (d : D) →
    is-equiv (functor-prod f g) → is-equiv f
  is-equiv-left-factor-is-equiv-functor-prod f g d is-equiv-fg =
    is-equiv-is-contr-map
      ( λ x → is-contr-left-factor-prod
        ( fib f x)
        ( fib g d)
        ( is-contr-is-equiv'
          ( fib (functor-prod f g) (pair x d))
          ( map-fib-functor-prod f g (pair x d))
          ( is-equiv-map-fib-functor-prod f g (pair x d))
          ( is-contr-map-is-equiv is-equiv-fg (pair x d))))

abstract
  is-equiv-right-factor-is-equiv-functor-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) (c : C) →
    is-equiv (functor-prod f g) → is-equiv g
  is-equiv-right-factor-is-equiv-functor-prod f g c is-equiv-fg =
    is-equiv-is-contr-map
      ( λ y → is-contr-right-factor-prod
        ( fib f c)
        ( fib g y)
        ( is-contr-is-equiv'
          ( fib (functor-prod f g) (pair c y))
          ( map-fib-functor-prod f g (pair c y))
          ( is-equiv-map-fib-functor-prod f g (pair c y))
          ( is-contr-map-is-equiv is-equiv-fg (pair c y))))

abstract
  is-pullback-left-factor-is-pullback-prod :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback
      ( functor-prod f f')
      ( functor-prod g g')
      ( cone-pair f g f' g' c c') →
    canonical-pullback f' g' → is-pullback f g c
  is-pullback-left-factor-is-pullback-prod f g c f' g' c' is-pb-cc' t =
    is-equiv-left-factor-is-equiv-functor-prod (gap f g c) (gap f' g' c') t
      ( is-equiv-right-factor
        ( gap
          ( functor-prod f f')
          ( functor-prod g g')
          ( cone-pair f g f' g' c c'))
      ( map-cone-pair f g f' g')
        ( functor-prod (gap f g c) (gap f' g' c'))
        ( triangle-map-cone-pair f g c f' g' c')
        ( is-equiv-map-cone-pair f g f' g')
        ( is-pb-cc'))

abstract
  is-pullback-right-factor-is-pullback-prod :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback
      ( functor-prod f f')
      ( functor-prod g g')
      ( cone-pair f g f' g' c c') →
    canonical-pullback f g → is-pullback f' g' c'
  is-pullback-right-factor-is-pullback-prod f g c f' g' c' is-pb-cc' t =
    is-equiv-right-factor-is-equiv-functor-prod (gap f g c) (gap f' g' c') t
      ( is-equiv-right-factor
        ( gap
          ( functor-prod f f')
          ( functor-prod g g')
          ( cone-pair f g f' g' c c'))
        ( map-cone-pair f g f' g')
        ( functor-prod (gap f g c) (gap f' g' c'))
        ( triangle-map-cone-pair f g c f' g' c')
        ( is-equiv-map-cone-pair f g f' g')
        ( is-pb-cc'))

-- Exercise 10.8

cone-Π :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i)) →
  cone (postcomp-Π f) (postcomp-Π g) ((i : I) → C i)
cone-Π f g c =
  pair
    ( postcomp-Π (λ i → pr1 (c i)))
    ( pair
      ( postcomp-Π (λ i → pr1 (pr2 (c i))))
      ( htpy-postcomp-Π (λ i → pr2 (pr2 (c i)))))

map-canonical-pullback-Π :
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
  canonical-pullback (postcomp-Π f) (postcomp-Π g) →
  (i : I) → canonical-pullback (f i) (g i)
map-canonical-pullback-Π f g (pair α (pair β γ)) i =
  pair (α i) (pair (β i) (htpy-eq γ i))

inv-map-canonical-pullback-Π :
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
  ((i : I) → canonical-pullback (f i) (g i)) →
  canonical-pullback (postcomp-Π f) (postcomp-Π g)
inv-map-canonical-pullback-Π f g h =
  pair
    ( λ i → (pr1 (h i)))
    ( pair
      ( λ i → (pr1 (pr2 (h i))))
      ( eq-htpy (λ i → (pr2 (pr2 (h i))))))

issec-inv-map-canonical-pullback-Π :
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
  ((map-canonical-pullback-Π f g) ∘ (inv-map-canonical-pullback-Π f g)) ~ id
issec-inv-map-canonical-pullback-Π f g h =
  eq-htpy
    ( λ i → eq-Eq-canonical-pullback (f i) (g i) refl refl
      ( inv
        ( ( right-unit) ∙
          ( htpy-eq (issec-eq-htpy (λ i → (pr2 (pr2 (h i))))) i))))

isretr-inv-map-canonical-pullback-Π :
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
  ((inv-map-canonical-pullback-Π f g) ∘ (map-canonical-pullback-Π f g)) ~ id
isretr-inv-map-canonical-pullback-Π f g (pair α (pair β γ)) =
  eq-Eq-canonical-pullback
    ( postcomp-Π f)
    ( postcomp-Π g)
    refl
    refl
    ( inv (right-unit ∙ (isretr-eq-htpy γ)))

abstract
  is-equiv-map-canonical-pullback-Π :
    {l1 l2 l3 l4 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
    is-equiv (map-canonical-pullback-Π f g)
  is-equiv-map-canonical-pullback-Π f g =
    is-equiv-has-inverse
      ( inv-map-canonical-pullback-Π f g)
      ( issec-inv-map-canonical-pullback-Π f g)
      ( isretr-inv-map-canonical-pullback-Π f g)

triangle-map-canonical-pullback-Π :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i)) →
  ( postcomp-Π (λ i → gap (f i) (g i) (c i))) ~
  ( ( map-canonical-pullback-Π f g) ∘
    ( gap (postcomp-Π f) (postcomp-Π g) (cone-Π f g c)))
triangle-map-canonical-pullback-Π f g c h =
  eq-htpy (λ i →
    eq-Eq-canonical-pullback
      (f i)
      (g i)
      refl refl
      ( (htpy-eq (issec-eq-htpy _) i) ∙ (inv right-unit)))

abstract
  is-pullback-cone-Π :
    {l1 l2 l3 l4 l5 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
    (c : (i : I) → cone (f i) (g i) (C i)) →
    ((i : I) → is-pullback (f i) (g i) (c i)) →
    is-pullback (postcomp-Π f) (postcomp-Π g) (cone-Π f g c)
  is-pullback-cone-Π f g c is-pb-c =
    is-equiv-right-factor
      ( postcomp-Π (λ i → gap (f i) (g i) (c i)))
      ( map-canonical-pullback-Π f g)
      ( gap (postcomp-Π f) (postcomp-Π g) (cone-Π f g c))
      ( triangle-map-canonical-pullback-Π f g c)
      ( is-equiv-map-canonical-pullback-Π f g)
      ( is-equiv-postcomp-Π _ is-pb-c)

-- Exercise 10.9

hom-cospan :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X') →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l1' ⊔ (l2' ⊔ l3')))))
hom-cospan {A = A} {B} {X} f g {A'} {B'} {X'} f' g' =
  Σ (A → A') (λ hA →
    Σ (B → B') (λ hB →
      Σ (X → X') (λ hX →
        ((f' ∘ hA) ~ (hX ∘ f)) × ((g' ∘ hB) ~ (hX ∘ g)))))

id-hom-cospan :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X) →
  hom-cospan f g f g
id-hom-cospan f g =
  pair id (pair id (pair id (pair htpy-refl htpy-refl)))

functor-canonical-pullback :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X') →
  hom-cospan f' g' f g →
  canonical-pullback f' g' → canonical-pullback f g
functor-canonical-pullback f g f' g'
  (pair hA (pair hB (pair hX (pair HA HB)))) (pair a' (pair b' p')) =
  pair (hA a') (pair (hB b') ((HA a') ∙ ((ap hX p') ∙ (inv (HB b')))))

cospan-hom-cospan-rotate :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B'' → X'')
  (h : hom-cospan f' g' f g) (h' : hom-cospan f'' g'' f g) →
  hom-cospan (pr1 h) (pr1 h') (pr1 (pr2 (pr2 h))) (pr1 (pr2 (pr2 h')))
cospan-hom-cospan-rotate f g f' g' f'' g'' (pair hA (pair hB (pair hX (pair HA HB)))) (pair hA' (pair hB' (pair hX' (pair HA' HB')))) =
  pair f' (pair f'' (pair f (pair (htpy-inv HA) (htpy-inv HA'))))

cospan-hom-cospan-rotate' :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B'' → X'')
  (h : hom-cospan f' g' f g) (h' : hom-cospan f'' g'' f g) →
  hom-cospan
    (pr1 (pr2 h)) (pr1 (pr2 h')) (pr1 (pr2 (pr2 h))) (pr1 (pr2 (pr2 h')))
cospan-hom-cospan-rotate' f g f' g' f'' g''
  (pair hA (pair hB (pair hX (pair HA HB))))
  (pair hA' (pair hB' (pair hX' (pair HA' HB')))) =
  pair g' (pair g'' (pair g (pair (htpy-inv HB) (htpy-inv HB'))))

{-
map-3-by-3-canonical-pullback' :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B → X'')
  (h : hom-cospan f' g' f g) (h' : hom-cospan f'' g'' f g) →
  Σ ( canonical-pullback f' g') (λ t' →
    Σ ( canonical-pullback f'' g'') (λ t'' →
      Eq-canonical-pullback f g
        ( functor-canonical-pullback f g f' g' h t')
        ( functor-canonical-pullback f g f'' g'' h' t''))) →
  Σ ( canonical-pullback (pr1 h) (pr1 h')) (λ s →
    Σ ( canonical-pullback (pr1 (pr2 h)) (pr1 (pr2 h'))) (λ s' →
      Eq-canonical-pullback (pr1 (pr2 (pr2 h))) (pr1 (pr2 (pr2 h')))
        ( functor-canonical-pullback
          ( pr1 (pr2 (pr2 h)))
          ( pr1 (pr2 (pr2 h')))
          ( pr1 h)
          ( pr1 h')
          ( cospan-hom-cospan-rotate f g f' g' f'' g'' h h')
          ( s))
        ( functor-canonical-pullback
          ( pr1 (pr2 (pr2 h)))
          ( pr1 (pr2 (pr2 h')))
          ( pr1 (pr2 h))
          ( pr1 (pr2 h'))
          ( cospan-hom-cospan-rotate' f g f' g' f'' g'' h h')
          ( s'))))
map-3-by-3-canonical-pullback' f g f' g' f'' g''
  ( pair hA (pair hB (pair hX (pair HA HB))))
  ( pair hA' (pair hB' (pair hX' (pair HA' HB'))))
  ( pair
    ( pair a' (pair b' p'))
    ( pair (pair a'' (pair b'' p'')) (pair α (pair β γ)))) =
  pair (pair a' (pair a'' α)) (pair (pair b' (pair b'' β)) (pair p' (pair p'' {!!})))

map-3-by-3-canonical-pullback :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B → X'')
  (h : hom-cospan f' g' f g) (h' : hom-cospan f'' g'' f g) →
  canonical-pullback
    ( functor-canonical-pullback f g f' g' h)
    ( functor-canonical-pullback f g f'' g'' h') →
  canonical-pullback
    ( functor-canonical-pullback
      ( pr1 (pr2 (pr2 h)))
      ( pr1 (pr2 (pr2 h')))
      ( pr1 h)
      ( pr1 h')
      ( cospan-hom-cospan-rotate f g f' g' f'' g'' h h'))
    ( functor-canonical-pullback
      ( pr1 (pr2 (pr2 h)))
      ( pr1 (pr2 (pr2 h')))
      ( pr1 (pr2 h))
      ( pr1 (pr2 h'))
      ( cospan-hom-cospan-rotate' f g f' g' f'' g'' h h'))
map-3-by-3-canonical-pullback = {!!}
-}
