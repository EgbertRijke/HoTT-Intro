{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 16-pushouts where

import 15-pullbacks
open 15-pullbacks public

-- Section 14.1

{- We define the type of cocones with vertex X on a span. Since we will use it
   later on, we will also characterize the identity type of the type of cocones
   with a given vertex X. -}

cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → UU l4 → UU _
cocone {A = A} {B = B} f g X =
  Σ (A → X) (λ i → Σ (B → X) (λ j → (i ∘ f) ~ (j ∘ g)))

coherence-htpy-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c c' : cocone f g X) →
  (K : (pr1 c) ~ (pr1 c')) (L : (pr1 (pr2 c)) ~ (pr1 (pr2 c'))) → UU (l1 ⊔ l4)
coherence-htpy-cocone f g c c' K L =
  ((pr2 (pr2 c)) ∙h (L ·r g)) ~ ((K ·r f) ∙h (pr2 (pr2 c')))

htpy-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} →
  cocone f g X → cocone f g X → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
htpy-cocone f g c c' =
  Σ ((pr1 c) ~ (pr1 c'))
    ( λ K → Σ ((pr1 (pr2 c)) ~ (pr1 (pr2 c')))
      ( coherence-htpy-cocone f g c c' K))

reflexive-htpy-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  htpy-cocone f g c c
reflexive-htpy-cocone f g (pair i (pair j H)) =
  pair
    ( htpy-refl i)
    ( pair
      ( htpy-refl j)
      ( htpy-right-unit H))

htpy-cocone-eq :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c c' : cocone f g X) →
  Id c c' → htpy-cocone f g c c'
htpy-cocone-eq f g c .c refl = reflexive-htpy-cocone f g c

is-contr-total-htpy-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  is-contr (Σ (cocone f g X) (htpy-cocone f g c))
is-contr-total-htpy-cocone f g c =
  is-contr-total-Eq-structure
    ( λ i' jH' K → Σ ((pr1 (pr2 c)) ~ (pr1 jH'))
      ( coherence-htpy-cocone f g c (pair i' jH') K))
    ( is-contr-total-htpy (pr1 c))
    ( pair (pr1 c) (htpy-refl (pr1 c)))
    ( is-contr-total-Eq-structure
      ( λ j' H' → coherence-htpy-cocone f g c
        ( pair (pr1 c) (pair j' H'))
        ( htpy-refl (pr1 c)))
      ( is-contr-total-htpy (pr1 (pr2 c)))
      ( pair (pr1 (pr2 c)) (htpy-refl (pr1 (pr2 c))))
      ( is-contr-is-equiv'
        ( Σ (((pr1 c) ∘ f) ~ ((pr1 (pr2 c)) ∘ g)) (λ H' → (pr2 (pr2 c)) ~ H'))
        ( tot (λ H' M → (htpy-right-unit (pr2 (pr2 c))) ∙h M))
        ( is-equiv-tot-is-fiberwise-equiv (λ H' → is-equiv-htpy-concat _ _))
        ( is-contr-total-htpy (pr2 (pr2 c)))))

is-equiv-htpy-cocone-eq :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c c' : cocone f g X) →
  is-equiv (htpy-cocone-eq f g c c')
is-equiv-htpy-cocone-eq f g c =
  id-fundamental-gen c
    ( reflexive-htpy-cocone f g c)
    ( is-contr-total-htpy-cocone f g c)
    ( htpy-cocone-eq f g c)

eq-htpy-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c c' : cocone f g X) →
  htpy-cocone f g c c' → Id c c'
eq-htpy-cocone f g c c' = inv-is-equiv (is-equiv-htpy-cocone-eq f g c c')

{-
issec-eq-htpy-cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c c' : cocone f g X) →
  ((htpy-cocone-eq f g c c') ∘ (eq-htpy-cocone f g c c')) ~ id
issec-eq-htpy-cocone f g c c' =
  issec-inv-is-equiv (is-equiv-htpy-cocone-eq f g c c')
-}

{- Given a cocone c with vertex X on a span, consider a dependent type P over
   X. The type generating-data-pushout describes how to generate a section of
   P if the cocone c is a pushout. In other words, a pushout will be defined
   below as a cocone such that every term of type generating-data-pushout
   uniquely determines a section of P. -}

generating-data-pushout : 
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l5)))
generating-data-pushout {S = S} {A} {B} f g c P =
  Σ ( (a : A) → P (pr1 c a))
    ( λ i' → Σ ( (b : B) → P (pr1 (pr2 c) b))
      ( λ j' → (s : S) → Id (tr P (pr2 (pr2 c) s) (i' (f s))) (j' (g s))))

{- Again, we proceed by immediately characterizing the idenity type of the
   type generating-data-pushout. -}

coherence-htpy-generating-data-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  (P : X → UU l5) (c' c'' : generating-data-pushout f g c P)
  (K : (pr1 c') ~ (pr1 c'')) (L : (pr1 (pr2 c')) ~ (pr1 (pr2 c''))) →
  UU (l1 ⊔ l5)
coherence-htpy-generating-data-pushout {S = S} f g (pair i (pair j H)) P
  c' c'' K L =
  (s : S) → 
    Id
      ( ((pr2 (pr2 c')) s) ∙ (L (g s)))
      ( (ap (tr P (H s)) (K (f s))) ∙ ((pr2 (pr2 c'')) s))

htpy-generating-data-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s t : generating-data-pushout f g c P) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l5)))
htpy-generating-data-pushout {S = S} f g (pair i (pair j H)) P
  (pair hA (pair hB hS)) t =
  let kA = pr1 t
      kB = pr1 (pr2 t)
      kS = pr2 (pr2 t)
  in
  Σ ( hA ~ kA)
    ( λ K → Σ ( hB ~ kB)
      ( λ L →
        coherence-htpy-generating-data-pushout f g
          ( pair i (pair j H)) P (pair hA (pair hB hS)) t K L))

reflexive-htpy-generating-data-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s : generating-data-pushout f g c P) →
  htpy-generating-data-pushout f g c P s s
reflexive-htpy-generating-data-pushout f g (pair i (pair j H)) P
  (pair hA (pair hB hS)) =
  pair
    ( htpy-refl hA)
    ( pair
      ( htpy-refl hB)
      ( htpy-right-unit hS))

htpy-generating-data-pushout-eq :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s t : generating-data-pushout f g c P) →
  Id s t → htpy-generating-data-pushout f g c P s t
htpy-generating-data-pushout-eq f g c P s .s refl =
  reflexive-htpy-generating-data-pushout f g c P s

is-contr-total-htpy-generating-data-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s : generating-data-pushout f g c P) →
  is-contr
    ( Σ (generating-data-pushout f g c P)
      ( htpy-generating-data-pushout f g c P s))
is-contr-total-htpy-generating-data-pushout
  {S = S} {A} {B} f g {X} (pair i (pair j H)) P (pair hA (pair hB hS)) =
  is-contr-total-Eq-structure
    {A = (a : A) → P (i a)}
    {B = λ α →
             Σ ((x : B) → P (j x))
             (λ β → (s : S) → Id (tr P (H s) (α (f s))) (β (g s)))}
    {C = λ α → hA ~ α}
    ( λ α βγ K →
      let β = pr1 βγ
          γ = pr2 βγ
      in
      Σ (hB ~ β) (λ L →
        coherence-htpy-generating-data-pushout f g
          ( pair i (pair j H)) P (pair hA (pair hB hS)) (pair α βγ) K L))
    ( is-contr-total-htpy hA)
    ( pair hA (htpy-refl _))
    ( is-contr-total-Eq-structure
      ( λ β γ L →
        coherence-htpy-generating-data-pushout f g
          ( pair i (pair j H))
          ( P)
          ( pair hA (pair hB hS))
          ( pair hA (pair β γ))
          ( htpy-refl hA)
          ( L))
      ( is-contr-total-htpy hB)
      ( pair hB (htpy-refl _))
      ( is-contr-is-equiv
        ( Σ ((s : S) → Id (tr P (H s) (hA (f s))) (hB (g s))) (λ γ → hS ~ γ))
        ( tot (λ γ → htpy-concat _ (htpy-inv (htpy-right-unit hS))))
        ( is-equiv-tot-is-fiberwise-equiv
          ( is-equiv-htpy-concat (htpy-inv (htpy-right-unit hS))))
        ( is-contr-total-htpy hS)))

is-fiberwise-equiv-htpy-generating-data-pushout-eq :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s : generating-data-pushout f g c P) →
  is-fiberwise-equiv (htpy-generating-data-pushout-eq f g c P s)
is-fiberwise-equiv-htpy-generating-data-pushout-eq f g c P s =
  id-fundamental-gen s
    ( reflexive-htpy-generating-data-pushout f g c P s)
    ( is-contr-total-htpy-generating-data-pushout f g c P s)
    ( htpy-generating-data-pushout-eq f g c P s)

eq-htpy-generating-data-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s t : generating-data-pushout f g c P) →
  htpy-generating-data-pushout f g c P s t → Id s t
eq-htpy-generating-data-pushout f g c P s t =
  inv-is-equiv (is-fiberwise-equiv-htpy-generating-data-pushout-eq f g c P s t)

issec-eq-htpy-generating-data-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s t : generating-data-pushout f g c P) →
  ( ( htpy-generating-data-pushout-eq f g c P s t) ∘
    ( eq-htpy-generating-data-pushout f g c P s t)) ~ id
issec-eq-htpy-generating-data-pushout f g c P s t =
  issec-inv-is-equiv
    ( is-fiberwise-equiv-htpy-generating-data-pushout-eq f g c P s t)

isretr-eq-htpy-generating-data-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s t : generating-data-pushout f g c P) →
  ( ( eq-htpy-generating-data-pushout f g c P s t) ∘
    ( htpy-generating-data-pushout-eq f g c P s t)) ~ id
isretr-eq-htpy-generating-data-pushout f g c P s t =
  isretr-inv-is-equiv
    ( is-fiberwise-equiv-htpy-generating-data-pushout-eq f g c P s t)

{- Given a cocone c with vertex X on a span, any section of any dependent type
   P over X determines generating data by "substituting the" cocone structure c
   into the section. -}

dgen-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) {P : X → UU l5} →
  ((x : X) → P x) → generating-data-pushout f g c P
dgen-pushout f g (pair i (pair j H)) h =
  pair
    ( λ a → h (i a))
    ( pair
      ( λ b → h (j b))
      ( λ s → apd h (H s)))

{- We now formulate the induction principle of pushouts: a cocone c with vertex
   X on a span S satisfies the induction principle of the pushout of S if the
   map dgen-pushout defined above has a section, for every type family P over
   X. -}

Ind-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) → UU _
Ind-pushout l f g {X} c = (P : X → UU l) → sec (dgen-pushout f g c {P})

{- The type of pushouts on a span S is now defined to be the type of types
   equipped with the structure of a cocone on S, that satisfies the induction
   principle for pushouts. -}

PUSHOUT :
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  UU (lsuc (lsuc l1) ⊔ (lsuc (lsuc l2) ⊔ (lsuc (lsuc l3))))
PUSHOUT {l1} {l2} {l3} f g =
  Σ ( UU (l1 ⊔ (l2 ⊔ l3)))
    ( λ X → Σ (cocone f g X)
      ( λ c → Ind-pushout (lsuc (l1 ⊔ (l2 ⊔ l3))) f g c)) 

-- Section 14.2 Examples of pushouts

-- Section 14.3 Duality of pushouts and pullbacks

-- We first give several different conditions that are equivalent to the
-- universal property of pushouts.

{- Given a cocone c on a span S with vertex X, and a type Y, the function 
   cocone-map sends a function X → Y to a new cocone with vertex Y. -}

cocone-map :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} {Y : UU l5} →
  cocone f g X → (X → Y) → cocone f g Y
cocone-map f g (pair i (pair j H)) h =
  pair (h ∘ i) (pair (h ∘ j) (h ·l H))

cocone-map-id :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  Id (cocone-map f g c id) c
cocone-map-id f g (pair i (pair j H)) =
  eq-pair ( pair refl
    ( eq-pair (pair refl
      ( eq-htpy (λ s → ap-id (H s))))))

cocone-map-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  {Y : UU l5} (h : X → Y) {Z : UU l6} (k : Y → Z) →
  Id (cocone-map f g c (k ∘ h)) ((cocone-map f g (cocone-map f g c h) k))
cocone-map-comp f g (pair i (pair j H)) h k =
  eq-pair (pair refl
    ( eq-pair (pair refl
      ( eq-htpy (λ s → ap-comp k h (H s))))))

{- A cocone c on a span S is said to satisfy the universal property of the
   pushout of S if the function cocone-map is an equivalence for every type Y.
   -}

universal-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} →
  cocone f g X → UU _
universal-property-pushout l f g c =
  (Y : UU l) → is-equiv (cocone-map f g {Y = Y} c)
  
{- The universal property of the pushout of a span S can also be stated as a
   pullback-property: a cocone c = (pair i (pair j H)) with vertex X
   satisfies the universal property of the pushout of S if and only if the
   square

     Y^X -----> Y^B
      |          |
      |          |
      V          V
     Y^A -----> Y^S

   is a pullback square for every type Y. Below, we first define the cone of
   this commuting square, and then we introduce the type 
   pullback-property-pushout, which states that the above square is a pullback.
   -}

precompose :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : UU l3) →
  (A → B) → (B → C) → (A → C)
precompose C f g = g ∘ f

htpy-precompose :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : UU l3)
  {f g : A → B} (H : f ~ g) →
  (precompose C f) ~ (precompose C g)
htpy-precompose C H h = eq-htpy (h ·l H)

compute-htpy-precompose :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : UU l3) (f : A → B) →
  (htpy-precompose C (htpy-refl f)) ~ (htpy-refl _)
compute-htpy-precompose C f h = eq-htpy-htpy-refl (h ∘ f)

cone-pullback-property-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (Y : UU l) →
  cone (λ (h : A → Y) → h ∘ f) (λ (h : B → Y) → h ∘ g) (X → Y)
cone-pullback-property-pushout f g {X} c Y =
  pair
    ( precompose Y (pr1 c))
    ( pair
      ( precompose Y (pr1 (pr2 c)))
      ( htpy-precompose Y (pr2 (pr2 c))))

pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l4 ⊔ lsuc l))))
pullback-property-pushout l {S} {A} {B} f g {X} c =
  (Y : UU l) → is-pullback
    ( precompose Y f)
    ( precompose Y g)
    ( cone-pullback-property-pushout f g c Y)

{- There is also a universal property of pushouts for dependent functions out
   of a pushout. It states that the map dgen-pushout is an equivalence, for
   every type family P over X. Compare this to the induction principle of
   pushouts, which only states that the map dgen-pushout has a section for
   every type family P over X. -}

dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) → UU _
dependent-universal-property-pushout l f g {X} c =
  (P : X → UU l) → is-equiv (dgen-pushout f g c {P})

{- Like the dependent universal property of pushouts, there is also a way of
   phrasing pullback-property-pushout dependently. -}

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

{- We will now start proving that the following properties are all equivalent:
 
   1. universal-property-pushout
   2. pullback-property-pushout
   3. Ind-pushout
   4. dependent-universal-property-pushout
   5. dependent-pullback-property-pushout

   We will first show that 1 ↔ 2, and that 3 ↔ 4 ↔ 5. Finally, we will show
   that 2 ↔ 5. -}

{- In order to show that the universal property of pushouts is equivalent to 
   the pullback property, we show that the maps cocone-map and the gap map fit 
   in a commuting triangle, where the third map is an equivalence. The claim 
   then follows from the 3-for-2 property of equivalences. -}
   
triangle-pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  {l : Level} (Y : UU l) →
  ( cocone-map f g c) ~
  ( ( tot (λ i' → tot (λ j' p → htpy-eq p))) ∘
    ( gap (λ h → h ∘ f) (λ h → h ∘ g) (cone-pullback-property-pushout f g c Y)))
triangle-pullback-property-pushout-universal-property-pushout
  {S = S} {A = A} {B = B} f g (pair i (pair j H)) Y h =
    eq-pair
      ( pair refl (eq-pair (pair refl (inv (issec-eq-htpy (h ·l H))))))

pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  universal-property-pushout l f g c → pullback-property-pushout l f g c
pullback-property-pushout-universal-property-pushout
  l f g (pair i (pair j H)) up-c Y =
  let c = (pair i (pair j H)) in
  is-equiv-right-factor
    ( cocone-map f g c)
    ( tot (λ i' → tot (λ j' p → htpy-eq p)))
    ( gap (λ h → h ∘ f) (λ h → h ∘ g) (cone-pullback-property-pushout f g c Y))
    ( triangle-pullback-property-pushout-universal-property-pushout f g c Y)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ i' → is-equiv-tot-is-fiberwise-equiv
        ( λ j' → funext (i' ∘ f) (j' ∘ g))))
    ( up-c Y)

universal-property-pushout-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  pullback-property-pushout l f g c → universal-property-pushout l f g c
universal-property-pushout-pullback-property-pushout
  l f g (pair i (pair j H)) pb-c Y =
  let c = (pair i (pair j H)) in
  is-equiv-comp
    ( cocone-map f g c)
    ( tot (λ i' → tot (λ j' p → htpy-eq p)))
    ( gap (λ h → h ∘ f) (λ h → h ∘ g) (cone-pullback-property-pushout f g c Y))
    ( triangle-pullback-property-pushout-universal-property-pushout f g c Y)
    ( pb-c Y)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ i' → is-equiv-tot-is-fiberwise-equiv
        ( λ j' → funext (i' ∘ f) (j' ∘ g))))

{- Our current goal is to prove the dependent universal property of pushouts
   from the induction principle of pushouts. -}

dependent-naturality-square :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f f' : (x : A) → B x)
  {x x' : A} (p : Id x x') (q : Id (f x) (f' x)) (q' : Id (f x') (f' x')) →
  Id ((apd f p) ∙ q') ((ap (tr B p) q) ∙ (apd f' p)) →
  Id (tr (λ y → Id (f y) (f' y)) p q) q' 
dependent-naturality-square f f' refl q q' s =
  inv (s ∙ ((right-unit (ap id q)) ∙ (ap-id q)))

htpy-eq-dgen-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ( H : (l : Level) → Ind-pushout l f g c) →
  {l : Level} {P : X → UU l} (h h' : (x : X) → P x) →
  Id (dgen-pushout f g c h) (dgen-pushout f g c h') → h ~ h'
htpy-eq-dgen-pushout f g (pair i (pair j H)) I {l} {P} h h' p =
  let c = (pair i (pair j H))
      K = pr1 (htpy-generating-data-pushout-eq f g c P _ _ p)
      L = pr1 (pr2 (htpy-generating-data-pushout-eq f g c P _ _ p))
      M = pr2 (pr2 (htpy-generating-data-pushout-eq f g c P _ _ p))
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
    ( pair
      ( ind-pushout)
      ( pair
        ( comp-pushout)
        ( λ h → eq-htpy (htpy-eq-dgen-pushout f g c H
          ( ind-pushout (dgen-pushout f g c h))
          ( h)
          ( pr2 (H l P) (dgen-pushout f g c h))))))

{- The converse, that the dependent universal property implies the induction
   principle, is a mere triviality. -}
   
Ind-pushout-dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) → dependent-universal-property-pushout l f g c) →
  ((l : Level) → Ind-pushout l f g c)
Ind-pushout-dependent-universal-property-pushout f g c dup-c l P =
  pr1 (dup-c l P)

{- Next, we will show that the dependent pullback property follows from the
   dependent universal property of pushouts. -}

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
triangle-dependent-pullback-property-pushout f g (pair i (pair j H)) P h =
  eq-pair (pair refl (eq-pair (pair refl
    ( inv (issec-eq-htpy (λ x → apd h (H x)))))))

dependent-pullback-property-dependent-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) → dependent-universal-property-pushout l f g c) →
  ((l : Level) → dependent-pullback-property-pushout l f g c)
dependent-pullback-property-dependent-universal-property-pushout
  f g (pair i (pair j H)) I l P =
  let c = (pair i (pair j H)) in
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

dependent-universal-property-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  ((l : Level) → dependent-pullback-property-pushout l f g c) →
  ((l : Level) → dependent-universal-property-pushout l f g c)
dependent-universal-property-dependent-pullback-property-pushout
  f g (pair i (pair j H)) dpullback-c l P =
  let c = (pair i (pair j H)) in
  is-equiv-comp
    ( dgen-pushout f g c)
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

{- We now show that the dependent pullback property implies the pullback
   property of pushouts. -}

concat-eq-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) → Id (eq-htpy (H ∙h K)) ((eq-htpy H) ∙ (eq-htpy K))
concat-eq-htpy {A = A} {B} {f} H K =
  ind-htpy f
    ( λ g H →
      ( h : (x : A) → B x) (K : g ~ h) →
      Id (eq-htpy (H ∙h K)) ((eq-htpy H) ∙ (eq-htpy K)))
    ( λ h K → ap (concat' _ (eq-htpy K)) (inv (eq-htpy-htpy-refl _))) H _ K

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
    ( htpy-refl _)
    { c = pair
      ( λ h a → h (i a))
      ( pair (λ h b → h (j b)) (λ h → eq-htpy (h ·l H)))}
    ( cone-dependent-pullback-property-pushout
      f g (pair i (pair j H)) (λ x → Y))
    ( pair
      ( λ h → refl)
      ( pair
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
    ( dpb (λ x → Y))

-- Exercises

-- Exercise 13.1

-- Exercise 13.2

is-equiv-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv f →
  ((l : Level) → universal-property-pushout l f g c) → is-equiv (pr1 (pr2 c))
is-equiv-universal-property-pushout
  {A = A} {B} f g (pair i (pair j H)) is-equiv-f up-c =
  is-equiv-is-equiv-precomp j
    ( λ l T →
      is-equiv-is-pullback'
        ( λ (h : A → T) → h ∘ f)
        ( λ (h : B → T) → h ∘ g)
        ( cone-pullback-property-pushout f g (pair i (pair j H)) T)
        ( is-equiv-precomp-is-equiv f is-equiv-f T)
        ( pullback-property-pushout-universal-property-pushout
          l f g (pair i (pair j H)) (up-c l) T))

universal-property-pushout-is-equiv :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv f → is-equiv (pr1 (pr2 c)) →
  ((l : Level) → universal-property-pushout l f g c)
universal-property-pushout-is-equiv f g (pair i (pair j H)) is-equiv-f is-equiv-j l =
  let c = (pair i (pair j H)) in
  universal-property-pushout-pullback-property-pushout l f g c
    ( λ T → is-pullback-is-equiv'
      ( λ h → h ∘ f)
      ( λ h → h ∘ g)
      ( cone-pullback-property-pushout f g c T)
      ( is-equiv-precomp-is-equiv f is-equiv-f T)
      ( is-equiv-precomp-is-equiv j is-equiv-j T))
  
