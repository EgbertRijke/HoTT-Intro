{-# OPTIONS --without-K --allow-unsolved-metas --cubical #-}

module Lecture13 where

import Lecture12
open Lecture12 public

-- Section 13.1

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
reflexive-htpy-cocone f g (dpair i (dpair j H)) =
  dpair
    ( htpy-refl i)
    ( dpair
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
      ( coherence-htpy-cocone f g c (dpair i' jH') K))
    ( is-contr-total-htpy (pr1 c))
    ( dpair (pr1 c) (htpy-refl (pr1 c)))
    ( is-contr-total-Eq-structure
      ( λ j' H' → coherence-htpy-cocone f g c
        ( dpair (pr1 c) (dpair j' H'))
        ( htpy-refl (pr1 c)))
      ( is-contr-total-htpy (pr1 (pr2 c)))
      ( dpair (pr1 (pr2 c)) (htpy-refl (pr1 (pr2 c))))
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
coherence-htpy-generating-data-pushout {S = S} f g (dpair i (dpair j H)) P
  c' c'' K L =
  (s : S) → 
    Id
      ( ((pr2 (pr2 c')) s) ∙ (L (g s)))
      ( (ap (tr P (H s)) (K (f s))) ∙ ((pr2 (pr2 c'')) s))

htpy-generating-data-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s t : generating-data-pushout f g c P) → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l5)))
htpy-generating-data-pushout {S = S} f g (dpair i (dpair j H)) P
  (dpair hA (dpair hB hS)) t =
  let kA = pr1 t
      kB = pr1 (pr2 t)
      kS = pr2 (pr2 t)
  in
  Σ ( hA ~ kA)
    ( λ K → Σ ( hB ~ kB)
      ( λ L →
        coherence-htpy-generating-data-pushout f g
          ( dpair i (dpair j H)) P (dpair hA (dpair hB hS)) t K L))

reflexive-htpy-generating-data-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  (s : generating-data-pushout f g c P) →
  htpy-generating-data-pushout f g c P s s
reflexive-htpy-generating-data-pushout f g (dpair i (dpair j H)) P
  (dpair hA (dpair hB hS)) =
  dpair
    ( htpy-refl hA)
    ( dpair
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
  {S = S} {A} {B} f g {X} (dpair i (dpair j H)) P (dpair hA (dpair hB hS)) =
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
          ( dpair i (dpair j H)) P (dpair hA (dpair hB hS)) (dpair α βγ) K L))
    ( is-contr-total-htpy hA)
    ( dpair hA (htpy-refl _))
    ( is-contr-total-Eq-structure
      ( λ β γ L →
        coherence-htpy-generating-data-pushout f g
          ( dpair i (dpair j H))
          ( P)
          ( dpair hA (dpair hB hS))
          ( dpair hA (dpair β γ))
          ( htpy-refl hA)
          ( L))
      ( is-contr-total-htpy hB)
      ( dpair hB (htpy-refl _))
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
dgen-pushout f g (dpair i (dpair j H)) h =
  dpair
    ( λ a → h (i a))
    ( dpair
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

-- Section 13.3

-- We first give several different conditions that are equivalent to the
-- universal property of pushouts.

{- Given a cocone c on a span S with vertex X, and a type Y, the function 
   cocone-map sends a function X → Y to a new cocone with vertex Y. -}

cocone-map :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} {Y : UU l5} →
  cocone f g X → (X → Y) → cocone f g Y
cocone-map f g (dpair i (dpair j H)) h =
  dpair (h ∘ i) (dpair (h ∘ j) (h ·l H))

cocone-map-id :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  Id (cocone-map f g c id) c
cocone-map-id f g (dpair i (dpair j H)) =
  eq-pair ( dpair refl
    ( eq-pair (dpair refl
      ( eq-htpy (λ s → ap-id (H s))))))

cocone-map-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  {Y : UU l5} (h : X → Y) {Z : UU l6} (k : Y → Z) →
  Id (cocone-map f g c (k ∘ h)) ((cocone-map f g (cocone-map f g c h) k))
cocone-map-comp f g (dpair i (dpair j H)) h k =
  eq-pair (dpair refl
    ( eq-pair (dpair refl
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
   pullback-property: a cocone c = (dpair i (dpair j H)) with vertex X
   satisfies the universal property of the pushout of S if and only if the
   square

     X^Y -----> B^Y
      |          |
      |          |
      V          V
     A^Y -----> S^Y

   is a pullback square for every type Y. Below, we first define the cone of
   this commuting square, and then we introduce the type 
   pullback-property-pushout, which states that the above square is a pullback.
   -}

cone-pullback-property-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (Y : UU l) →
  cone (λ (h : A → Y) → h ∘ f) (λ (h : B → Y) → h ∘ g) (X → Y)
cone-pullback-property-pushout f g {X} (dpair i (dpair j H)) Y =
  dpair
    ( λ (h : X → Y) → h ∘ i)
    ( dpair
      ( λ (h : X → Y) → h ∘ j)
      ( λ h → eq-htpy (h ·l H)))

pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l4 ⊔ lsuc l))))
pullback-property-pushout l {S} {A} {B} f g {X} c =
  (Y : UU l) → is-pullback
    ( λ (h : A → Y) → h ∘ f)
    ( λ (h : B → Y) → h ∘ g)
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
cone-dependent-pullback-property-pushout f g (dpair i (dpair j H)) P =
  dpair
    ( λ h → λ a → h (i a))
    ( dpair
      ( λ h → λ b → h (j b))
       λ h → eq-htpy (λ s → apd h (H s)))

dependent-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ (l4 ⊔ lsuc l))))
dependent-pullback-property-pushout l {S} {A} {B} f g {X}
  (dpair i (dpair j H)) =
  (P : X → UU l) →
  is-pullback
    ( λ (h : (a : A) → P (i a)) → λ s → tr P (H s) (h (f s)))
    ( λ (h : (b : B) → P (j b)) → λ s → h (g s))
    ( cone-dependent-pullback-property-pushout f g (dpair i (dpair j H)) P)

{- We will now start proving that the following properties are all equivalent:
 
   * universal-property-pushout
   * pullback-property-pushout
   * Ind-pushout
   * dependent-universal-property-pushout
   * dependent-pullback-property-pushout

   -}

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
  {S = S} {A = A} {B = B} f g (dpair i (dpair j H)) Y h =
    eq-pair
      ( dpair refl (eq-pair (dpair refl (inv (issec-eq-htpy (h ·l H))))))

pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  universal-property-pushout l f g c → pullback-property-pushout l f g c
pullback-property-pushout-universal-property-pushout
  l f g (dpair i (dpair j H)) up-c Y =
  let c = (dpair i (dpair j H)) in
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
  l f g (dpair i (dpair j H)) pb-c Y =
  let c = (dpair i (dpair j H)) in
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
htpy-eq-dgen-pushout f g (dpair i (dpair j H)) I {l} {P} h h' p =
  let c = (dpair i (dpair j H))
      K = pr1 (htpy-generating-data-pushout-eq f g c P _ _ p)
      L = pr1 (pr2 (htpy-generating-data-pushout-eq f g c P _ _ p))
      M = pr2 (pr2 (htpy-generating-data-pushout-eq f g c P _ _ p))
  in
  pr1
    ( I _ (λ x → Id (h x) (h' x)))
    ( dpair
      ( K)
      ( dpair
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
  ((l : Level) → dependent-universal-property-pushout l f g c) →
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

concat-eq-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) → Id (eq-htpy (H ∙h K)) ((eq-htpy H) ∙ (eq-htpy K))
concat-eq-htpy {A = A} {B} {f} H K =
  ind-htpy f
    ( λ g H →
      ( h : (x : A) → B x) (K : g ~ h) →
      Id (eq-htpy (H ∙h K)) ((eq-htpy H) ∙ (eq-htpy K)))
    ( λ h K → ap (concat' _ (eq-htpy K)) (inv (eq-htpy-htpy-refl _))) _ H _ K

pullback-property-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  dependent-pullback-property-pushout l f g c →
  pullback-property-pushout l f g c
pullback-property-dependent-pullback-property-pushout
  l f g (dpair i (dpair j H)) dpb Y =
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
    ( dpb (λ x → Y))

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
