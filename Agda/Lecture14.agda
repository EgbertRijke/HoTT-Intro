{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture14 where

import Lecture13
open Lecture13 public

-- Cubes

{- 
  We specify the type of the homotopy witnessing that a cube commutes. Imagine
  that the cube is presented as a lattice

           *
         / | \
        /  |  \
       /   |   \
      *    *    *
      |\ /   \ /| 
      | \     ‌/ |
      |/ \   / \|
      *    *    *
       \   |   /
        \  |  /
         \ | /
           *

  with all maps pointing in the downwards direction. Presented in this way, a
  cube of maps has a top face, a back-left face, a back-right face, a front-left
  face, a front-right face, and a bottom face, all of which are homotopies.

  A term of type coherence-cube is a homotopy filling the cube.
-}

coherence-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) → UU _
coherence-cube f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom =
  ((((h ·l back-left) ∙h (front-left ·r f')) ∙h (hD ·l top))) ~
  ((bottom ·r hA) ∙h ((k ·l back-right) ∙h (front-right ·r g')))

{-
  The symmetry group D_3 acts on a cube. However, the coherence filling a
  a cube needs to be modified to show that the rotated/reflected cube again
  commutes. In the following definitions we provide the homotopies witnessing
  that the rotated/reflected cubes again commute.

  Note: although in principle it ought to be enough to show this for the
  generators of the symmetry group D_3, in practice it is more straightforward
  to just do the work for each of the symmetries separately. One reason is
  that some of the homotopies witnessing that the faces commute will be
  inverted as the result of an application of a symmetry. Inverting a homotopy
  twice results in a new homotopy that is only homotopic to the original
  homotopy.

  We first provide some constructions involving homotopies that will help us
  manipulating coherences of cubes.
-}

htpy-inv-con :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K : g ~ h) (L : f ~ h) →
  (H ∙h K) ~ L → K ~ ((htpy-inv H) ∙h L)
htpy-inv-con H K L M x = inv-con (H x) (K x) (L x) (M x)

htpy-con-inv :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K : g ~ h) (L : f ~ h) →
  (H ∙h K) ~ L → H ~ (L ∙h (htpy-inv K))
htpy-con-inv H K L M x = con-inv (H x) (K x) (L x) (M x)

htpy-ap-concat :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K K' : g ~ h) →
  K ~ K' → (H ∙h K) ~ (H ∙h K')
htpy-ap-concat {g = g} {h} H K K' L x =
  ap (concat (g x) {z = h x} (H x)) (L x)

htpy-ap-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H H' : f ~ g) (K : g ~ h) →
  H ~ H' → (H ∙h K) ~ (H' ∙h K)
htpy-ap-concat' H H' K L x =
  ap (concat' _ (K x)) (L x)

htpy-left-whisk-htpy-inv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f f' : A → B} (g : B → C) (H : f ~ f') →
  (g ·l (htpy-inv H)) ~ htpy-inv (g ·l H)
htpy-left-whisk-htpy-inv g H x = ap-inv g (H x)

htpy-right-whisk-htpy-inv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g g' : B → C} (H : g ~ g') (f : A → B) →
  ((htpy-inv H) ·r f) ~ (htpy-inv (H ·r f))
htpy-right-whisk-htpy-inv H f = htpy-refl _

htpy-cone-htpy-refl-vertical :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') (g : B → X)
  (p : C → A) {q q' : C → B} (Hq : q ~ q') →
  (H : (f ∘ p) ~ (g ∘ q)) (H' : (f' ∘ p) ~ (g ∘ q')) →
  (H ∙h (g ·l Hq)) ~ ((Hf ·r p) ∙h H') →
  htpy-cone Hf (htpy-refl g) (dpair p (dpair q H)) (dpair p (dpair q' H'))
htpy-cone-htpy-refl-vertical Hf g p Hq H H' K =
  dpair
    ( htpy-refl p)
    ( dpair Hq (htpy-ap-concat H _ _ (htpy-right-unit (g ·l Hq)) ∙h K))

htpy-cone-htpy-refl-horizontal :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) {g g' : B → X} (Hg : g ~ g')
  {p p' : C → A} (Hp : p ~ p') (q : C → B)
  (H : (f ∘ p) ~ (g ∘ q)) (H' : (f ∘ p') ~ (g' ∘ q)) →
  ((H ∙h (Hg ·r q)) ~ ((f ·l Hp) ∙h H')) →
  htpy-cone (htpy-refl f) Hg (dpair p (dpair q H)) (dpair p' (dpair q H'))
htpy-cone-htpy-refl-horizontal f Hg Hp q H H' K =
  dpair Hp
    ( dpair
      ( htpy-refl q)
      ( K ∙h (htpy-ap-concat' _ _ H' (htpy-inv (htpy-right-unit (f ·l Hp))))))

-- We show that a rotation of a commuting cube again commutes.
coherence-cube-rotate-120 :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g))
  (c : coherence-cube
       f g h k f' g' h' k' hA hB hC hD
       top back-left back-right front-left front-right bottom) →
  coherence-cube
    hC k' k hD hA f' f hB g' g h' h
    back-left
    (htpy-inv back-right) (htpy-inv top)
    (htpy-inv bottom) (htpy-inv front-left)
    front-right
coherence-cube-rotate-120
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c =
  ( htpy-inv
    ( htpy-assoc
      ( k ·l (htpy-inv back-right))
      ( (htpy-inv bottom) ·r hA)
      ( h ·l back-left))) ∙h
      ( ( htpy-ap-concat'
            ( k ·l (htpy-inv back-right))
            ( htpy-inv (k ·l back-right))
            ( _)
            ( htpy-left-whisk-htpy-inv k back-right)) ∙h
          ( htpy-inv
            ( htpy-inv-con
              ( k ·l back-right)
              ( _)
              ( ((htpy-inv bottom) ·r hA) ∙h (h ·l back-left))
              ( htpy-inv-con
                ( bottom ·r hA)
                ( _)
                ( h ·l back-left)
                ( ( htpy-assoc (bottom ·r hA) (k ·l back-right) _) ∙h
                  ( ( htpy-assoc
                      ( (bottom ·r hA) ∙h (k ·l back-right))
                      ( front-right ·r g')
                      ( _)) ∙h
                    ( ( htpy-assoc
                        ( ( (bottom ·r hA) ∙h (k ·l back-right)) ∙h
                          ( front-right ·r g'))
                        ( hD ·l htpy-inv top)
                        ( htpy-inv front-left ·r f')) ∙h
                      ( htpy-inv
                        ( htpy-con-inv
                          ( h ·l back-left)
                          ( front-left ·r f')
                          ( _)
                          ( htpy-con-inv _
                              ( hD ·l top)
                              ( ( (bottom ·r hA) ∙h (k ·l back-right)) ∙h
                                  (front-right ·r g'))
                              ( c ∙h
                                ( htpy-assoc
                                    ( bottom ·r hA)
                                    ( k ·l back-right)
                                    ( front-right ·r g'))) ∙h
                            ( htpy-inv
                              ( htpy-ap-concat _
                                ( hD ·l (htpy-inv top))
                                ( htpy-inv (hD ·l top))
                                ( htpy-left-whisk-htpy-inv hD top)))))))))))))

coherence-cube-rotate-240 :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g))
  (c : coherence-cube
       f g h k f' g' h' k' hA hB hC hD
       top back-left back-right front-left front-right bottom) →
  coherence-cube
    h' hB hD h g' hA hC g f' k' f k
    (htpy-inv back-right)
    top (htpy-inv back-left)
    (htpy-inv front-right) bottom
    (htpy-inv front-left)
coherence-cube-rotate-240 f g h k f' g' h' k' hA hB hC hD top back-left back-right front-left front-right bottom c = {!!}

-- We show that a reflection through the "z-axis" of a commuting cube again commutes.
coherence-cube-mirror-z :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g))
  (c : coherence-cube
       f g h k f' g' h' k' hA hB hC hD
       top back-left back-right front-left front-right bottom) →
  coherence-cube g f k h g' f' k' h' hA hC hB hD
    (htpy-inv top) back-right back-left front-right front-left (htpy-inv bottom)
coherence-cube-mirror-z f g h k f' g' h' k' hA hB hC hD top back-left back-right front-left front-right bottom c = {!!}

rectangle-back-left-front-left-cube : 
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  ((h ∘ f) ∘ hA) ~ (hD ∘ (h' ∘ f'))
rectangle-back-left-front-left-cube f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom =
  (h ·l back-left) ∙h (front-left ·r f')

rectangle-back-right-front-right-cube : 
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  ((k ∘ g) ∘ hA) ~ (hD ∘ (k' ∘ g'))
rectangle-back-right-front-right-cube f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom =
  (k ·l back-right) ∙h (front-right ·r g')

coherence-htpy-cone-rectangle-bl-fl-rectangle-br-fr-cube : 
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g))
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
    top back-left back-right front-left front-right bottom) →
  coherence-htpy-cone
    ( bottom)
    ( htpy-refl hD)
    ( dpair hA
      ( dpair
        ( h' ∘ f')
        ( rectangle-back-left-front-left-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom)))
    ( dpair hA
      ( dpair
        ( k' ∘ g')
        ( rectangle-back-right-front-right-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom)))
    ( htpy-refl hA)
    ( top)
coherence-htpy-cone-rectangle-bl-fl-rectangle-br-fr-cube
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c =
  ( λ a' →
    ( ap
      ( concat
        ( hD (h' (f' a')))
        { z = hD (k' (g' a'))}
        ( rectangle-back-left-front-left-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom a'))
      ( right-unit (ap hD (top a'))))) ∙h
  ( c)

rectangle-top-front-left-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  ((h ∘ hB) ∘ f') ~ ((hD ∘ k') ∘ g') 
rectangle-top-front-left-cube
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom =
  (front-left ·r f') ∙h (hD ·l top)

rectangle-back-right-bottom-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  ((h ∘ f) ∘ hA) ~ ((k ∘ hC) ∘ g')
rectangle-back-right-bottom-cube
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom =
  ( bottom ·r hA) ∙h (k ·l back-right)

{-
coherence-htpy-cone-rectangle-top-fl-rectangle-br-bot-cube : 
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g))
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
    top back-left back-right front-left front-right bottom) →
  coherence-htpy-cone
    ( htpy-inv front-right)
    ( htpy-refl h)
    ( dpair g' (dpair (hB ∘ f')
      ( htpy-inv (rectangle-top-front-left-cube f g h k f' g' h' k' hA hB hC hD
        top back-left back-right front-left front-right bottom))))
    ( dpair g' (dpair (f ∘ hA)
      ( htpy-inv
        ( rectangle-back-right-bottom-cube f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom))))
    ( htpy-refl g')
    ( htpy-inv back-left)
coherence-htpy-cone-rectangle-top-fl-rectangle-br-bot-cube = {!!}
-}

rectangle-top-front-right-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  ((hD ∘ h') ∘ f') ~ ((k ∘ hC) ∘ g')
rectangle-top-front-right-cube
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom =
  (hD ·l top) ∙h (htpy-inv (front-right) ·r g')

rectangle-back-left-bottom-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g))→
  ((h ∘ hB) ∘ f') ~ ((k ∘ g) ∘ hA)
rectangle-back-left-bottom-cube
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom =
  (h ·l (htpy-inv back-left)) ∙h (bottom ·r hA)

is-pullback-back-left-is-pullback-back-right-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : A → C} {h : B → D} {k : C → D}
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  {f' : A' → B'} {g' : A' → C'} {h' : B' → D'} {k' : C' → D'}
  {hA : A' → A} {hB : B' → B} {hC : C' → C} {hD : D' → D}
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
    top back-left back-right front-left front-right bottom) →
  is-pullback h hD (dpair hB (dpair h' front-left)) →
  is-pullback k hD (dpair hC (dpair k' front-right)) →
  is-pullback g hC (dpair hA (dpair g' back-right)) →
  is-pullback f hB (dpair hA (dpair f' back-left))
is-pullback-back-left-is-pullback-back-right-cube
  {f = f} {g} {h} {k} {f' = f'} {g'} {h'} {k'} {hA = hA} {hB} {hC} {hD}
  top back-left back-right front-left front-right bottom c
  is-pb-front-left is-pb-front-right is-pb-back-right =
  is-pullback-left-square-is-pullback-rectangle f h hD
    ( dpair hB (dpair h' front-left))
    ( dpair hA (dpair f' back-left))
    ( is-pb-front-left)
    ( is-pullback-htpy
      { f = h ∘ f}
      ( k ∘ g)
      ( bottom)
      { g = hD}
      ( hD)
      ( htpy-refl hD)
      { c = dpair hA (dpair (h' ∘ f')
        ( rectangle-back-left-front-left-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom))}
      ( dpair hA (dpair (k' ∘ g')
        ( rectangle-back-right-front-right-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom)))
      ( dpair
        ( htpy-refl _)
        ( dpair top
          ( coherence-htpy-cone-rectangle-bl-fl-rectangle-br-fr-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c)))
      ( is-pullback-rectangle-is-pullback-left-square g k hD
        ( dpair hC (dpair k' front-right))
        ( dpair hA (dpair g' back-right))
        ( is-pb-front-right)
        ( is-pb-back-right)))

is-pullback-back-right-is-pullback-back-left-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : A → C} {h : B → D} {k : C → D}
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  {f' : A' → B'} {g' : A' → C'} {h' : B' → D'} {k' : C' → D'}
  {hA : A' → A} {hB : B' → B} {hC : C' → C} {hD : D' → D}
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
    top back-left back-right front-left front-right bottom) →
  is-pullback h hD (dpair hB (dpair h' front-left)) →
  is-pullback k hD (dpair hC (dpair k' front-right)) →
  is-pullback f hB (dpair hA (dpair f' back-left)) →
  is-pullback g hC (dpair hA (dpair g' back-right))
is-pullback-back-right-is-pullback-back-left-cube
  {f = f} {g} {h} {k} {f' = f'} {g'} {h'} {k'} {hA = hA} {hB} {hC} {hD}
  top back-left back-right front-left front-right bottom c
  is-pb-front-left is-pb-front-right is-pb-back-left =
  is-pullback-left-square-is-pullback-rectangle g k hD
    ( dpair hC (dpair k' front-right))
    ( dpair hA (dpair g' back-right))
    ( is-pb-front-right)
    ( is-pullback-htpy'
      ( h ∘ f)
      { f' = k ∘ g}
      ( bottom)
      ( hD)
      { g' = hD}
      ( htpy-refl hD)
      ( dpair hA (dpair (h' ∘ f')
        ( rectangle-back-left-front-left-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom)))
      { c' = dpair hA (dpair (k' ∘ g')
        ( rectangle-back-right-front-right-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom))}
      ( dpair
        ( htpy-refl _)
        ( dpair top
          ( coherence-htpy-cone-rectangle-bl-fl-rectangle-br-fr-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c)))
      ( is-pullback-rectangle-is-pullback-left-square f h hD
        ( dpair hB (dpair h' front-left))
        ( dpair hA (dpair f' back-left))
        ( is-pb-front-left)
        ( is-pb-back-left)))

descent-is-equiv :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  (c : cone j h B) (d : cone i (pr1 c) A) →
  is-equiv i → is-equiv (pr1 (pr2 d)) →
  is-pullback (j ∘ i) h (cone-comp-horizontal i j h c d) →
  is-pullback j h c
descent-is-equiv i j h c d
  is-equiv-i is-equiv-k is-pb-rectangle =
  is-pullback-is-fiberwise-equiv-fib-square j h c
    ( ind-is-equiv
      ( λ y → is-equiv (fib-square j h c y))
      ( i)
      ( is-equiv-i)
      ( λ x → is-equiv-left-factor
        ( fib-square (j ∘ i) h
          ( cone-comp-horizontal i j h c d) x)
        ( fib-square j h c (i x))
        ( fib-square i (pr1 c) d x)
        ( triangle-fib-square i j h c d x)
        ( is-fiberwise-equiv-fib-square-is-pullback (j ∘ i) h
          ( cone-comp-horizontal i j h c d)
          ( is-pb-rectangle)
          ( x))
        ( is-fiberwise-equiv-fib-square-is-pullback i (pr1 c) d
          ( is-pullback-is-equiv' i (pr1 c) d is-equiv-i is-equiv-k) x)))

coherence-htpy-cone-is-pullback-bottom-is-pullback-top-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
       top back-left back-right front-left front-right bottom) →
  coherence-htpy-cone
    ( front-left)
    ( htpy-refl k)
    ( dpair f'
      ( dpair
        ( g ∘ hA)
        ( rectangle-back-left-bottom-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom)))
    ( dpair f'
      ( dpair
        ( hC ∘ g')
        ( rectangle-top-front-right-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom)))
    ( htpy-refl f')
    ( back-right)
coherence-htpy-cone-is-pullback-bottom-is-pullback-top-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c =
  ( htpy-inv
    ( htpy-assoc
      ( h ·l (htpy-inv back-left))
      ( bottom ·r hA)
      ( (k ·l back-right) ∙h (htpy-refl (k ∘ (hC ∘ g')))))) ∙h
  ( ( htpy-ap-concat'
      ( h ·l (htpy-inv back-left))
      ( htpy-inv (h ·l back-left))
      ( _)
      ( htpy-left-whisk-htpy-inv h back-left)) ∙h
      ( htpy-inv (htpy-inv-con (h ·l back-left) _ _
        ( ( ( htpy-assoc (h ·l back-left) (front-left ·r f') _) ∙h
            ( htpy-assoc
                ( (h ·l back-left) ∙h (front-left ·r f'))
                ( hD ·l top)
                ( (htpy-inv front-right) ·r g') ∙h
              htpy-inv
              ( htpy-con-inv _ (front-right ·r g') _
                ( htpy-inv (c ∙h (htpy-assoc (bottom ·r hA) _ _)))))) ∙h
          ( htpy-inv
            ( htpy-ap-concat (bottom ·r hA) _ _
              ( htpy-right-unit (k ·l back-right))))))))

is-pullback-bottom-is-pullback-top-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
       top back-left back-right front-left front-right bottom) →
  is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
  is-pullback h' k' (dpair f' (dpair g' top)) →
  is-pullback h k (dpair f (dpair g bottom))
is-pullback-bottom-is-pullback-top-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-top =
  descent-is-equiv hB h k
    ( dpair f (dpair g bottom))
    ( dpair f' (dpair hA (htpy-inv (back-left))))
    ( is-equiv-hB)
    ( is-equiv-hA)
    ( is-pullback-htpy
      {f = h ∘ hB}
      ( hD ∘ h')
      ( front-left)
      {g = k}
      ( k)
      ( htpy-refl k)
      { c = dpair f'
        ( dpair
          ( g ∘ hA)
          ( rectangle-back-left-bottom-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom))}
       ( dpair
        ( f')
        ( dpair
          ( hC ∘ g')
          ( rectangle-top-front-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom)))
      ( dpair
        ( htpy-refl f')
        ( dpair
          ( back-right)
          ( coherence-htpy-cone-is-pullback-bottom-is-pullback-top-cube-is-equiv
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c)))
      ( is-pullback-rectangle-is-pullback-left-square
        ( h')
        ( hD)
        ( k)
        ( dpair k' (dpair hC (htpy-inv front-right)))
        ( dpair f' (dpair g' top))
        ( is-pullback-is-equiv' hD k
          ( dpair k' (dpair hC (htpy-inv front-right)))
          ( is-equiv-hD)
          ( is-equiv-hC))
        ( is-pb-top)))
