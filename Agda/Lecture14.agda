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

htpy-square-htpy-refl-vertical :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') (g : B → X)
  (p : C → A) {q q' : C → B} (Hq : q ~ q') →
  (H : (f ∘ p) ~ (g ∘ q)) (H' : (f' ∘ p) ~ (g ∘ q')) →
  (H ∙h (g ·l Hq)) ~ ((Hf ·r p) ∙h H') →
  htpy-square Hf (htpy-refl g) (dpair p (dpair q H)) (dpair p (dpair q' H'))
htpy-square-htpy-refl-vertical Hf g p Hq H H' K =
  dpair
    ( htpy-refl p)
    ( dpair Hq (htpy-ap-concat H _ _ (htpy-right-unit (g ·l Hq)) ∙h K))

htpy-square-htpy-refl-horizontal :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) {g g' : B → X} (Hg : g ~ g')
  {p p' : C → A} (Hp : p ~ p') (q : C → B)
  (H : (f ∘ p) ~ (g ∘ q)) (H' : (f ∘ p') ~ (g' ∘ q)) →
  ((H ∙h (Hg ·r q)) ~ ((f ·l Hp) ∙h H')) →
  htpy-square (htpy-refl f) Hg (dpair p (dpair q H)) (dpair p' (dpair q H'))
htpy-square-htpy-refl-horizontal f Hg Hp q H H' K =
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
coherence-cube-rotate-240 f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c =
  ( htpy-ap-concat
     ( (hD ·l top) ∙h ((htpy-inv front-right) ·r g')) _ _
     ( htpy-left-whisk-htpy-inv k back-right)) ∙h
  ( htpy-inv
    ( htpy-con-inv _
      ( htpy-left-whisk k back-right)
      ( (hD ·l top) ∙h ((htpy-inv front-right) ·r g'))
      ( htpy-con-inv _ (front-right ·r g') (hD ·l top)
        ( htpy-inv
          ( ( ( htpy-inv-con
                ( front-left ·r f')
                ( hD ·l top) _
                ( ( ( htpy-inv-con
                      ( h ·l back-left)
                      ( (front-left ·r f') ∙h (hD ·l top)) _
                      ( ( htpy-assoc
                            ( h ·l back-left)
                            ( front-left ·r f')
                            ( hD ·l top)) ∙h
                          c)) ∙h
                    ( htpy-ap-concat'
                      ( htpy-inv (h ·l back-left))
                      ( h ·l (htpy-inv back-left)) _
                      ( htpy-inv (htpy-left-whisk-htpy-inv h back-left)))) ∙h
                  ( htpy-assoc
                    ( h ·l (htpy-inv back-left))
                    ( bottom ·r hA)
                    ( (k ·l back-right) ∙h (front-right ·r g'))))) ∙h
              ( htpy-assoc
                ( (htpy-inv front-left) ·r f')
                ( (h ·l (htpy-inv back-left)) ∙h ( bottom ·r hA))
                ( (k ·l back-right) ∙h (front-right ·r g')))) ∙h
            ( htpy-assoc _ (k ·l back-right) (front-right ·r g')))))))

{- 
  We show that a reflection through the plane spanned by the vertices
  A', A, and D of a commuting cube again commutes.

  Note: Since the vertices A' and D must always be fixed, the vertex A
  determines the mirror symmetry.
-}

coherence-cube-mirror-A :
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
coherence-cube-mirror-A f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c =
  ( htpy-ap-concat
    ( (k ·l back-right) ∙h (front-right ·r g')) _ _
    ( htpy-left-whisk-htpy-inv hD top)) ∙h
  ( htpy-inv-con
    ( bottom ·r hA) _
    ( (h ·l back-left) ∙h (front-left ·r f'))
    ( ( htpy-assoc
        ( bottom ·r hA)
        ( (k ·l back-right) ∙h (front-right ·r g'))
        ( htpy-inv (hD ·l top))) ∙h
      ( htpy-inv
        ( htpy-con-inv
          ( (h ·l back-left) ∙h (front-left ·r f'))
          ( hD ·l top)
          ( (bottom ·r hA) ∙h ((k ·l back-right) ∙h (front-right ·r g')))
          ( c)))))

coherence-cube-mirror-B :
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
  coherence-cube hB h' h hD hA g' g hC f' f k' k
  back-right (htpy-inv back-left) top bottom (htpy-inv front-right) front-left
coherence-cube-mirror-B f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c =
  ( htpy-inv
    ( htpy-assoc
      ( h ·l (htpy-inv back-left))
      ( bottom ·r hA)
      ( k ·l back-right))) ∙h
  ( ( ( htpy-ap-concat' _ _
        ( (bottom ·r hA) ∙h (k ·l back-right))
        ( htpy-left-whisk-htpy-inv h back-left)) ∙h
      ( htpy-con-inv _
        ( front-right ·r g')
        ( (front-left ·r f') ∙h (hD ·l top))
        ( ( htpy-inv
            ( htpy-assoc (htpy-inv (h ·l back-left)) _ (front-right ·r g'))) ∙h
          ( htpy-inv
            ( htpy-inv-con (h ·l back-left) _ _
              ( ( htpy-assoc (h ·l back-left) (front-left ·r f') (hD ·l top)) ∙h
                ( c ∙h
                  ( htpy-assoc
                    ( bottom ·r hA)
                    ( k ·l back-right)
                    ( front-right ·r g'))))))))) ∙h
    ( htpy-inv
      ( htpy-assoc
        ( front-left ·r f')
        ( hD ·l top)
        ( (htpy-inv front-right) ·r g'))))

coherence-cube-mirror-C :
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
  coherence-cube k' hC hD k f' hA hB f g' h' g h
  (htpy-inv back-left) (htpy-inv top) (htpy-inv back-right)
  (htpy-inv front-left) (htpy-inv bottom) (htpy-inv front-right)
coherence-cube-mirror-C f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c =
  ( htpy-ap-concat
    ( (hD ·l (htpy-inv top)) ∙h ((htpy-inv front-left) ·r f')) _ _
    ( htpy-left-whisk-htpy-inv h back-left)) ∙h
  ( ( htpy-ap-concat' _ _
      ( htpy-inv (h ·l back-left))
      ( htpy-ap-concat' _ _
        ( (htpy-inv front-left) ·r f')
        ( htpy-left-whisk-htpy-inv hD top))) ∙h
    ( ( ( htpy-ap-concat' _ _
          ( htpy-inv (h ·l back-left))
          ( htpy-inv (htpy-inv-assoc (front-left ·r f') (hD ·l top)))) ∙h
        ( ( htpy-inv
            ( htpy-inv-assoc
              ( h ·l back-left)
              ( (front-left ·r f') ∙h (hD ·l top)))) ∙h
          ( ( ( htpy-ap-inv
                ( ( htpy-assoc
                    ( h ·l back-left)
                    ( front-left ·r f')
                    ( hD ·l top)) ∙h
                  ( ( c) ∙h
                    ( htpy-assoc
                      ( bottom ·r hA)
                      ( k ·l back-right)
                      ( front-right ·r g'))))) ∙h
              ( htpy-inv-assoc _ (front-right ·r g'))) ∙h
            ( htpy-ap-concat (htpy-inv (front-right ·r g')) _ _
              ( htpy-inv-assoc (bottom ·r hA) (k ·l back-right)))))) ∙h
      ( htpy-ap-concat ((htpy-inv front-right) ·r g') _ _
        ( htpy-ap-concat' _ _
          ( (htpy-inv bottom) ·r hA)
          ( htpy-inv (htpy-left-whisk-htpy-inv k back-right))))))

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

coherence-htpy-square-rectangle-bl-fl-rectangle-br-fr-cube : 
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
  coherence-htpy-square
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
coherence-htpy-square-rectangle-bl-fl-rectangle-br-fr-cube
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
coherence-htpy-square-rectangle-top-fl-rectangle-br-bot-cube : 
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
  coherence-htpy-square
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
coherence-htpy-square-rectangle-top-fl-rectangle-br-bot-cube = {!!}
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
          ( coherence-htpy-square-rectangle-bl-fl-rectangle-br-fr-cube
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
          ( coherence-htpy-square-rectangle-bl-fl-rectangle-br-fr-cube
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
        ( fib-square-comp-horizontal i j h c d x)
        ( is-fiberwise-equiv-fib-square-is-pullback (j ∘ i) h
          ( cone-comp-horizontal i j h c d)
          ( is-pb-rectangle)
          ( x))
        ( is-fiberwise-equiv-fib-square-is-pullback i (pr1 c) d
          ( is-pullback-is-equiv' i (pr1 c) d is-equiv-i is-equiv-k) x)))

coherence-htpy-square-is-pullback-bottom-is-pullback-top-cube-is-equiv :
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
  coherence-htpy-square
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
coherence-htpy-square-is-pullback-bottom-is-pullback-top-cube-is-equiv
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
          ( coherence-htpy-square-is-pullback-bottom-is-pullback-top-cube-is-equiv
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

is-pullback-top-is-pullback-bottom-cube-is-equiv :
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
  is-pullback h k (dpair f (dpair g bottom)) →
  is-pullback h' k' (dpair f' (dpair g' top))
is-pullback-top-is-pullback-bottom-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-bottom =
  is-pullback-top-is-pullback-rectangle h hD k'
    ( dpair hB (dpair h' front-left))
    ( dpair f' (dpair g' top))
    ( is-pullback-is-equiv h hD
      ( dpair hB (dpair h' front-left))
      is-equiv-hD is-equiv-hB)
    ( is-pullback-htpy' h (htpy-refl h) (k ∘ hC) front-right
      ( cone-comp-vertical h k hC
        ( dpair f (dpair g bottom))
        ( dpair hA (dpair g' back-right)))
      { c' = cone-comp-vertical h hD k'
        ( dpair hB (dpair h' front-left))
        ( dpair f' (dpair g' top))}
      ( dpair back-left
        ( dpair
          ( htpy-refl g')
          ( ( ( ( htpy-inv
                  ( htpy-assoc
                    ( bottom ·r hA) (k ·l back-right) (front-right ·r g'))) ∙h
                ( htpy-inv c)) ∙h
              ( htpy-inv
                ( htpy-assoc
                  ( h ·l back-left) (front-left ·r f') (hD ·l top)))) ∙h
            ( htpy-ap-concat' _ _ ((front-left ·r f') ∙h (hD ·l top))
              ( htpy-inv (htpy-right-unit (h ·l back-left)))))))
      ( is-pullback-rectangle-is-pullback-top h k hC
        ( dpair f (dpair g bottom))
        ( dpair hA (dpair g' back-right))
        ( is-pb-bottom)
        ( is-pullback-is-equiv g hC
          ( dpair hA (dpair g' back-right))
          is-equiv-hC is-equiv-hA)))

is-pullback-front-left-is-pullback-back-right-cube-is-equiv :
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
  is-equiv f' → is-equiv f → is-equiv k' → is-equiv k →
  is-pullback g hC (dpair hA (dpair g' back-right)) →
  is-pullback h hD (dpair hB (dpair h' front-left))
is-pullback-front-left-is-pullback-back-right-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right =
  is-pullback-bottom-is-pullback-top-cube-is-equiv
    hB h' h hD hA g' g hC f' f k' k
    back-right (htpy-inv back-left) top bottom (htpy-inv front-right) front-left
    ( coherence-cube-mirror-B f g h k f' g' h' k' hA hB hC hD top
      back-left back-right front-left front-right bottom c)
    is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right

is-pullback-front-right-is-pullback-back-left-cube-is-equiv :
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
  is-equiv g' → is-equiv h' → is-equiv g → is-equiv h →
  is-pullback f hB (dpair hA (dpair f' back-left)) →
  is-pullback k hD (dpair hC (dpair k' front-right))
is-pullback-front-right-is-pullback-back-left-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-g' is-equiv-h' is-equiv-g is-equiv-h is-pb-back-left =
  is-pullback-bottom-is-pullback-top-cube-is-equiv
    hC k' k hD hA f' f hB g' g h' h
    back-left (htpy-inv back-right) (htpy-inv top)
    ( htpy-inv bottom) (htpy-inv front-left) front-right
    ( coherence-cube-rotate-120 f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom c)
    is-equiv-g' is-equiv-g is-equiv-h' is-equiv-h is-pb-back-left

-- Section 14.2 Fiberwise pullbacks.

{- We show that if we have a square of families, such that the base square is
   a pullback square, then each square of fibers is a pullback square if and
   only if the square of total spaces is a pullback square. -}

cone-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  cone f g C → (C → UU l8) → UU (l4 ⊔ (l5 ⊔ (l6 ⊔ (l7 ⊔ l8))))
cone-family {C = C} PX f' g' c PC =
  (x : C) →
  cone ((tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x))) (g' (pr1 (pr2 c) x)) (PC x)

tot-cone-cone-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) → cone-family PX f' g' c PC →
  cone (toto PX f f') (toto PX g g') (Σ C PC)
tot-cone-cone-family PX f' g' c c' =
  dpair
    ( toto _ (pr1 c) (λ x → pr1 (c' x)))
    ( dpair
      ( toto _ (pr1 (pr2 c)) (λ x → (pr1 (pr2 (c' x)))))
      ( λ t → eq-pair
         ( dpair
           ( pr2 (pr2 c) (pr1 t))
           ( pr2 (pr2 (c' (pr1 t))) (pr2 t)))))

map-canpb-tot-cone-cone-fam-right-factor :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) →
  Σ ( canonical-pullback f g)
    ( λ t → canonical-pullback ((tr PX (π₃ t)) ∘ (f' (π₁ t))) (g' (π₂ t))) →
  Σ ( Σ A PA)
    ( λ aa' → Σ (Σ B (λ b → Id (f (pr1 aa')) (g b)))
      ( λ bα → Σ (PB (pr1 bα))
        ( λ b' → Id
          ( tr PX (pr2 bα) (f' (pr1 aa') (pr2 aa')))
          ( g' (pr1 bα) b'))))
map-canpb-tot-cone-cone-fam-right-factor
  {X = X} {A} {B} {C} PX {PA} {PB} {PC} {f} {g} f' g' c c' =
  swap-total-Eq-structure
    ( λ a → Σ B (λ b → Id (f a) (g b)))
    ( PA)
    ( λ a bα a' → Σ (PB (pr1 bα))
      ( λ b' → Id (tr PX (pr2 bα) (f' a a')) (g' (pr1 bα) b')))

map-canpb-tot-cone-cone-fam-left-factor :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) → (aa' : Σ A PA) →
  Σ (Σ B (λ b → Id (f (pr1 aa')) (g b)))
    ( λ bα → Σ (PB (pr1 bα))
      ( λ b' → Id
        ( tr PX (pr2 bα) (f' (pr1 aa') (pr2 aa')))
        ( g' (pr1 bα) b'))) →
  Σ ( Σ B PB)
    ( λ bb' → Σ (Id (f (pr1 aa')) (g (pr1 bb')))
      ( λ α → Id (tr PX α (f' (pr1 aa') (pr2 aa'))) (g' (pr1 bb') (pr2 bb'))))
map-canpb-tot-cone-cone-fam-left-factor
  {X = X} {A} {B} {C} PX {PA} {PB} {PC} {f} {g} f' g' c c' aa' =
  ( swap-total-Eq-structure
    ( λ b → Id (f (pr1 aa')) (g b))
      ( PB)
      ( λ b α b' → Id (tr PX α (f' (pr1 aa') (pr2 aa'))) (g' b b')))

map-canonical-pullback-tot-cone-cone-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) →
  Σ ( canonical-pullback f g)
    ( λ t → canonical-pullback ((tr PX (π₃ t)) ∘ (f' (π₁ t))) (g' (π₂ t))) →
  canonical-pullback (toto PX f f') (toto PX g g')
map-canonical-pullback-tot-cone-cone-family
  {X = X} {A} {B} {C} PX {PA} {PB} {PC} {f} {g} f' g' c c' =
  ( tot (λ aa' →
    ( tot (λ bb' → eq-pair)) ∘
    ( map-canpb-tot-cone-cone-fam-left-factor PX f' g' c c' aa'))) ∘
  ( map-canpb-tot-cone-cone-fam-right-factor PX f' g' c c')
  
is-equiv-map-canonical-pullback-tot-cone-cone-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) →
  is-equiv (map-canonical-pullback-tot-cone-cone-family PX f' g' c c')
is-equiv-map-canonical-pullback-tot-cone-cone-family
  {X = X} {A} {B} {C} PX {PA} {PB} {PC} {f} {g} f' g' c c' =
  is-equiv-comp
    ( map-canonical-pullback-tot-cone-cone-family PX f' g' c c')
    ( tot (λ aa' →
      ( tot (λ bb' → eq-pair)) ∘
      ( map-canpb-tot-cone-cone-fam-left-factor PX f' g' c c' aa')))
    ( map-canpb-tot-cone-cone-fam-right-factor PX f' g' c c')
    ( htpy-refl _)
    ( is-equiv-swap-total-Eq-structure
      ( λ a → Σ B (λ b → Id (f a) (g b)))
      ( PA)
      ( λ a bα a' → Σ (PB (pr1 bα))
        ( λ b' → Id (tr PX (pr2 bα) (f' a a')) (g' (pr1 bα) b'))))
    ( is-equiv-tot-is-fiberwise-equiv (λ aa' → is-equiv-comp
      ( ( tot (λ bb' → eq-pair)) ∘
        ( map-canpb-tot-cone-cone-fam-left-factor PX f' g' c c' aa'))
      ( tot (λ bb' → eq-pair))
      ( map-canpb-tot-cone-cone-fam-left-factor PX f' g' c c' aa')
      ( htpy-refl _)
      ( is-equiv-swap-total-Eq-structure _ _ _)
      ( is-equiv-tot-is-fiberwise-equiv (λ bb' → is-equiv-eq-pair'
        ( dpair (f (pr1 aa')) (f' (pr1 aa') (pr2 aa')))
        ( dpair (g (pr1 bb')) (g' (pr1 bb') (pr2 bb')))))))

triangle-canonical-pullback-tot-cone-cone-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) →
  ( gap (toto PX f f') (toto PX g g') (tot-cone-cone-family PX f' g' c c')) ~
  ( ( map-canonical-pullback-tot-cone-cone-family PX f' g' c c') ∘
    ( toto _
      ( gap f g c)
      ( λ x → gap
        ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
        ( g' (pr1 (pr2 c) x))
        ( c' x))))
triangle-canonical-pullback-tot-cone-cone-family PX f' g' c c' (dpair x y) =
  refl

is-pullback-family-is-pullback-tot :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) →
  is-pullback f g c →
  is-pullback
    (toto PX f f') (toto PX g g') (tot-cone-cone-family PX f' g' c c') →
  (x : C) →
  is-pullback
    ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
    ( g' (pr1 (pr2 c) x))
    ( c' x)
is-pullback-family-is-pullback-tot
  PX {PA} {PB} {PC} {f} {g} f' g' c c' is-pb-c is-pb-tot =
  is-fiberwise-equiv-is-equiv-toto-is-equiv-base-map _
    ( gap f g c)
    ( λ x → gap
      ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
      ( g' (pr1 (pr2 c) x))
      ( c' x))
    ( is-pb-c)
    ( is-equiv-right-factor
      ( gap (toto PX f f') (toto PX g g') (tot-cone-cone-family PX f' g' c c'))
      ( map-canonical-pullback-tot-cone-cone-family PX f' g' c c')
      ( toto _
        ( gap f g c)
        ( λ x → gap
          ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
          ( g' (pr1 (pr2 c) x))
          ( c' x)))
      ( triangle-canonical-pullback-tot-cone-cone-family PX f' g' c c')
      ( is-equiv-map-canonical-pullback-tot-cone-cone-family PX f' g' c c')
      ( is-pb-tot)) 

is-pullback-tot-is-pullback-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  (c : cone f g C) (c' : cone-family PX f' g' c PC) →
  is-pullback f g c →
  ( (x : C) →
    is-pullback
      ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
      ( g' (pr1 (pr2 c) x))
      ( c' x)) →
  is-pullback
    (toto PX f f') (toto PX g g') (tot-cone-cone-family PX f' g' c c')
is-pullback-tot-is-pullback-family
  PX {PA} {PB} {PC} {f} {g} f' g' c c' is-pb-c is-pb-c' =
  is-equiv-comp
    ( gap (toto PX f f') (toto PX g g') (tot-cone-cone-family PX f' g' c c'))
    ( map-canonical-pullback-tot-cone-cone-family PX f' g' c c')
    ( toto _
      ( gap f g c)
      ( λ x → gap
        ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
        ( g' (pr1 (pr2 c) x))
        ( c' x)))
    ( triangle-canonical-pullback-tot-cone-cone-family PX f' g' c c')
    ( is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map _
      ( gap f g c)
      ( λ x → gap
        ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
        ( g' (pr1 (pr2 c) x))
        ( c' x))
        ( is-pb-c)
        ( is-pb-c'))
    ( is-equiv-map-canonical-pullback-tot-cone-cone-family PX f' g' c c')

{- We show that identity types commute with pullbacks. -}

cone-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) (c1 c2 : C) →
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  cone
    ( λ (α : Id (p c1) (p c2)) → (ap f α) ∙ (H c2))
    ( λ (β : Id (q c1) (q c2)) → (H c1) ∙ (ap g β))
    ( Id c1 c2)
cone-ap f g (dpair p (dpair q H)) c1 c2 =
  dpair
    ( ap p)
    ( dpair
      ( ap q)
      ( λ γ →
        ( ap (λ t → t ∙ (H c2)) (inv (ap-comp f p γ))) ∙
        ( ( inv (htpy-nat H γ)) ∙
          ( ap (λ t → (H c1) ∙ t) (ap-comp g q γ)))))

tr-id-right :
  {l1 : Level} {A : UU l1} {a b c : A} (q : Id b c) (p : Id a b) →
  Id (tr (λ y → Id a y) q p) (p ∙ q)
tr-id-right refl refl = refl

cone-ap' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) (c1 c2 : C) →
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  cone
    ( λ (α : Id (p c1) (p c2)) → tr (λ t → Id (f (p c1)) t) (H c2) (ap f α))
    ( λ (β : Id (q c1) (q c2)) → (H c1) ∙ (ap g β))
    ( Id c1 c2)
cone-ap' f g (dpair p (dpair q H)) c1 c2 =
  dpair
    ( ap p)
    ( dpair
      ( ap q)
      ( λ γ →
        ( tr-id-right (H c2) (ap f (ap p γ))) ∙
        ( ( ap (λ t → t ∙ (H c2)) (inv (ap-comp f p γ))) ∙
          ( ( inv (htpy-nat H γ)) ∙
            ( ap (λ t → (H c1) ∙ t) (ap-comp g q γ))))))

is-pullback-cone-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) → is-pullback f g c →
  (c1 c2 : C) →
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  is-pullback
    ( λ (α : Id (p c1) (p c2)) → (ap f α) ∙ (H c2))
    ( λ (β : Id (q c1) (q c2)) → (H c1) ∙ (ap g β))
    ( cone-ap f g c c1 c2)
is-pullback-cone-ap f g (dpair p (dpair q H)) is-pb-c c1 c2 =
  is-pullback-htpy'
    ( λ α → tr (λ x → Id (f (p c1)) x) (H c2) (ap f α))
    ( λ α → tr-id-right (H c2) (ap f α))
    ( λ β → (H c1) ∙ (ap g β))
    ( htpy-refl _)
    ( cone-ap' f g (dpair p (dpair q H)) c1 c2)
    { c' = cone-ap f g (dpair p (dpair q H)) c1 c2}
    ( dpair (htpy-refl _) (dpair (htpy-refl _) (htpy-right-unit _)))
    ( is-pullback-family-is-pullback-tot
      ( λ x → Id (f (p c1)) x)
      ( λ a → ap f {x = p c1} {y = a})
      ( λ b β → (H c1) ∙ (ap g β))
      ( dpair p (dpair q H))
      ( cone-ap' f g (dpair p (dpair q H)) c1)
      ( is-pb-c)
      ( is-pullback-is-equiv
        ( toto _ f (λ a α → ap f α))
        ( toto _ g (λ b β → (H c1) ∙ (ap g β)))
        ( tot-cone-cone-family
          ( Id (f (p c1)))
          ( λ a → ap f)
          ( λ b β → (H c1) ∙ (ap g β))
          ( dpair p (dpair q H))
          ( cone-ap' f g (dpair p (dpair q H)) c1))
        ( is-equiv-is-contr _
          ( is-contr-total-path _ (q c1))
          ( is-contr-total-path _ (f (p c1))))
        ( is-equiv-is-contr _
          ( is-contr-total-path _ c1)
          ( is-contr-total-path _ (p c1))))
      ( c2))

{- Next we show that for any commuting cube, if the bottom and top squares are
   pullback squares, then so is the square of fibers of the vertical maps in
   cube. -}

{-
square-fib-cube :
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
  (a : A) →
  ( ( tot (λ d' p → p ∙ (bottom a)) ∘
      ( fib-square h hD (dpair hB (dpair h' front-left)) (f a))) ∘
    ( fib-square f hB (dpair hA (dpair f' back-left)) a)) ~
  ( ( fib-square k hD (dpair hC (dpair k' front-right)) (g a)) ∘
    ( fib-square g hC (dpair hA (dpair g' back-right)) a))
square-fib-cube f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  .(hA a') (dpair a' refl) =
  eq-pair
    ( dpair
      ( top a')
      ( ( tr-id-left-subst
          ( top a')
          ( k (g (hA a')))
          ( ( ( inv (front-left (f' a'))) ∙
              ( ap h ((inv (back-left a')) ∙ refl))) ∙
            ( bottom (hA a')))) ∙
        ( ( ( assoc (inv (ap hD (top a'))) _ (bottom (hA a'))) ∙
            {!!}) ∙
          ( inv-assoc (ap k (back-right a')) (front-right (g' a')) ∙
            ( ( ap
                ( concat _ (inv (front-right (g' a'))))
                ( inv (ap-inv k (back-right a')))) ∙
              ( ap
                ( concat (k (hC (g' a'))) (inv (front-right (g' a'))))
                ( ap (ap k) (inv (right-unit (inv (back-right a')))))))))))
-}
