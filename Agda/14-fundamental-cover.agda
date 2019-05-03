{-# OPTIONS --without-K --exact-split #-}

module 14-fundamental-cover where

import 13-circle
open 13-circle public

{- Section 12.1 Families over the circle -}

Aut :
  { l1 : Level} → UU l1 → UU l1
Aut Y = Y ≃ Y

Fam-circle :
  ( l1 : Level) → UU (lsuc l1)
Fam-circle l1 = Σ (UU l1) Aut

Eq-Fam-circle :
  { l1 : Level} → Fam-circle l1 → Fam-circle l1 → UU l1
Eq-Fam-circle P Q =
  Σ ( (pr1 P) ≃ (pr1 Q))
    ( λ h →
      ( (map-equiv h) ∘ (map-equiv (pr2 P))) ~ ((map-equiv (pr2 Q)) ∘ (map-equiv h)))
  
reflexive-Eq-Fam-circle :
  { l1 : Level} (P : Fam-circle l1) → Eq-Fam-circle P P
reflexive-Eq-Fam-circle (pair X e) =
  pair (equiv-id X) htpy-refl

Eq-Fam-circle-eq :
  { l1 : Level} (P Q : Fam-circle l1) → Id P Q → Eq-Fam-circle P Q
Eq-Fam-circle-eq P .P refl = reflexive-Eq-Fam-circle P

abstract
  is-contr-total-Eq-Fam-circle :
    { l1 : Level} (P : Fam-circle l1) →
    is-contr (Σ (Fam-circle l1) (Eq-Fam-circle P))
  is-contr-total-Eq-Fam-circle (pair X e) =
    is-contr-total-Eq-structure
      ( λ Y f h →
        ((map-equiv h) ∘ (map-equiv e)) ~ ((map-equiv f) ∘ (map-equiv h)))
      ( is-contr-total-equiv X)
      ( pair X (equiv-id X))
    ( is-contr-total-htpy-equiv e)

abstract
  is-equiv-Eq-Fam-circle-eq :
    { l1 : Level} (P Q : Fam-circle l1) → is-equiv (Eq-Fam-circle-eq P Q)
  is-equiv-Eq-Fam-circle-eq P =
    fundamental-theorem-id P
      ( reflexive-Eq-Fam-circle P)
      ( is-contr-total-Eq-Fam-circle P)
      ( Eq-Fam-circle-eq P)

eq-Eq-Fam-circle :
  { l1 : Level} (P Q : Fam-circle l1) → Eq-Fam-circle P Q → Id P Q
eq-Eq-Fam-circle P Q = inv-is-equiv (is-equiv-Eq-Fam-circle-eq P Q)

ev-fam-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
  ( X → UU l2) → Fam-circle l2
ev-fam-circle l P =
  pair
    ( P (base-free-loop l))
    ( equiv-tr P (loop-free-loop l))

comparison-fam-circle :
  ( l1 : Level) → free-loops (UU l1) → Fam-circle l1
comparison-fam-circle l1 = tot (λ Y → equiv-eq)

abstract
  is-equiv-comparison-fam-circle :
    ( l1 : Level) → is-equiv (comparison-fam-circle l1)
  is-equiv-comparison-fam-circle l1 =
    is-equiv-tot-is-fiberwise-equiv (λ Y → univalence Y Y)

triangle-comparison-fam-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
  (ev-fam-circle l) ~ ((comparison-fam-circle l2) ∘ (ev-free-loop l (UU l2)))
triangle-comparison-fam-circle l P =
  eq-Eq-Fam-circle
    ( ev-fam-circle l P)
    ( comparison-fam-circle _ (ev-free-loop l (UU _) P))
    ( pair (equiv-id _) (htpy-inv (tr-equiv-eq-ap (pr2 l))))

abstract
  is-equiv-ev-fam-circle-universal-property-circle :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X)
    ( up-circle : universal-property-circle (lsuc l2) l) →
    is-equiv (ev-fam-circle {l2 = l2} l)
  is-equiv-ev-fam-circle-universal-property-circle {l2 = l2} l up-circle =
    is-equiv-comp
      ( ev-fam-circle l)
      ( comparison-fam-circle l2)
      ( ev-free-loop l (UU l2))
      ( triangle-comparison-fam-circle l)
      ( up-circle (UU l2))
      ( is-equiv-comparison-fam-circle l2)

unique-family-property-circle :
  { l1 : Level} (l2 : Level) {X : UU l1} (l : free-loops X) →
  UU (l1 ⊔ (lsuc l2))
unique-family-property-circle l2 {X} l =
  ( Q : Fam-circle l2) →
    is-contr (Σ (X → UU l2) (λ P → Eq-Fam-circle Q (ev-fam-circle l P)))

abstract
  unique-family-property-universal-property-circle :
    { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
    universal-property-circle (lsuc l2) l → unique-family-property-circle l2 l
  unique-family-property-universal-property-circle l up-circle Q =
    is-contr-is-equiv'
      ( fib (ev-fam-circle l) Q)
      ( tot (λ P → (Eq-Fam-circle-eq Q (ev-fam-circle l P)) ∘ inv))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ P →
          is-equiv-comp' _ _
            ( is-equiv-inv _ _)
            ( is-equiv-Eq-Fam-circle-eq Q (ev-fam-circle l P))))
      ( is-contr-map-is-equiv
        ( is-equiv-ev-fam-circle-universal-property-circle l up-circle)
        ( Q))

Section-Fam-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) (P : Fam-circle l2) → UU _
Section-Fam-circle l P =
  Σ (pr1 P) (λ p → Id (map-equiv (pr2 P) p) p)

fam-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
  ( dependent-universal-property-circle (lsuc l2) l) →
  Fam-circle l2 → X → UU l2
fam-circle {l1} {l2} l dup-circle =
  inv-is-equiv
    ( is-equiv-ev-fam-circle-universal-property-circle l
      ( universal-property-dependent-universal-property-circle l dup-circle))

section-fam-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle l2 l) →
  ( Q : X → UU l2) (P : Fam-circle l2) →
  ( e : Eq-Fam-circle P (ev-fam-circle l Q)) →
  Section-Fam-circle l P → (x : X) → Q x
section-fam-circle l dup-circle Q P (pair e H) (pair p α) =
  inv-is-equiv
    ( dup-circle Q)
    ( pair (map-equiv e p) ((inv (H p)) ∙ (ap (map-equiv e) α)))

{- Section 12.2 The fundamental cover of the circle -}

{- The definition of the fundamental cover -}

{- The fundamental cover -}

abstract
  Fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loops X) →
    dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l →
    Σ ( X → UU lzero)
      ( λ P → Eq-Fam-circle (pair ℤ equiv-succ-ℤ) (ev-fam-circle l P))
  Fundamental-cover-circle {l1} l dup-circle =
    center
      ( unique-family-property-universal-property-circle l
        ( universal-property-dependent-universal-property-circle l
          ( lower-dependent-universal-property-circle
            {l2 = l1} (lsuc lzero) l dup-circle))
        ( pair ℤ equiv-succ-ℤ))
  
  fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loops X) →
    dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l →
    X → UU lzero
  fundamental-cover-circle l dup-circle =
    pr1 (Fundamental-cover-circle l dup-circle)
    
  comp-fiber-fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loops X) →
    ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
    ℤ ≃ fundamental-cover-circle l dup-circle (base-free-loop l)
  comp-fiber-fundamental-cover-circle l dup-circle =
    pr1 ( pr2 ( Fundamental-cover-circle l dup-circle))
  
  comp-tr-fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loops X) →
    ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
    ( ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle)) ∘
      ( succ-ℤ)) ~
    ( ( tr (fundamental-cover-circle l dup-circle) (loop-free-loop l)) ∘
      ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle)))
  comp-tr-fundamental-cover-circle l dup-circle =
    pr2 ( pr2 ( Fundamental-cover-circle l dup-circle))

{- We show that the fundamental cover of the circle is a family of sets. -}

abstract
  is-set-fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loops X) →
    ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
    ( x : X) → is-set (fundamental-cover-circle l dup-circle x)
  is-set-fundamental-cover-circle l dup-circle =
    is-connected-circle' l
      ( lower-dependent-universal-property-circle lzero l dup-circle)
      ( λ x → is-set (fundamental-cover-circle l dup-circle x))
      ( λ x → is-prop-is-set (fundamental-cover-circle l dup-circle x))
      ( is-trunc-is-equiv' zero-𝕋 ℤ
        ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle))
        ( is-equiv-map-equiv (comp-fiber-fundamental-cover-circle l dup-circle))
        ( is-set-ℤ))

{- Contractibility of a general total space -}

contraction-total-space :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} (center : Σ A B) →
  ( x : A) → UU (l1 ⊔ l2)
contraction-total-space {B = B} center x =
  ( y : B x) → Id center (pair x y)

path-total-path-fiber :
  { l1 l2 : Level} {A : UU l1} (B : A → UU l2) (x : A) →
  { y y' : B x} (q : Id y' y) → Id {A = Σ A B} (pair x y) (pair x y')
path-total-path-fiber B x q = eq-pair refl (inv q)

tr-path-total-path-fiber :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) (x : A) →
  { y y' : B x} (q : Id y' y) (α : Id c (pair x y')) →
  Id ( tr (λ z → Id c (pair x z)) q α)
     ( α ∙ (inv (path-total-path-fiber B x q)))
tr-path-total-path-fiber c x refl α = inv right-unit

segment-Σ :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  { x x' : A} (p : Id x x')
  { F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) (y : F) →
  Id (pair x (map-equiv e y)) (pair x' (map-equiv e' (map-equiv f y)))
segment-Σ refl f e e' H y = path-total-path-fiber _ _ (H y)

contraction-total-space' :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  ( x : A) → {F : UU l3} (e : F ≃ B x) → UU (l1 ⊔ (l2 ⊔ l3))
contraction-total-space' c x {F} e =
  ( y : F) → Id c (pair x (map-equiv e y))

equiv-tr-contraction-total-space' :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  { x x' : A} (p : Id x x') →
  { F : UU l3} {F' : UU l4} (f : F ≃ F') (e : F ≃ B x) (e' : F' ≃ B x') →
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  ( contraction-total-space' c x' e') ≃ (contraction-total-space' c x e)
equiv-tr-contraction-total-space' c p f e e' H =
  ( postcomp-Π-equiv
    ( λ y → equiv-concat' c (inv (segment-Σ p f e e' H y)))) ∘e
  ( precomp-Π-equiv f _)

equiv-contraction-total-space :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  ( x : A) → {F : UU l3} (e : F ≃ B x) →
  ( contraction-total-space c x) ≃ (contraction-total-space' c x e)
equiv-contraction-total-space c x e =
  precomp-Π-equiv e (λ y → Id c (pair x y))

tr-path-total-tr-coherence :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) (x : A) →
  { F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x)
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ (map-equiv e)) →
  (y : F) (α : Id c (pair x (map-equiv e' (map-equiv f y)))) →
  Id ( tr (λ z → Id c (pair x z)) (H y) α)
     ( α ∙ (inv (segment-Σ refl f e e' H y)))
tr-path-total-tr-coherence c x f e e' H y α =
  tr-path-total-path-fiber c x (H y) α

square-tr-contraction-total-space :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  { x x' : A} (p : Id x x')
  { F : UU l3} {F' : UU l4} (f : F ≃ F') (e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e)))
  (h : contraction-total-space c x) →
  ( map-equiv
    ( ( equiv-tr-contraction-total-space' c p f e e' H) ∘e
      ( ( equiv-contraction-total-space c x' e') ∘e
        ( equiv-tr (contraction-total-space c) p)))
    ( h)) ~
  ( map-equiv (equiv-contraction-total-space c x e) h)
square-tr-contraction-total-space c refl f e e' H h y =
  ( inv (tr-path-total-tr-coherence c _ f e e' H y
    ( h (map-equiv e' (map-equiv f y))))) ∙
  ( apd h (H y))

path-over-contraction-total-space' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  {x x' : A} (p : Id x x') →
  {F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  (H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  (h : (y : F) → Id c (pair x (map-equiv e y))) →
  (h' : (y' : F') → Id c (pair x' (map-equiv e' y'))) →
  UU _
path-over-contraction-total-space' c {x} {x'} p {F} {F'} f e e' H h h' =
  ( postcomp-Π
    ( λ y → concat' c (segment-Σ p f e e' H y)) h) ~
  ( precomp-Π
    ( map-equiv f)
    ( λ y' → Id c (pair x' (map-equiv e' y')))
    ( h'))

map-path-over-contraction-total-space' :
    { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
    { x x' : A} (p : Id x x') →
    { F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
    ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
    ( h : contraction-total-space' c x e) →
    ( h' : contraction-total-space' c x' e') →
    ( path-over-contraction-total-space' c p f e e' H h h') →
    ( path-over (contraction-total-space c) p
      ( inv-map-equiv (equiv-contraction-total-space c x e) h)
      ( inv-map-equiv (equiv-contraction-total-space c x' e') h'))
map-path-over-contraction-total-space' c {x} {.x} refl f e e' H h h' α =
  inv-map-equiv
    ( equiv-ap
      ( ( equiv-tr-contraction-total-space' c refl f e e' H) ∘e
        ( equiv-contraction-total-space c x e'))
      ( inv-map-equiv (equiv-contraction-total-space c x e) h)
      ( inv-map-equiv (equiv-contraction-total-space c x e') h'))
    ( ( ( eq-htpy
          ( square-tr-contraction-total-space c refl f e e' H
            ( inv-map-equiv (equiv-contraction-total-space c x e) h))) ∙
        ( issec-inv-is-equiv
          ( is-equiv-map-equiv (equiv-contraction-total-space c x e))
          ( h))) ∙ 
      ( ( eq-htpy
          ( htpy-con-inv h
            ( segment-Σ refl f e e' H)
            ( precomp-Π
              ( map-equiv f)
              ( λ y' → Id c (pair x (map-equiv e' y')))
              ( h'))
            ( α))) ∙
        ( inv
          ( ap
            ( map-equiv (equiv-tr-contraction-total-space' c refl f e e' H))
            ( issec-inv-is-equiv
              ( is-equiv-map-equiv
                ( precomp-Π-equiv e' (λ y' → Id c (pair x y'))))
              ( h'))))))

equiv-path-over-contraction-total-space' :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  { x x' : A} (p : Id x x') →
  { F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  ( h : contraction-total-space' c x e) →
  ( h' : contraction-total-space' c x' e') →
  ( path-over (contraction-total-space c) p
    ( inv-map-equiv (equiv-contraction-total-space c x e) h)
    ( inv-map-equiv (equiv-contraction-total-space c x' e') h')) ≃
  ( path-over-contraction-total-space' c p f e e' H h h')
equiv-path-over-contraction-total-space' c {x} {.x} refl f e e' H h h' =
  ( inv-equiv
    ( equiv-htpy-con-inv h
      ( segment-Σ refl f e e' H)
      ( precomp-Π
        ( map-equiv f)
        ( λ y' → Id c (pair x (map-equiv e' y')))
        ( h')))) ∘e
  ( ( equiv-funext) ∘e
    ( ( equiv-concat' h
        ( ap
          ( map-equiv (equiv-tr-contraction-total-space' c refl f e e' H))
          ( issec-inv-is-equiv
            ( is-equiv-map-equiv
              ( precomp-Π-equiv e' (λ y' → Id c (pair x y'))))
            ( h')))) ∘e
      ( ( equiv-concat
          ( inv
            ( ( eq-htpy
                ( square-tr-contraction-total-space c refl f e e' H
                  ( inv-map-equiv (equiv-contraction-total-space c x e) h))) ∙
              ( issec-inv-is-equiv
                ( is-equiv-map-equiv (equiv-contraction-total-space c x e))
                ( h))))
          ( map-equiv
            ( ( equiv-tr-contraction-total-space' c refl f e e' H) ∘e
              ( ( equiv-contraction-total-space c x e') ∘e
                ( inv-equiv (equiv-contraction-total-space c x e'))))
            ( h'))) ∘e
        ( equiv-ap
          ( ( equiv-tr-contraction-total-space' c refl f e e' H) ∘e
            ( equiv-contraction-total-space c x e'))
          ( inv-map-equiv (equiv-contraction-total-space c x e) h)
          ( inv-map-equiv (equiv-contraction-total-space c x e') h')))))

{- We use the above construction to provide sufficient conditions for the total
   space of the fundamental cover to be contractible. -}

center-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  Σ X (fundamental-cover-circle l dup-circle)
center-total-fundamental-cover-circle l dup-circle =
  pair
    ( base-free-loop l)
    ( map-equiv
      ( comp-fiber-fundamental-cover-circle l dup-circle) zero-ℤ)

path-over-loop-contraction-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  ( h : contraction-total-space'
        ( center-total-fundamental-cover-circle l dup-circle)
        ( base-free-loop l)
        ( comp-fiber-fundamental-cover-circle l dup-circle)) →
  ( p : path-over-contraction-total-space'
        ( center-total-fundamental-cover-circle l dup-circle)
        ( loop-free-loop l)
        ( equiv-succ-ℤ)
        ( comp-fiber-fundamental-cover-circle l dup-circle)
        ( comp-fiber-fundamental-cover-circle l dup-circle)
        ( comp-tr-fundamental-cover-circle l dup-circle)
        ( h)
        ( h)) →
  path-over
    ( contraction-total-space
      ( center-total-fundamental-cover-circle l dup-circle))
    ( pr2 l)
    ( inv-map-equiv
      ( equiv-contraction-total-space
        ( center-total-fundamental-cover-circle l dup-circle)
        ( base-free-loop l)
        ( comp-fiber-fundamental-cover-circle l dup-circle))
      ( h))
    ( inv-map-equiv
      ( equiv-contraction-total-space
        ( center-total-fundamental-cover-circle l dup-circle)
        ( base-free-loop l)
        ( comp-fiber-fundamental-cover-circle l dup-circle))
      ( h))
path-over-loop-contraction-total-fundamental-cover-circle l dup-circle h p =
  map-path-over-contraction-total-space'
    ( center-total-fundamental-cover-circle l dup-circle)
    ( loop-free-loop l)
    ( equiv-succ-ℤ)
    ( comp-fiber-fundamental-cover-circle l dup-circle)
    ( comp-fiber-fundamental-cover-circle l dup-circle)
    ( comp-tr-fundamental-cover-circle l dup-circle)
    ( h)
    ( h)
    ( p)

contraction-total-fundamental-cover-circle-data :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  ( h : contraction-total-space'
        ( center-total-fundamental-cover-circle l dup-circle)
        ( base-free-loop l)
        ( comp-fiber-fundamental-cover-circle l dup-circle)) →
  ( p : path-over-contraction-total-space'
        ( center-total-fundamental-cover-circle l dup-circle)
        ( loop-free-loop l)
        ( equiv-succ-ℤ)
        ( comp-fiber-fundamental-cover-circle l dup-circle)
        ( comp-fiber-fundamental-cover-circle l dup-circle)
        ( comp-tr-fundamental-cover-circle l dup-circle)
        ( h)
        ( h)) →
  ( t : Σ X (fundamental-cover-circle l dup-circle)) →
  Id (center-total-fundamental-cover-circle l dup-circle) t
contraction-total-fundamental-cover-circle-data
  {l1} l dup-circle h p (pair x y) =
  inv-is-equiv
    ( lower-dependent-universal-property-circle
      { l2 = lsuc lzero} l1 l dup-circle
      ( contraction-total-space
        ( center-total-fundamental-cover-circle l dup-circle)))
    ( pair
      ( inv-map-equiv
        ( equiv-contraction-total-space
          ( center-total-fundamental-cover-circle l dup-circle)
          ( base-free-loop l)
          ( comp-fiber-fundamental-cover-circle l dup-circle))
        ( h))
      ( path-over-loop-contraction-total-fundamental-cover-circle
        l dup-circle h p))
    x y

is-contr-total-fundamental-cover-circle-data :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  ( h : contraction-total-space'
        ( center-total-fundamental-cover-circle l dup-circle)
        ( base-free-loop l)
        ( comp-fiber-fundamental-cover-circle l dup-circle)) →
  ( p : path-over-contraction-total-space'
        ( center-total-fundamental-cover-circle l dup-circle)
        ( loop-free-loop l)
        ( equiv-succ-ℤ)
        ( comp-fiber-fundamental-cover-circle l dup-circle)
        ( comp-fiber-fundamental-cover-circle l dup-circle)
        ( comp-tr-fundamental-cover-circle l dup-circle)
        ( h)
        ( h)) →
  is-contr (Σ X (fundamental-cover-circle l dup-circle))
is-contr-total-fundamental-cover-circle-data l dup-circle h p =
  pair
    ( center-total-fundamental-cover-circle l dup-circle)
    ( contraction-total-fundamental-cover-circle-data l dup-circle h p)

{- Section 12.4 The dependent universal property of ℤ -}

abstract
  elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( k : ℤ) → P k
  elim-ℤ P p0 pS (inl zero-ℕ) =
    inv-is-equiv (is-equiv-map-equiv (pS neg-one-ℤ)) p0
  elim-ℤ P p0 pS (inl (succ-ℕ x)) =
    inv-is-equiv
      ( is-equiv-map-equiv (pS (inl (succ-ℕ x))))
      ( elim-ℤ P p0 pS (inl x))
  elim-ℤ P p0 pS (inr (inl star)) = p0
  elim-ℤ P p0 pS (inr (inr zero-ℕ)) = map-equiv (pS zero-ℤ) p0
  elim-ℤ P p0 pS (inr (inr (succ-ℕ x))) =
    map-equiv
      ( pS (inr (inr x)))
      ( elim-ℤ P p0 pS (inr (inr x)))
  
  comp-zero-elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    Id (elim-ℤ P p0 pS zero-ℤ) p0
  comp-zero-elim-ℤ P p0 pS = refl
  
  comp-succ-elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) (k : ℤ) →
    Id ( elim-ℤ P p0 pS (succ-ℤ k)) (map-equiv (pS k)
      ( elim-ℤ P p0 pS k))
  comp-succ-elim-ℤ P p0 pS (inl zero-ℕ) =
    inv
      ( issec-inv-is-equiv
        ( is-equiv-map-equiv (pS (inl zero-ℕ)))
        ( elim-ℤ P p0 pS (succ-ℤ (inl zero-ℕ))))
  comp-succ-elim-ℤ P p0 pS (inl (succ-ℕ x)) =
    inv
      ( issec-inv-is-equiv
        ( is-equiv-map-equiv (pS (inl (succ-ℕ x))))
        ( elim-ℤ P p0 pS (succ-ℤ (inl (succ-ℕ x)))))
  comp-succ-elim-ℤ P p0 pS (inr (inl star)) = refl
  comp-succ-elim-ℤ P p0 pS (inr (inr x)) = refl
  
ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) → UU l1
ELIM-ℤ P p0 pS =
  Σ ( (k : ℤ) → P k) (λ f →
    ( ( Id (f zero-ℤ) p0) ×
      ( (k : ℤ) → Id (f (succ-ℤ k)) ((map-equiv (pS k)) (f k)))))


Elim-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) → ELIM-ℤ P p0 pS
Elim-ℤ P p0 pS =
  pair
    ( elim-ℤ P p0 pS)
    ( pair
      ( comp-zero-elim-ℤ P p0 pS)
      ( comp-succ-elim-ℤ P p0 pS))

equiv-comparison-map-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (k : ℤ) →
  Id ((pr1 s) k) ((pr1 t) k) ≃ Id ((pr1 s) (succ-ℤ k)) ((pr1 t) (succ-ℤ k))
equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t k =
  ( ( equiv-concat (pr2 (pr2 s) k) (pr1 t (succ-ℤ k))) ∘e
    ( equiv-concat' (map-equiv (pS k) (pr1 s k)) (inv (pr2 (pr2 t) k)))) ∘e
  ( equiv-ap (pS k) (pr1 s k) (pr1 t k))

zero-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (H : (pr1 s) ~ (pr1 t)) → UU l1
zero-Eq-ELIM-ℤ P p0 pS s t H =
  Id (H zero-ℤ) ((pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))

succ-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (H : (pr1 s) ~ (pr1 t)) → UU l1
succ-Eq-ELIM-ℤ P p0 pS s t H =
  ( k : ℤ) → Id
    ( H (succ-ℤ k))
    ( map-equiv (equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t k) (H k))

Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → UU l1
Eq-ELIM-ℤ P p0 pS s t =
  ELIM-ℤ
    ( λ k → Id (pr1 s k) (pr1 t k))
    ( (pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))
    ( equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t)

reflexive-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ P p0 pS s s
reflexive-Eq-ELIM-ℤ P p0 pS (pair f (pair p H)) =
  pair
    ( htpy-refl)
    ( pair
      ( inv (right-inv p))
      ( λ k → inv (right-inv (H k))))

Eq-ELIM-ℤ-eq :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → Id s t → Eq-ELIM-ℤ P p0 pS s t
Eq-ELIM-ℤ-eq P p0 pS s .s refl = reflexive-Eq-ELIM-ℤ P p0 pS s

abstract
  is-contr-total-htpy' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    is-contr (Σ ((x : A) → B x) (λ g → g ~ f))
  is-contr-total-htpy' {A = A} {B} f =
    is-contr-is-equiv'
      ( Σ ((x : A) → B x) (λ g → f ~ g))
      ( tot (λ g → htpy-inv))
      ( is-equiv-tot-is-fiberwise-equiv (λ g → is-equiv-htpy-inv f g))
      ( is-contr-total-htpy f)

abstract
  is-contr-total-Eq-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( s : ELIM-ℤ P p0 pS) → is-contr (Σ (ELIM-ℤ P p0 pS) (Eq-ELIM-ℤ P p0 pS s))
  is-contr-total-Eq-ELIM-ℤ P p0 pS s =
    is-contr-total-Eq-structure
      ( λ f t H →
        ( zero-Eq-ELIM-ℤ P p0 pS s (pair f t) H) ×
        ( succ-Eq-ELIM-ℤ P p0 pS s (pair f t) H))
      ( is-contr-total-htpy (pr1 s))
      ( pair (pr1 s) htpy-refl)
      ( is-contr-total-Eq-structure
        ( λ p K
          ( q : zero-Eq-ELIM-ℤ P p0 pS s
            ( pair (pr1 s) (pair p K))
            ( htpy-refl)) →
          succ-Eq-ELIM-ℤ P p0 pS s
            ( pair (pr1 s) (pair p K))
            ( htpy-refl))
        ( is-contr-is-equiv'
          ( Σ (Id (pr1 s zero-ℤ) p0) (λ α → Id α (pr1 (pr2 s))))
             ( tot (λ α → con-inv refl α (pr1 (pr2 s))))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ α → is-equiv-con-inv refl α (pr1 (pr2 s))))
          ( is-contr-total-path' (pr1 (pr2 s))))
        ( pair (pr1 (pr2 s)) (inv (right-inv (pr1 (pr2 s)))))
        ( is-contr-is-equiv'
          ( Σ ( ( k : ℤ) → Id (pr1 s (succ-ℤ k)) (pr1 (pS k) (pr1 s k)))
              ( λ β → β ~ (pr2 (pr2 s))))
          ( tot (λ β → htpy-con-inv htpy-refl β (pr2 (pr2 s))))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ β → is-equiv-htpy-con-inv htpy-refl β (pr2 (pr2 s))))
          ( is-contr-total-htpy' (pr2 (pr2 s)))))

abstract
  is-equiv-Eq-ELIM-ℤ-eq :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( s t : ELIM-ℤ P p0 pS) → is-equiv (Eq-ELIM-ℤ-eq P p0 pS s t)
  is-equiv-Eq-ELIM-ℤ-eq P p0 pS s =
    fundamental-theorem-id s
      ( reflexive-Eq-ELIM-ℤ P p0 pS s)
      ( is-contr-total-Eq-ELIM-ℤ P p0 pS s)
      ( Eq-ELIM-ℤ-eq P p0 pS s)

eq-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ P p0 pS s t → Id s t
eq-Eq-ELIM-ℤ P p0 pS s t = inv-is-equiv (is-equiv-Eq-ELIM-ℤ-eq P p0 pS s t)

abstract
  is-prop-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    is-prop (ELIM-ℤ P p0 pS)
  is-prop-ELIM-ℤ P p0 pS =
    is-prop-is-prop'
      ( λ s t → eq-Eq-ELIM-ℤ P p0 pS s t
        ( Elim-ℤ
          ( λ k → Id (pr1 s k) (pr1 t k))
          ( (pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))
          ( equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t)))

-- We finally arrive at the dependent universal property of ℤ

abstract
  is-contr-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    is-contr (ELIM-ℤ P p0 pS)
  is-contr-ELIM-ℤ P p0 pS =
    is-contr-is-prop-inh (is-prop-ELIM-ℤ P p0 pS) (Elim-ℤ P p0 pS)

-- The universal property of ℤ is now just a special case

ELIM-ℤ' :
  { l1 : Level} {X : UU l1} (x : X) (e : X ≃ X) → UU l1
ELIM-ℤ' {X = X} x e = ELIM-ℤ (λ k → X) x (λ k → e)

abstract
  universal-property-ℤ :
    { l1 : Level} {X : UU l1} (x : X) (e : X ≃ X) → is-contr (ELIM-ℤ' x e)
  universal-property-ℤ {X = X} x e = is-contr-ELIM-ℤ (λ k → X) x (λ k → e)

{- Section 12.5 The identity type of the circle -}

path-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l)
  (k : ℤ) →
  Id {A = Σ X (fundamental-cover-circle l dup-circle)}
     ( pair
       ( base-free-loop l)
       ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle) k))
     ( pair
       ( base-free-loop l)
       ( map-equiv
         ( comp-fiber-fundamental-cover-circle l dup-circle)
         ( succ-ℤ k)))
path-total-fundamental-cover-circle l dup-circle k =
  segment-Σ
    ( loop-free-loop l)
    ( equiv-succ-ℤ)
    ( comp-fiber-fundamental-cover-circle l dup-circle)
    ( comp-fiber-fundamental-cover-circle l dup-circle)
    ( comp-tr-fundamental-cover-circle l dup-circle)
    k

CONTRACTION-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  UU l1
CONTRACTION-fundamental-cover-circle l dup-circle =
  ELIM-ℤ
    ( λ k →
      Id ( center-total-fundamental-cover-circle l dup-circle)
         ( pair
           ( base-free-loop l)
           ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle) k)))
    ( refl)
    ( λ k → equiv-concat'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( path-total-fundamental-cover-circle l dup-circle k))

Contraction-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  CONTRACTION-fundamental-cover-circle l dup-circle
Contraction-fundamental-cover-circle l dup-circle =
  Elim-ℤ
    ( λ k →
      Id ( center-total-fundamental-cover-circle l dup-circle)
         ( pair
           ( base-free-loop l)
           ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle) k)))
    ( refl)
    ( λ k → equiv-concat'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( path-total-fundamental-cover-circle l dup-circle k))

abstract
  is-contr-total-fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loops X) →
    ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
    is-contr (Σ X (fundamental-cover-circle l dup-circle))
  is-contr-total-fundamental-cover-circle l dup-circle =
    is-contr-total-fundamental-cover-circle-data l dup-circle
      ( pr1 (Contraction-fundamental-cover-circle l dup-circle))
      ( htpy-inv
        ( pr2 (pr2 (Contraction-fundamental-cover-circle l dup-circle))))

pt-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  fundamental-cover-circle l dup-circle (base-free-loop l)
pt-fundamental-cover-circle l dup-circle =
  map-equiv (comp-fiber-fundamental-cover-circle l dup-circle) zero-ℤ

fundamental-cover-circle-eq :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  ( x : X) → Id (base-free-loop l) x → fundamental-cover-circle l dup-circle x
fundamental-cover-circle-eq l dup-circle .(base-free-loop l) refl =
  pt-fundamental-cover-circle l dup-circle

abstract
  is-equiv-fundamental-cover-circle-eq :
    { l1 : Level} {X : UU l1} (l : free-loops X) →
    ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
    ( x : X) → is-equiv (fundamental-cover-circle-eq l dup-circle x)
  is-equiv-fundamental-cover-circle-eq l dup-circle =
    fundamental-theorem-id
      ( base-free-loop l)
      ( pt-fundamental-cover-circle l dup-circle)
      ( is-contr-total-fundamental-cover-circle l dup-circle)
      ( fundamental-cover-circle-eq l dup-circle)

equiv-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  ( x : X) →
  ( Id (base-free-loop l) x) ≃ (fundamental-cover-circle l dup-circle x)
equiv-fundamental-cover-circle l dup-circle x =
  pair
    ( fundamental-cover-circle-eq l dup-circle x)
    ( is-equiv-fundamental-cover-circle-eq l dup-circle x)

comp-loop-space-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  ( Id (base-free-loop l) (base-free-loop l)) ≃ ℤ
comp-loop-space-circle l dup-circle =
  ( inv-equiv (comp-fiber-fundamental-cover-circle l dup-circle)) ∘e
  ( equiv-fundamental-cover-circle l dup-circle (base-free-loop l))
