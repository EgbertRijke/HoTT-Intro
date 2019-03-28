{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture12 where

import Lecture11
open Lecture11 public

{- Section 12.1 Families over the circle -}

Automorphisms :
  ( l1 : Level) → UU l1 → UU l1
Automorphisms l1 Y = Y ≃ Y

Fam-circle :
  ( l1 : Level) → UU (lsuc l1)
Fam-circle l1 = Σ (UU l1) (Automorphisms l1)

Eq-Fam-circle :
  { l1 : Level} → Fam-circle l1 → Fam-circle l1 → UU l1
Eq-Fam-circle P Q =
  Σ ( (pr1 P) ≃ (pr1 Q))
    ( λ h →
      ( (eqv-map h) ∘ (eqv-map (pr2 P))) ~ ((eqv-map (pr2 Q)) ∘ (eqv-map h)))
  
reflexive-Eq-Fam-circle :
  { l1 : Level} (P : Fam-circle l1) → Eq-Fam-circle P P
reflexive-Eq-Fam-circle (dpair X e) =
  dpair (equiv-id X) (htpy-refl _)

Eq-Fam-circle-eq :
  { l1 : Level} (P Q : Fam-circle l1) → Id P Q → Eq-Fam-circle P Q
Eq-Fam-circle-eq P .P refl = reflexive-Eq-Fam-circle P

is-contr-total-Eq-Fam-circle :
  { l1 : Level} (P : Fam-circle l1) →
  is-contr (Σ (Fam-circle l1) (Eq-Fam-circle P))
is-contr-total-Eq-Fam-circle (dpair X e) =
  is-contr-total-Eq-structure
    ( λ Y f h → ((eqv-map h) ∘ (eqv-map e)) ~ ((eqv-map f) ∘ (eqv-map h)))
    ( is-contr-total-equiv X)
    ( dpair X (equiv-id X))
    ( is-contr-total-htpy-equiv e)

is-equiv-Eq-Fam-circle-eq :
  { l1 : Level} (P Q : Fam-circle l1) → is-equiv (Eq-Fam-circle-eq P Q)
is-equiv-Eq-Fam-circle-eq P =
  id-fundamental-gen P
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
  dpair
    ( P (base-free-loop l))
    ( equiv-tr P (loop-free-loop l))

comparison-fam-circle :
  ( l1 : Level) → free-loops (UU l1) → Fam-circle l1
comparison-fam-circle l1 = tot (λ Y → equiv-eq)

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
    ( dpair (equiv-id _) (htpy-inv (tr-equiv-eq-ap (pr2 l))))

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
  Σ (pr1 P) (λ p → Id (eqv-map (pr2 P) p) p)

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
  ( Q : X → UU l2) {P : Fam-circle l2} →
  ( e : Eq-Fam-circle P (ev-fam-circle l Q)) →
  Section-Fam-circle l P → (x : X) → Q x
section-fam-circle l dup-circle Q (dpair e H) (dpair p α) =
  inv-is-equiv
    ( dup-circle Q)
    ( dpair (eqv-map e p) ((inv (H p)) ∙ (ap (eqv-map e) α)))

{- Section 12.2 The fundamental cover of the circle -}

{- The definition of the fundamental cover -}

{- The fundamental cover -}

Fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l →
  Σ ( X → UU lzero)
    ( λ P → Eq-Fam-circle (dpair ℤ equiv-succ-ℤ) (ev-fam-circle l P))
Fundamental-cover-circle {l1} l dup-circle =
  center
    ( unique-family-property-universal-property-circle l
      ( universal-property-dependent-universal-property-circle l
        ( lower-dependent-universal-property-circle
          {l2 = l1} (lsuc lzero) l dup-circle))
      ( dpair ℤ equiv-succ-ℤ))

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
  ( ( eqv-map (comp-fiber-fundamental-cover-circle l dup-circle)) ∘
    ( succ-ℤ)) ~
  ( ( tr (fundamental-cover-circle l dup-circle) (loop-free-loop l)) ∘
    ( eqv-map (comp-fiber-fundamental-cover-circle l dup-circle)))
comp-tr-fundamental-cover-circle l dup-circle =
   pr2 ( pr2 ( Fundamental-cover-circle l dup-circle))

{- We show that the fundamental cover of the circle is a family of sets. -}

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
      ( eqv-map (comp-fiber-fundamental-cover-circle l dup-circle))
      ( is-equiv-eqv-map (comp-fiber-fundamental-cover-circle l dup-circle))
      ( is-set-ℤ))

{- Contractibility of a general total space -}

contraction-total-space :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} (center : Σ A B) →
  ( x : A) → UU (l1 ⊔ l2)
contraction-total-space {B = B} center x =
  ( y : B x) → Id center (dpair x y)

tr-contraction-total-space :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} (center : Σ A B) →
  { x x' : A} (p : Id x x') →
  ( tr (contraction-total-space center) p) ~
  ( map-equiv-Π
    ( λ (y : B x') → Id center (dpair x' y))
    ( equiv-tr B p)
    ( λ y → equiv-concat' center (lift p y)))
tr-contraction-total-space {B = B} c {x} refl =
  ( htpy-inv (id-map-equiv-Π (λ y → Id c (dpair x y)))) ∙h
  ( htpy-map-equiv-Π-htpy-refl
    ( λ (y : B x) → Id c (dpair x y))
    ( equiv-id _)
    ( λ y → equiv-id (Id c (dpair x y)))
    ( λ y → equiv-concat' c (lift refl y))
    ( λ y q → inv (right-unit q)))

contraction-total-space' :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  (x : A) → {F : UU l3} (e : F ≃ B x) → UU (l1 ⊔ (l2 ⊔ l3))
contraction-total-space' c x {F} e =
  (y : F) → Id c (dpair x (eqv-map e y))

tr-contraction-total-space' :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  { x x' : A} (p : Id x x') → {F : UU l3} {F' : UU l4} (f : F ≃ F')
  ( e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((eqv-map e') ∘ (eqv-map f)) ~ ((tr B p) ∘ (eqv-map e))) →
  ( contraction-total-space' c x e) → (contraction-total-space' c x' e')
tr-contraction-total-space' c {x} {x'} p f e e' H =
  map-equiv-Π
    ( λ y' → Id c (dpair x' (eqv-map e' y')))
    ( f)
    ( λ y → equiv-concat' c (eq-pair (dpair p (inv (H y)))))

square-tr-contraction-total-space' :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  { x x' : A} (p : Id x x') → {F : UU l3} {F' : UU l4} (f : F ≃ F')
  ( e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((eqv-map e') ∘ (eqv-map f)) ~ ((tr B p) ∘ (eqv-map e))) →
  ( ( precomp-Π (eqv-map e') (λ y' → Id c (dpair x' y'))) ∘
    ( tr (contraction-total-space c) p)) ~
  ( ( tr-contraction-total-space' c p f e e' H) ∘
    ( precomp-Π (eqv-map e) (λ y → Id c (dpair x y))))
square-tr-contraction-total-space' c {x} {x'} p f e e' H =
  ( ( precomp-Π (eqv-map e') (λ y' → Id c (dpair x' y'))) ·l
    ( tr-contraction-total-space c p)) ∙h
  {! htpy-refl _!}

{- An elimination principle for ℤ -}

elim-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( k : ℤ) → P k
elim-ℤ P p0 pS (inl zero-ℕ) =
  inv-is-equiv (is-equiv-eqv-map (pS neg-one-ℤ)) p0
elim-ℤ P p0 pS (inl (succ-ℕ x)) =
  inv-is-equiv
    ( is-equiv-eqv-map (pS (inl (succ-ℕ x))))
    ( elim-ℤ P p0 pS (inl x))
elim-ℤ P p0 pS (inr (inl star)) = p0
elim-ℤ P p0 pS (inr (inr zero-ℕ)) = eqv-map (pS zero-ℤ) p0
elim-ℤ P p0 pS (inr (inr (succ-ℕ x))) =
  eqv-map
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
  Id ( elim-ℤ P p0 pS (succ-ℤ k)) (eqv-map (pS k)
     ( elim-ℤ P p0 pS k))
comp-succ-elim-ℤ P p0 pS (inl zero-ℕ) =
  inv
    ( issec-inv-is-equiv
      ( is-equiv-eqv-map (pS (inl zero-ℕ)))
      ( elim-ℤ P p0 pS (succ-ℤ (inl zero-ℕ))))
comp-succ-elim-ℤ P p0 pS (inl (succ-ℕ x)) =
  inv
    ( issec-inv-is-equiv
      ( is-equiv-eqv-map (pS (inl (succ-ℕ x))))
      ( elim-ℤ P p0 pS (succ-ℤ (inl (succ-ℕ x)))))
comp-succ-elim-ℤ P p0 pS (inr (inl star)) = refl
comp-succ-elim-ℤ P p0 pS (inr (inr x)) = refl

path-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l)
  (k : ℤ) →
  Id {A = Σ X (fundamental-cover-circle l dup-circle)}
     ( dpair
       ( base-free-loop l)
       ( eqv-map (comp-fiber-fundamental-cover-circle l dup-circle) k))
     ( dpair
       ( base-free-loop l)
       ( eqv-map (comp-fiber-fundamental-cover-circle l dup-circle) (succ-ℤ k)))
path-total-fundamental-cover-circle l dup-circle k =
  eq-pair
    ( dpair
      ( loop-free-loop l)
      ( inv (comp-tr-fundamental-cover-circle l dup-circle k)))
  

center-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  Σ X (fundamental-cover-circle l dup-circle)
center-total-fundamental-cover-circle l dup-circle =
  dpair
    ( base-free-loop l)
    ( eqv-map
      ( comp-fiber-fundamental-cover-circle l dup-circle) zero-ℤ)

CONTRACTION-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  ( x : X) → UU l1
CONTRACTION-total-fundamental-cover-circle l dup-circle x =
  ( t : fundamental-cover-circle l dup-circle x) →
    Id ( center-total-fundamental-cover-circle l dup-circle)
       ( dpair x t)

contraction-base-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l)
  ( k : ℤ) →
  Id ( center-total-fundamental-cover-circle l dup-circle)
     ( dpair
       ( base-free-loop l)
       ( eqv-map (comp-fiber-fundamental-cover-circle l dup-circle) k))
contraction-base-fundamental-cover-circle l dup-circle =
  elim-ℤ
    ( λ k →
      Id ( center-total-fundamental-cover-circle l dup-circle)
         ( dpair
           ( base-free-loop l)
           ( eqv-map (comp-fiber-fundamental-cover-circle l dup-circle) k)))
    ( refl)
    ( λ k → equiv-concat'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( path-total-fundamental-cover-circle l dup-circle k))


{-

tr-contraction-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  { x y : X} (p : Id x y) →
  ( tr (CONTRACTION-total-fundamental-cover-circle l dup-circle) p) ~
  ( map-equiv-Π
    ( λ t → Id
      ( center-total-fundamental-cover-circle l dup-circle)
      ( dpair y t))
    ( equiv-tr (fundamental-cover-circle l dup-circle) p)
    ( λ t → equiv-concat'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( lift p t)))
tr-contraction-total-fundamental-cover-circle l dup-circle refl = {!htpy-refl _!}

PATH-center-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  ( k : ℤ) → UU l1
PATH-center-total-fundamental-cover-circle l dup-circle k =
  Id ( center-total-fundamental-cover-circle l dup-circle)
     ( dpair
       ( base-free-loop l)
       ( eqv-map
         ( comp-fiber-fundamental-cover-circle l dup-circle) k))

CONTRACTION-total-fundamental-cover-circle' :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  Fam-circle l1
CONTRACTION-total-fundamental-cover-circle' l dup-circle =
  dpair
    ( ( k : ℤ) → PATH-center-total-fundamental-cover-circle l dup-circle k)
    ( automorphism-Π equiv-succ-ℤ
      ( λ k → equiv-concat'
        ( center-total-fundamental-cover-circle l dup-circle)
        ( path-total-fundamental-cover-circle l dup-circle k)))

comp-CONTRACTION-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  Eq-Fam-circle
    ( CONTRACTION-total-fundamental-cover-circle' l dup-circle)
    ( ev-fam-circle l
      ( CONTRACTION-total-fundamental-cover-circle l dup-circle))
comp-CONTRACTION-total-fundamental-cover-circle l dup-circle =
  dpair
    ( equiv-Π
      ( λ t → Id
        ( center-total-fundamental-cover-circle l dup-circle)
        ( dpair (base-free-loop l) t))
      ( comp-fiber-fundamental-cover-circle l dup-circle)
      ( λ k → equiv-id _))
    {!!}  

contraction-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  ( t :
    Σ X (fundamental-cover-circle l dup-circle)) →
  Id (center-total-fundamental-cover-circle l dup-circle) t
contraction-total-fundamental-cover-circle
  {l1} l dup-circle (dpair x' t) =
  section-fam-circle l
    ( lower-dependent-universal-property-circle
      { l2 = lsuc lzero} l1 l dup-circle)
    ( CONTRACTION-total-fundamental-cover-circle l dup-circle)
    { P = CONTRACTION-total-fundamental-cover-circle' l dup-circle}
    ( comp-CONTRACTION-total-fundamental-cover-circle l dup-circle)
    {!!}
    x' t

is-contr-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l) →
  is-contr (Σ X (fundamental-cover-circle l dup-circle))
is-contr-total-fundamental-cover-circle l dup-circle =
  dpair
    ( center-total-fundamental-cover-circle l dup-circle)
    ( contraction-total-fundamental-cover-circle l dup-circle)
-}
