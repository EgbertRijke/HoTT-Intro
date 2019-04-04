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
      ( (map-equiv h) ∘ (map-equiv (pr2 P))) ~ ((map-equiv (pr2 Q)) ∘ (map-equiv h)))
  
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
    ( λ Y f h → ((map-equiv h) ∘ (map-equiv e)) ~ ((map-equiv f) ∘ (map-equiv h)))
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
  ( Q : X → UU l2) {P : Fam-circle l2} →
  ( e : Eq-Fam-circle P (ev-fam-circle l Q)) →
  Section-Fam-circle l P → (x : X) → Q x
section-fam-circle l dup-circle Q (dpair e H) (dpair p α) =
  inv-is-equiv
    ( dup-circle Q)
    ( dpair (map-equiv e p) ((inv (H p)) ∙ (ap (map-equiv e) α)))

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
  ( ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle)) ∘
    ( succ-ℤ)) ~
  ( ( tr (fundamental-cover-circle l dup-circle) (loop-free-loop l)) ∘
    ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle)))
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
      ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle))
      ( is-equiv-map-equiv (comp-fiber-fundamental-cover-circle l dup-circle))
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
  (y : F) → Id c (dpair x (map-equiv e y))

segment-Σ :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  { x x' : A} (p : Id x x')
  {F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) (y : F) →
  Id (dpair x (map-equiv e y)) (dpair x' (map-equiv e' (map-equiv f y)))
segment-Σ p f e e' H y =
  eq-pair (dpair p (inv (H y)))

pathover-contraction-total-space :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  {x x' : A} (p : Id x x') →
  {F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  (H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  (h : (y : F) → Id c (dpair x (map-equiv e y))) →
  (h' : (y' : F') → Id c (dpair x' (map-equiv e' y'))) →
  UU _
pathover-contraction-total-space c {x} {x'} p f e e' H h h' =
  Id ( tr
       ( contraction-total-space c)
       ( p)
       ( inv-map-equiv (precomp-Π-equiv e (λ y → Id c (dpair x y))) h))
     ( inv-map-equiv (precomp-Π-equiv e' (λ y' → Id c (dpair x' y'))) h')

is-contr-total-pathover-contraction-total-space :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  {x x' : A} (p : Id x x') →
  {F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  (H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  (h : (y : F) → Id c (dpair x (map-equiv e y))) →
  is-contr
    ( Σ ( (y' : F') → Id c (dpair x' (map-equiv e' y')))
        ( pathover-contraction-total-space c p f e e' H h))
is-contr-total-pathover-contraction-total-space
  c {x} {x'} p {F} {F'} f e e' H h =
  is-contr-equiv
    ( Σ ( (y' : F') → Id c (dpair x' (map-equiv e' y')))
        ( Id
          ( map-equiv (precomp-Π-equiv e' (λ y' → Id c (dpair x' y')))
            ( tr (contraction-total-space c) p
              ( inv-map-equiv
                ( precomp-Π-equiv e (λ y → Id c (dpair x y)))
                ( h))))))
    {!!}
    {!!}

pathover-contraction-total-space' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  {x x' : A} (p : Id x x') →
  {F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  (H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  (h : (y : F) → Id c (dpair x (map-equiv e y))) →
  (h' : (y' : F') → Id c (dpair x' (map-equiv e' y'))) →
  UU _
pathover-contraction-total-space' c {x} {x'} p f e e' H h h' =
  ( precomp-Π (map-equiv f) (λ y' → Id c (dpair x' (map-equiv e' y'))) h') ~
  ( postcomp-Π
    ( λ y → concat' (dpair x (map-equiv e y)) (segment-Σ p f e e' H y)) h)

{-
COMPUTE-tr-contraction-total-space :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  { x x' : A} (p : Id x x') → {F : UU l3} {F' : UU l4} (f : F ≃ F')
  ( e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  ( h : contraction-total-space' c x e)
  ( h' : contraction-total-space' c x' e') → UU _
COMPUTE-tr-contraction-total-space c p f e e' H h h' =
  Id {!!}
     ( precomp-Π (map-equiv e') (λ y' → Id c (dpair _ y')) h')
 -}

{- Section 12.4 The dependent universal property of ℤ -}

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
  dpair
    ( elim-ℤ P p0 pS)
    ( dpair
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
reflexive-Eq-ELIM-ℤ P p0 pS (dpair f (dpair p H)) =
  dpair
    ( htpy-refl f)
    ( dpair
      ( inv (right-inv p))
      ( λ k → inv (right-inv (H k))))

Eq-ELIM-ℤ-eq :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → Id s t → Eq-ELIM-ℤ P p0 pS s t
Eq-ELIM-ℤ-eq P p0 pS s .s refl = reflexive-Eq-ELIM-ℤ P p0 pS s

is-equiv-htpy-con-inv :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K : g ~ h) (L : f ~ h) →
  is-equiv (htpy-con-inv H K L)
is-equiv-htpy-con-inv H K L =
  is-equiv-postcomp-Π
    ( λ x → con-inv (H x) (K x) (L x))
    ( λ x → is-equiv-con-inv (H x) (K x) (L x))

is-contr-total-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
  is-contr (Σ ((x : A) → B x) (λ g → g ~ f))
is-contr-total-htpy' {A = A} {B} f =
  is-contr-is-equiv'
    ( Σ ((x : A) → B x) (λ g → f ~ g))
    ( tot (λ g → htpy-inv))
    ( is-equiv-tot-is-fiberwise-equiv (λ g → is-equiv-htpy-inv f g))
    ( is-contr-total-htpy f)

is-contr-total-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s : ELIM-ℤ P p0 pS) → is-contr (Σ (ELIM-ℤ P p0 pS) (Eq-ELIM-ℤ P p0 pS s))
is-contr-total-Eq-ELIM-ℤ P p0 pS s =
  is-contr-total-Eq-structure
    ( λ f t H →
      ( zero-Eq-ELIM-ℤ P p0 pS s (dpair f t) H) ×
      ( succ-Eq-ELIM-ℤ P p0 pS s (dpair f t) H))
    ( is-contr-total-htpy (pr1 s))
    ( dpair (pr1 s) (htpy-refl (pr1 s)))
    ( is-contr-total-Eq-structure
      ( λ p K
        ( q : zero-Eq-ELIM-ℤ P p0 pS s
          ( dpair (pr1 s) (dpair p K))
          ( htpy-refl (pr1 s))) →
        succ-Eq-ELIM-ℤ P p0 pS s
          ( dpair (pr1 s) (dpair p K))
          ( htpy-refl (pr1 s)))
      ( is-contr-is-equiv'
        ( Σ (Id (pr1 s zero-ℤ) p0) (λ α → Id α (pr1 (pr2 s))))
        ( tot (λ α → con-inv refl α (pr1 (pr2 s))))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ α → is-equiv-con-inv refl α (pr1 (pr2 s))))
        ( is-contr-total-path' _ (pr1 (pr2 s))))
      ( dpair (pr1 (pr2 s)) (inv (right-inv (pr1 (pr2 s)))))
      ( is-contr-is-equiv'
        ( Σ ( ( k : ℤ) → Id (pr1 s (succ-ℤ k)) (pr1 (pS k) (pr1 s k)))
            ( λ β → β ~ (pr2 (pr2 s))))
        ( tot (λ β → htpy-con-inv (htpy-refl _) β (pr2 (pr2 s))))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ β → is-equiv-htpy-con-inv (htpy-refl _) β (pr2 (pr2 s))))
        ( is-contr-total-htpy' (pr2 (pr2 s)))))

is-equiv-Eq-ELIM-ℤ-eq :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → is-equiv (Eq-ELIM-ℤ-eq P p0 pS s t)
is-equiv-Eq-ELIM-ℤ-eq P p0 pS s =
  id-fundamental-gen s
    ( reflexive-Eq-ELIM-ℤ P p0 pS s)
    ( is-contr-total-Eq-ELIM-ℤ P p0 pS s)
    ( Eq-ELIM-ℤ-eq P p0 pS s)

eq-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ P p0 pS s t → Id s t
eq-Eq-ELIM-ℤ P p0 pS s t = inv-is-equiv (is-equiv-Eq-ELIM-ℤ-eq P p0 pS s t)

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

universal-property-ℤ :
  { l1 : Level} {X : UU l1} (x : X) (e : X ≃ X) → is-contr (ELIM-ℤ' x e)
universal-property-ℤ {X = X} x e = is-contr-ELIM-ℤ (λ k → X) x (λ k → e)

{- Section 12.5 The identity type of the circle -}

path-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loops X) →
  ( dup-circle : dependent-universal-property-circle (l1 ⊔ (lsuc lzero)) l)
  (k : ℤ) →
  Id {A = Σ X (fundamental-cover-circle l dup-circle)}
     ( dpair
       ( base-free-loop l)
       ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle) k))
     ( dpair
       ( base-free-loop l)
       ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle) (succ-ℤ k)))
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
    ( map-equiv
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
       ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle) k))
contraction-base-fundamental-cover-circle l dup-circle =
  elim-ℤ
    ( λ k →
      Id ( center-total-fundamental-cover-circle l dup-circle)
         ( dpair
           ( base-free-loop l)
           ( map-equiv (comp-fiber-fundamental-cover-circle l dup-circle) k)))
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
       ( map-equiv
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
