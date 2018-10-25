\begin{code}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture11 where

import Lecture10
open Lecture10 public

-- Section 11.1 Type extensionality

equiv-eq : {i : Level} {A : UU i} {B : UU i} → Id A B → A ≃ B
equiv-eq {A = A} refl = dpair id (is-equiv-id A)

UNIVALENCE : {i : Level} (A B : UU i) → UU (lsuc i)
UNIVALENCE A B = is-equiv (equiv-eq {A = A} {B = B})

is-contr-total-equiv-UNIVALENCE : {i : Level} (A : UU i) →
  ((B : UU i) → UNIVALENCE A B) → is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv-UNIVALENCE A UA =
  id-fundamental-gen' A
    ( dpair id (is-equiv-id A))
    ( λ B → equiv-eq {B = B})
    ( UA)

UNIVALENCE-is-contr-total-equiv : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X)) → (B : UU i) → UNIVALENCE A B
UNIVALENCE-is-contr-total-equiv A c =
  id-fundamental-gen A
    ( dpair id (is-equiv-id A))
    ( c)
    ( λ B → equiv-eq {B = B})

ev-id : {i j : Level} {A : UU i} (P : (B : UU i) → (A ≃ B) → UU j) →
  ((B : UU i) (e : A ≃ B) → P B e) → P A (dpair id (is-equiv-id A))
ev-id {A = A} P f = f A (dpair id (is-equiv-id A))

IND-EQUIV : {i j : Level} {A : UU i} → ((B : UU i) (e : A ≃ B) → UU j) → UU _
IND-EQUIV P = sec (ev-id P)

triangle-ev-id : {i j : Level} {A : UU i}
  (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) →
  (ev-pt (Σ (UU i) (λ X → A ≃ X)) (dpair A (dpair id (is-equiv-id A))) P)
  ~ ((ev-id (λ X e → P (dpair X e))) ∘ (ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P}))
triangle-ev-id P f = refl

IND-EQUIV-is-contr-total-equiv : {i j : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X)) →
  (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) → IND-EQUIV (λ B e → P (dpair B e))
IND-EQUIV-is-contr-total-equiv {i} {j} A c P =
  section-comp
    ( ev-pt (Σ (UU i) (λ X → A ≃ X)) (dpair A (dpair id (is-equiv-id A))) P)
    ( ev-id (λ X e → P (dpair X e)))
    ( ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P})
    ( triangle-ev-id P)
    ( sec-ev-pair (UU i) (λ X → A ≃ X) P)
    ( is-sing-is-contr (Σ (UU i) (λ X → A ≃ X))
      ( dpair
        ( dpair A (dpair id (is-equiv-id A)))
        ( λ t → concat (center c)
          ( inv (contraction c (dpair A (dpair id (is-equiv-id A)))))
          ( contraction c t))) P)

is-contr-total-equiv-IND-EQUIV : {i : Level} (A : UU i) →
  ( {j : Level} (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) →
    IND-EQUIV (λ B e → P (dpair B e))) →
  is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv-IND-EQUIV {i} A ind =
  is-contr-is-sing
    ( Σ (UU i) (λ X → A ≃ X))
    ( dpair A (dpair id (is-equiv-id A)))
    ( λ P → section-comp'
      ( ev-pt (Σ (UU i) (λ X → A ≃ X)) (dpair A (dpair id (is-equiv-id A))) P)
      ( ev-id (λ X e → P (dpair X e)))
      ( ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P})
      ( triangle-ev-id P)
      ( sec-ev-pair (UU i) (λ X → A ≃ X) P)
      ( ind P))

-- The univalence axiom

postulate univalence : {i : Level} (A B : UU i) → UNIVALENCE A B

eq-equiv : {i : Level} (A B : UU i) → (A ≃ B) → Id A B
eq-equiv A B = inv-is-equiv (univalence A B)

is-contr-total-equiv : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv A = is-contr-total-equiv-UNIVALENCE A (univalence A)

Ind-equiv : {i j : Level} (A : UU i) (P : (B : UU i) (e : A ≃ B) → UU j) →
  sec (ev-id P)
Ind-equiv A P =
  IND-EQUIV-is-contr-total-equiv A
   ( is-contr-total-equiv A)
   ( λ t → P (pr1 t) (pr2 t))

ind-equiv : {i j : Level} (A : UU i) (P : (B : UU i) (e : A ≃ B) → UU j) →
  P A (dpair id (is-equiv-id A)) → (B : UU i) (e : A ≃ B) → P B e
ind-equiv A P = pr1 (Ind-equiv A P)

-- Raising universe levels

postulate Raise : {l1 : Level} (l2 : Level) → (A : UU l1) → Σ (UU (l1 ⊔ l2)) (λ X → A ≃ X)

raise : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ l2)
raise l2 A = pr1 (Raise l2 A)

eqv-raise : {l1 : Level} (l2 : Level) (A : UU l1) → A ≃ raise l2 A
eqv-raise l2 A = pr2 (Raise l2 A)

map-raise : {l1 : Level} (l2 : Level) (A : UU l1) → A → raise l2 A
map-raise l2 A = eqv-map (eqv-raise l2 A)

is-equiv-map-raise : {l1 : Level} (l2 : Level) (A : UU l1) →
  is-equiv (map-raise l2 A)
is-equiv-map-raise l2 A = is-equiv-eqv-map (eqv-raise l2 A)

-- Exercises

-- Exercise 11.1

tr-equiv-eq-ap : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A}
  (p : Id x y) → (eqv-map (equiv-eq (ap B p))) ~ tr B p
tr-equiv-eq-ap refl = htpy-refl id

-- Exercise 11.2

is-subtype-is-contr : {l : Level} (X : UU l) → is-prop (is-contr X)
is-subtype-is-contr = {!!}

is-contr-UU-contr : (i : Level) → is-contr (Σ (UU i) is-contr)
is-contr-UU-contr i =
  let UNIT-i = Raise i unit
      unit-i = (pr1 UNIT-i)
      e = pr2 UNIT-i
      f = eqv-map e
      is-equiv-f = is-equiv-eqv-map e
  in 
  dpair
    ( dpair unit-i
      ( is-contr-is-equiv' unit
        ( eqv-map e)
        ( is-equiv-eqv-map e)
        is-contr-unit))
     (λ T → let X = pr1 T
                is-contr-X = pr2 T
            in
       eq-pair (dpair
         ( inv
           ( eq-equiv X unit-i
             ( dpair
               ( f ∘ (const X unit star))
               ( is-equiv-comp
                 ( f ∘ (const X unit star))
                 f
                 (const X unit star)
                 (htpy-refl _)
                 (is-equiv-const-is-contr is-contr-X)
                 is-equiv-f))))
         (center ((is-subtype-is-contr X) _ is-contr-X))))



\end{code}
