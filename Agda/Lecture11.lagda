\begin{code}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture11 where

import Lecture10
open Lecture10 public

-- Section 11.1 Type extensionality

equiv-eq : {i : Level} (A : UU i) (B : UU i) → Id A B → A ≃ B
equiv-eq A .A refl = dpair id (is-equiv-id A)

UNIVALENCE : {i : Level} (A B : UU i) → UU (lsuc i)
UNIVALENCE A B = is-equiv (equiv-eq A B)

is-contr-total-equiv-UNIVALENCE : {i : Level} (A : UU i) →
  ((B : UU i) → UNIVALENCE A B) → is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv-UNIVALENCE A UA =
  id-fundamental-gen' A
    ( dpair id (is-equiv-id A))
    ( equiv-eq A)
    ( UA)

UNIVALENCE-is-contr-total-equiv : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X)) → (B : UU i) → UNIVALENCE A B
UNIVALENCE-is-contr-total-equiv A c =
  id-fundamental-gen A
    ( dpair id (is-equiv-id A))
    ( c)
    ( equiv-eq A)

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
      (dpair (dpair A (dpair id (is-equiv-id A))) (λ t → concat (center c) (inv (contraction c (dpair A (dpair id (is-equiv-id A))))) (contraction c t))) P)


postulate univalence : {i : Level} (A B : UU i) → UNIVALENCE A B

eq-equiv : {i : Level} (A B : UU i) → (A ≃ B) → Id A B
eq-equiv A B = inv-is-equiv (univalence A B)

is-contr-total-equiv : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv A = is-contr-total-equiv-UNIVALENCE A (univalence A)

\end{code}
