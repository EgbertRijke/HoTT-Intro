\begin{code}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture09 where

import Lecture08
open Lecture08 public

htpy-eq : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) → (f ~ g)
htpy-eq refl = htpy-refl _

Funext : {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → UU (i ⊔ j)
Funext f = is-fiberwise-equiv (λ g → htpy-eq {f = f} {g = g})

is-contr-total-htpy-Funext : {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → Funext f → is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
is-contr-total-htpy-Funext f funext-f =
  id-fundamental-gen' f (htpy-refl f) (λ g → htpy-eq {g = g}) funext-f

ev-htpy-refl : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f (htpy-refl f)
ev-htpy-refl f C φ = φ f (htpy-refl f)

Ind-htpy : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
Ind-htpy f C = sec (ev-htpy-refl f C)

ev-pair : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((t : Σ A B) → C t) → (x : A) (y : B x) → C (dpair x y)
ev-pair f x y = f (dpair x y)

sec-ev-pair : {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2)
  (C : Σ A B → UU l3) → sec (ev-pair {A = A} {B = B} {C = C})
sec-ev-pair A B C =
  dpair (λ f → ind-Σ f) (λ f → refl)

triangle-ev-htpy-refl : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C :  Σ ((x : A) → B x) (λ g → f ~ g) → UU l3) →
    ev-pt (Σ ((x : A) → B x) (λ g → f ~ g)) (dpair f (htpy-refl f)) C ~
    ((ev-htpy-refl f (λ x y → C (dpair x y))) ∘ (ev-pair {C = C}))
triangle-ev-htpy-refl f C φ = refl

Ind-htpy-Funext : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  Funext f → Ind-htpy f C
Ind-htpy-Funext {l3 = l3} {A = A} {B = B} f C funext-f =
  let total-C = λ t → C (pr1 t) (pr2 t) in
  section-comp
    ( ev-pt
      ( Σ ((x : A) → B x) (λ g → f ~ g))
      ( dpair f (htpy-refl f))
      ( total-C))
    ( ev-htpy-refl f C)
    ( ev-pair)
    ( triangle-ev-htpy-refl f total-C)
    ( sec-ev-pair ((x : A) → B x) (λ g → f ~ g) total-C)
    ( sec-ev-pt-is-contr
      ( Σ ((x : A) → B x) (λ g → f ~ g))
      ( is-contr-total-htpy-Funext f funext-f)
      ( total-C))

postulate funext : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → Funext f

ind-htpy : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  Ind-htpy f C
ind-htpy f C = Ind-htpy-Funext f C (funext f)

\end{code}
