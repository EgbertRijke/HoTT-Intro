\begin{code}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture09 where

import Lecture08
open Lecture08 public

-- Section 9.1 Equivalent forms of Function Extensionality.

-- We first define the types Funext, Ind-htpy, and Weak-Funext. 

htpy-eq : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) → (f ~ g)
htpy-eq refl = htpy-refl _

Funext : {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → UU (i ⊔ j)
Funext f = is-fiberwise-equiv (λ g → htpy-eq {f = f} {g = g})

ev-htpy-refl : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f (htpy-refl f)
ev-htpy-refl f C φ = φ f (htpy-refl f)

Ind-htpy : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → UU _
Ind-htpy {l1} {l2} {l3} {A} {B} f =
  (C : (g : (x : A) → B x) → (f ~ g) → UU l3) → sec (ev-htpy-refl f C)

Weak-Funext : {i j : Level} (A : UU i) (B : A → UU j) → UU (i ⊔ j)
Weak-Funext A B = ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)

-- Our goal is now to show that function extensionality holds if and only if the homotopy induction principle is valid, if and only if the weak function extensionality principle holds. This is Theorem 9.1.1 in the notes.

is-contr-total-htpy-Funext : {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → Funext f → is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
is-contr-total-htpy-Funext f funext-f =
  id-fundamental-gen' f (htpy-refl f) (λ g → htpy-eq {g = g}) funext-f

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
  (f : (x : A) → B x) →
  Funext f → Ind-htpy {l3 = l3} f
Ind-htpy-Funext {l3 = l3} {A = A} {B = B} f funext-f C =
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

Funext-Ind-htpy : {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) →
  Ind-htpy {l3 = l1 ⊔ l2} f → Funext f
Funext-Ind-htpy f ind-htpy-f =
  let eq-htpy-f = pr1 (ind-htpy-f (λ h H → Id f h)) refl in
  id-fundamental-sec f (λ h → htpy-eq {g = h}) (λ g → dpair
    ( eq-htpy-f g)
    ( pr1 (ind-htpy-f (λ h H → Id (htpy-eq (eq-htpy-f h H)) H))
      ( ap htpy-eq (pr2 (ind-htpy-f (λ h H → Id f h)) refl)) g))

Weak-Funext-Funext : {l1 l2 : Level} →
  ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → Funext f) →
  ((A : UU l1) (B : A → UU l2) → Weak-Funext A B)
Weak-Funext-Funext funext A B is-contr-B =
  let pi-center = (λ x → center (is-contr-B x)) in
  dpair
    ( pi-center)
    ( λ f → inv-is-equiv (funext A B pi-center f)
      ( λ x → contraction (is-contr-B x) (f x)))

Funext-Weak-Funext : {l1 l2 : Level} →
  ((A : UU l1) (B : A → UU l2) → Weak-Funext A B) →
  ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → Funext f)
Funext-Weak-Funext weak-funext A B f =
  id-fundamental-gen f (htpy-refl f)
    ( is-contr-retract-of
      ( (x : A) → Σ (B x) (λ b → Id (f x) b))
      ( dpair
        ( λ t x → dpair (pr1 t x) (pr2 t x))
        ( dpair (λ t → dpair (λ x → pr1 (t x)) (λ x → pr2 (t x)))
        ( λ t → eq-pair (dpair refl refl))))
      ( weak-funext A
        ( λ x → Σ (B x) (λ b → Id (f x) b))
        ( λ x → is-contr-total-path (B x) (f x))))
    ( λ g → htpy-eq {g = g})

-- From now on we will be assuming that function extensionality holds

postulate funext : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → Funext f

eq-htpy : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) → Id f g
eq-htpy = inv-is-equiv (funext _ _)

issec-eq-htpy : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  ((htpy-eq {f = f} {g = g}) ∘ (eq-htpy {f = f} {g = g})) ~ id
issec-eq-htpy = issec-inv-is-equiv (funext _ _)

isretr-eq-htpy : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  ((eq-htpy {f = f} {g = g}) ∘ (htpy-eq {f = f} {g = g})) ~ id
isretr-eq-htpy = isretr-inv-is-equiv (funext _ _)

is-equiv-eq-htpy : {i j : Level} {A : UU i} {B : A → UU j}
  (f g : (x : A) → B x) → is-equiv (eq-htpy {f = f} {g = g})
is-equiv-eq-htpy f g = is-equiv-inv-is-equiv (funext _ _)

ind-htpy : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → Ind-htpy {l3 = l3} f
ind-htpy f C = Ind-htpy-Funext f (funext f) C

is-contr-Π : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
is-contr-Π {A = A} {B = B} = Weak-Funext-Funext (λ X Y → funext) A B

is-trunc-Π : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
  ((x : A) → is-trunc k (B x)) → is-trunc k ((x : A) → B x)
is-trunc-Π neg-two-𝕋 is-trunc-B = is-contr-Π is-trunc-B
is-trunc-Π (succ-𝕋 k) is-trunc-B f g =
  is-trunc-is-equiv k htpy-eq
    ( funext f g)
    ( is-trunc-Π k (λ x → is-trunc-B x (f x) (g x)))

is-trunc-function-type : {l1 l2 : Level} (k : 𝕋) (A : UU l1) (B : UU l2) →
  is-trunc k B → is-trunc k (A → B)
is-trunc-function-type k A B is-trunc-B =
  is-trunc-Π k {B = λ (x : A) → B} (λ x → is-trunc-B)

\end{code}
