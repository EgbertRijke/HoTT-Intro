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

FUNEXT : {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → UU (i ⊔ j)
FUNEXT f = is-fiberwise-equiv (λ g → htpy-eq {f = f} {g = g})

ev-htpy-refl : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f (htpy-refl f)
ev-htpy-refl f C φ = φ f (htpy-refl f)

IND-HTPY : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → UU _
IND-HTPY {l1} {l2} {l3} {A} {B} f =
  (C : (g : (x : A) → B x) → (f ~ g) → UU l3) → sec (ev-htpy-refl f C)

WEAK-FUNEXT : {i j : Level} (A : UU i) (B : A → UU j) → UU (i ⊔ j)
WEAK-FUNEXT A B = ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)

-- Our goal is now to show that function extensionality holds if and only if the homotopy induction principle is valid, if and only if the weak function extensionality principle holds. This is Theorem 9.1.1 in the notes.

is-contr-total-htpy-Funext : {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → FUNEXT f → is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
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

IND-HTPY-FUNEXT : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) →
  FUNEXT f → IND-HTPY {l3 = l3} f
IND-HTPY-FUNEXT {l3 = l3} {A = A} {B = B} f funext-f C =
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

abstract
  FUNEXT-IND-HTPY : {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    (f : (x : A) → B x) → IND-HTPY {l3 = l1 ⊔ l2} f → FUNEXT f
  FUNEXT-IND-HTPY f ind-htpy-f =
    let eq-htpy-f = pr1 (ind-htpy-f (λ h H → Id f h)) refl in
    id-fundamental-sec f (λ h → htpy-eq {g = h}) (λ g → dpair
      ( eq-htpy-f g)
      ( pr1 (ind-htpy-f (λ h H → Id (htpy-eq (eq-htpy-f h H)) H))
        ( ap htpy-eq (pr2 (ind-htpy-f (λ h H → Id f h)) refl)) g))

abstract
  WEAK-FUNEXT-FUNEXT : {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f) →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B)
  WEAK-FUNEXT-FUNEXT funext A B is-contr-B =
    let pi-center = (λ x → center (is-contr-B x)) in
    dpair
      ( pi-center)
      ( λ f → inv-is-equiv (funext A B pi-center f)
        ( λ x → contraction (is-contr-B x) (f x)))

abstract
  FUNEXT-WEAK-FUNEXT : {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B) →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f)
  FUNEXT-WEAK-FUNEXT weak-funext A B f =
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

postulate funext : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → FUNEXT f

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

{-
The immediate proof of the following theorem would be

  is-contr-total-htpy-Funext f (funext f)

We give a different proof to ensure that the center of contraction is the 
expected thing: 

  dpair f (htpy-refl f)

-}

is-contr-total-htpy : {i j : Level} {A : UU i} {B : A → UU j}
  (f : (x : A) → B x) → is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
is-contr-total-htpy f =
  dpair
    ( dpair f (htpy-refl f))
    ( λ t → concat
      ( center (is-contr-total-htpy-Funext f (funext f)))
      ( inv (contraction
        ( is-contr-total-htpy-Funext f (funext f))
        ( dpair f (htpy-refl f))))
      ( contraction (is-contr-total-htpy-Funext f (funext f)) t))

is-contr-total-htpy-nondep : {i j : Level} {A : UU i} {B : UU j}
  (f : A → B) → is-contr (Σ (A → B) (λ g → f ~ g))
is-contr-total-htpy-nondep {B = B} f = is-contr-total-htpy-Funext {B = λ x → B} f (funext f)

Ind-htpy : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → IND-HTPY {l3 = l3} f
Ind-htpy f = IND-HTPY-FUNEXT f (funext f)

ind-htpy : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  C f (htpy-refl f) → (g : (x : A) → B x) (H : f ~ g) → C g H
ind-htpy f C = pr1 (Ind-htpy f C)

abstract
  is-contr-Π : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
  is-contr-Π {A = A} {B = B} = WEAK-FUNEXT-FUNEXT (λ X Y → funext) A B

abstract
  is-trunc-Π : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-trunc k (B x)) → is-trunc k ((x : A) → B x)
  is-trunc-Π neg-two-𝕋 is-trunc-B = is-contr-Π is-trunc-B
  is-trunc-Π (succ-𝕋 k) is-trunc-B f g =
    is-trunc-is-equiv k htpy-eq
      ( funext f g)
      ( is-trunc-Π k (λ x → is-trunc-B x (f x) (g x)))

abstract
  is-trunc-function-type : {l1 l2 : Level} (k : 𝕋) (A : UU l1) (B : UU l2) →
    is-trunc k B → is-trunc k (A → B)
  is-trunc-function-type k A B is-trunc-B =
    is-trunc-Π k {B = λ (x : A) → B} (λ x → is-trunc-B)

choice-∞ : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  {C : (x : A) → B x → UU l3} → ((x : A) → Σ (B x) (λ y → C x y)) →
  Σ ((x : A) → B x) (λ f → (x : A) → C x (f x))
choice-∞ φ = dpair (λ x → pr1 (φ x)) (λ x → pr2 (φ x))

abstract
  is-equiv-choice-∞ : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
    {C : (x : A) → B x → UU l3} → is-equiv (choice-∞ {A = A} {B = B} {C = C})
  is-equiv-choice-∞ {A = A} {B = B} {C = C} =
    is-equiv-has-inverse
      ( dpair
        ( λ ψ x → dpair ((pr1 ψ) x) ((pr2 ψ) x))
        ( dpair
          ( λ ψ → eq-pair (dpair
            ( eq-htpy (λ x → refl))
            ( ap
              ( λ t → tr (λ f → (x : A) → C x (f x)) t (λ x → (pr2 ψ) x))
              ( isretr-eq-htpy refl))))
          ( λ φ → eq-htpy λ x → eq-pair (dpair refl refl))))

mapping-into-Σ : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3} →
  (A → Σ B C) → Σ (A → B) (λ f → (x : A) → C (f x))
mapping-into-Σ {B = B} = choice-∞ {B = λ x → B}

is-equiv-mapping-into-Σ : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {C : B → UU l3} → is-equiv (mapping-into-Σ {A = A} {C = C})
is-equiv-mapping-into-Σ = is-equiv-choice-∞

-- Section 9.2 Universal properties

is-equiv-ev-pair : {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} → is-equiv (ev-pair {C = C})
is-equiv-ev-pair =
  dpair
    ( sec-ev-pair _ _ _)
    ( dpair ind-Σ
      ( λ f → eq-htpy
        ( ind-Σ
          {C = (λ t → Id (ind-Σ (ev-pair f) t) (f t))}
          (λ x y → refl))))

ev-refl : {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → Id a x → UU l2} →
  ((x : A) (p : Id a x) → B x p) → B a refl
ev-refl a f = f a refl

is-equiv-ev-refl : {l1 l2 : Level} {A : UU l1} (a : A)
  {B : (x : A) → Id a x → UU l2} → is-equiv (ev-refl a {B = B})
is-equiv-ev-refl a =
  is-equiv-has-inverse
    ( dpair (ind-Id a _)
      ( dpair
        ( λ b → refl)
        ( λ f → eq-htpy
          ( λ x → eq-htpy
            ( ind-Id a
              ( λ x' p' → Id (ind-Id a _ (f a refl) x' p') (f x' p'))
              ( refl) x)))))

-- Section 9.3 Composing with equivalences.

is-half-adjoint-equivalence : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → UU (l1 ⊔ l2)
is-half-adjoint-equivalence {A = A} {B = B} f =
  Σ (B → A)
    ( λ g → Σ ((f ∘ g) ~ id)
      ( λ G → Σ ((g ∘ f) ~ id)
        ( λ H → (htpy-right-whisk G f) ~ (htpy-left-whisk f H))))

is-path-split : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → UU (l1 ⊔ l2)
is-path-split {A = A} {B = B} f =
  sec f × ((x y : A) → sec (ap f {x = x} {y = y}))

is-path-split-is-equiv : {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-path-split f
is-path-split-is-equiv f (dpair sec-f retr-f) =
  pair sec-f (λ x y → pr1 (is-emb-is-equiv f (dpair sec-f retr-f) x y))

is-half-adjoint-equivalence-is-path-split : {l1 l2 : Level} {A : UU l1}
  {B : UU l2} (f : A → B) → is-path-split f → is-half-adjoint-equivalence f
is-half-adjoint-equivalence-is-path-split {A = A} {B = B} f
  ( dpair (dpair g issec-g) sec-ap-f) =
  let φ : ((x : A) → fib (ap f) (issec-g (f x))) → Σ ((g ∘ f) ~ id) (λ H → (htpy-right-whisk issec-g f) ~ (htpy-left-whisk f H))
      φ =  (tot (λ H' → htpy-inv)) ∘ choice-∞ in
  dpair g
    ( dpair issec-g
      ( φ (λ x → dpair
        ( pr1 (sec-ap-f (g (f x)) x) (issec-g (f x)))
        ( pr2 (sec-ap-f (g (f x)) x) (issec-g (f x))))))

tr-precompose-fam : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) {x y : A} (p : Id x y) → tr C (ap f p) ~ tr (λ x → C (f x)) p
tr-precompose-fam C f refl = htpy-refl _

is-equiv-precomp-Π-is-half-adjoint-equivalence : {l1 l2 l3 : Level} {A : UU l1}
  {B : UU l2} (f : A → B) → is-half-adjoint-equivalence f →
  (C : B → UU l3) → is-equiv (λ (s : (y : B) → C y) (x : A) → s (f x))
is-equiv-precomp-Π-is-half-adjoint-equivalence f
  ( dpair g (dpair issec-g (dpair isretr-g coh))) C =
  is-equiv-has-inverse
    ( dpair (λ s y → tr C (issec-g y) (s (g y)))
      ( dpair
        ( λ s → eq-htpy (λ x → concat
          ( tr C (ap f (isretr-g x)) (s (g (f x))))
          ( ap (λ t → tr C t (s (g (f x)))) (coh x))
          ( concat
            ( tr (λ x → C (f x)) (isretr-g x) (s (g (f x))))
            ( tr-precompose-fam C f (isretr-g x) (s (g (f x))))
            ( apd s (isretr-g x)))))
        ( λ s → eq-htpy λ y → apd s (issec-g y))))

abstract
  is-equiv-precomp-Π-is-equiv : {l1 l2 l3 : Level} {A : UU l1}
    {B : UU l2} (f : A → B) → is-equiv f →
    (C : B → UU l3) → is-equiv (λ (s : (y : B) → C y) (x : A) → s (f x))
  is-equiv-precomp-Π-is-equiv f is-equiv-f =
    is-equiv-precomp-Π-is-half-adjoint-equivalence f
      ( is-half-adjoint-equivalence-is-path-split f
        ( is-path-split-is-equiv f is-equiv-f))

is-equiv-precomp-is-equiv-precomp-Π : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) →
  ((C : B → UU l3) → is-equiv (λ (s : (y : B) → C y) (x : A) → s (f x))) →
  ((C : UU l3) → is-equiv (λ (g : B → C) → g ∘ f))
is-equiv-precomp-is-equiv-precomp-Π f is-equiv-precomp-Π-f C =
  is-equiv-precomp-Π-f (λ y → C)

is-equiv-precomp-is-equiv : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) → is-equiv f →
  (C : UU l3) → is-equiv (λ (g : B → C) → g ∘ f)
is-equiv-precomp-is-equiv f is-equiv-f =
  is-equiv-precomp-is-equiv-precomp-Π f
    ( is-equiv-precomp-Π-is-equiv f is-equiv-f)

is-equiv-is-equiv-precomp : {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) →
  ({l3 : Level} (C : UU l3) → is-equiv (λ (g : B → C) → g ∘ f)) →
  is-equiv f
is-equiv-is-equiv-precomp {A = A} {B = B} f is-equiv-precomp-f =
  let retr-f = center (is-contr-map-is-equiv (is-equiv-precomp-f A) id) in
  is-equiv-has-inverse
    ( dpair
      ( pr1 retr-f)
      ( pair
        ( htpy-eq (ap pr1 (center (is-prop-is-contr
          ( is-contr-map-is-equiv (is-equiv-precomp-f B) f)
          ( dpair (f ∘ (pr1 retr-f)) (ap (λ (g : A → A) → f ∘ g) (pr2 retr-f)))
          ( dpair id refl)))))
        ( htpy-eq (pr2 retr-f))))

-- Exercises

-- Exercise 9.1

is-equiv-htpy-concat : {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g) →
  (h : (x : A) → B x) → is-equiv (htpy-concat g {h = h} H)
is-equiv-htpy-concat {A = A} {B = B} {f} {g} H =
  ind-htpy f
    ( λ g H → (h : (x : A) → B x) → is-equiv (htpy-concat g {h = h} H))
    ( λ h → is-equiv-id (f ~ h))
    g H

-- Exercise 9.4

is-equiv-is-equiv-postcomp : {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (f : X → Y) →
  ({l3 : Level} (A : UU l3) → is-equiv (λ (h : A → X) → f ∘ h)) → is-equiv f
is-equiv-is-equiv-postcomp {X = X} {Y = Y} f post-comp-equiv-f =
  let sec-f = center (is-contr-map-is-equiv (post-comp-equiv-f Y) id) in
  is-equiv-has-inverse
    ( dpair
      ( pr1 sec-f)
      ( dpair
        ( htpy-eq (pr2 sec-f))
        ( htpy-eq (ap pr1 (center (is-prop-is-contr
          ( is-contr-map-is-equiv (post-comp-equiv-f X) f)
          ( dpair ((pr1 sec-f) ∘ f) (ap (λ t → t ∘ f) (pr2 sec-f)))
          ( dpair id refl)))))))

is-equiv-postcomp-is-equiv : {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (f : X → Y) → is-equiv f →
  ({l3 : Level} (A : UU l3) → is-equiv (λ (h : A → X) → f ∘ h))
is-equiv-postcomp-is-equiv {X = X} {Y = Y} f is-equiv-f A =
  is-equiv-has-inverse (dpair
    ( λ (g : A → Y) → (inv-is-equiv is-equiv-f) ∘ g)
    ( dpair
      ( λ g → eq-htpy (htpy-right-whisk (issec-inv-is-equiv is-equiv-f) g))
      ( λ h → eq-htpy (htpy-right-whisk (isretr-inv-is-equiv is-equiv-f) h))))

-- Exercise 9.5

is-contr-sec-is-equiv : {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-contr (sec f)
is-contr-sec-is-equiv {A = A} {B = B} {f = f} is-equiv-f =
  is-contr-is-equiv'
    ( Σ (B → A) (λ g → Id (f ∘ g) id))
    ( tot (λ g → htpy-eq))
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ g → htpy-eq)
      ( λ g → funext (f ∘ g) id))
    ( is-contr-map-is-equiv (is-equiv-postcomp-is-equiv f is-equiv-f B) id)

is-contr-retr-is-equiv : {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-contr (retr f)
is-contr-retr-is-equiv {A = A} {B = B} {f = f} is-equiv-f =
  is-contr-is-equiv'
    ( Σ (B → A) (λ h → Id (h ∘ f) id))
    ( tot (λ h → htpy-eq))
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ h → htpy-eq)
      ( λ h → funext (h ∘ f) id))
    ( is-contr-map-is-equiv (is-equiv-precomp-is-equiv f is-equiv-f A) id)

is-contr-is-equiv-is-equiv : {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} → is-equiv f → is-contr (is-equiv f)
is-contr-is-equiv-is-equiv is-equiv-f =
  is-contr-prod
    ( is-contr-sec-is-equiv is-equiv-f)
    ( is-contr-retr-is-equiv is-equiv-f)

is-subtype-is-equiv : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-subtype (is-equiv {A = A} {B = B})
is-subtype-is-equiv f = is-prop-is-contr-if-inh
  ( λ is-equiv-f → is-contr-prod
    ( is-contr-sec-is-equiv is-equiv-f)
    ( is-contr-retr-is-equiv is-equiv-f))



\end{code}
