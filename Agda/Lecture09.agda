{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture09 where

import Lecture08
open Lecture08 public

-- Section 9.1 Equivalent forms of Function Extensionality.

-- We first define the types Funext, Ind-htpy, and Weak-Funext. 

htpy-eq :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) → (f ~ g)
htpy-eq refl = htpy-refl _

FUNEXT :
  {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → UU (i ⊔ j)
FUNEXT f = is-fiberwise-equiv (λ g → htpy-eq {f = f} {g = g})

ev-htpy-refl :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f (htpy-refl f)
ev-htpy-refl f C φ = φ f (htpy-refl f)

IND-HTPY :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → UU _
IND-HTPY {l1} {l2} {l3} {A} {B} f =
  (C : (g : (x : A) → B x) → (f ~ g) → UU l3) → sec (ev-htpy-refl f C)

WEAK-FUNEXT :
  {i j : Level} (A : UU i) (B : A → UU j) → UU (i ⊔ j)
WEAK-FUNEXT A B =
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)

-- Our goal is now to show that function extensionality holds if and only if the homotopy induction principle is valid, if and only if the weak function extensionality principle holds. This is Theorem 9.1.1 in the notes.

is-contr-total-htpy-Funext :
  {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → FUNEXT f → is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
is-contr-total-htpy-Funext f funext-f =
  id-fundamental-gen' f (htpy-refl f) (λ g → htpy-eq {g = g}) funext-f

ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((t : Σ A B) → C t) → (x : A) (y : B x) → C (dpair x y)
ev-pair f x y = f (dpair x y)

sec-ev-pair :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2)
  (C : Σ A B → UU l3) → sec (ev-pair {A = A} {B = B} {C = C})
sec-ev-pair A B C =
  dpair (λ f → ind-Σ f) (λ f → refl)

triangle-ev-htpy-refl :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C :  Σ ((x : A) → B x) (λ g → f ~ g) → UU l3) →
  ev-pt (Σ ((x : A) → B x) (λ g → f ~ g)) (dpair f (htpy-refl f)) C ~
  ((ev-htpy-refl f (λ x y → C (dpair x y))) ∘ (ev-pair {C = C}))
triangle-ev-htpy-refl f C φ = refl

IND-HTPY-FUNEXT :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
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

FUNEXT-IND-HTPY :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
  IND-HTPY {l3 = l1 ⊔ l2} f → FUNEXT f
FUNEXT-IND-HTPY f ind-htpy-f =
  let eq-htpy-f = pr1 (ind-htpy-f (λ h H → Id f h)) refl in
  id-fundamental-sec f (λ h → htpy-eq {g = h}) (λ g → dpair
    ( eq-htpy-f g)
    ( pr1 (ind-htpy-f (λ h H → Id (htpy-eq (eq-htpy-f h H)) H))
      ( ap htpy-eq (pr2 (ind-htpy-f (λ h H → Id f h)) refl)) g))

WEAK-FUNEXT-FUNEXT :
  {l1 l2 : Level} →
  ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f) →
  ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B)
WEAK-FUNEXT-FUNEXT funext A B is-contr-B =
  let pi-center = (λ x → center (is-contr-B x)) in
  dpair
    ( pi-center)
    ( λ f → inv-is-equiv (funext A B pi-center f)
      ( λ x → contraction (is-contr-B x) (f x)))

FUNEXT-WEAK-FUNEXT :
  {l1 l2 : Level} →
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

eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) → Id f g
eq-htpy = inv-is-equiv (funext _ _)

issec-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  ((htpy-eq {f = f} {g = g}) ∘ (eq-htpy {f = f} {g = g})) ~ id
issec-eq-htpy = issec-inv-is-equiv (funext _ _)

isretr-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  ((eq-htpy {f = f} {g = g}) ∘ (htpy-eq {f = f} {g = g})) ~ id
isretr-eq-htpy = isretr-inv-is-equiv (funext _ _)

is-equiv-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j}
  (f g : (x : A) → B x) → is-equiv (eq-htpy {f = f} {g = g})
is-equiv-eq-htpy f g = is-equiv-inv-is-equiv (funext _ _)

eq-htpy-htpy-refl :
  {i j : Level} {A : UU i} {B : A → UU j}
  (f : (x : A) → B x) → Id (eq-htpy (htpy-refl f)) refl
eq-htpy-htpy-refl f = isretr-eq-htpy refl

{-
The immediate proof of the following theorem would be

  is-contr-total-htpy-Funext f (funext f)

We give a different proof to ensure that the center of contraction is the 
expected thing: 

  dpair f (htpy-refl f)

-}

is-contr-total-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) →
  is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
is-contr-total-htpy f =
  dpair
    ( dpair f (htpy-refl f))
    ( λ t → concat
      ( center (is-contr-total-htpy-Funext f (funext f)))
      ( inv (contraction
        ( is-contr-total-htpy-Funext f (funext f))
        ( dpair f (htpy-refl f))))
      ( contraction (is-contr-total-htpy-Funext f (funext f)) t))

is-contr-total-htpy-nondep :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  is-contr (Σ (A → B) (λ g → f ~ g))
is-contr-total-htpy-nondep {B = B} f =
  is-contr-total-htpy-Funext {B = λ x → B} f (funext f)

Ind-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
  IND-HTPY {l3 = l3} f
Ind-htpy f = IND-HTPY-FUNEXT f (funext f)

ind-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  C f (htpy-refl f) → (g : (x : A) → B x) (H : f ~ g) → C g H
ind-htpy f C = pr1 (Ind-htpy f C)

comp-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  (c : C f (htpy-refl f)) →
  Id (ind-htpy f C c f (htpy-refl f)) c
comp-htpy f C = pr2 (Ind-htpy f C)

is-contr-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
is-contr-Π {A = A} {B = B} = WEAK-FUNEXT-FUNEXT (λ X Y → funext) A B

is-trunc-Π :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
  ((x : A) → is-trunc k (B x)) → is-trunc k ((x : A) → B x)
is-trunc-Π neg-two-𝕋 is-trunc-B = is-contr-Π is-trunc-B
is-trunc-Π (succ-𝕋 k) is-trunc-B f g =
  is-trunc-is-equiv k (f ~ g) htpy-eq
    ( funext f g)
    ( is-trunc-Π k (λ x → is-trunc-B x (f x) (g x)))

is-prop-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-subtype B → is-prop ((x : A) → B x)
is-prop-Π = is-trunc-Π neg-one-𝕋

is-set-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → is-set (B x)) → is-set ((x : A) → (B x))
is-set-Π = is-trunc-Π zero-𝕋

is-trunc-function-type :
  {l1 l2 : Level} (k : 𝕋) (A : UU l1) (B : UU l2) →
  is-trunc k B → is-trunc k (A → B)
is-trunc-function-type k A B is-trunc-B =
  is-trunc-Π k {B = λ (x : A) → B} (λ x → is-trunc-B)

is-prop-function-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-prop B → is-prop (A → B)
is-prop-function-type = is-trunc-function-type neg-one-𝕋

is-set-function-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-set B → is-set (A → B)
is-set-function-type = is-trunc-function-type zero-𝕋

choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  {C : (x : A) → B x → UU l3} → ((x : A) → Σ (B x) (λ y → C x y)) →
  Σ ((x : A) → B x) (λ f → (x : A) → C x (f x))
choice-∞ φ = dpair (λ x → pr1 (φ x)) (λ x → pr2 (φ x))

is-equiv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
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

mapping-into-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3} →
  (A → Σ B C) → Σ (A → B) (λ f → (x : A) → C (f x))
mapping-into-Σ {B = B} = choice-∞ {B = λ x → B}

is-equiv-mapping-into-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {C : B → UU l3} → is-equiv (mapping-into-Σ {A = A} {C = C})
is-equiv-mapping-into-Σ = is-equiv-choice-∞

-- Section 9.2 Universal properties

is-equiv-ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  is-equiv (ev-pair {C = C})
is-equiv-ev-pair =
  dpair
    ( sec-ev-pair _ _ _)
    ( dpair ind-Σ
      ( λ f → eq-htpy
        ( ind-Σ
          {C = (λ t → Id (ind-Σ (ev-pair f) t) (f t))}
          (λ x y → refl))))

ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → Id a x → UU l2} →
  ((x : A) (p : Id a x) → B x p) → B a refl
ev-refl a f = f a refl

is-equiv-ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A)
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

is-equiv-precomp-Π-is-half-adjoint-equivalence :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-half-adjoint-equivalence f →
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

is-equiv-precomp-Π-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
  (C : B → UU l3) → is-equiv (λ (s : (y : B) → C y) (x : A) → s (f x))
is-equiv-precomp-Π-is-equiv f is-equiv-f =
  is-equiv-precomp-Π-is-half-adjoint-equivalence f
    ( is-half-adjoint-equivalence-is-path-split f
      ( is-path-split-is-equiv f is-equiv-f))

ind-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f) →
  ((x : A) → C (f x)) → ((y : B) → C y)
ind-is-equiv C f is-equiv-f =
  inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C)

comp-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) (is-equiv-f : is-equiv f) (h : (x : A) → C (f x)) →
  Id (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) h
comp-is-equiv C f is-equiv-f h =
  issec-inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C) h

htpy-comp-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f)
  (h : (x : A) → C (f x)) →
  (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) ~ h
htpy-comp-is-equiv C f is-equiv-f h = htpy-eq (comp-is-equiv C f is-equiv-f h)

is-equiv-precomp-is-equiv-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ((C : B → UU l3) → is-equiv (λ (s : (y : B) → C y) (x : A) → s (f x))) →
  ((C : UU l3) → is-equiv (λ (g : B → C) → g ∘ f))
is-equiv-precomp-is-equiv-precomp-Π f is-equiv-precomp-Π-f C =
  is-equiv-precomp-Π-f (λ y → C)

is-equiv-precomp-is-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
  (C : UU l3) → is-equiv (λ (g : B → C) → g ∘ f)
is-equiv-precomp-is-equiv f is-equiv-f =
  is-equiv-precomp-is-equiv-precomp-Π f
    ( is-equiv-precomp-Π-is-equiv f is-equiv-f)

is-equiv-is-equiv-precomp :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
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

is-equiv-htpy-inv :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → is-equiv (htpy-inv {f = f} {g = g})
is-equiv-htpy-inv f g =
  is-equiv-has-inverse
    ( dpair htpy-inv
      ( dpair
        ( λ H → eq-htpy (λ x → inv-inv (H x)))
        ( λ H → eq-htpy (λ x → inv-inv (H x)))))

is-equiv-htpy-concat :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g) →
  (h : (x : A) → B x) → is-equiv (htpy-concat g {h = h} H)
is-equiv-htpy-concat {A = A} {B = B} {f} {g} H =
  ind-htpy f
    ( λ g H → (h : (x : A) → B x) → is-equiv (htpy-concat g {h = h} H))
    ( λ h → is-equiv-id (f ~ h))
    g H

htpy-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} →
  (g ~ h) → (f ~ g) → (f ~ h)
htpy-concat' f K H = H ∙h K

inv-htpy-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} →
  (g ~ h) → (f ~ h) → (f ~ g)
inv-htpy-concat' f K = htpy-concat' f (htpy-inv K)

issec-inv-htpy-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x}
  (K : g ~ h) → ((htpy-concat' f K) ∘ (inv-htpy-concat' f K)) ~ id
issec-inv-htpy-concat' f K L =
  eq-htpy (λ x → right-inv-inv-concat' (f x) (K x) (L x))

isretr-inv-htpy-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x}
  (K : g ~ h) → ((inv-htpy-concat' f K) ∘ (htpy-concat' f K)) ~ id
isretr-inv-htpy-concat' f K L =
  eq-htpy (λ x → left-inv-inv-concat' (f x) (K x) (L x))

is-equiv-htpy-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} (K : g ~ h) →
  is-equiv (htpy-concat' f K)
is-equiv-htpy-concat' f K =
  is-equiv-has-inverse
    ( dpair
      ( inv-htpy-concat' f K)
      ( dpair
        ( issec-inv-htpy-concat' f K)
        ( isretr-inv-htpy-concat' f K)))

-- Exercise 9.2

is-subtype-is-contr :
  {l : Level} → is-subtype {lsuc l} {A = UU l} is-contr
is-subtype-is-contr A =
  is-prop-is-contr-if-inh
    ( λ is-contr-A →
      is-contr-Σ
        ( is-contr-A)
        ( λ x → is-contr-Π (is-prop-is-contr is-contr-A x)))

is-prop-is-trunc :
  {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-trunc k A)
is-prop-is-trunc neg-two-𝕋 = is-subtype-is-contr
is-prop-is-trunc (succ-𝕋 k) A =
  is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-trunc k (Id x y)))

-- Exercise 9.3

is-equiv-is-equiv-postcomp :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
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

is-equiv-postcomp-is-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) → is-equiv f →
  ({l3 : Level} (A : UU l3) → is-equiv (λ (h : A → X) → f ∘ h))
is-equiv-postcomp-is-equiv {X = X} {Y = Y} f is-equiv-f A =
  is-equiv-has-inverse (dpair
    ( λ (g : A → Y) → (inv-is-equiv is-equiv-f) ∘ g)
    ( dpair
      ( λ g → eq-htpy (htpy-right-whisk (issec-inv-is-equiv is-equiv-f) g))
      ( λ h → eq-htpy (htpy-right-whisk (isretr-inv-is-equiv is-equiv-f) h)))) 

-- Exercise 9.4

is-contr-sec-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-contr (sec f)
is-contr-sec-is-equiv {A = A} {B = B} {f = f} is-equiv-f =
  is-contr-is-equiv'
    ( Σ (B → A) (λ g → Id (f ∘ g) id))
    ( tot (λ g → htpy-eq))
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ g → funext (f ∘ g) id))
    ( is-contr-map-is-equiv (is-equiv-postcomp-is-equiv f is-equiv-f B) id)

is-contr-retr-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-contr (retr f)
is-contr-retr-is-equiv {A = A} {B = B} {f = f} is-equiv-f =
  is-contr-is-equiv'
    ( Σ (B → A) (λ h → Id (h ∘ f) id))
    ( tot (λ h → htpy-eq))
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ h → funext (h ∘ f) id))
    ( is-contr-map-is-equiv (is-equiv-precomp-is-equiv f is-equiv-f A) id)

is-contr-is-equiv-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} → is-equiv f → is-contr (is-equiv f)
is-contr-is-equiv-is-equiv is-equiv-f =
  is-contr-prod
    ( is-contr-sec-is-equiv is-equiv-f)
    ( is-contr-retr-is-equiv is-equiv-f)

is-subtype-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-subtype (is-equiv {A = A} {B = B})
is-subtype-is-equiv f = is-prop-is-contr-if-inh
  ( λ is-equiv-f → is-contr-prod
    ( is-contr-sec-is-equiv is-equiv-f)
    ( is-contr-retr-is-equiv is-equiv-f))

is-emb-eqv-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-emb (eqv-map {A = A} {B = B})
is-emb-eqv-map = is-emb-pr1-is-subtype is-subtype-is-equiv

-- Exercise 9.5

_↔_ :
  {l1 l2 : Level} → hProp l1 → hProp l2 → UU (l1 ⊔ l2)
P ↔ Q = (pr1 P → pr1 Q) × (pr1 Q → pr1 P)

equiv-iff :
  {l1 l2 : Level} (P : hProp l1) (Q : hProp l2) →
  (P ↔ Q) → (pr1 P ≃ pr1 Q)
equiv-iff P Q t = dpair (pr1 t) (is-equiv-is-prop (pr2 P) (pr2 Q) (pr2 t))

iff-equiv :
  {l1 l2 : Level} (P : hProp l1) (Q : hProp l2) →
  (pr1 P ≃ pr1 Q) → (P ↔ Q)
iff-equiv P Q equiv-PQ = dpair (pr1 equiv-PQ) (inv-is-equiv (pr2 equiv-PQ))

is-prop-iff :
  {l1 l2 : Level} (P : hProp l1) (Q : hProp l2) → is-prop (P ↔ Q)
is-prop-iff P Q =
  is-prop-prod
    ( is-prop-function-type (pr1 P) (pr1 Q) (pr2 Q))
    ( is-prop-function-type (pr1 Q) (pr1 P) (pr2 P))

is-prop-equiv-is-prop :
  {l1 l2 : Level} (P : hProp l1) (Q : hProp l2) →
  is-prop ((pr1 P) ≃ (pr1 Q))
is-prop-equiv-is-prop P Q =
  is-prop-Σ
    ( is-prop-function-type (pr1 P) (pr1 Q) (pr2 Q))
    ( is-subtype-is-equiv)

is-equiv-equiv-iff :
  {l1 l2 : Level} (P : hProp l1) (Q : hProp l2) → is-equiv (equiv-iff P Q)
is-equiv-equiv-iff P Q =
  is-equiv-is-prop
    ( is-prop-iff P Q)
    ( is-prop-equiv-is-prop P Q)
    ( iff-equiv P Q)

is-prop-is-contr-endomaps :
  {l : Level} (P : UU l) → is-contr (P → P) → is-prop P
is-prop-is-contr-endomaps P H =
  is-prop-is-prop'
    ( λ x → htpy-eq (center (is-prop-is-contr H (const P P x) id)))

is-contr-endomaps-is-prop :
  {l : Level} (P : UU l) → is-prop P → is-contr (P → P)
is-contr-endomaps-is-prop P is-prop-P =
  is-contr-is-prop-inh (is-prop-function-type P P is-prop-P) id

-- Exercise 9.6

is-prop-is-path-split :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-path-split f)
is-prop-is-path-split f =
  is-prop-is-contr-if-inh (λ is-path-split-f →
    let is-equiv-f = is-equiv-is-path-split f is-path-split-f in
    is-contr-prod
      ( is-contr-sec-is-equiv is-equiv-f)
      ( is-contr-Π
        ( λ x → is-contr-Π
          ( λ y → is-contr-sec-is-equiv (is-emb-is-equiv f is-equiv-f x y)))))

is-prop-is-half-adjoint-equivalence :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-half-adjoint-equivalence f)
is-prop-is-half-adjoint-equivalence {l1} {l2} {A} {B} f =
  is-prop-is-contr-if-inh (λ is-hae-f →
    let is-equiv-f = is-equiv-is-half-adjoint-equivalence f is-hae-f in
    is-contr-is-equiv'
      ( Σ (sec f)
        ( λ sf → Σ (((pr1 sf) ∘ f) ~ id)
          ( λ H → (htpy-right-whisk (pr2 sf) f) ~ (htpy-left-whisk f H))))
      ( Σ-assoc (B → A)
        ( λ g → ((f ∘ g) ~ id))
        ( λ sf → Σ (((pr1 sf) ∘ f) ~ id)
          ( λ H → (htpy-right-whisk (pr2 sf) f) ~ (htpy-left-whisk f H))))
      ( is-equiv-Σ-assoc _ _ _)
      ( is-contr-Σ
        ( is-contr-sec-is-equiv is-equiv-f)
        ( λ sf → is-contr-is-equiv'
          ( (x : A) →
            Σ (Id ((pr1 sf) (f x)) x) (λ p → Id ((pr2 sf) (f x)) (ap f p)))
          ( choice-∞)
          ( is-equiv-choice-∞)
          ( is-contr-Π (λ x →
             is-contr-is-equiv'
               ( fib (ap f) ((pr2 sf) (f x)))
               ( tot (λ p → inv))
               ( is-equiv-tot-is-fiberwise-equiv
                 ( λ p → is-equiv-inv (ap f p) ((pr2 sf) (f x))))
               ( is-contr-map-is-equiv
                 ( is-emb-is-equiv f is-equiv-f ((pr1 sf) (f x)) x)
                 ( (pr2 sf) (f x))))))))

-- Exercise 9.7

left-unit-law-Σ-map-gen :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  is-contr A → (x : A) → B x → Σ A B
left-unit-law-Σ-map-gen B is-contr-A x y = dpair x y

is-equiv-left-unit-law-Σ-map-gen :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  (is-contr-A : is-contr A) →
  (x : A) → is-equiv (left-unit-law-Σ-map-gen B is-contr-A x)
is-equiv-left-unit-law-Σ-map-gen B is-contr-A x =
   is-equiv-comp
     ( left-unit-law-Σ-map-gen B is-contr-A x)
     ( left-unit-law-Σ-map B is-contr-A)
     ( tr B (inv (contraction is-contr-A x)))
     ( λ y → eq-pair (dpair (inv (contraction is-contr-A x)) refl))
     ( is-equiv-tr B (inv (contraction is-contr-A x)))
     ( is-equiv-left-unit-law-Σ-map B is-contr-A)

is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  (id {A = A} ~ id {A = A}) → has-inverse (id {A = A})
is-invertible-id-htpy-id-id A H = dpair id (dpair (htpy-refl id) H)

triangle-is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  ( is-invertible-id-htpy-id-id A) ~
    ( (Σ-assoc (A → A) (λ g → (id ∘ g) ~ id) (λ s → ((pr1 s) ∘ id) ~ id)) ∘
      ( left-unit-law-Σ-map-gen
        ( λ s → ((pr1 s) ∘ id) ~ id)
        ( is-contr-sec-is-equiv (is-equiv-id A)) (dpair id (htpy-refl id))))
triangle-is-invertible-id-htpy-id-id A H = refl

is-equiv-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) → is-equiv (is-invertible-id-htpy-id-id A)
is-equiv-invertible-id-htpy-id-id A =
   is-equiv-comp
     ( is-invertible-id-htpy-id-id A)
     ( Σ-assoc (A → A) (λ g → (id ∘ g) ~ id) (λ s → ((pr1 s) ∘ id) ~ id))
     ( left-unit-law-Σ-map-gen
       ( λ s → ((pr1 s) ∘ id) ~ id)
       ( is-contr-sec-is-equiv (is-equiv-id A))
       ( dpair id (htpy-refl id)))
     ( triangle-is-invertible-id-htpy-id-id A)
     ( is-equiv-left-unit-law-Σ-map-gen
       ( λ s → ((pr1 s) ∘ id) ~ id)
       ( is-contr-sec-is-equiv (is-equiv-id A))
       ( dpair id (htpy-refl id)))
     ( is-equiv-Σ-assoc _ _ _)

-- Exercise 9.8

dependent-universal-property-empty :
  {l : Level} (P : empty → UU l) → is-contr ((x : empty) → P x)
dependent-universal-property-empty P =
  dpair
    ( ind-empty {P = P})
    ( λ f → eq-htpy ind-empty)

universal-property-empty :
  {l : Level} (X : UU l) → is-contr (empty → X)
universal-property-empty X = dependent-universal-property-empty (λ t → X)

uniqueness-empty :
  {l : Level} (Y : UU l) → ((l' : Level) (X : UU l') →
  is-contr (Y → X)) → is-equiv (ind-empty {P = λ t → Y})
uniqueness-empty Y H =
  is-equiv-is-equiv-precomp ind-empty
    ( λ X → is-equiv-is-contr
      ( λ g → g ∘ ind-empty)
      ( H _ X)
      ( universal-property-empty X))

universal-property-empty-is-equiv-ind-empty :
  {l : Level} (X : UU l) → is-equiv (ind-empty {P = λ t → X}) →
  ((l' : Level) (Y : UU l') → is-contr (X → Y))
universal-property-empty-is-equiv-ind-empty X is-equiv-ind-empty l' Y =
  is-contr-is-equiv
    ( empty → Y)
    ( λ f → f ∘ ind-empty)
    ( is-equiv-precomp-is-equiv ind-empty is-equiv-ind-empty Y)
    ( universal-property-empty Y)

-- Exercise 9.9

ev-inl-inr :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (P : coprod A B → UU l3) →
  ((t : coprod A B) → P t) → ((x : A) → P (inl x)) × ((y : B) → P (inr y))
ev-inl-inr P s = pair (λ x → s (inl x)) (λ y → s (inr y))

dependent-universal-property-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (P : coprod A B → UU l3) → is-equiv (ev-inl-inr P)
dependent-universal-property-coprod P =
  is-equiv-has-inverse
    ( dpair
      ( λ p → ind-coprod P (pr1 p) (pr2 p))
      ( dpair
        ( ind-Σ (λ f g → eq-pair-triv _ (pair f g) (pair refl refl)))
        ( λ s → eq-htpy (ind-coprod _ (λ x → refl) λ y → refl))))

universal-property-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (X : UU l3) →
  is-equiv (ev-inl-inr (λ (t : coprod A B) → X))
universal-property-coprod X = dependent-universal-property-coprod (λ t → X)

uniqueness-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {Y : UU l3}
  (i : A → Y) (j : B → Y) →
  ((l : Level) (X : UU l) → is-equiv (λ (s : Y → X) → pair (s ∘ i) (s ∘ j))) →
  is-equiv (ind-coprod (λ t → Y) i j)
uniqueness-coprod {Y = Y} i j H =
  is-equiv-is-equiv-precomp
    ( ind-coprod _ i j)
    ( λ X → is-equiv-right-factor
      ( λ (s : Y → X) → pair (s ∘ i) (s ∘ j))
      ( ev-inl-inr (λ t → X))
      ( λ s → s ∘ (ind-coprod (λ t → Y) i j))
      ( λ s → refl)
      ( universal-property-coprod X)
      ( H _ X))

universal-property-coprod-is-equiv-ind-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (X : UU l3)
  (i : A → X) (j : B → X) → is-equiv (ind-coprod (λ t → X) i j) →
  ((l4 : Level) (Y : UU l4) → is-equiv (λ (s : X → Y) → pair (s ∘ i) (s ∘ j)))
universal-property-coprod-is-equiv-ind-coprod X i j is-equiv-ind-coprod l Y =
  is-equiv-comp
    ( λ s → pair (s ∘ i) (s ∘ j))
    ( ev-inl-inr (λ t → Y))
    ( λ s → s ∘ (ind-coprod (λ t → X) i j))
    ( λ s → refl)
    ( is-equiv-precomp-is-equiv
      ( ind-coprod (λ t → X) i j)
      ( is-equiv-ind-coprod)
      ( Y))
    ( universal-property-coprod Y)

-- Exercise 9.10

ev-star :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) → P star
ev-star P f = f star

dependent-universal-property-unit :
  {l : Level} (P : unit → UU l) → is-equiv (ev-star P)
dependent-universal-property-unit P =
  is-equiv-has-inverse
    ( dpair
      ( ind-unit)
      ( dpair
        ( λ p → refl)
        ( λ f → eq-htpy (ind-unit refl))))
  
universal-property-unit :
  {l : Level} (Y : UU l) → is-equiv (ev-star (λ t → Y))
universal-property-unit Y = dependent-universal-property-unit (λ t → Y)

is-equiv-ind-unit-universal-property-unit :
  {l1 : Level} (X : UU l1) (x : X) →
  ((l2 : Level) (Y : UU l2) → is-equiv (λ (f : X → Y) → f x)) →
  is-equiv (ind-unit {P = λ t → X} x)
is-equiv-ind-unit-universal-property-unit X x H =
   is-equiv-is-equiv-precomp
     ( ind-unit x)
     ( λ Y → is-equiv-right-factor
       ( λ f → f x)
       ( ev-star (λ t → Y))
       ( λ f → f ∘ (ind-unit x))
       ( λ f → refl)
       ( universal-property-unit Y)
       ( H _ Y))

universal-property-unit-is-equiv-ind-unit :
  {l1 : Level} (X : UU l1) (x : X) →
  is-equiv (ind-unit {P = λ t → X} x) →
  ((l2 : Level) (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
universal-property-unit-is-equiv-ind-unit X x is-equiv-ind-unit l2 Y =
  is-equiv-comp
    ( λ f → f x)
    ( ev-star (λ t → Y))
    ( λ f → f ∘ (ind-unit x))
    ( λ f → refl)
    ( is-equiv-precomp-is-equiv (ind-unit x) is-equiv-ind-unit Y)
    ( universal-property-unit Y)

-- Exercise 9.11

tr-issec-eq-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (g g' : B → A) (H : g ~ g') (G : (f ∘ g) ~ id) →
  (tr (λ (h : B → A) → (f ∘ h) ~ id) (eq-htpy H) G) ~ ((htpy-inv (f ·l H)) ∙h G)
tr-issec-eq-htpy {A = A} {B = B} f g =
  let P = λ (h : B → A) → (f ∘ h) ~ id in
  ind-htpy g
    ( λ g' H → (G : (f ∘ g) ~ id) →
      ( tr P (eq-htpy H) G) ~ ((htpy-inv (f ·l H)) ∙h G))
    ( λ G → htpy-eq (ap (λ t → tr P t G) (eq-htpy-htpy-refl g))) 

sec-left-factor-retract-of-sec-composition :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → (sec g) retract-of (sec f)
sec-left-factor-retract-of-sec-composition {X = X} f g h H sec-h =
  dpair
    ( section-comp' f g h H sec-h)
    ( dpair
      ( section-comp f g h H sec-h)
      ( λ sec-g →
        let K = htpy-right-whisk (pr2 sec-h) (pr1 sec-g) in
        eq-pair
          ( dpair
          ( eq-htpy K)
          ( eq-htpy
            ( ( tr-issec-eq-htpy g
                ( h ∘ ((pr1 sec-h) ∘ (pr1 sec-g)))
                ( pr1 sec-g)
                ( K)
                ( pr2
                  ( section-comp f g h H sec-h
                    ( section-comp' f g h H sec-h sec-g)))) ∙h
              ( ( htpy-ap-concat
                  ( htpy-inv (g ·l ((pr2 sec-h) ·r (pr1 sec-g)))) _ _
                  ( ( htpy-assoc
                      ( htpy-inv (H ·r ((pr1 sec-h) ∘ (pr1 sec-g))))
                      ( H ·r ((pr1 sec-h) ∘ (pr1 sec-g)))
                      ( _)) ∙h
                    ( htpy-ap-concat' _ _
                      ( ( g ·l ((pr2 sec-h) ·r (pr1 sec-g))) ∙h
                        ( pr2 sec-g))
                      ( htpy-left-inv (H ·r ((pr1 sec-h) ∘ (pr1 sec-g))))))) ∙h
                ( ( htpy-assoc
                    ( htpy-inv (g ·l ((pr2 sec-h) ·r (pr1 sec-g))))
                    ( g ·l ((pr2 sec-h) ·r (pr1 sec-g)))
                    ( pr2 sec-g)) ∙h
                  ( htpy-ap-concat'
                    ( ( htpy-inv (g ·l ((pr2 sec-h) ·r (pr1 sec-g)))) ∙h
                      ( g ·l ((pr2 sec-h) ·r (pr1 sec-g))))
                    ( htpy-refl (g ∘ (pr1 sec-g)))
                    ( pr2 sec-g)
                    ( htpy-left-inv
                      ( g ·l ((pr2 sec-h) ·r (pr1 sec-g))))))))))))

tr-isretr-eq-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (h h' : B → A) (H : h ~ h') (is-retr-h : (h ∘ f) ~ id) →
  (tr (λ (k : B → A) → (k ∘ f) ~ id) (eq-htpy H) is-retr-h) ~
  ((htpy-inv (H ·r f)) ∙h is-retr-h)
tr-isretr-eq-htpy {A = A} {B} f h h' H is-retr-h =
  let P = λ (k : B → A) → (k ∘ f) ~ id in
  ind-htpy h
    ( λ h' H →
      ( K : (h ∘ f) ~ id) → (tr P (eq-htpy H) K) ~ ((htpy-inv (H ·r f)) ∙h K))
    ( λ K → htpy-eq (ap (λ t → tr P t K) (eq-htpy-htpy-refl h)))
    h' H is-retr-h
  
sec-right-factor-retract-of-sec-left-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → (retr h) retract-of (retr f)
sec-right-factor-retract-of-sec-left-factor f g h H retr-g =
  dpair
    ( retraction-comp' f g h H retr-g)
    ( dpair
      ( retraction-comp f g h H retr-g)
      ( λ retr-h →
        eq-pair
        ( dpair 
          ( eq-htpy ((pr1 retr-h) ·l (pr2 retr-g)))
          ( eq-htpy
            ( ( tr-isretr-eq-htpy h _ _
                ( (pr1 retr-h) ·l (pr2 retr-g))
                ( pr2
                  ( retraction-comp f g h H retr-g
                  ( retraction-comp' f g h H retr-g retr-h)))) ∙h
              ( ( htpy-ap-concat
                  ( htpy-inv (((pr1 retr-h) ·l (pr2 retr-g)) ·r h))
                  ( _)
                  ( _)
                  ( ( htpy-assoc
                      ( htpy-inv (((pr1 retr-h) ∘ (pr1 retr-g)) ·l H))
                      ( ((pr1 retr-h) ∘ (pr1 retr-g)) ·l H)
                      ( _)) ∙h
                     ( htpy-ap-concat' _ _
                       ( ((pr1 retr-h) ·l ((pr2 retr-g) ·r h)) ∙h (pr2 retr-h))
                       ( htpy-left-inv
                         ( ((pr1 retr-h) ∘ (pr1 retr-g)) ·l H))))) ∙h
                ( ( htpy-assoc
                    ( htpy-inv ((pr1 retr-h) ·l ((pr2 retr-g) ·r h)))
                    ( (pr1 retr-h) ·l ((pr2 retr-g) ·r h))
                    ( pr2 retr-h)) ∙h
                  ( htpy-ap-concat' _ _ (pr2 retr-h)
                    ( htpy-left-inv
                      ( (pr1 retr-h) ·l ((pr2 retr-g) ·r h)))))))))))

-- Exercise 9.12

postcomp-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (e : (i : I) → A i → B i) →
  ((i : I) → A i) → ((i : I) → B i)
postcomp-Π e f i = e i (f i)

is-equiv-postcomp-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (e : (i : I) → A i → B i) (is-equiv-e : is-fiberwise-equiv e) →
  is-equiv (postcomp-Π e)
is-equiv-postcomp-Π e is-equiv-e =
  is-equiv-has-inverse
    ( dpair
      ( λ g i → inv-is-equiv (is-equiv-e i) (g i))
      ( dpair
        ( λ g → eq-htpy (λ i → issec-inv-is-equiv (is-equiv-e i) (g i)))
         λ f → eq-htpy (λ i → isretr-inv-is-equiv (is-equiv-e i) (f i))))

-- Exercise 9.13

hom-slice :
  {l1 l2 l3 : Level} (X : UU l1) {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
hom-slice X {A} {B} f g = Σ (A → B) (λ h → f ~ (g ∘ h))
  
fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  hom-slice X f g → (x : X) → (fib f x) → (fib g x)
fiberwise-hom-hom-slice f g (dpair h H) = fib-triangle f g h H

hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((x : X) → (fib f x) → (fib g x)) → hom-slice X f g
hom-slice-fiberwise-hom f g α =
  dpair
    ( λ a → pr1 (α (f a) (dpair a refl)))
    ( λ a → inv (pr2 (α (f a) (dpair a refl))))

issec-hom-slice-fiberwise-hom-eq-htpy :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (α : (x : X) → (fib f x) → (fib g x)) (x : X) →
  (fiberwise-hom-hom-slice f g (hom-slice-fiberwise-hom f g α) x) ~ (α x)
issec-hom-slice-fiberwise-hom-eq-htpy f g α .(f a) (dpair a refl) =
  eq-pair (dpair refl (inv-inv (pr2 (α (f a) (dpair a refl)))))

issec-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((fiberwise-hom-hom-slice f g) ∘ (hom-slice-fiberwise-hom f g)) ~ id
issec-hom-slice-fiberwise-hom f g α =
  eq-htpy (λ x → eq-htpy (issec-hom-slice-fiberwise-hom-eq-htpy f g α x))

isretr-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((hom-slice-fiberwise-hom f g) ∘ (fiberwise-hom-hom-slice f g)) ~ id
isretr-hom-slice-fiberwise-hom f g (dpair h H) =
  eq-pair
    ( dpair
      ( refl)
      ( eq-htpy (λ a → (inv-inv (H a)))))

is-equiv-fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  is-equiv (fiberwise-hom-hom-slice f g)
is-equiv-fiberwise-hom-hom-slice f g =
  is-equiv-has-inverse
    ( dpair
      ( hom-slice-fiberwise-hom f g)
      ( dpair
        ( issec-hom-slice-fiberwise-hom f g)
        ( isretr-hom-slice-fiberwise-hom f g)))

is-equiv-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  is-equiv (hom-slice-fiberwise-hom f g)
is-equiv-hom-slice-fiberwise-hom f g =
  is-equiv-has-inverse
    ( dpair
      ( fiberwise-hom-hom-slice f g)
      ( dpair
        ( isretr-hom-slice-fiberwise-hom f g)
        ( issec-hom-slice-fiberwise-hom f g)))

equiv-slice :
  {l1 l2 l3 : Level} (X : UU l1) {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
equiv-slice X {A} {B} f g = Σ (A ≃ B) (λ e → f ~ (g ∘ (eqv-map e)))

hom-slice-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice X f g → hom-slice X f g
hom-slice-equiv-slice f g (dpair (dpair h is-equiv-h) H) = dpair h H

{- We first prove two closely related generic lemmas that establishes 
   equivalences of subtypes -}

is-equiv-subtype-is-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3} {Q : B → UU l4}
  (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
  (f : A → B) (g : (x : A) → P x → Q (f x)) →
  is-equiv f → ((x : A) → (Q (f x)) → P x) → is-equiv (toto Q f g)
is-equiv-subtype-is-equiv {Q = Q} is-subtype-P is-subtype-Q f g is-equiv-f h =
  is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map Q f g is-equiv-f
    ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x)) (h x))

is-equiv-subtype-is-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3} {Q : B → UU l4}
  (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
  (f : A → B) (g : (x : A) → P x → Q (f x)) →
  (is-equiv-f : is-equiv f) →
  ((y : B) → (Q y) → P (inv-is-equiv is-equiv-f y)) →
  is-equiv (toto Q f g)
is-equiv-subtype-is-equiv' {P = P} {Q}
  is-subtype-P is-subtype-Q f g is-equiv-f h =
  is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map Q f g is-equiv-f
    ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x))
      ( (tr P (isretr-inv-is-equiv is-equiv-f x)) ∘ (h (f x))))

is-fiberwise-equiv-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  (t : hom-slice X f g) → is-equiv (pr1 t) →
  is-fiberwise-equiv (fiberwise-hom-hom-slice f g t)
is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g (dpair h H) =
  is-fiberwise-equiv-is-equiv-triangle f g h H

α-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  Σ (hom-slice X f g) (λ hH → is-equiv (pr1 hH)) →
  Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
α-fiberwise-equiv-equiv-slice f g =
  toto
    ( is-fiberwise-equiv)
    ( fiberwise-hom-hom-slice f g)
    ( is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g)

β-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  Σ (A → B) (λ h → (f ~ (g ∘ h)) × is-equiv h) →
  Σ (hom-slice X f g) (λ hH → is-equiv (pr1 hH))
β-fiberwise-equiv-equiv-slice {X = X} {A} {B} f g =
  inv-is-equiv
    ( is-equiv-Σ-assoc
      ( A → B)
      ( λ h → f ~ (g ∘ h))
      ( λ t → is-equiv (pr1 t)))

γ-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  Σ (A → B) (λ h → (is-equiv h) × (f ~ (g ∘ h))) →
  Σ (A → B) (λ h → (f ~ (g ∘ h)) × is-equiv h)
γ-fiberwise-equiv-equiv-slice f g =
  tot (λ h → swap-prod (is-equiv h) (f ~ (g ∘ h)))

δ-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice X f g → Σ (A → B) (λ h → (is-equiv h) × (f ~ (g ∘ h)))
δ-fiberwise-equiv-equiv-slice {X = X} {A} {B} f g =
  Σ-assoc (A → B) is-equiv (λ t → f ~ (g ∘ (pr1 t)))

fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice X f g → Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
fiberwise-equiv-equiv-slice {X = X} {A} {B} f g =
  ( ( ( α-fiberwise-equiv-equiv-slice f g) ∘
      ( β-fiberwise-equiv-equiv-slice f g)) ∘
    ( γ-fiberwise-equiv-equiv-slice f g)) ∘
  ( δ-fiberwise-equiv-equiv-slice f g)

is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  (t : hom-slice X f g) →
  ((x : X) → is-equiv (fiberwise-hom-hom-slice f g t x)) →
  is-equiv (pr1 t)
is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
  f g (dpair h H) =
  is-equiv-triangle-is-fiberwise-equiv f g h H

is-equiv-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  is-equiv (fiberwise-equiv-equiv-slice f g)
is-equiv-fiberwise-equiv-equiv-slice {X = X} {A} {B} f g =
  is-equiv-comp
    ( fiberwise-equiv-equiv-slice f g)
    ( ( ( α-fiberwise-equiv-equiv-slice f g) ∘
        ( β-fiberwise-equiv-equiv-slice f g)) ∘
      ( γ-fiberwise-equiv-equiv-slice f g))
    ( δ-fiberwise-equiv-equiv-slice f g)
    ( htpy-refl _)
    ( is-equiv-Σ-assoc _ _ _)
    ( is-equiv-comp
      ( ( ( α-fiberwise-equiv-equiv-slice f g) ∘
          ( β-fiberwise-equiv-equiv-slice f g)) ∘
        ( γ-fiberwise-equiv-equiv-slice f g))
      ( ( α-fiberwise-equiv-equiv-slice f g) ∘
        ( β-fiberwise-equiv-equiv-slice f g))
      ( γ-fiberwise-equiv-equiv-slice f g)
      ( htpy-refl _)
      ( is-equiv-tot-is-fiberwise-equiv (λ h → is-equiv-swap-prod _ _))
      ( is-equiv-comp
        ( ( α-fiberwise-equiv-equiv-slice f g) ∘
          ( β-fiberwise-equiv-equiv-slice f g))
        ( α-fiberwise-equiv-equiv-slice f g)
        ( β-fiberwise-equiv-equiv-slice f g)
        ( htpy-refl _)
        ( is-equiv-inv-is-equiv (is-equiv-Σ-assoc _ _ _))
        ( is-equiv-subtype-is-equiv
          ( λ t → is-subtype-is-equiv (pr1 t))
          ( λ α → is-prop-Π (λ x → is-subtype-is-equiv (α x)))
          ( fiberwise-hom-hom-slice f g)
          ( is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g)
          ( is-equiv-fiberwise-hom-hom-slice f g)
          ( is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
            f g))))

-- Exercise 9.14

hom-over-morphism :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) → UU (l1 ⊔ (l2 ⊔ l4))
hom-over-morphism i f g = hom-slice _ (i ∘ f) g

fiberwise-hom-hom-over-morphism :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  hom-over-morphism i f g → (x : X) → (fib f x) → (fib g (i x))
fiberwise-hom-hom-over-morphism i f g (dpair h H) .(f a) (dpair a refl) =
  dpair (h a) (inv (H a))

hom-over-morphism-fiberwise-hom :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  ((x : X) → (fib f x) → (fib g (i x))) → hom-over-morphism i f g
hom-over-morphism-fiberwise-hom i f g α =
  dpair
    ( λ a → pr1 (α (f a) (dpair a refl)))
    ( λ a → inv (pr2 (α (f a) (dpair a refl))))

issec-hom-over-morphism-fiberwise-hom-eq-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  (α : (x : X) → (fib f x) → (fib g (i x))) (x : X) →
  ( fiberwise-hom-hom-over-morphism i f g
    ( hom-over-morphism-fiberwise-hom i f g α) x) ~ (α x)
issec-hom-over-morphism-fiberwise-hom-eq-htpy i f g α .(f a) (dpair a refl) =
  eq-pair (dpair refl (inv-inv (pr2 (α (f a) (dpair a refl)))))

issec-hom-over-morphism-fiberwise-hom :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  ( ( fiberwise-hom-hom-over-morphism i f g) ∘
    ( hom-over-morphism-fiberwise-hom i f g)) ~ id
issec-hom-over-morphism-fiberwise-hom i f g α =
  eq-htpy
    ( λ x →
      ( eq-htpy
        ( issec-hom-over-morphism-fiberwise-hom-eq-htpy i f g α x)))

isretr-hom-over-morphism-fiberwise-hom :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  ( ( hom-over-morphism-fiberwise-hom i f g) ∘
    ( fiberwise-hom-hom-over-morphism i f g)) ~ id
isretr-hom-over-morphism-fiberwise-hom i f g (dpair h H) =
  eq-pair (dpair refl (eq-htpy (λ a → (inv-inv (H a)))))

is-equiv-fiberwise-hom-hom-over-morphism :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  is-equiv (fiberwise-hom-hom-over-morphism i f g)
is-equiv-fiberwise-hom-hom-over-morphism i f g =
  is-equiv-has-inverse
    ( dpair
      ( hom-over-morphism-fiberwise-hom i f g)
      ( dpair
        ( issec-hom-over-morphism-fiberwise-hom i f g)
        ( isretr-hom-over-morphism-fiberwise-hom i f g)))

is-equiv-hom-over-morphism-fiberwise-hom :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  is-equiv (hom-over-morphism-fiberwise-hom i f g)
is-equiv-hom-over-morphism-fiberwise-hom i f g =
  is-equiv-has-inverse
    ( dpair
      ( fiberwise-hom-hom-over-morphism i f g)
      ( dpair
        ( isretr-hom-over-morphism-fiberwise-hom i f g)
        ( issec-hom-over-morphism-fiberwise-hom i f g)))
