{-# OPTIONS --without-K --exact-split #-}

module 11-function-extensionality where

import 10-number-theory
open 10-number-theory public

-- Section 9.1 Equivalent forms of Function Extensionality.

-- We first define the types Funext, Ind-htpy, and Weak-Funext. 

htpy-eq :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) → (f ~ g)
htpy-eq refl = htpy-refl

FUNEXT :
  {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → UU (i ⊔ j)
FUNEXT f = is-fiberwise-equiv (λ g → htpy-eq {f = f} {g = g})

ev-htpy-refl :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f htpy-refl
ev-htpy-refl f C φ = φ f htpy-refl

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

abstract
  is-contr-total-htpy-Funext :
    {i j : Level} {A : UU i} {B : A → UU j} →
    (f : (x : A) → B x) → FUNEXT f → is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
  is-contr-total-htpy-Funext f funext-f =
    fundamental-theorem-id' f htpy-refl (λ g → htpy-eq {g = g}) funext-f

ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((t : Σ A B) → C t) → (x : A) (y : B x) → C (pair x y)
ev-pair f x y = f (pair x y)

sec-ev-pair :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2)
  (C : Σ A B → UU l3) → sec (ev-pair {A = A} {B = B} {C = C})
sec-ev-pair A B C =
  pair (λ f → ind-Σ f) (λ f → refl)

triangle-ev-htpy-refl :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C :  Σ ((x : A) → B x) (λ g → f ~ g) → UU l3) →
  ev-pt (Σ ((x : A) → B x) (λ g → f ~ g)) (pair f htpy-refl) C ~
  ((ev-htpy-refl f (λ x y → C (pair x y))) ∘ (ev-pair {C = C}))
triangle-ev-htpy-refl f C φ = refl

abstract
  IND-HTPY-FUNEXT :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    FUNEXT f → IND-HTPY {l3 = l3} f
  IND-HTPY-FUNEXT {l3 = l3} {A = A} {B = B} f funext-f =
    Ind-identity-system l3 f
      ( htpy-refl)
      ( is-contr-total-htpy-Funext f funext-f)

abstract
  FUNEXT-IND-HTPY :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    IND-HTPY {l3 = l1 ⊔ l2} f → FUNEXT f
  FUNEXT-IND-HTPY f ind-htpy-f =
    fundamental-theorem-id-IND-identity-system f
      ( htpy-refl)
      ( ind-htpy-f)
      ( λ g → htpy-eq)

abstract
  WEAK-FUNEXT-FUNEXT :
    {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f) →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B)
  WEAK-FUNEXT-FUNEXT funext A B is-contr-B =
    let pi-center = (λ x → center (is-contr-B x)) in
    pair
      ( pi-center)
      ( λ f → inv-is-equiv (funext A B pi-center f)
        ( λ x → contraction (is-contr-B x) (f x)))

abstract
  FUNEXT-WEAK-FUNEXT :
    {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B) →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f)
  FUNEXT-WEAK-FUNEXT weak-funext A B f =
    fundamental-theorem-id f
      ( htpy-refl)
      ( is-contr-retract-of
        ( (x : A) → Σ (B x) (λ b → Id (f x) b))
        ( pair
          ( λ t x → pair (pr1 t x) (pr2 t x))
          ( pair (λ t → pair (λ x → pr1 (t x)) (λ x → pr2 (t x)))
          ( λ t → eq-pair refl refl)))
        ( weak-funext A
          ( λ x → Σ (B x) (λ b → Id (f x) b))
          ( λ x → is-contr-total-path (f x))))
      ( λ g → htpy-eq {g = g})

-- From now on we will be assuming that function extensionality holds

postulate funext : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → FUNEXT f

equiv-funext : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) ≃ (f ~ g)
equiv-funext {f = f} {g} = pair htpy-eq (funext f g) 

abstract
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
    (f : (x : A) → B x) → Id (eq-htpy (htpy-refl {f = f})) refl
  eq-htpy-htpy-refl f = isretr-eq-htpy refl

{-
The immediate proof of the following theorem would be

  is-contr-total-htpy-Funext f (funext f)

We give a different proof to ensure that the center of contraction is the 
expected thing: 

  pair f htpy-refl

-}

abstract
  is-contr-total-htpy :
    {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) →
    is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
  is-contr-total-htpy f =
    pair
      ( pair f htpy-refl)
      ( λ t →
        ( inv (contraction
          ( is-contr-total-htpy-Funext f (funext f))
          ( pair f htpy-refl))) ∙
        ( contraction (is-contr-total-htpy-Funext f (funext f)) t))

abstract
  Ind-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    IND-HTPY {l3 = l3} f
  Ind-htpy f = IND-HTPY-FUNEXT f (funext f)
  
  ind-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
    (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
    C f htpy-refl → {g : (x : A) → B x} (H : f ~ g) → C g H
  ind-htpy f C t {g} = pr1 (Ind-htpy f C) t g
  
  comp-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
    (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
    (c : C f htpy-refl) →
    Id (ind-htpy f C c htpy-refl) c
  comp-htpy f C = pr2 (Ind-htpy f C)

abstract
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

{- The type theoretic principle of choice is the assertion that Π distributes
   over Σ. In other words, there is an equivalence

   ((x : A) → Σ (B x) (C x)) ≃ Σ ((x : A) → B x) (λ f → (x : A) → C x (f x)).

   In the following we construct this equivalence, and we also characterize the
   relevant identity types. 

   We call the type on the left-hand side Π-total-fam, and we call the type on
   the right-hand side type-choice-∞. -}
   
Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
Π-total-fam {A = A} {B} C = (x : A) → Σ (B x) (C x)

type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
type-choice-∞ {A = A} {B} C = Σ ((x : A) → B x) (λ f → (x : A) → C x (f x))

{- We compute the identity type of Π-total-fam. Note that its characterization
   is again of the form Π-total-fam. -}

{- We compute the identity type of type-choice-∞. Note that its identity 
   type is again of the form type-choice-∞. -}

Eq-type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : type-choice-∞ C) → UU (l1 ⊔ (l2 ⊔ l3))
Eq-type-choice-∞ {A = A} {B} C t t' =
  type-choice-∞
    ( λ (x : A) (p : Id ((pr1 t) x) ((pr1 t') x)) →
      Id (tr (C x) p ((pr2 t) x)) ((pr2 t') x))

reflexive-Eq-type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : type-choice-∞ C) → Eq-type-choice-∞ C t t
reflexive-Eq-type-choice-∞ C (pair f g) = pair htpy-refl htpy-refl

Eq-type-choice-∞-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : type-choice-∞ C) → Id t t' → Eq-type-choice-∞ C t t'
Eq-type-choice-∞-eq C t .t refl = reflexive-Eq-type-choice-∞ C t

abstract
  is-contr-total-Eq-type-choice-∞ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
    (t : type-choice-∞ C) →
    is-contr (Σ (type-choice-∞ C) (Eq-type-choice-∞ C t))
  is-contr-total-Eq-type-choice-∞ {A = A} {B} C t =
    is-contr-total-Eq-structure
      ( λ f g H → (x : A) → Id (tr (C x) (H x) ((pr2 t) x)) (g x))
      ( is-contr-total-htpy (pr1 t))
      ( pair (pr1 t) htpy-refl)
      ( is-contr-total-htpy (pr2 t))
  
  is-equiv-Eq-type-choice-∞-eq :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
    (t t' : type-choice-∞ C) → is-equiv (Eq-type-choice-∞-eq C t t')
  is-equiv-Eq-type-choice-∞-eq C t =
    fundamental-theorem-id t
      ( reflexive-Eq-type-choice-∞ C t)
      ( is-contr-total-Eq-type-choice-∞ C t)
      ( Eq-type-choice-∞-eq C t)
  
  eq-Eq-type-choice-∞ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
    {t t' : type-choice-∞ C} → Eq-type-choice-∞ C t t' → Id t t'
  eq-Eq-type-choice-∞ C {t} {t'} =
    inv-is-equiv (is-equiv-Eq-type-choice-∞-eq C t t')

choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C → type-choice-∞ C
choice-∞ φ = pair (λ x → pr1 (φ x)) (λ x → pr2 (φ x))

inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  type-choice-∞ C → Π-total-fam C
inv-choice-∞ ψ x = pair ((pr1 ψ) x) ((pr2 ψ) x)

issec-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  ( ( choice-∞ {A = A} {B = B} {C = C}) ∘
    ( inv-choice-∞ {A = A} {B = B} {C = C})) ~ id
issec-inv-choice-∞ {A = A} {C = C} (pair ψ ψ') =
  eq-Eq-type-choice-∞ C (pair htpy-refl htpy-refl)

isretr-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  ( ( inv-choice-∞ {A = A} {B = B} {C = C}) ∘
    ( choice-∞ {A = A} {B = B} {C = C})) ~ id
isretr-inv-choice-∞ φ =
  eq-htpy (λ x → eq-pair refl refl)

abstract
  is-equiv-choice-∞ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
    is-equiv (choice-∞ {A = A} {B = B} {C = C})
  is-equiv-choice-∞ {A = A} {B = B} {C = C} =
    is-equiv-has-inverse
      ( inv-choice-∞ {A = A} {B = B} {C = C})
      ( issec-inv-choice-∞ {A = A} {B = B} {C = C})
      ( isretr-inv-choice-∞ {A = A} {B = B} {C = C})

equiv-choice-∞ :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3) →
  Π-total-fam C ≃ type-choice-∞ C
equiv-choice-∞ C = pair choice-∞ is-equiv-choice-∞

abstract
  is-equiv-inv-choice-∞ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
    is-equiv (inv-choice-∞ {A = A} {B = B} {C = C})
  is-equiv-inv-choice-∞ {A = A} {B = B} {C = C} =
    is-equiv-has-inverse
      ( choice-∞ {A = A} {B = B} {C = C})
      ( isretr-inv-choice-∞ {A = A} {B = B} {C = C})
      ( issec-inv-choice-∞ {A = A} {B = B} {C = C})

equiv-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3) →
  (type-choice-∞ C) ≃ (Π-total-fam C)
equiv-inv-choice-∞ C = pair inv-choice-∞ is-equiv-inv-choice-∞

mapping-into-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3} →
  (A → Σ B C) → Σ (A → B) (λ f → (x : A) → C (f x))
mapping-into-Σ {B = B} = choice-∞ {B = λ x → B}

abstract
  is-equiv-mapping-into-Σ :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {C : B → UU l3} → is-equiv (mapping-into-Σ {A = A} {C = C})
  is-equiv-mapping-into-Σ = is-equiv-choice-∞

{- Next we compute the identity type of products of total spaces. Note again
   that the identity type of a product of total spaces is again a product of
   total spaces. -}

Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → UU (l1 ⊔ (l2 ⊔ l3))
Eq-Π-total-fam {A = A} C t t' =
  Π-total-fam (λ x (p : Id (pr1 (t x)) (pr1 (t' x))) →
    Id (tr (C x) p (pr2 (t x))) (pr2 (t' x)))

reflexive-Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : (a : A) → Σ (B a) (C a)) → Eq-Π-total-fam C t t
reflexive-Eq-Π-total-fam C t a = pair refl refl

Eq-Π-total-fam-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → Id t t' → Eq-Π-total-fam C t t'
Eq-Π-total-fam-eq C t .t refl = reflexive-Eq-Π-total-fam C t

is-contr-total-Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : (a : A) → Σ (B a) (C a)) →
  is-contr (Σ ((a : A) → Σ (B a) (C a)) (Eq-Π-total-fam C t))
is-contr-total-Eq-Π-total-fam {A = A} {B} C t =
  is-contr-equiv'
    ( (a : A) →
      Σ (Σ (B a) (C a)) (λ t' →
        Σ (Id (pr1 (t a)) (pr1 t')) (λ p →
          Id (tr (C a) p (pr2 (t a))) (pr2 t'))))
    ( equiv-choice-∞
      ( λ x t' →
        Σ ( Id (pr1 (t x)) (pr1 t'))
          ( λ p → Id (tr (C x) p (pr2 (t x))) (pr2 t'))))
    ( is-contr-Π
      ( λ a →
        is-contr-total-Eq-structure
        ( λ b c p → Id (tr (C a) p (pr2 (t a))) c)
        ( is-contr-total-path (pr1 (t a)))
        ( pair (pr1 (t a)) refl)
        ( is-contr-total-path (pr2 (t a)))))

is-equiv-Eq-Π-total-fam-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → is-equiv (Eq-Π-total-fam-eq C t t')
is-equiv-Eq-Π-total-fam-eq C t =
  fundamental-theorem-id t
    ( reflexive-Eq-Π-total-fam C t)
    ( is-contr-total-Eq-Π-total-fam C t)
    ( Eq-Π-total-fam-eq C t)

eq-Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → Eq-Π-total-fam C t t' → Id t t'
eq-Eq-Π-total-fam C t t' = inv-is-equiv (is-equiv-Eq-Π-total-fam-eq C t t')

-- Section 9.2 Universal properties

abstract
  is-equiv-ev-pair :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
    is-equiv (ev-pair {C = C})
  is-equiv-ev-pair =
    pair
      ( sec-ev-pair _ _ _)
      ( pair ind-Σ
        ( λ f → eq-htpy
          ( ind-Σ
            {C = (λ t → Id (ind-Σ (ev-pair f) t) (f t))}
            (λ x y → refl))))

ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → Id a x → UU l2} →
  ((x : A) (p : Id a x) → B x p) → B a refl
ev-refl a f = f a refl

abstract
  is-equiv-ev-refl :
    {l1 l2 : Level} {A : UU l1} (a : A)
    {B : (x : A) → Id a x → UU l2} → is-equiv (ev-refl a {B = B})
  is-equiv-ev-refl a =
    is-equiv-has-inverse
      ( ind-Id a _)
      ( λ b → refl)
      ( λ f → eq-htpy
        ( λ x → eq-htpy
          ( ind-Id a
            ( λ x' p' → Id (ind-Id a _ (f a refl) x' p') (f x' p'))
            ( refl) x)))

-- Section 9.3 Composing with equivalences.

tr-precompose-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) {x y : A} (p : Id x y) → tr C (ap f p) ~ tr (λ x → C (f x)) p
tr-precompose-fam C f refl = htpy-refl

abstract
  is-equiv-precomp-Π-is-half-adjoint-equivalence :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-half-adjoint-equivalence f →
    (C : B → UU l3) → is-equiv (λ (s : (y : B) → C y) (x : A) → s (f x))
  is-equiv-precomp-Π-is-half-adjoint-equivalence f
    ( pair g (pair issec-g (pair isretr-g coh))) C =
    is-equiv-has-inverse
      (λ s y → tr C (issec-g y) (s (g y)))
      ( λ s → eq-htpy (λ x → 
        ( ap (λ t → tr C t (s (g (f x)))) (coh x)) ∙
        ( ( tr-precompose-fam C f (isretr-g x) (s (g (f x)))) ∙
          ( apd s (isretr-g x)))))
      ( λ s → eq-htpy λ y → apd s (issec-g y))

precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ((b : B) → C b) → ((a : A) → C (f a))
precomp-Π f C h a = h (f a)

abstract
  is-equiv-precomp-Π-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
    (C : B → UU l3) → is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-is-equiv f is-equiv-f =
    is-equiv-precomp-Π-is-half-adjoint-equivalence f
      ( is-half-adjoint-equivalence-is-path-split f
        ( is-path-split-is-equiv f is-equiv-f))

precomp-Π-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : B → UU l3) → ((b : B) → C b) ≃ ((a : A) → C (map-equiv e a))
precomp-Π-equiv e C =
  pair
    ( precomp-Π (map-equiv e) C)
    ( is-equiv-precomp-Π-is-equiv (map-equiv e) (is-equiv-map-equiv e) C)

abstract
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

precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  (B → C) → (A → C)
precomp f C = precomp-Π f (λ b → C)

abstract
  is-equiv-precomp-is-equiv-precomp-Π :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ((C : B → UU l3) → is-equiv (precomp-Π f C)) →
    ((C : UU l3) → is-equiv (precomp f C))
  is-equiv-precomp-is-equiv-precomp-Π f is-equiv-precomp-Π-f C =
    is-equiv-precomp-Π-f (λ y → C)

abstract
  is-equiv-precomp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
    (C : UU l3) → is-equiv (precomp f C)
  is-equiv-precomp-is-equiv f is-equiv-f =
    is-equiv-precomp-is-equiv-precomp-Π f
      ( is-equiv-precomp-Π-is-equiv f is-equiv-f)

abstract
  is-equiv-is-equiv-precomp :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ((l : Level) (C : UU l) → is-equiv (precomp f C)) → is-equiv f
  is-equiv-is-equiv-precomp {A = A} {B = B} f is-equiv-precomp-f =
    let retr-f = center (is-contr-map-is-equiv (is-equiv-precomp-f _ A) id) in
    is-equiv-has-inverse
      ( pr1 retr-f)
      ( htpy-eq (ap pr1 (is-prop-is-contr'
        ( is-contr-map-is-equiv (is-equiv-precomp-f _ B) f)
          ( pair
            ( f ∘ (pr1 retr-f))
            ( ap (λ (g : A → A) → f ∘ g) (pr2 retr-f)))
        ( pair id refl))))
      ( htpy-eq (pr2 retr-f))

-- Exercises

-- Exercise 9.1

abstract
  is-equiv-htpy-inv :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    (f g : (x : A) → B x) → is-equiv (htpy-inv {f = f} {g = g})
  is-equiv-htpy-inv f g =
    is-equiv-has-inverse
      ( htpy-inv)
      ( λ H → eq-htpy (λ x → inv-inv (H x)))
      ( λ H → eq-htpy (λ x → inv-inv (H x)))

equiv-htpy-inv :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → (f ~ g) ≃ (g ~ f)
equiv-htpy-inv f g = pair htpy-inv (is-equiv-htpy-inv f g)

abstract
  is-equiv-htpy-concat :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    {f g : (x : A) → B x} (H : f ~ g) →
    (h : (x : A) → B x) → is-equiv (htpy-concat H h)
  is-equiv-htpy-concat {A = A} {B = B} {f} =
    ind-htpy f
      ( λ g H → (h : (x : A) → B x) → is-equiv (htpy-concat H h))
      ( λ h → is-equiv-id (f ~ h))

equiv-htpy-concat :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g) (h : (x : A) → B x) →
  (g ~ h) ≃ (f ~ h)
equiv-htpy-concat H h =
  pair (htpy-concat H h) (is-equiv-htpy-concat H h)

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
  eq-htpy (λ x → issec-inv-concat' (f x) (K x) (L x))

isretr-inv-htpy-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x}
  (K : g ~ h) → ((inv-htpy-concat' f K) ∘ (htpy-concat' f K)) ~ id
isretr-inv-htpy-concat' f K L =
  eq-htpy (λ x → isretr-inv-concat' (f x) (K x) (L x))

is-equiv-htpy-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} (K : g ~ h) →
  is-equiv (htpy-concat' f K)
is-equiv-htpy-concat' f K =
  is-equiv-has-inverse
    ( inv-htpy-concat' f K)
    ( issec-inv-htpy-concat' f K)
    ( isretr-inv-htpy-concat' f K)

equiv-htpy-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} (K : g ~ h) →
  (f ~ g) ≃ (f ~ h)
equiv-htpy-concat' f K =
  pair (htpy-concat' f K) (is-equiv-htpy-concat' f K)

-- Exercise 9.2

abstract
  is-subtype-is-contr :
    {l : Level} → is-subtype {lsuc l} {A = UU l} is-contr
  is-subtype-is-contr A =
    is-prop-is-contr-if-inh
      ( λ is-contr-A →
        is-contr-Σ
          ( is-contr-A)
          ( λ x → is-contr-Π (is-prop-is-contr is-contr-A x)))

abstract
  is-prop-is-trunc :
    {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-trunc k A)
  is-prop-is-trunc neg-two-𝕋 = is-subtype-is-contr
  is-prop-is-trunc (succ-𝕋 k) A =
    is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-trunc k (Id x y)))

abstract
  is-prop-is-prop :
    {l : Level} (A : UU l) → is-prop (is-prop A)
  is-prop-is-prop = is-prop-is-trunc neg-one-𝕋

abstract
  is-prop-is-set :
    {l : Level} (A : UU l) → is-prop (is-set A)
  is-prop-is-set = is-prop-is-trunc zero-𝕋

-- Exercise 9.3

abstract
  is-equiv-is-equiv-postcomp :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
    ({l3 : Level} (A : UU l3) → is-equiv (λ (h : A → X) → f ∘ h)) → is-equiv f
  is-equiv-is-equiv-postcomp {X = X} {Y = Y} f post-comp-equiv-f =
    let sec-f = center (is-contr-map-is-equiv (post-comp-equiv-f Y) id) in
    is-equiv-has-inverse
      ( pr1 sec-f)
      ( htpy-eq (pr2 sec-f))
      ( htpy-eq (ap pr1 (is-prop-is-contr'
        ( is-contr-map-is-equiv (post-comp-equiv-f X) f)
        ( pair ((pr1 sec-f) ∘ f) (ap (λ t → t ∘ f) (pr2 sec-f)))
        ( pair id refl))))

abstract
  is-equiv-postcomp-is-equiv :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) → is-equiv f →
    ({l3 : Level} (A : UU l3) → is-equiv (λ (h : A → X) → f ∘ h))
  is-equiv-postcomp-is-equiv {X = X} {Y = Y} f is-equiv-f A =
    is-equiv-has-inverse 
      ( λ (g : A → Y) → (inv-is-equiv is-equiv-f) ∘ g)
      ( λ g → eq-htpy (htpy-right-whisk (issec-inv-is-equiv is-equiv-f) g))
      ( λ h → eq-htpy (htpy-right-whisk (isretr-inv-is-equiv is-equiv-f) h))

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

abstract
  is-subtype-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-subtype (is-equiv {A = A} {B = B})
  is-subtype-is-equiv f = is-prop-is-contr-if-inh
    ( λ is-equiv-f → is-contr-prod
      ( is-contr-sec-is-equiv is-equiv-f)
      ( is-contr-retr-is-equiv is-equiv-f))

abstract
  is-emb-map-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-emb (map-equiv {A = A} {B = B})
  is-emb-map-equiv = is-emb-pr1-is-subtype is-subtype-is-equiv

{- For example, we show that homotopies are equivalent to identifications of
   equivalences. -}

htpy-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A ≃ B → A ≃ B → UU (l1 ⊔ l2)
htpy-equiv e e' = (map-equiv e) ~ (map-equiv e')

reflexive-htpy-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) → htpy-equiv e e
reflexive-htpy-equiv e = htpy-refl

htpy-equiv-eq :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {e e' : A ≃ B} (p : Id e e') → htpy-equiv e e'
htpy-equiv-eq {e = e} {.e} refl =
  reflexive-htpy-equiv e

abstract
  is-contr-total-htpy-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-contr (Σ (A ≃ B) (λ e' → htpy-equiv e e'))
  is-contr-total-htpy-equiv (pair f is-equiv-f) =
    is-contr-total-Eq-substructure
      ( is-contr-total-htpy f)
      ( is-subtype-is-equiv)
      ( f)
      ( htpy-refl)
      ( is-equiv-f)

  is-equiv-htpy-equiv-eq :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e e' : A ≃ B) →
    is-equiv (htpy-equiv-eq {e = e} {e'})
  is-equiv-htpy-equiv-eq e =
    fundamental-theorem-id e
      ( reflexive-htpy-equiv e)
      ( is-contr-total-htpy-equiv e)
      ( λ e' → htpy-equiv-eq {e = e} {e'})

eq-htpy-equiv :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} {e e' : A ≃ B} →
  ( htpy-equiv e e') → Id e e'
eq-htpy-equiv {e = e} {e'} = inv-is-equiv (is-equiv-htpy-equiv-eq e e')

abstract
  Ind-htpy-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
    sec
      ( λ (h : (e' : A ≃ B) (H : htpy-equiv e e') → P e' H) →
        h e (reflexive-htpy-equiv e))
  Ind-htpy-equiv {l3 = l3} e =
    Ind-identity-system l3 e
      ( reflexive-htpy-equiv e)
      ( is-contr-total-htpy-equiv e)
  
  ind-htpy-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
    P e (reflexive-htpy-equiv e) → (e' : A ≃ B) (H : htpy-equiv e e') → P e' H
  ind-htpy-equiv e P = pr1 (Ind-htpy-equiv e P)
  
  comp-htpy-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3)
    (p : P e (reflexive-htpy-equiv e)) →
    Id (ind-htpy-equiv e P p e (reflexive-htpy-equiv e)) p
  comp-htpy-equiv e P = pr2 (Ind-htpy-equiv e P)

-- Exercise 9.5

_↔_ :
  {l1 l2 : Level} → hProp l1 → hProp l2 → UU (l1 ⊔ l2)
P ↔ Q = (pr1 P → pr1 Q) × (pr1 Q → pr1 P)

equiv-iff :
  {l1 l2 : Level} (P : hProp l1) (Q : hProp l2) →
  (P ↔ Q) → (pr1 P ≃ pr1 Q)
equiv-iff P Q t = pair (pr1 t) (is-equiv-is-prop (pr2 P) (pr2 Q) (pr2 t))

iff-equiv :
  {l1 l2 : Level} (P : hProp l1) (Q : hProp l2) →
  (pr1 P ≃ pr1 Q) → (P ↔ Q)
iff-equiv P Q equiv-PQ = pair (pr1 equiv-PQ) (inv-is-equiv (pr2 equiv-PQ))

abstract
  is-prop-iff :
    {l1 l2 : Level} (P : hProp l1) (Q : hProp l2) → is-prop (P ↔ Q)
  is-prop-iff P Q =
    is-prop-prod
      ( is-prop-function-type (pr1 P) (pr1 Q) (pr2 Q))
      ( is-prop-function-type (pr1 Q) (pr1 P) (pr2 P))

abstract
  is-prop-equiv-is-prop :
    {l1 l2 : Level} (P : hProp l1) (Q : hProp l2) →
    is-prop ((pr1 P) ≃ (pr1 Q))
  is-prop-equiv-is-prop P Q =
    is-prop-Σ
      ( is-prop-function-type (pr1 P) (pr1 Q) (pr2 Q))
      ( is-subtype-is-equiv)

abstract
  is-equiv-equiv-iff :
    {l1 l2 : Level} (P : hProp l1) (Q : hProp l2) → is-equiv (equiv-iff P Q)
  is-equiv-equiv-iff P Q =
    is-equiv-is-prop
      ( is-prop-iff P Q)
      ( is-prop-equiv-is-prop P Q)
      ( iff-equiv P Q)

abstract
  is-prop-is-contr-endomaps :
    {l : Level} (P : UU l) → is-contr (P → P) → is-prop P
  is-prop-is-contr-endomaps P H =
    is-prop-is-prop'
      ( λ x → htpy-eq (is-prop-is-contr' H (const P P x) id))

abstract
  is-contr-endomaps-is-prop :
    {l : Level} (P : UU l) → is-prop P → is-contr (P → P)
  is-contr-endomaps-is-prop P is-prop-P =
    is-contr-is-prop-inh (is-prop-function-type P P is-prop-P) id

-- Exercise 9.6

abstract
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

abstract
  is-equiv-is-path-split-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (is-path-split-is-equiv f)
  is-equiv-is-path-split-is-equiv f =
    is-equiv-is-prop
      ( is-subtype-is-equiv f)
      ( is-prop-is-path-split f)
      ( is-equiv-is-path-split f)

abstract
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

abstract
  is-equiv-is-half-adjoint-equivalence-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (is-half-adjoint-equivalence-is-equiv f)
  is-equiv-is-half-adjoint-equivalence-is-equiv f =
    is-equiv-is-prop
      ( is-subtype-is-equiv f)
      ( is-prop-is-half-adjoint-equivalence f)
      ( is-equiv-is-half-adjoint-equivalence f)

-- Exercise 9.7

is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  (id {A = A} ~ id {A = A}) → has-inverse (id {A = A})
is-invertible-id-htpy-id-id A H = pair id (pair htpy-refl H)

triangle-is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  ( is-invertible-id-htpy-id-id A) ~
    ( (Σ-assoc (A → A) (λ g → (id ∘ g) ~ id) (λ s → ((pr1 s) ∘ id) ~ id)) ∘
      ( left-unit-law-Σ-map-gen
        ( λ s → ((pr1 s) ∘ id) ~ id)
        ( is-contr-sec-is-equiv (is-equiv-id A)) (pair id htpy-refl)))
triangle-is-invertible-id-htpy-id-id A H = refl

abstract
  is-equiv-invertible-id-htpy-id-id :
    {l : Level} (A : UU l) → is-equiv (is-invertible-id-htpy-id-id A)
  is-equiv-invertible-id-htpy-id-id A =
    is-equiv-comp
      ( is-invertible-id-htpy-id-id A)
      ( Σ-assoc (A → A) (λ g → (id ∘ g) ~ id) (λ s → ((pr1 s) ∘ id) ~ id))
      ( left-unit-law-Σ-map-gen
        ( λ s → ((pr1 s) ∘ id) ~ id)
        ( is-contr-sec-is-equiv (is-equiv-id A))
        ( pair id htpy-refl))
      ( triangle-is-invertible-id-htpy-id-id A)
      ( is-equiv-left-unit-law-Σ-map-gen
        ( λ s → ((pr1 s) ∘ id) ~ id)
        ( is-contr-sec-is-equiv (is-equiv-id A))
        ( pair id htpy-refl))
      ( is-equiv-Σ-assoc _ _ _)

-- Exercise 9.8

abstract
  dependent-universal-property-empty :
    {l : Level} (P : empty → UU l) → is-contr ((x : empty) → P x)
  dependent-universal-property-empty P =
    pair
      ( ind-empty {P = P})
      ( λ f → eq-htpy ind-empty)

abstract
  universal-property-empty :
    {l : Level} (X : UU l) → is-contr (empty → X)
  universal-property-empty X = dependent-universal-property-empty (λ t → X)

abstract
  uniqueness-empty :
    {l : Level} (Y : UU l) → ((l' : Level) (X : UU l') →
    is-contr (Y → X)) → is-equiv (ind-empty {P = λ t → Y})
  uniqueness-empty Y H =
    is-equiv-is-equiv-precomp ind-empty
      ( λ l X → is-equiv-is-contr
        ( λ g → g ∘ ind-empty)
        ( H _ X)
        ( universal-property-empty X))

abstract
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

abstract
  dependent-universal-property-coprod :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    (P : coprod A B → UU l3) → is-equiv (ev-inl-inr P)
  dependent-universal-property-coprod P =
    is-equiv-has-inverse
      ( λ p → ind-coprod P (pr1 p) (pr2 p))
      ( ind-Σ (λ f g → eq-pair-triv (pair refl refl)))
      ( λ s → eq-htpy (ind-coprod _ (λ x → refl) λ y → refl))

abstract
  universal-property-coprod :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (X : UU l3) →
    is-equiv (ev-inl-inr (λ (t : coprod A B) → X))
  universal-property-coprod X = dependent-universal-property-coprod (λ t → X)

abstract
  uniqueness-coprod :
    { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {Y : UU l3}
    ( i : A → Y) (j : B → Y) →
    ( (l : Level) (X : UU l) →
      is-equiv (λ (s : Y → X) → pair' (s ∘ i) (s ∘ j))) →
    is-equiv (ind-coprod (λ t → Y) i j)
  uniqueness-coprod {Y = Y} i j H =
    is-equiv-is-equiv-precomp
      ( ind-coprod _ i j)
      ( λ l X → is-equiv-right-factor
        ( λ (s : Y → X) → pair (s ∘ i) (s ∘ j))
        ( ev-inl-inr (λ t → X))
        ( precomp (ind-coprod (λ t → Y) i j) X)
        ( λ s → refl)
        ( universal-property-coprod X)
        ( H _ X))

abstract
  universal-property-coprod-is-equiv-ind-coprod :
    { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (X : UU l3)
    ( i : A → X) (j : B → X) → is-equiv (ind-coprod (λ t → X) i j) →
    ( (l4 : Level) (Y : UU l4) →
      is-equiv (λ (s : X → Y) → pair' (s ∘ i) (s ∘ j)))
  universal-property-coprod-is-equiv-ind-coprod X i j is-equiv-ind-coprod l Y =
    is-equiv-comp
      ( λ s → pair (s ∘ i) (s ∘ j))
      ( ev-inl-inr (λ t → Y))
      ( precomp (ind-coprod (λ t → X) i j) Y)
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

abstract
  dependent-universal-property-unit :
    {l : Level} (P : unit → UU l) → is-equiv (ev-star P)
  dependent-universal-property-unit P =
    is-equiv-has-inverse
      ( ind-unit)
      ( λ p → refl)
      ( λ f → eq-htpy (ind-unit refl))

abstract
  universal-property-unit :
    {l : Level} (Y : UU l) → is-equiv (ev-star (λ t → Y))
  universal-property-unit Y = dependent-universal-property-unit (λ t → Y)

abstract
  is-equiv-ind-unit-universal-property-unit :
    {l1 : Level} (X : UU l1) (x : X) →
    ((l2 : Level) (Y : UU l2) → is-equiv (λ (f : X → Y) → f x)) →
    is-equiv (ind-unit {P = λ t → X} x)
  is-equiv-ind-unit-universal-property-unit X x H =
    is-equiv-is-equiv-precomp
      ( ind-unit x)
      ( λ l Y → is-equiv-right-factor
        ( λ f → f x)
        ( ev-star (λ t → Y))
        ( precomp (ind-unit x) Y)
        ( λ f → refl)
        ( universal-property-unit Y)
        ( H _ Y))

abstract
  universal-property-unit-is-equiv-ind-unit :
    {l1 : Level} (X : UU l1) (x : X) →
    is-equiv (ind-unit {P = λ t → X} x) →
    ((l2 : Level) (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
  universal-property-unit-is-equiv-ind-unit X x is-equiv-ind-unit l2 Y =
    is-equiv-comp
      ( λ f → f x)
      ( ev-star (λ t → Y))
      ( precomp (ind-unit x) Y)
      ( λ f → refl)
      ( is-equiv-precomp-is-equiv (ind-unit x) is-equiv-ind-unit Y)
      ( universal-property-unit Y)
  
-- Exercise 9.11

Eq-sec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  sec f → sec f → UU (l1 ⊔ l2)
Eq-sec f sec-f sec-f' =
  Σ ( (pr1 sec-f) ~ (pr1 sec-f'))
    ( λ H → (pr2 sec-f) ~ ((f ·l H) ∙h (pr2 sec-f')))

reflexive-Eq-sec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (sec-f : sec f) → Eq-sec f sec-f sec-f
reflexive-Eq-sec f (pair g G) = pair htpy-refl htpy-refl

Eq-sec-eq :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (sec-f sec-f' : sec f) → Id sec-f sec-f' → Eq-sec f sec-f sec-f'
Eq-sec-eq f sec-f .sec-f refl = reflexive-Eq-sec f sec-f

abstract
  is-contr-total-Eq-sec :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (sec-f : sec f) →
    is-contr (Σ (sec f) (Eq-sec f sec-f))
  is-contr-total-Eq-sec f (pair g G) =
    is-contr-total-Eq-structure
      ( λ g' G' H → G ~ ((f ·l H) ∙h G'))
      ( is-contr-total-htpy g)
      ( pair g htpy-refl)
      ( is-contr-total-htpy G)

abstract
  is-equiv-Eq-sec-eq :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    (sec-f sec-f' : sec f) → is-equiv (Eq-sec-eq f sec-f sec-f')
  is-equiv-Eq-sec-eq f sec-f =
    fundamental-theorem-id sec-f
      ( reflexive-Eq-sec f sec-f)
      ( is-contr-total-Eq-sec f sec-f)
      ( Eq-sec-eq f sec-f)
  
  eq-Eq-sec :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    {sec-f sec-f' : sec f} → Eq-sec f sec-f sec-f' → Id sec-f sec-f'
  eq-Eq-sec f {sec-f} {sec-f'} =
    inv-is-equiv (is-equiv-Eq-sec-eq f sec-f sec-f')

isretr-section-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (sec-h : sec h) →
  ((section-comp f g h H sec-h) ∘ (section-comp' f g h H sec-h)) ~ id
isretr-section-comp f g h H (pair k K) (pair l L) =
  eq-Eq-sec g
    ( pair
      ( K ·r l)
      ( ( htpy-inv
          ( htpy-assoc
            ( htpy-inv (H ·r (k ∘ l)))
            ( H ·r (k ∘ l))
            ( (g ·l (K ·r l)) ∙h L))) ∙h
        ( htpy-ap-concat'
          ( (htpy-inv (H ·r (k ∘ l))) ∙h (H ·r (k ∘ l)))
          ( htpy-refl)
          ( (g ·l (K ·r l)) ∙h L)
          ( htpy-left-inv (H ·r (k ∘ l))))))

sec-left-factor-retract-of-sec-composition :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → (sec g) retract-of (sec f)
sec-left-factor-retract-of-sec-composition {X = X} f g h H sec-h =
  pair
    ( section-comp' f g h H sec-h)
    ( pair
      ( section-comp f g h H sec-h)
      ( isretr-section-comp f g h H sec-h))

Eq-retr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  retr f → retr f → UU (l1 ⊔ l2)
Eq-retr f retr-f retr-f' =
  Σ ( (pr1 retr-f) ~ (pr1 retr-f'))
    ( λ H → (pr2 retr-f) ~ ((H ·r f) ∙h (pr2 retr-f')))

reflexive-Eq-retr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (retr-f : retr f) → Eq-retr f retr-f retr-f
reflexive-Eq-retr f (pair h H) = pair htpy-refl htpy-refl

Eq-retr-eq :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (retr-f retr-f' : retr f) → Id retr-f retr-f' → Eq-retr f retr-f retr-f'
Eq-retr-eq f retr-f .retr-f refl = reflexive-Eq-retr f retr-f

abstract
  is-contr-total-Eq-retr :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (retr-f : retr f) →
    is-contr (Σ (retr f) (Eq-retr f retr-f))
  is-contr-total-Eq-retr f (pair h H) =
    is-contr-total-Eq-structure
      ( λ h' H' K → H ~ ((K ·r f) ∙h H'))
      ( is-contr-total-htpy h)
      ( pair h htpy-refl)
      ( is-contr-total-htpy H)

abstract
  is-equiv-Eq-retr-eq :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    (retr-f retr-f' : retr f) → is-equiv (Eq-retr-eq f retr-f retr-f')
  is-equiv-Eq-retr-eq f retr-f =
    fundamental-theorem-id retr-f
      ( reflexive-Eq-retr f retr-f)
      ( is-contr-total-Eq-retr f retr-f)
      ( Eq-retr-eq f retr-f)
  
  eq-Eq-retr :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    {retr-f retr-f' : retr f} → Eq-retr f retr-f retr-f' → Id retr-f retr-f'
  eq-Eq-retr f {retr-f} {retr-f'} =
    inv-is-equiv (is-equiv-Eq-retr-eq f retr-f retr-f')

isretr-retraction-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (retr-g : retr g) →
  ((retraction-comp f g h H retr-g) ∘ (retraction-comp' f g h H retr-g)) ~ id
isretr-retraction-comp f g h H (pair l L) (pair k K) =
  eq-Eq-retr h
    ( pair
      ( k ·l L)
      ( ( htpy-inv
          ( htpy-assoc
            ( htpy-inv ((k ∘ l) ·l H))
            ( (k ∘ l) ·l H)
            ( (k ·l (L ·r h)) ∙h K))) ∙h
        ( htpy-ap-concat'
          ( (htpy-inv ((k ∘ l) ·l H)) ∙h ((k ∘ l) ·l H))
          ( htpy-refl)
          ( (k ·l (L ·r h)) ∙h K)
          ( htpy-left-inv ((k ∘ l) ·l H)))))
  
sec-right-factor-retract-of-sec-left-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → (retr h) retract-of (retr f)
sec-right-factor-retract-of-sec-left-factor f g h H retr-g =
  pair
    ( retraction-comp' f g h H retr-g)
    ( pair
      ( retraction-comp f g h H retr-g)
      ( isretr-retraction-comp f g h H retr-g))

-- Exercise 9.12

postcomp-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (e : (i : I) → A i → B i) →
  ((i : I) → A i) → ((i : I) → B i)
postcomp-Π e f i = e i (f i)

htpy-postcomp-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {f f' : (i : I) → A i → B i} (H : (i : I) → (f i) ~ (f' i)) →
  (postcomp-Π f) ~ (postcomp-Π f')
htpy-postcomp-Π H h = eq-htpy (λ i → H i (h i))

abstract
  is-equiv-postcomp-Π :
    {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
    (e : (i : I) → A i → B i) (is-equiv-e : is-fiberwise-equiv e) →
    is-equiv (postcomp-Π e)
  is-equiv-postcomp-Π e is-equiv-e =
    is-equiv-has-inverse
      ( λ g i → inv-is-equiv (is-equiv-e i) (g i))
      ( λ g → eq-htpy (λ i → issec-inv-is-equiv (is-equiv-e i) (g i)))
      ( λ f → eq-htpy (λ i → isretr-inv-is-equiv (is-equiv-e i) (f i)))

postcomp-Π-equiv :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (e : (i : I) → (A i) ≃ (B i)) → ((i : I) → A i) ≃ ((i : I) → B i)
postcomp-Π-equiv e =
  pair
    ( postcomp-Π (λ i → map-equiv (e i)))
    ( is-equiv-postcomp-Π _ (λ i → is-equiv-map-equiv (e i)))

-- Exercise 9.13

hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
hom-slice {A = A} {B} f g = Σ (A → B) (λ h → f ~ (g ∘ h))

map-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → A → B
map-hom-slice f g h = pr1 h

triangle-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : hom-slice f g) →
  f ~ (g ∘ (map-hom-slice f g h))
triangle-hom-slice f g h = pr2 h
  
fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  hom-slice f g → (x : X) → (fib f x) → (fib g x)
fiberwise-hom-hom-slice f g (pair h H) = fib-triangle f g h H

hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((x : X) → (fib f x) → (fib g x)) → hom-slice f g
hom-slice-fiberwise-hom f g α =
  pair
    ( λ a → pr1 (α (f a) (pair a refl)))
    ( λ a → inv (pr2 (α (f a) (pair a refl))))

issec-hom-slice-fiberwise-hom-eq-htpy :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (α : (x : X) → (fib f x) → (fib g x)) (x : X) →
  (fiberwise-hom-hom-slice f g (hom-slice-fiberwise-hom f g α) x) ~ (α x)
issec-hom-slice-fiberwise-hom-eq-htpy f g α .(f a) (pair a refl) =
  eq-pair refl (inv-inv (pr2 (α (f a) (pair a refl))))

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
isretr-hom-slice-fiberwise-hom f g (pair h H) =
  eq-pair refl (eq-htpy (λ a → (inv-inv (H a))))

abstract
  is-equiv-fiberwise-hom-hom-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    is-equiv (fiberwise-hom-hom-slice f g)
  is-equiv-fiberwise-hom-hom-slice f g =
    is-equiv-has-inverse
      ( hom-slice-fiberwise-hom f g)
      ( issec-hom-slice-fiberwise-hom f g)
      ( isretr-hom-slice-fiberwise-hom f g)

abstract
  is-equiv-hom-slice-fiberwise-hom :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    is-equiv (hom-slice-fiberwise-hom f g)
  is-equiv-hom-slice-fiberwise-hom f g =
    is-equiv-has-inverse
      ( fiberwise-hom-hom-slice f g)
      ( isretr-hom-slice-fiberwise-hom f g)
      ( issec-hom-slice-fiberwise-hom f g)

equiv-slice :
  {l1 l2 l3 : Level} (X : UU l1) {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
equiv-slice X {A} {B} f g = Σ (A ≃ B) (λ e → f ~ (g ∘ (map-equiv e)))

hom-slice-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice X f g → hom-slice f g
hom-slice-equiv-slice f g (pair (pair h is-equiv-h) H) = pair h H

{- We first prove two closely related generic lemmas that establishes 
   equivalences of subtypes -}

abstract
  is-equiv-subtype-is-equiv :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    is-equiv f → ((x : A) → (Q (f x)) → P x) → is-equiv (toto Q f g)
  is-equiv-subtype-is-equiv {Q = Q} is-subtype-P is-subtype-Q f g is-equiv-f h =
    is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map Q f g is-equiv-f
      ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x)) (h x))

abstract
  is-equiv-subtype-is-equiv' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
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

abstract
  is-fiberwise-equiv-fiberwise-equiv-equiv-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X)
    (t : hom-slice f g) → is-equiv (pr1 t) →
    is-fiberwise-equiv (fiberwise-hom-hom-slice f g t)
  is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g (pair h H) =
    is-fiberwise-equiv-is-equiv-triangle f g h H

left-factor-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  Σ (hom-slice f g) (λ hH → is-equiv (pr1 hH)) →
  Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
left-factor-fiberwise-equiv-equiv-slice f g =
  toto
    ( is-fiberwise-equiv)
    ( fiberwise-hom-hom-slice f g)
    ( is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g)

swap-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice X f g →
  Σ (hom-slice f g) (λ hH → is-equiv (pr1 hH))
swap-equiv-slice {A = A} {B} f g =
  double-structure-swap (A → B) is-equiv (λ h → f ~ (g ∘ h))

abstract
  is-equiv-swap-equiv-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    is-equiv (swap-equiv-slice f g)
  is-equiv-swap-equiv-slice f g =
    is-equiv-double-structure-swap _ is-equiv (λ h → (f ~ (g ∘ h)))

abstract
  fiberwise-equiv-equiv-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    equiv-slice X f g → Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
  fiberwise-equiv-equiv-slice {X = X} {A} {B} f g =
    ( left-factor-fiberwise-equiv-equiv-slice f g) ∘
    ( swap-equiv-slice f g)

abstract
  is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    (t : hom-slice f g) →
    ((x : X) → is-equiv (fiberwise-hom-hom-slice f g t x)) →
    is-equiv (pr1 t)
  is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
    f g (pair h H) =
    is-equiv-triangle-is-fiberwise-equiv f g h H

abstract
  is-equiv-fiberwise-equiv-equiv-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    is-equiv (fiberwise-equiv-equiv-slice f g)
  is-equiv-fiberwise-equiv-equiv-slice {X = X} {A} {B} f g =
    is-equiv-comp
      ( fiberwise-equiv-equiv-slice f g)
      ( left-factor-fiberwise-equiv-equiv-slice f g)
      ( swap-equiv-slice f g)
      ( htpy-refl)
      ( is-equiv-swap-equiv-slice f g)
      ( is-equiv-subtype-is-equiv
        ( λ t → is-subtype-is-equiv (pr1 t))
        ( λ α → is-prop-Π (λ x → is-subtype-is-equiv (α x)))
        ( fiberwise-hom-hom-slice f g)
        ( is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g)
        ( is-equiv-fiberwise-hom-hom-slice f g)
        ( is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
          f g))

-- Exercise 9.14

hom-over-morphism :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) → UU (l1 ⊔ (l2 ⊔ l4))
hom-over-morphism i f g = hom-slice (i ∘ f) g

fiberwise-hom-hom-over-morphism :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  hom-over-morphism i f g → (x : X) → (fib f x) → (fib g (i x))
fiberwise-hom-hom-over-morphism i f g (pair h H) .(f a) (pair a refl) =
  pair (h a) (inv (H a))

hom-over-morphism-fiberwise-hom :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  ((x : X) → (fib f x) → (fib g (i x))) → hom-over-morphism i f g
hom-over-morphism-fiberwise-hom i f g α =
  pair
    ( λ a → pr1 (α (f a) (pair a refl)))
    ( λ a → inv (pr2 (α (f a) (pair a refl))))

issec-hom-over-morphism-fiberwise-hom-eq-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : X → Y) (f : A → X) (g : B → Y) →
  (α : (x : X) → (fib f x) → (fib g (i x))) (x : X) →
  ( fiberwise-hom-hom-over-morphism i f g
    ( hom-over-morphism-fiberwise-hom i f g α) x) ~ (α x)
issec-hom-over-morphism-fiberwise-hom-eq-htpy i f g α .(f a) (pair a refl) =
  eq-pair refl (inv-inv (pr2 (α (f a) (pair a refl))))

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
isretr-hom-over-morphism-fiberwise-hom i f g (pair h H) =
  eq-pair refl (eq-htpy (λ a → (inv-inv (H a))))

abstract
  is-equiv-fiberwise-hom-hom-over-morphism :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
    (i : X → Y) (f : A → X) (g : B → Y) →
    is-equiv (fiberwise-hom-hom-over-morphism i f g)
  is-equiv-fiberwise-hom-hom-over-morphism i f g =
    is-equiv-has-inverse
      ( hom-over-morphism-fiberwise-hom i f g)
      ( issec-hom-over-morphism-fiberwise-hom i f g)
      ( isretr-hom-over-morphism-fiberwise-hom i f g)

abstract
  is-equiv-hom-over-morphism-fiberwise-hom :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
    (i : X → Y) (f : A → X) (g : B → Y) →
    is-equiv (hom-over-morphism-fiberwise-hom i f g)
  is-equiv-hom-over-morphism-fiberwise-hom i f g =
    is-equiv-has-inverse
      ( fiberwise-hom-hom-over-morphism i f g)
      ( isretr-hom-over-morphism-fiberwise-hom i f g)
      ( issec-hom-over-morphism-fiberwise-hom i f g)

-- Exercise 9.15

set-isomorphism :
  {l1 l2 : Level} (A : hSet l1) (B : hSet l2) → UU (l1 ⊔ l2)
set-isomorphism A B =
  Σ ((pr1 A) → (pr1 B)) has-inverse

has-inverse-is-half-adjoint-equivalence :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-half-adjoint-equivalence f → has-inverse f
has-inverse-is-half-adjoint-equivalence f =
  tot (λ g → tot (λ G → pr1))

set-isomorphism-equiv-fiberwise :
  {l1 l2 : Level} (A : hSet l1) (B : hSet l2) →
  (f : (pr1 A) → (pr1 B)) → is-equiv f → has-inverse f
set-isomorphism-equiv-fiberwise A B f =
  ( has-inverse-is-half-adjoint-equivalence f) ∘
  ( is-half-adjoint-equivalence-is-equiv f)

abstract
  is-equiv-has-inverse-is-half-adjoint-equivalence-is-set :
    {l1 l2 : Level} (A : hSet l1) (B : hSet l2) (f : (pr1 A) → (pr1 B)) →
    is-equiv (has-inverse-is-half-adjoint-equivalence f)
  is-equiv-has-inverse-is-half-adjoint-equivalence-is-set
    (pair A is-set-A) (pair B is-set-B) f =
    is-equiv-tot-is-fiberwise-equiv
      ( λ g → is-equiv-tot-is-fiberwise-equiv
        ( λ G → is-equiv-pr1-is-contr
          ( coherence-is-half-adjoint-equivalence f g G)
          ( λ H → is-contr-Π
            ( λ x → is-set-B _ _ (G (f x)) (ap f (H x))))))

abstract
  is-fiberwise-equiv-set-isomorphism-equiv-fiberwise :
    {l1 l2 : Level} (A : hSet l1) (B : hSet l2) →
    is-fiberwise-equiv (set-isomorphism-equiv-fiberwise A B)
  is-fiberwise-equiv-set-isomorphism-equiv-fiberwise A B f =
    is-equiv-comp
      ( set-isomorphism-equiv-fiberwise A B f)
      ( has-inverse-is-half-adjoint-equivalence f)
      ( is-half-adjoint-equivalence-is-equiv f)
      ( htpy-refl)
      ( is-equiv-is-half-adjoint-equivalence-is-equiv f)
      ( is-equiv-has-inverse-is-half-adjoint-equivalence-is-set A B f)

set-isomorphism-equiv :
  {l1 l2 : Level} (A : hSet l1) (B : hSet l2) →
  ((pr1 A) ≃ (pr1 B)) → set-isomorphism A B
set-isomorphism-equiv A B =
  tot (set-isomorphism-equiv-fiberwise A B)

abstract
  is-equiv-set-isomorphism-equiv :
    {l1 l2 : Level} (A : hSet l1) (B : hSet l2) →
    is-equiv (set-isomorphism-equiv A B)
  is-equiv-set-isomorphism-equiv A B =
    is-equiv-tot-is-fiberwise-equiv
      ( is-fiberwise-equiv-set-isomorphism-equiv-fiberwise A B)

{- Some lemmas about equivalences on Π-types -}

abstract
  is-equiv-htpy-inv-con :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
    ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
    is-equiv (htpy-inv-con H K L)
  is-equiv-htpy-inv-con H K L =
    is-equiv-postcomp-Π _ (λ x → is-equiv-inv-con (H x) (K x) (L x))

equiv-htpy-inv-con :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
  ( (H ∙h K) ~ L) ≃ (K ~ ((htpy-inv H) ∙h L))
equiv-htpy-inv-con H K L =
  pair
    ( htpy-inv-con H K L)
    ( is-equiv-htpy-inv-con H K L)

abstract
  is-equiv-htpy-con-inv :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
    ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
    is-equiv (htpy-con-inv H K L)
  is-equiv-htpy-con-inv H K L =
    is-equiv-postcomp-Π _ (λ x → is-equiv-con-inv (H x) (K x) (L x))

equiv-htpy-con-inv :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
  ( (H ∙h K) ~ L) ≃ (H ~ (L ∙h (htpy-inv K)))
equiv-htpy-con-inv H K L =
  pair
    ( htpy-con-inv H K L)
    ( is-equiv-htpy-con-inv H K L)

map-equiv-Π :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a')) →
  ( (a' : A') → B' a') → ( (a : A) → B a)
map-equiv-Π {B' = B'} B e f =
  ( postcomp-Π (λ a →
    ( tr B (issec-inv-is-equiv (is-equiv-map-equiv e) a)) ∘
    ( map-equiv (f (inv-is-equiv (is-equiv-map-equiv e) a))))) ∘
  ( precomp-Π (inv-is-equiv (is-equiv-map-equiv e)) B')

id-map-equiv-Π :
  { l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  ( map-equiv-Π B (equiv-id A) (λ a → equiv-id (B a))) ~ id
id-map-equiv-Π B = htpy-refl

abstract
  is-equiv-map-equiv-Π :
    { l1 l2 l3 l4 : Level}
    { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
    ( e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a')) →
    is-equiv (map-equiv-Π B e f)
  is-equiv-map-equiv-Π {B' = B'} B e f =
    is-equiv-comp'
      ( postcomp-Π (λ a →
        ( tr B (issec-inv-is-equiv (is-equiv-map-equiv e) a)) ∘
        ( map-equiv (f (inv-is-equiv (is-equiv-map-equiv e) a)))))
      ( precomp-Π (inv-is-equiv (is-equiv-map-equiv e)) B')
      ( is-equiv-precomp-Π-is-equiv
        ( inv-is-equiv (is-equiv-map-equiv e))
        ( is-equiv-inv-is-equiv (is-equiv-map-equiv e))
        ( B'))
      ( is-equiv-postcomp-Π _
        ( λ a → is-equiv-comp'
          ( tr B (issec-inv-is-equiv (is-equiv-map-equiv e) a))
          ( map-equiv (f (inv-is-equiv (is-equiv-map-equiv e) a)))
          ( is-equiv-map-equiv (f (inv-is-equiv (is-equiv-map-equiv e) a)))
          ( is-equiv-tr B (issec-inv-is-equiv (is-equiv-map-equiv e) a))))

equiv-Π :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a')) →
  ( (a' : A') → B' a') ≃ ( (a : A) → B a)
equiv-Π B e f = pair (map-equiv-Π B e f) (is-equiv-map-equiv-Π B e f)

HTPY-map-equiv-Π :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} (B' : A' → UU l2) {A : UU l3} (B : A → UU l4)
  ( e e' : A' ≃ A) (H : htpy-equiv e e') →
  UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
HTPY-map-equiv-Π {A' = A'} B' {A} B e e' H =
  ( f : (a' : A') → B' a' ≃ B (map-equiv e a')) →
  ( f' : (a' : A') → B' a' ≃ B (map-equiv e' a')) →
  ( K : (a' : A') → ((tr B (H a')) ∘ (map-equiv (f a'))) ~ (map-equiv (f' a'))) →
  ( map-equiv-Π B e f) ~ (map-equiv-Π B e' f')

htpy-map-equiv-Π-htpy-refl :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) →
  HTPY-map-equiv-Π B' B e e (reflexive-htpy-equiv e)
htpy-map-equiv-Π-htpy-refl {B' = B'} B e f f' K =
  ( htpy-postcomp-Π
    ( λ a →
      ( tr B (issec-inv-is-equiv (is-equiv-map-equiv e) a)) ·l
      ( K (inv-is-equiv (is-equiv-map-equiv e) a)))) ·r
  ( precomp-Π (inv-is-equiv (is-equiv-map-equiv e)) B')

abstract
  htpy-map-equiv-Π :
    { l1 l2 l3 l4 : Level}
    { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
    ( e e' : A' ≃ A) (H : htpy-equiv e e') →
    HTPY-map-equiv-Π B' B e e' H
  htpy-map-equiv-Π {B' = B'} B e e' H f f' K =
    ind-htpy-equiv e
      ( HTPY-map-equiv-Π B' B e)
      ( htpy-map-equiv-Π-htpy-refl B e)
      e' H f f' K
  
  comp-htpy-map-equiv-Π :
    { l1 l2 l3 l4 : Level}
    { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
    ( e : A' ≃ A) →
    Id ( htpy-map-equiv-Π {B' = B'} B e e (reflexive-htpy-equiv e))
      ( ( htpy-map-equiv-Π-htpy-refl B e))
  comp-htpy-map-equiv-Π {B' = B'} B e =
    comp-htpy-equiv e
      ( HTPY-map-equiv-Π B' B e)
      ( htpy-map-equiv-Π-htpy-refl B e)

map-automorphism-Π :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
  ( (a : A) → B a) → ((a : A) → B a)
map-automorphism-Π {B = B} e f =
  ( postcomp-Π (λ a → (inv-is-equiv (is-equiv-map-equiv (f a))))) ∘
  ( precomp-Π (map-equiv e) B)

abstract
  is-equiv-map-automorphism-Π :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
    is-equiv (map-automorphism-Π e f)
  is-equiv-map-automorphism-Π {B = B} e f =
    is-equiv-comp' _ _
      ( is-equiv-precomp-Π-is-equiv _ (is-equiv-map-equiv e) B)
      ( is-equiv-postcomp-Π _
        ( λ a → is-equiv-inv-is-equiv (is-equiv-map-equiv (f a))))

automorphism-Π :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
  ( (a : A) → B a) ≃ ((a : A) → B a)
automorphism-Π e f =
  pair (map-automorphism-Π e f) (is-equiv-map-automorphism-Π e f)

-- is-contr-total-Eq-Π

is-contr-total-Eq-Π :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3) →
  ( is-contr-total-C : (x : A) → is-contr (Σ (B x) (C x))) →
  ( f : (x : A) → B x) →
  is-contr (Σ ((x : A) → B x) (λ g → (x : A) → C x (g x)))
is-contr-total-Eq-Π {A = A} {B} C is-contr-total-C f =
  is-contr-equiv'
    ( (x : A) → Σ (B x) (C x))
    ( equiv-choice-∞ C)
    ( is-contr-Π is-contr-total-C)
