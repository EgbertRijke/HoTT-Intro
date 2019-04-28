{-# OPTIONS --without-K #-}

module 07-contractible-types where

import 06-equivalences
open 06-equivalences public

-- Section 6.1 Contractible types

is-contr :
  {i : Level} → UU i → UU i
is-contr A = Σ A (λ a → (x : A) → Id a x)

abstract
  center :
    {i : Level} {A : UU i} → is-contr A → A
  center (pair c is-contr-A) = c
  
  -- We make sure that the contraction is coherent in a straightforward way
  contraction :
    {i : Level} {A : UU i} (is-contr-A : is-contr A) →
    (const A A (center is-contr-A) ~ id)
  contraction (pair c C) x = (inv (C c)) ∙ (C x)
  
  coh-contraction :
    {i : Level} {A : UU i} (is-contr-A : is-contr A) →
    Id (contraction is-contr-A (center is-contr-A)) refl
  coh-contraction (pair c C) = left-inv (C c)

-- We show that contractible types satisfy an induction principle akin to the induction principle of the unit type: singleton induction. This can be helpful to give short proofs of many facts.

ev-pt :
  {i j : Level} (A : UU i) (a : A) (B : A → UU j) → ((x : A) → B x) → B a
ev-pt A a B f = f a

abstract
  sing-ind-is-contr :
    {i j : Level} (A : UU i) (is-contr-A : is-contr A) (B : A → UU j) →
    (a : A) → B a → (x : A) → B x
  sing-ind-is-contr A is-contr-A B a b x =
    tr B ((inv (contraction is-contr-A a)) ∙ (contraction is-contr-A x)) b
  
  sing-comp-is-contr :
    {i j : Level} (A : UU i) (is-contr-A : is-contr A) (B : A → UU j) (a : A) →
    ((ev-pt A a B) ∘ (sing-ind-is-contr A is-contr-A B a)) ~ id
  sing-comp-is-contr A is-contr-A B a b =
    ap (λ ω → tr B ω b) (left-inv (contraction is-contr-A a))

  sec-ev-pt-is-contr :
    {i j : Level} (A : UU i) (is-contr-A : is-contr A) (B : A → UU j) (a : A) →
    sec (ev-pt A a B)
  sec-ev-pt-is-contr A is-contr-A B a =
    pair
      ( sing-ind-is-contr A is-contr-A B a)
      ( sing-comp-is-contr A is-contr-A B a)

abstract
  is-sing-is-contr :
    {i j : Level} (A : UU i) (is-contr-A : is-contr A) (B : A → UU j) →
    ( a : A) → sec (ev-pt A a B)
  is-sing-is-contr A is-contr-A B a =
    pair
      ( sing-ind-is-contr A is-contr-A B a)
      ( sing-comp-is-contr A is-contr-A B a)

is-sing :
  {i : Level} (A : UU i) → A → UU (lsuc i)
is-sing {i} A a = (B : A → UU i) → sec (ev-pt A a B)

abstract
  is-contr-sing-ind :
    {i : Level} (A : UU i) (a : A) →
    ((P : A → UU i) → P a → (x : A) → P x) → is-contr A
  is-contr-sing-ind A a S = pair a (S (λ x → Id a x) refl)

abstract
  is-contr-is-sing :
    {i : Level} (A : UU i) (a : A) → is-sing A a → is-contr A
  is-contr-is-sing A a S = is-contr-sing-ind A a (λ P → pr1 (S P))

abstract
  is-sing-unit : is-sing unit star
  is-sing-unit B = pair ind-unit (λ b → refl)

is-contr-unit : is-contr unit
is-contr-unit = is-contr-is-sing unit star (is-sing-unit)

abstract
  is-sing-total-path :
    {i : Level} (A : UU i) (a : A) →
    is-sing (Σ A (λ x → Id a x)) (pair a refl)
  is-sing-total-path A a B = pair (ind-Σ ∘ (ind-Id a _)) (λ b → refl)

abstract
  is-contr-total-path :
    {i : Level} {A : UU i} (a : A) → is-contr (Σ A (λ x → Id a x))
  is-contr-total-path {A = A} a = is-contr-is-sing _ _ (is-sing-total-path A a)

-- Section 6.2 Contractible maps

-- We first introduce the notion of a fiber of a map.
fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (b : B) → UU (i ⊔ j)
fib f b = Σ _ (λ x → Id (f x) b)

fib' :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (b : B) → UU (i ⊔ j)
fib' f b = Σ _ (λ x → Id b (f x))

-- A map is said to be contractible if its fibers are contractible in the usual sense.
is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-contr-map f = (y : _) → is-contr (fib f y)

-- Our goal is to show that contractible maps are equivalences.
-- First we construct the inverse of a contractible map.
inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-contr-map f → B → A
inv-is-contr-map is-contr-f y = pr1 (center (is-contr-f y))

-- Then we show that the inverse is a section.
issec-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (is-contr-f : is-contr-map f) → (f ∘ (inv-is-contr-map is-contr-f)) ~ id
issec-is-contr-map is-contr-f y = pr2 (center (is-contr-f y))

-- Then we show that the inverse is also a retraction.
isretr-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (is-contr-f : is-contr-map f) → ((inv-is-contr-map is-contr-f) ∘ f) ~ id
isretr-is-contr-map {_} {_} {A} {B} {f} is-contr-f x =
  ap ( pr1 {B = λ z → Id (f z) (f x)})
     ( ( inv
         ( contraction
           ( is-contr-f (f x))
           ( pair
             ( inv-is-contr-map is-contr-f (f x))
             ( issec-is-contr-map is-contr-f (f x))))) ∙
       ( contraction (is-contr-f (f x)) (pair x refl)))

-- Finally we put it all together to show that contractible maps are equivalences.

abstract
  is-equiv-is-contr-map :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    is-contr-map f → is-equiv f
  is-equiv-is-contr-map is-contr-f =
    is-equiv-has-inverse
      ( inv-is-contr-map is-contr-f)
      ( issec-is-contr-map is-contr-f)
      ( isretr-is-contr-map is-contr-f)

-- Section 6.3 Equivalences are contractible maps

-- The goal in this section is to show that all equivalences are contractible maps. This theorem is much harder than anything we've seen so far, but many future results will depend on it.

-- We characterize the identity types of fibers

Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  fib f y → fib f y → UU (i ⊔ j)
Eq-fib f y s t =
  Σ (Id (pr1 s) (pr1 t)) (λ α → Id ((ap f α) ∙ (pr2 t)) (pr2 s))

reflexive-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  (s : fib f y) → Eq-fib f y s s
reflexive-Eq-fib f y s = pair refl refl

Eq-fib-eq :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → (Id s t) → Eq-fib f y s t
Eq-fib-eq f y {s} refl = reflexive-Eq-fib f y s

eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → Eq-fib f y s t → Id s t
eq-Eq-fib f y {pair x p} {pair .x .p} (pair refl refl) = refl

issec-eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → ((Eq-fib-eq f y {s} {t}) ∘ (eq-Eq-fib f y {s} {t})) ~ id
issec-eq-Eq-fib f y {pair x p} {pair .x .p} (pair refl refl) = refl

isretr-eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → ((eq-Eq-fib f y {s} {t}) ∘ (Eq-fib-eq f y {s} {t})) ~ id
isretr-eq-Eq-fib f y {pair x p} {.(pair x p)} refl = refl

abstract
  is-equiv-Eq-fib-eq :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
    {s t : fib f y} → is-equiv (Eq-fib-eq f y {s} {t})
  is-equiv-Eq-fib-eq f y {s} {t} =
    is-equiv-has-inverse
      ( eq-Eq-fib f y)
      ( issec-eq-Eq-fib f y)
      ( isretr-eq-Eq-fib f y)

abstract
  is-equiv-eq-Eq-fib :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
    {s t : fib f y} → is-equiv (eq-Eq-fib f y {s} {t})
  is-equiv-eq-Eq-fib f y {s} {t} =
    is-equiv-has-inverse
      ( Eq-fib-eq f y)
      ( isretr-eq-Eq-fib f y)
      ( issec-eq-Eq-fib f y)

-- Next, we improve the homotopy G : f ∘ g ~ id if f comes equipped with the
-- structure has-inverse f.

inv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  has-inverse f → B → A
inv-has-inverse inv-f = pr1 inv-f

issec-inv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (inv-f : has-inverse f) → (f ∘ (inv-has-inverse inv-f)) ~ id
issec-inv-has-inverse {f = f} (pair g (pair G H)) y =
  (inv (G (f (g y)))) ∙ (ap f (H (g y)) ∙ (G y))

isretr-inv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (inv-f : has-inverse f) → ((inv-has-inverse inv-f) ∘ f) ~ id
isretr-inv-has-inverse inv-f = pr2 (pr2 inv-f)

-- Before we start we will develop some of the ingredients of the construction.

-- We will need the naturality of homotopies.
htpy-nat :
  {i j : Level} {A : UU i} {B : UU j} {f g : A → B} (H : f ~ g)
  {x y : A} (p : Id x y) →
  Id ((H x) ∙ (ap g p)) ((ap f p) ∙ (H y))
htpy-nat H refl = right-unit

-- We will also need to undo concatenation on the left and right. One might notice that, in the terminology of Lecture 7, we almost show here that concat p and concat' q are embeddings.
left-unwhisk :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) {q r : Id y z} →
  Id (p ∙ q) (p ∙ r) → Id q r
left-unwhisk refl s = (inv left-unit) ∙ (s ∙ left-unit)

right-unwhisk :
  {i : Level} {A : UU i} {x y z : A} {p q : Id x y}
  (r : Id y z) → Id (p ∙ r) (q ∙ r) → Id p q
right-unwhisk refl s = (inv right-unit) ∙ (s ∙ right-unit)

-- We will also need to compute with homotopies to the identity function. 
htpy-red :
  {i : Level} {A : UU i} {f : A → A} (H : f ~ id) →
  (x : A) → Id (H (f x)) (ap f (H x))
htpy-red {_} {A} {f} H x =
  right-unwhisk (H x)
    ( ( ap (concat (H (f x)) x) (inv (ap-id (H x)))) ∙
      ( htpy-nat H (H x)))

square :
  {i : Level} {A : UU i} {x y1 y2 z : A}
  (p1 : Id x y1) (q1 : Id y1 z) (p2 : Id x y2) (q2 : Id y2 z) → UU i
square p q p' q' = Id (p ∙ q) (p' ∙ q')

sq-left-whisk :
  {i : Level} {A : UU i} {x y1 y2 z : A} {p1 p1' : Id x y1}
  (s : Id p1 p1') {q1 : Id y1 z} {p2 : Id x y2} {q2 : Id y2 z} →
  square p1 q1 p2 q2 → square p1' q1 p2 q2
sq-left-whisk refl sq = sq

sq-top-whisk :
  {i : Level} {A : UU i} {x y1 y2 z : A}
  (p1 : Id x y1) (q1 : Id y1 z)
  (p2 : Id x y2) {p2' : Id x y2} (s : Id p2 p2') (q2 : Id y2 z) →
  square p1 q1 p2 q2 → square p1 q1 p2' q2
sq-top-whisk p1 q1 p2 refl q2 sq = sq

coherence-inv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (inv-f : has-inverse f) →
  (f ·l (isretr-inv-has-inverse inv-f)) ~ ((issec-inv-has-inverse inv-f) ·r f)
coherence-inv-has-inverse {f = f} (pair g (pair G H)) x =
  inv-con
    ( G (f (g (f x))))
    ( ap f (H x))
    ( (ap f (H (g (f x)))) ∙ (G (f x)))
    ( sq-top-whisk
      ( G (f (g (f x))))
      ( ap f (H x))
      ( (ap (f ∘ (g ∘ f)) (H x)))
      ( (ap-comp f (g ∘ f) (H x)) ∙ (inv (ap (ap f) (htpy-red H x))))
      ( G (f x))
      ( htpy-nat (htpy-right-whisk G f) (H x)))

-- Now the proof that equivalences are contractible maps really begins. Note that we have already shown that any equivalence has an inverse. Our strategy is therefore to first show that maps with inverses are contractible, and then deduce the claim about equivalences.

abstract
  center-has-inverse :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    has-inverse f → (y : B) → fib f y
  center-has-inverse {i} {j} {A} {B} {f} inv-f y =
    pair
      ( inv-has-inverse inv-f y)
      ( issec-inv-has-inverse inv-f y)
  
  contraction-has-inverse :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    (I : has-inverse f) → (y : B) → (t : fib f y) →
    Id (center-has-inverse I y) t
  contraction-has-inverse {i} {j} {A} {B} {f}
    ( pair g (pair G H)) y (pair x refl) =
    eq-Eq-fib f y (pair 
      ( H x)
      ( ( right-unit) ∙
        ( coherence-inv-has-inverse (pair g (pair G H)) x)))
  
  is-contr-map-has-inverse : {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    has-inverse f → is-contr-map f
  is-contr-map-has-inverse inv-f y =
    pair
      ( center-has-inverse inv-f y)
      ( contraction-has-inverse inv-f y)
  
  is-contr-map-is-equiv : {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    is-equiv f → is-contr-map f
  is-contr-map-is-equiv = is-contr-map-has-inverse ∘ has-inverse-is-equiv

abstract
  is-contr-total-path' :
    {i : Level} {A : UU i} (a : A) → is-contr (Σ A (λ x → Id x a))
  is-contr-total-path' a = is-contr-map-is-equiv (is-equiv-id _) a

-- Exercises

-- Exercise 6.1

-- In this exercise we are asked to show that the identity types of a contractible type are again contractible. In the terminology of Lecture 8: we are showing that contractible types are propositions.

abstract
  is-prop-is-contr : {i : Level} {A : UU i} → is-contr A →
    (x y : A) → is-contr (Id x y)
  is-prop-is-contr {i} {A} is-contr-A =
    sing-ind-is-contr A is-contr-A
      ( λ x → ((y : A) → is-contr (Id x y)))
      ( center is-contr-A)
      ( λ y → pair
        ( contraction is-contr-A y)
        ( ind-Id
          ( center is-contr-A)
          ( λ z (p : Id (center is-contr-A) z) →
            Id (contraction is-contr-A z) p)
          ( coh-contraction is-contr-A)
          ( y)))

abstract
  is-prop-is-contr' : {i : Level} {A : UU i} → is-contr A →
    (x y : A) → Id x y
  is-prop-is-contr' is-contr-A x y =
    center (is-prop-is-contr is-contr-A x y)

-- Exercise 6.2

-- In this exercise we are showing that contractible types are closed under retracts.

abstract
  is-contr-retract-of : {i j : Level} {A : UU i} (B : UU j) →
    A retract-of B → is-contr B → is-contr A
  is-contr-retract-of B (pair i (pair r isretr)) is-contr-B =
    pair
      ( r (center is-contr-B))
      ( λ x → (ap r (contraction is-contr-B (i x))) ∙ (isretr x))

-- Exercise 6.3

-- In this exercise we are showing that a type is contractible if and only if the constant map to the unit type is an equivalence. This can be used to derive a '3-for-2 property' for contractible types, which may come in handy sometimes.

abstract
  is-equiv-const-is-contr :
    {i : Level} {A : UU i} → is-contr A → is-equiv (const A unit star)
  is-equiv-const-is-contr {i} {A} is-contr-A =
    pair
      ( pair (ind-unit (center is-contr-A)) (ind-unit refl))
      ( pair (const unit A (center is-contr-A)) (contraction is-contr-A))

abstract
  is-contr-is-equiv-const :
    {i : Level} {A : UU i} → is-equiv (const A unit star) → is-contr A
  is-contr-is-equiv-const (pair (pair g issec) (pair h isretr)) =
    pair (h star) isretr

abstract
  is-contr-is-equiv :
    {i j : Level} {A : UU i} (B : UU j) (f : A → B) →
    is-equiv f → is-contr B → is-contr A
  is-contr-is-equiv B f is-equiv-f is-contr-B =
    is-contr-is-equiv-const
      ( is-equiv-comp'
        ( const B unit star)
        ( f)
        ( is-equiv-f)
        ( is-equiv-const-is-contr is-contr-B))

abstract
  is-contr-equiv :
    {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) → is-contr B → is-contr A
  is-contr-equiv B (pair e is-equiv-e) is-contr-B =
    is-contr-is-equiv B e is-equiv-e is-contr-B

abstract
  is-contr-is-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (f : A → B) →
    is-equiv f → is-contr A → is-contr B
  is-contr-is-equiv' A f is-equiv-f is-contr-A =
    is-contr-is-equiv A
      ( inv-is-equiv is-equiv-f)
      ( is-equiv-inv-is-equiv is-equiv-f)
      ( is-contr-A)

abstract
  is-contr-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) → is-contr A → is-contr B
  is-contr-equiv' A (pair e is-equiv-e) is-contr-A =
    is-contr-is-equiv' A e is-equiv-e is-contr-A

abstract
  is-equiv-is-contr :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
    is-contr A → is-contr B → is-equiv f
  is-equiv-is-contr {i} {j} {A} {B} f is-contr-A is-contr-B =
    is-equiv-has-inverse
      ( const B A (center is-contr-A))
      ( sing-ind-is-contr B is-contr-B _ _
        ( inv (contraction is-contr-B (f (center is-contr-A)))))
      ( contraction is-contr-A)

equiv-is-contr :
  {i j : Level} {A : UU i} {B : UU j} →
  is-contr A → is-contr B → A ≃ B
equiv-is-contr is-contr-A is-contr-B =
  pair
    ( λ a → center is-contr-B)
    ( is-equiv-is-contr _ is-contr-A is-contr-B)

-- Exercise 6.4

-- In this exercise we will show that if the base type in a Σ-type is contractible, then the Σ-type is equivalent to the fiber at the center of contraction. This can be seen as a left unit law for Σ-types. We will derive a right unit law for Σ-types in Lecture 7 (not because it is unduable here, but it is useful to have some knowledge of fiberwise equivalences).

left-unit-law-Σ-map :
  {i j : Level} {C : UU i} (B : C → UU j)
  (is-contr-C : is-contr C) → B (center is-contr-C) → Σ C B
left-unit-law-Σ-map B is-contr-C y = pair (center is-contr-C) y

left-unit-law-Σ-map-conv :
  {i j : Level} {C : UU i} (B : C → UU j)
  (is-contr-C : is-contr C) → Σ C B → B (center is-contr-C)
left-unit-law-Σ-map-conv B is-contr-C =
  ind-Σ
    ( sing-ind-is-contr _ is-contr-C
      ( λ x → B x → B (center is-contr-C))
      ( center is-contr-C)
      ( id))

left-inverse-left-unit-law-Σ-map-conv :
  {i j : Level} {C : UU i} (B : C → UU j) (is-contr-C : is-contr C) →
  ( ( left-unit-law-Σ-map-conv B is-contr-C) ∘
    ( left-unit-law-Σ-map B is-contr-C)) ~ id
left-inverse-left-unit-law-Σ-map-conv B is-contr-C y =
  ap
    ( λ (f : B (center is-contr-C) → B (center is-contr-C)) → f y)
    ( sing-comp-is-contr _ is-contr-C
      ( λ x → B x → B (center is-contr-C))
      ( center is-contr-C)
      ( id))

right-inverse-left-unit-law-Σ-map-conv :
  {i j : Level} {C : UU i} (B : C → UU j) (is-contr-C : is-contr C) →
  ( ( left-unit-law-Σ-map B is-contr-C) ∘
    ( left-unit-law-Σ-map-conv B is-contr-C)) ~ id
right-inverse-left-unit-law-Σ-map-conv B is-contr-C =
  ind-Σ
    ( sing-ind-is-contr _ is-contr-C
      ( λ x → (y : B x) →
        Id ( ( ( left-unit-law-Σ-map B is-contr-C) ∘
               ( left-unit-law-Σ-map-conv B is-contr-C))
             ( pair x y))
           ( id (pair x y))) (center is-contr-C)
      ( λ y → ap
        ( left-unit-law-Σ-map B is-contr-C)
        ( ap
          ( λ f → f y)
          ( sing-comp-is-contr _ is-contr-C
            ( λ x → B x → B (center is-contr-C)) (center is-contr-C) id))))

abstract
  is-equiv-left-unit-law-Σ-map :
    {i j : Level} {C : UU i} (B : C → UU j) (is-contr-C : is-contr C) →
    is-equiv (left-unit-law-Σ-map B is-contr-C)
  is-equiv-left-unit-law-Σ-map B is-contr-C =
    is-equiv-has-inverse
      ( left-unit-law-Σ-map-conv B is-contr-C)
      ( right-inverse-left-unit-law-Σ-map-conv B is-contr-C)
      ( left-inverse-left-unit-law-Σ-map-conv B is-contr-C)

abstract
  is-equiv-left-unit-law-Σ-map-conv :
    {i j : Level} {C : UU i} (B : C → UU j) (is-contr-C : is-contr C) →
    is-equiv (left-unit-law-Σ-map-conv B is-contr-C)
  is-equiv-left-unit-law-Σ-map-conv B is-contr-C =
    is-equiv-has-inverse
      ( left-unit-law-Σ-map B is-contr-C)
      ( left-inverse-left-unit-law-Σ-map-conv B is-contr-C)
      ( right-inverse-left-unit-law-Σ-map-conv B is-contr-C)

left-unit-law-Σ : {i j : Level} {C : UU i} (B : C → UU j)
  (is-contr-C : is-contr C) → B (center is-contr-C) ≃ Σ C B
left-unit-law-Σ B is-contr-C =
  pair
    ( left-unit-law-Σ-map B is-contr-C)
    ( is-equiv-left-unit-law-Σ-map B is-contr-C)

left-unit-law-Σ-map-gen :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  is-contr A → (x : A) → B x → Σ A B
left-unit-law-Σ-map-gen B is-contr-A x y = pair x y

abstract
  is-equiv-left-unit-law-Σ-map-gen :
    {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
    (is-contr-A : is-contr A) →
    (x : A) → is-equiv (left-unit-law-Σ-map-gen B is-contr-A x)
  is-equiv-left-unit-law-Σ-map-gen B is-contr-A x =
    is-equiv-comp
      ( left-unit-law-Σ-map-gen B is-contr-A x)
      ( left-unit-law-Σ-map B is-contr-A)
      ( tr B (inv (contraction is-contr-A x)))
      ( λ y → eq-pair (inv (contraction is-contr-A x)) refl)
      ( is-equiv-tr B (inv (contraction is-contr-A x)))
      ( is-equiv-left-unit-law-Σ-map B is-contr-A)

left-unit-law-Σ-gen :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  (is-contr-A : is-contr A) →
  (x : A) → B x ≃ Σ A B
left-unit-law-Σ-gen B is-contr-A x =
  pair
    ( left-unit-law-Σ-map-gen B is-contr-A x)
    ( is-equiv-left-unit-law-Σ-map-gen B is-contr-A x)

-- Exercise 6.6

-- In this exercise we show that the domain of a map is equivalent to the total space of its fibers.

Σ-fib-to-domain :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) → (Σ B (fib f)) → A
Σ-fib-to-domain f t = pr1 (pr2 t)

triangle-Σ-fib-to-domain :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) →
  pr1 ~ (f ∘ (Σ-fib-to-domain f))
triangle-Σ-fib-to-domain f t = inv (pr2 (pr2 t))

domain-to-Σ-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → A → Σ B (fib f)
domain-to-Σ-fib f x = pair (f x) (pair x refl)

left-inverse-domain-to-Σ-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) →
  ((domain-to-Σ-fib f) ∘ (Σ-fib-to-domain f)) ~ id
left-inverse-domain-to-Σ-fib f (pair .(f x) (pair x refl)) = refl

right-inverse-domain-to-Σ-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) →
  ((Σ-fib-to-domain f) ∘ (domain-to-Σ-fib f)) ~ id
right-inverse-domain-to-Σ-fib f x = refl

abstract
  is-equiv-Σ-fib-to-domain :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B ) →
    is-equiv (Σ-fib-to-domain f)
  is-equiv-Σ-fib-to-domain f =
    is-equiv-has-inverse
      ( domain-to-Σ-fib f)
      ( right-inverse-domain-to-Σ-fib f)
      ( left-inverse-domain-to-Σ-fib f)

equiv-Σ-fib-to-domain :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) → Σ B (fib f) ≃ A
equiv-Σ-fib-to-domain f =
  pair (Σ-fib-to-domain f) (is-equiv-Σ-fib-to-domain f)

-- Exercise 6.7

-- In this exercise we show that if a cartesian product is contractible, then so are its factors. We make use of the fact that contractible types are closed under retracts, just because that is a useful property to practice with. Other proofs are possible too.

abstract
  is-contr-left-factor-prod :
    {i j : Level} (A : UU i) (B : UU j) → is-contr (A × B) → is-contr A
  is-contr-left-factor-prod A B is-contr-AB =
    is-contr-retract-of
      ( A × B)
      ( pair
        ( λ x → pair x (pr2 (center is-contr-AB)))
        ( pair pr1 (λ x → refl)))
      ( is-contr-AB)

abstract
  is-contr-right-factor-prod :
    {i j : Level} (A : UU i) (B : UU j) → is-contr (A × B) → is-contr B
  is-contr-right-factor-prod A B is-contr-AB =
    is-contr-left-factor-prod B A
      ( is-contr-equiv
        ( A × B)
        ( equiv-swap-prod B A)
        ( is-contr-AB))

abstract
  is-contr-prod :
    {i j : Level} {A : UU i} {B : UU j} →
    is-contr A → is-contr B → is-contr (A × B)
  is-contr-prod {A = A} {B = B} is-contr-A is-contr-B =
    is-contr-equiv' B
      ( left-unit-law-Σ (λ x → B) is-contr-A)
      ( is-contr-B)

-- Exercise 6.8

-- Given any family B over A, there is a map from the fiber of the projection map (pr1 : Σ A B → A) to the type (B a), i.e. the fiber of B at a. In this exercise we define this map, and show that it is an equivalence, for every a : A.

fib-fam-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j)
  (a : A) → fib (pr1 {B = B}) a → B a
fib-fam-fib-pr1 B a (pair (pair x y) p) = tr B p y

fib-pr1-fib-fam :
  {i j : Level} {A : UU i} (B : A → UU j)
  (a : A) → B a → fib (pr1 {B = B}) a
fib-pr1-fib-fam B a b = pair (pair a b) refl

left-inverse-fib-pr1-fib-fam :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  ((fib-pr1-fib-fam B a) ∘ (fib-fam-fib-pr1 B a)) ~ id
left-inverse-fib-pr1-fib-fam B a (pair (pair .a y) refl) = refl

right-inverse-fib-pr1-fib-fam :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  ((fib-fam-fib-pr1 B a) ∘ (fib-pr1-fib-fam B a)) ~ id
right-inverse-fib-pr1-fib-fam B a b = refl

abstract
  is-equiv-fib-fam-fib-pr1 :
    {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
    is-equiv (fib-fam-fib-pr1 B a)
  is-equiv-fib-fam-fib-pr1 B a =
    is-equiv-has-inverse
      ( fib-pr1-fib-fam B a)
      ( right-inverse-fib-pr1-fib-fam B a)
      ( left-inverse-fib-pr1-fib-fam B a)

equiv-fib-fam-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  fib (pr1 {B = B}) a ≃ B a
equiv-fib-fam-fib-pr1 B a =
  pair (fib-fam-fib-pr1 B a) (is-equiv-fib-fam-fib-pr1 B a)

abstract
  is-equiv-fib-pr1-fib-fam :
    {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
    is-equiv (fib-pr1-fib-fam B a)
  is-equiv-fib-pr1-fib-fam B a =
    is-equiv-has-inverse
      ( fib-fam-fib-pr1 B a)
      ( left-inverse-fib-pr1-fib-fam B a)
      ( right-inverse-fib-pr1-fib-fam B a)

equiv-fib-pr1-fib-fam :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  B a ≃ fib (pr1 {B = B}) a
equiv-fib-pr1-fib-fam B a =
  pair (fib-pr1-fib-fam B a) (is-equiv-fib-pr1-fib-fam B a)

abstract
  is-equiv-pr1-is-contr :
    {i j : Level} {A : UU i} (B : A → UU j) →
    ((a : A) → is-contr (B a)) → is-equiv (pr1 {B = B})
  is-equiv-pr1-is-contr B is-contr-B =
    is-equiv-is-contr-map
      ( λ x → is-contr-equiv
        ( B x)
        ( equiv-fib-fam-fib-pr1 B x)
        ( is-contr-B x))

abstract
  is-contr-is-equiv-pr1 :
    {i j : Level} {A : UU i} (B : A → UU j) →
    (is-equiv (pr1 {B = B})) → ((a : A) → is-contr (B a))
  is-contr-is-equiv-pr1 B is-equiv-pr1-B a =
    is-contr-equiv'
      ( fib pr1 a)
      ( equiv-fib-fam-fib-pr1 B a)
      ( is-contr-map-is-equiv is-equiv-pr1-B a)

right-unit-law-Σ :
  {i j : Level} {A : UU i} (B : A → UU j) →
  ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
right-unit-law-Σ B is-contr-B =
  pair pr1 (is-equiv-pr1-is-contr B is-contr-B)
