{-# OPTIONS --without-K --exact-split --safe #-}

module 08-equivalences where

import 07-finite-sets
open 07-finite-sets public

--------------------------------------------------------------------------------

-- Section 8.1 Homotopies

-- Definition 8.1.2

_~_ :
  {i j : Level} {A : UU i} {B : A → UU j} (f g : (x : A) → B x) → UU (i ⊔ j)
f ~ g = (x : _) → Id (f x) (g x)

-- Example 8.1.3

neg-neg-𝟚 : (neg-𝟚 ∘ neg-𝟚) ~ id
neg-neg-𝟚 true = refl
neg-neg-𝟚 false = refl

-- Definition 8.1.5

refl-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f : (x : A) → B x} → f ~ f
refl-htpy x = refl

{- Most of the time we get by with refl-htpy. However, sometimes Agda wants us
   to specify the implicit argument. The it is easier to call refl-htpy' than
   to use Agda's {f = ?} notation. -}
   
refl-htpy' :
  {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → f ~ f
refl-htpy' f = refl-htpy

htpy-inv :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) → (g ~ f)
htpy-inv H x = inv (H x)

_∙h_ :
  {i j : Level} {A : UU i} {B : A → UU j} {f g h : (x : A) → B x} →
  (f ~ g) → (g ~ h) → (f ~ h)
_∙h_ H K x = (H x) ∙ (K x)

htpy-concat :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) → (h : (x : A) → B x) → (g ~ h) → (f ~ h)
htpy-concat H h K x = concat (H x) (h x) (K x)

htpy-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} →
  (g ~ h) → (f ~ g) → (f ~ h)
htpy-concat' f K H = H ∙h K

-- Proposition 8.1.6

-- Proposition 8.1.6 (i)

htpy-assoc :
  {i j : Level} {A : UU i} {B : A → UU j} {f g h k : (x : A) → B x} →
  (H : f ~ g) → (K : g ~ h) → (L : h ~ k) →
  ((H ∙h K) ∙h L) ~ (H ∙h (K ∙h L))
htpy-assoc H K L x = assoc (H x) (K x) (L x)

-- Proposition 8.1.6 (ii)

htpy-left-unit :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (refl-htpy ∙h H) ~ H
htpy-left-unit x = left-unit

htpy-right-unit :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (H ∙h refl-htpy) ~ H
htpy-right-unit x = right-unit

-- Proposition 8.1.6 (iii)

htpy-left-inv :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → ((htpy-inv H) ∙h H) ~ refl-htpy
htpy-left-inv H x = left-inv (H x)

htpy-right-inv :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → (H ∙h (htpy-inv H)) ~ refl-htpy
htpy-right-inv H x = right-inv (H x)

-- Definition 8.1.7

-- Definition 8.1.7 (i)

htpy-left-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  (h : B → C) {f g : A → B} → (f ~ g) → ((h ∘ f) ~ (h ∘ g))
htpy-left-whisk h H x = ap h (H x)

_·l_ = htpy-left-whisk

-- Definition 8.1.7 (ii)

htpy-right-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  {g h : B → C} (H : g ~ h) (f : A → B) → ((g ∘ f) ~ (h ∘ f))
htpy-right-whisk H f x = H (f x)

_·r_ = htpy-right-whisk

--------------------------------------------------------------------------------

-- Section 8.2 Bi-invertible maps

-- Definition 8.2.1

-- Definition 8.2.1 (i)

sec :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
sec {i} {j} {A} {B} f = Σ (B → A) (λ g → (f ∘ g) ~ id)

-- Definition 8.2.1 (ii)

retr :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
retr {i} {j} {A} {B} f = Σ (B → A) (λ g → (g ∘ f) ~ id)

_retract-of_ :
  {i j : Level} → UU i → UU j → UU (i ⊔ j)
A retract-of B = Σ (A → B) retr

section-retract-of :
  {i j : Level} {A : UU i} {B : UU j} → A retract-of B → A → B
section-retract-of = pr1

retr-section-retract-of :
  {i j : Level} {A : UU i} {B : UU j} (R : A retract-of B) →
  retr (section-retract-of R)
retr-section-retract-of = pr2

retraction-retract-of :
  {i j : Level} {A : UU i} {B : UU j} → (A retract-of B) → B → A
retraction-retract-of R = pr1 (retr-section-retract-of R)

is-retr-retraction-retract-of :
  {i j : Level} {A : UU i} {B : UU j} (R : A retract-of B) →
  ((retraction-retract-of R) ∘ (section-retract-of R)) ~ id
is-retr-retraction-retract-of R = pr2 (retr-section-retract-of R)

-- Definition 8.2.1 (ii)

is-equiv :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-equiv f = sec f × retr f

_≃_ :
  {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B) (λ f → is-equiv f)

map-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (A → B)
map-equiv e = pr1 e

is-equiv-map-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) → is-equiv (map-equiv e)
is-equiv-map-equiv e = pr2 e

-- Example 8.2.3

is-equiv-id :
  {i : Level} (A : UU i) → is-equiv (id {i} {A})
is-equiv-id A = pair (pair id refl-htpy) (pair id refl-htpy)

equiv-id :
  {i : Level} (A : UU i) → A ≃ A
equiv-id A = pair id (is-equiv-id A)

-- Example 8.2.4

abstract
  is-equiv-neg-𝟚 : is-equiv neg-𝟚
  is-equiv-neg-𝟚 =
    pair (pair neg-𝟚 neg-neg-𝟚) (pair neg-𝟚 neg-neg-𝟚)

equiv-neg-𝟚 : bool ≃ bool
equiv-neg-𝟚 = pair neg-𝟚 is-equiv-neg-𝟚

-- Example 8.2.5

-- We show that succ-ℤ is an equivalence

abstract
  is-equiv-succ-ℤ : is-equiv succ-ℤ
  is-equiv-succ-ℤ =
    pair (pair pred-ℤ right-inverse-pred-ℤ) (pair pred-ℤ left-inverse-pred-ℤ)

equiv-succ-ℤ : ℤ ≃ ℤ
equiv-succ-ℤ = pair succ-ℤ is-equiv-succ-ℤ

-- We show that pred-ℤ is an equivalence

abstract
  is-equiv-pred-ℤ : is-equiv pred-ℤ
  is-equiv-pred-ℤ =
    pair (pair succ-ℤ left-inverse-pred-ℤ) (pair succ-ℤ right-inverse-pred-ℤ)

equiv-pred-ℤ : ℤ ≃ ℤ
equiv-pred-ℤ = pair pred-ℤ is-equiv-pred-ℤ

-- We show that add-ℤ x is an equivalence

abstract
  is-equiv-add-ℤ : (x : ℤ) → is-equiv (add-ℤ x)
  is-equiv-add-ℤ x =
    pair
      ( pair
        ( add-ℤ (neg-ℤ x))
        ( λ y →
          ( inv (associative-add-ℤ x (neg-ℤ x) y)) ∙
          ( ( ap (add-ℤ' y) (right-inverse-law-add-ℤ x)) ∙
            ( left-unit-law-add-ℤ y))))
      ( pair
        ( add-ℤ (neg-ℤ x))
        ( λ y →
          ( inv (associative-add-ℤ (neg-ℤ x) x y)) ∙
          ( ( ap (add-ℤ' y) (left-inverse-law-add-ℤ x)) ∙
            ( left-unit-law-add-ℤ y))))

equiv-add-ℤ : ℤ → (ℤ ≃ ℤ)
equiv-add-ℤ x = pair (add-ℤ x) (is-equiv-add-ℤ x)

-- We show that add-ℤ' y is an equivalence

abstract
  is-equiv-add-ℤ' : (y : ℤ) → is-equiv (add-ℤ' y)
  is-equiv-add-ℤ' y =
    pair
      ( pair
        ( add-ℤ' (neg-ℤ y))
        ( λ x →
          ( associative-add-ℤ x (neg-ℤ y) y) ∙
          ( ( ap (add-ℤ x) (left-inverse-law-add-ℤ y)) ∙
            ( right-unit-law-add-ℤ x))))
      ( pair
        ( add-ℤ' (neg-ℤ y))
        ( λ x →
          ( associative-add-ℤ x y (neg-ℤ y)) ∙
          ( ( ap (add-ℤ x) (right-inverse-law-add-ℤ y)) ∙
            ( right-unit-law-add-ℤ x))))

equiv-add-ℤ' : ℤ → (ℤ ≃ ℤ)
equiv-add-ℤ' y = pair (add-ℤ' y) (is-equiv-add-ℤ' y)

-- We show that neg-ℤ is an equivalence

abstract
  is-equiv-neg-ℤ : is-equiv neg-ℤ
  is-equiv-neg-ℤ = pair (pair neg-ℤ neg-neg-ℤ) (pair neg-ℤ neg-neg-ℤ)

equiv-neg-ℤ : ℤ ≃ ℤ
equiv-neg-ℤ = pair neg-ℤ is-equiv-neg-ℤ

-- We show that succ-Fin k is an equivalence

-- We show that pred-Fin k is an equivalence

-- We show that add-Fin k x is an equivalence

-- We show that add-Fin' k y is an equivalence

-- We show that neg-Fin k is an equivalence

-- Remark 8.2.6

has-inverse :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
has-inverse {i} {j} {A} {B} f =
  Σ (B → A) (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

-- Proposition 8.2.7

is-equiv-has-inverse' :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  has-inverse f → is-equiv f
is-equiv-has-inverse' (pair g (pair H K)) = pair (pair g H) (pair g K)

is-equiv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (g : B → A) (H : (f ∘ g) ~ id) (K : (g ∘ f) ~ id) → is-equiv f
is-equiv-has-inverse g H K =
  is-equiv-has-inverse' (pair g (pair H K))

-- Corollary 8.2.8

htpy-section-retraction :
  { i j : Level} {A : UU i} {B : UU j} {f : A → B}
  ( is-equiv-f : is-equiv f) →
  ( (pr1 (pr1 is-equiv-f))) ~ (pr1 (pr2 is-equiv-f))
htpy-section-retraction {i} {j} {A} {B} {f} (pair (pair g G) (pair h H)) =
    (htpy-inv (H ·r g)) ∙h (h ·l G)

has-inverse-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-equiv f → has-inverse f
has-inverse-is-equiv {i} {j} {A} {B} {f} (pair (pair g G) (pair h H)) =
  let is-equiv-f = pair (pair g G) (pair h H) in
  pair g (pair G (((htpy-section-retraction is-equiv-f) ·r f) ∙h H))

inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → B → A
inv-is-equiv is-equiv-f = pr1 (has-inverse-is-equiv is-equiv-f)

issec-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → (f ∘ (inv-is-equiv is-equiv-f)) ~ id
issec-inv-is-equiv is-equiv-f = pr1 (pr2 (has-inverse-is-equiv is-equiv-f))

isretr-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → ((inv-is-equiv is-equiv-f) ∘ f) ~ id
isretr-inv-is-equiv is-equiv-f = pr2 (pr2 (has-inverse-is-equiv is-equiv-f))

is-equiv-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → is-equiv (inv-is-equiv is-equiv-f)
is-equiv-inv-is-equiv {i} {j} {A} {B} {f} is-equiv-f =
  is-equiv-has-inverse f
    ( isretr-inv-is-equiv is-equiv-f)
    ( issec-inv-is-equiv is-equiv-f)

inv-map-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (B → A)
inv-map-equiv e = inv-is-equiv (is-equiv-map-equiv e)

issec-inv-map-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  ((map-equiv e) ∘ (inv-map-equiv e)) ~ id
issec-inv-map-equiv e = issec-inv-is-equiv (is-equiv-map-equiv e)

isretr-inv-map-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  ((inv-map-equiv e) ∘ (map-equiv e)) ~ id
isretr-inv-map-equiv e = isretr-inv-is-equiv (is-equiv-map-equiv e)

is-equiv-inv-map-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) → is-equiv (inv-map-equiv e)
is-equiv-inv-map-equiv e =
  is-equiv-inv-is-equiv (is-equiv-map-equiv e)

inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (B ≃ A)
inv-equiv e = pair (inv-map-equiv e) (is-equiv-inv-map-equiv e)

-- Section 8.3 The identity type of a Σ-type

-- Definition 8.3.1

Eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) → UU (i ⊔ j)
Eq-Σ {B = B} s t = Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))

-- Lemma 8.3.2

reflexive-Eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s : Σ A B) → Eq-Σ s s
reflexive-Eq-Σ (pair a b) = pair refl refl

-- Definition 8.3.3

pair-eq :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  (Id s t) → Eq-Σ s t
pair-eq {s = s} refl = reflexive-Eq-Σ s

-- Theorem 8.3.4

eq-pair :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  (α : Id (pr1 s) (pr1 t)) → Id (tr B α (pr2 s)) (pr2 t) → Id s t
eq-pair {B = B} {pair x y} {pair .x .y} refl refl = refl

eq-pair' :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  Eq-Σ s t → Id s t
eq-pair' (pair α β) = eq-pair α β

isretr-pair-eq :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  ((pair-eq {s = s} {t}) ∘ (eq-pair' {s = s} {t})) ~ id {A = Eq-Σ s t}
isretr-pair-eq (pair x y) (pair .x .y) (pair refl refl) = refl

issec-pair-eq :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  ((eq-pair' {s = s} {t}) ∘ (pair-eq {s = s} {t})) ~ id
issec-pair-eq (pair x y) .(pair x y) refl = refl

abstract
  is-equiv-eq-pair :
    {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
    is-equiv (eq-pair' {s = s} {t})
  is-equiv-eq-pair s t =
    is-equiv-has-inverse
      ( pair-eq)
      ( issec-pair-eq s t)
      ( isretr-pair-eq s t)

abstract
  is-equiv-pair-eq :
    {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
    is-equiv (pair-eq {s = s} {t})
  is-equiv-pair-eq s t =
    is-equiv-has-inverse
      ( eq-pair')
      ( isretr-pair-eq s t)
      ( issec-pair-eq s t)

η-pair :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (t : Σ A B) →
  Id (pair (pr1 t) (pr2 t)) t
η-pair t = eq-pair refl refl

{- For our convenience, we repeat the above argument for cartesian products. -}

Eq-prod :
  {i j : Level} {A : UU i} {B : UU j} (s t : A × B) → UU (i ⊔ j)
Eq-prod s t = (Id (pr1 s) (pr1 t)) × (Id (pr2 s) (pr2 t))

{- We also define a function eq-pair-triv, which is like eq-pair but simplified 
   for the case where B is just a type. -}

eq-pair-triv' :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  Eq-prod s t → Id s t
eq-pair-triv' (pair x y) (pair .x .y) (pair refl refl) = refl

eq-pair-triv :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  Eq-prod s t → Id s t
eq-pair-triv {s = s} {t} = eq-pair-triv' s t

{- Ideally, we would use the 3-for-2 property of equivalences to show that 
   eq-pair-triv is an equivalence, using that eq-pair is an equivalence. 
   Indeed, there is an equivalence 
   
     (Id x x') × (Id y y') → Σ (Id x x') (λ p → Id (tr (λ x → B) p y) y'). 

   However, to show that this map is an equivalence we either give a direct 
   proof (in which case we might as well have given a direct proof that 
   eq-pair-triv is an equivalence), or we use the fact that it is the induced 
   map on total spaces of a fiberwise equivalence (the topic of Lecture 8). 
   Thus it seems that a direct proof showing that eq-pair-triv is an 
   equivalence is quickest for now. -}

pair-eq-triv' :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  Id s t → Eq-prod s t
pair-eq-triv' s t α = pair (ap pr1 α) (ap pr2 α)

isretr-pair-eq-triv' :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  ((pair-eq-triv' s t) ∘ (eq-pair-triv' s t)) ~ id
isretr-pair-eq-triv' (pair x y) (pair .x .y) (pair refl refl) = refl

issec-pair-eq-triv' :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  ((eq-pair-triv' s t) ∘ (pair-eq-triv' s t)) ~ id
issec-pair-eq-triv' (pair x y) (pair .x .y) refl = refl

abstract
  is-equiv-eq-pair-triv' :
    {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
    is-equiv (eq-pair-triv' s t)
  is-equiv-eq-pair-triv' s t =
    is-equiv-has-inverse
      ( pair-eq-triv' s t)
      ( issec-pair-eq-triv' s t)
      ( isretr-pair-eq-triv' s t)

-- Exercises

-- Exercise 8.1

{- We show that inv is an equivalence. -}

inv-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (inv (inv p)) p
inv-inv refl = refl

abstract
  is-equiv-inv :
    {i : Level} {A : UU i} (x y : A) →
    is-equiv (λ (p : Id x y) → inv p)
  is-equiv-inv x y =
    is-equiv-has-inverse inv inv-inv inv-inv

equiv-inv :
  {i : Level} {A : UU i} (x y : A) → (Id x y) ≃ (Id y x)
equiv-inv x y = pair inv (is-equiv-inv x y)

{- We show that concat p is an equivalence, for any path p. -}

inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  (Id x z) → (Id y z)
inv-concat p = concat (inv p)

isretr-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  ((inv-concat p z) ∘ (concat p z)) ~ id
isretr-inv-concat refl z q = refl

issec-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  ((concat p z) ∘ (inv-concat p z)) ~ id
issec-inv-concat refl z refl = refl

abstract
  is-equiv-concat :
    {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
    is-equiv (concat p z)
  is-equiv-concat p z =
    is-equiv-has-inverse
      ( inv-concat p z)
      ( issec-inv-concat p z)
      ( isretr-inv-concat p z)

equiv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  Id y z ≃ Id x z
equiv-concat p z = pair (concat p z) (is-equiv-concat p z)

{- We show that concat' q is an equivalence, for any path q. -}

concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} → Id y z → Id x y → Id x z
concat' x q p = p ∙ q

inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} → Id y z →
  Id x z → Id x y
inv-concat' x q = concat' x (inv q)

isretr-inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  ((inv-concat' x q) ∘ (concat' x q)) ~ id
isretr-inv-concat' x refl refl = refl

issec-inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  ((concat' x q) ∘ (inv-concat' x q)) ~ id
issec-inv-concat' x refl refl = refl

abstract
  is-equiv-concat' :
    {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
    is-equiv (concat' x q)
  is-equiv-concat' x q =
    is-equiv-has-inverse
      ( inv-concat' x q)
      ( issec-inv-concat' x q)
      ( isretr-inv-concat' x q)

equiv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  Id x y ≃ Id x z
equiv-concat' x q = pair (concat' x q) (is-equiv-concat' x q)

{- We show that tr B p is an equivalence, for an path p and any type family B.
   -}
   
inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A} →
  Id x y → B y → B x
inv-tr B p = tr B (inv p)

isretr-inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → ((inv-tr B p ) ∘ (tr B p)) ~ id
isretr-inv-tr B refl b = refl

issec-inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → ((tr B p) ∘ (inv-tr B p)) ~ id
issec-inv-tr B refl b = refl

abstract
  is-equiv-tr :
    {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
    (p : Id x y) → is-equiv (tr B p)
  is-equiv-tr B p =
    is-equiv-has-inverse
      ( inv-tr B p)
      ( issec-inv-tr B p)
      ( isretr-inv-tr B p)

equiv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → (B x) ≃ (B y)
equiv-tr B p = pair (tr B p) (is-equiv-tr B p)

-- Exercise 8.2

abstract
  not-equiv-const :
    (b : bool) → ¬ (is-equiv (const bool bool b))
  not-equiv-const true (pair (pair s issec) (pair r isretr)) =
    neq-false-true-𝟚 (inv (issec false))
  not-equiv-const false (pair (pair s issec) (pair r isretr)) =
    neq-false-true-𝟚 (issec true)

-- Exercise 8.3

-- Exercise 8.3(a)

abstract
  is-equiv-htpy :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} (g : A → B) →
    f ~ g → is-equiv g → is-equiv f
  is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)) =
    pair
      ( pair gs ((H ·r gs) ∙h issec))
      ( pair gr ((gr ·l H) ∙h isretr))

abstract
  is-equiv-htpy' :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) {g : A → B} →
    f ~ g → is-equiv f → is-equiv g
  is-equiv-htpy' f H = is-equiv-htpy f (htpy-inv H)

-- Exercise 8.3(b)

htpy-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f f' : A → B} (H : f ~ f') →
  (is-equiv-f : is-equiv f) (is-equiv-f' : is-equiv f') →
  (inv-is-equiv is-equiv-f) ~ (inv-is-equiv is-equiv-f')
htpy-inv-is-equiv H is-equiv-f is-equiv-f' b =
  ( inv (isretr-inv-is-equiv is-equiv-f' (inv-is-equiv is-equiv-f b))) ∙
  ( ap (inv-is-equiv is-equiv-f')
    ( ( inv (H (inv-is-equiv is-equiv-f b))) ∙
      ( issec-inv-is-equiv is-equiv-f b)))

-- Exercise 8.4

-- Exercise 8.4(a)

{- Exercise 8.4 (a) asks to show that, given a commuting triangle f ~ g ∘ h and
   a section s of h, we get a new commuting triangle g ~ f ∘ s. Moreover, under
   the same assumptions it follows that f has a section if and only if g has a 
   section. -}

triangle-section :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (S : sec h) →
  g ~ (f ∘ (pr1 S))
triangle-section f g h H (pair s issec) =
  htpy-inv (( H ·r s) ∙h (g ·l issec))

section-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → sec f → sec g
section-comp f g h H sec-h sec-f =
  pair (h ∘ (pr1 sec-f)) ((htpy-inv (H ·r (pr1 sec-f))) ∙h (pr2 sec-f))

section-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → sec g → sec f
section-comp' f g h H sec-h sec-g =
  pair
    ( (pr1 sec-h) ∘ (pr1 sec-g))
    ( ( H ·r ((pr1 sec-h) ∘ (pr1 sec-g))) ∙h
      ( ( g ·l ((pr2 sec-h) ·r (pr1 sec-g))) ∙h ((pr2 sec-g))))

-- Exercise 8.4(b)

{- Exercise 8.4 (b) is dual to exercise 8.4 (a). It asks to show that, given a 
   commuting triangle f ~ g ∘ h and a retraction r of g, we get a new commuting
   triangle h ~ r ∘ f. Moreover, under these assumptions it also follows that f
   has a retraction if and only if h has a retraction. -}

triangle-retraction :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (R : retr g) →
  h ~ ((pr1 R) ∘ f)
triangle-retraction f g h H (pair r isretr) =
  htpy-inv (( r ·l H) ∙h (isretr ·r h))

retraction-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → retr f → retr h
retraction-comp f g h H retr-g retr-f =
  pair
    ( (pr1 retr-f) ∘ g)
    ( (htpy-inv ((pr1 retr-f) ·l H)) ∙h (pr2 retr-f))

retraction-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → retr h → retr f
retraction-comp' f g h H retr-g retr-h =
  pair
    ( (pr1 retr-h) ∘ (pr1 retr-g))
    ( ( ((pr1 retr-h) ∘ (pr1 retr-g)) ·l H) ∙h
      ( ((pr1 retr-h) ·l ((pr2 retr-g) ·r h)) ∙h (pr2 retr-h)))

-- Exercise 8.4(c)

{- In Exercise 8.4 (c) we use the constructions of parts (a) and (b) to derive 
   the 3-for-2 property of equivalences. -}

abstract
  is-equiv-comp :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-equiv h → is-equiv g → is-equiv f
  is-equiv-comp f g h H (pair sec-h retr-h) (pair sec-g retr-g) =
    pair
      ( section-comp' f g h H sec-h sec-g)
      ( retraction-comp' f g h H retr-g retr-h)

abstract
  is-equiv-comp' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) →
    is-equiv h → is-equiv g → is-equiv (g ∘ h)
  is-equiv-comp' g h = is-equiv-comp (g ∘ h) g h refl-htpy

equiv-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} →
  (B ≃ X) → (A ≃ B) → (A ≃ X)
equiv-comp g h =
  pair ((pr1 g) ∘ (pr1 h)) (is-equiv-comp' (pr1 g) (pr1 h) (pr2 h) (pr2 g))

_∘e_ :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} →
  (B ≃ X) → (A ≃ B) → (A ≃ X)
_∘e_ = equiv-comp

abstract
  is-equiv-left-factor :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-equiv f → is-equiv h → is-equiv g
  is-equiv-left-factor f g h H
    ( pair sec-f retr-f)
    ( pair (pair sh sh-issec) retr-h) =
    pair
      ( section-comp f g h H (pair sh sh-issec) sec-f)
      ( retraction-comp' g f sh
        ( triangle-section f g h H (pair sh sh-issec))
        ( retr-f)
        ( pair h sh-issec))

abstract
  is-equiv-left-factor' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) →
    is-equiv (g ∘ h) → is-equiv h → is-equiv g
  is-equiv-left-factor' g h =
    is-equiv-left-factor (g ∘ h) g h refl-htpy

abstract
  is-equiv-right-factor :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-equiv g → is-equiv f → is-equiv h
  is-equiv-right-factor f g h H
    ( pair sec-g (pair rg rg-isretr))
    ( pair sec-f retr-f) =
    pair
      ( section-comp' h rg f
        ( triangle-retraction f g h H (pair rg rg-isretr))
        ( sec-f)
        ( pair g rg-isretr))
      ( retraction-comp f g h H (pair rg rg-isretr) retr-f)

abstract
  is-equiv-right-factor' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) → 
    is-equiv g → is-equiv (g ∘ h) → is-equiv h
  is-equiv-right-factor' g h =
    is-equiv-right-factor (g ∘ h) g h refl-htpy

abstract
  is-equiv-is-section-is-equiv :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
    is-equiv f → (f ∘ g) ~ id → is-equiv g
  is-equiv-is-section-is-equiv {B = B} {f = f} {g = g} is-equiv-f H =
    is-equiv-right-factor id f g (htpy-inv H) is-equiv-f (is-equiv-id B)

abstract
  is-equiv-is-retraction-is-equiv :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
    is-equiv f  → (g ∘ f) ~ id → is-equiv g
  is-equiv-is-retraction-is-equiv {A = A} {f = f} {g = g} is-equiv-f H =
    is-equiv-left-factor id g f (htpy-inv H) (is-equiv-id A) is-equiv-f
    
-- Exercise 8.5

-- Exercise 8.5 (a)

-- Exercise 8.5 (b)

{- We prove the left unit law for coproducts. -}

inv-inr-coprod-empty :
  {l : Level} (X : UU l) → coprod empty X → X
inv-inr-coprod-empty X (inr x) = x

issec-inv-inr-coprod-empty :
  {l : Level} (X : UU l) → (inr ∘ (inv-inr-coprod-empty X)) ~ id
issec-inv-inr-coprod-empty X (inr x) = refl

isretr-inv-inr-coprod-empty :
  {l : Level} (X : UU l) → ((inv-inr-coprod-empty X) ∘ inr) ~ id
isretr-inv-inr-coprod-empty X x = refl

is-equiv-inr-coprod-empty :
  {l : Level} (X : UU l) → is-equiv (inr {A = empty} {B = X})
is-equiv-inr-coprod-empty X =
  is-equiv-has-inverse
    ( inv-inr-coprod-empty X)
    ( issec-inv-inr-coprod-empty X)
    ( isretr-inv-inr-coprod-empty X)

left-unit-law-coprod :
  {l : Level} (X : UU l) → X ≃ (coprod empty X)
left-unit-law-coprod X = pair inr (is-equiv-inr-coprod-empty X)

{- We prove the right unit law for coproducts. -}

inv-inl-coprod-empty :
  {l : Level} (X : UU l) → (coprod X empty) → X
inv-inl-coprod-empty X (inl x) = x

issec-inv-inl-coprod-empty :
  {l : Level} (X : UU l) → (inl ∘ (inv-inl-coprod-empty X)) ~ id
issec-inv-inl-coprod-empty X (inl x) = refl

isretr-inv-inl-coprod-empty :
  {l : Level} (X : UU l) → ((inv-inl-coprod-empty X) ∘ inl) ~ id
isretr-inv-inl-coprod-empty X x = refl

is-equiv-inl-coprod-empty :
  {l : Level} (X : UU l) → is-equiv (inl {A = X} {B = empty})
is-equiv-inl-coprod-empty X =
  is-equiv-has-inverse
    ( inv-inl-coprod-empty X)
    ( issec-inv-inl-coprod-empty X)
    ( isretr-inv-inl-coprod-empty X)

right-unit-law-coprod :
  {l : Level} (X : UU l) → X ≃ (coprod X empty)
right-unit-law-coprod X =
  pair inl (is-equiv-inl-coprod-empty X)

{- We prove a left zero law for cartesian products. -}

inv-pr1-prod-empty :
  {l : Level} (X : UU l) → empty → empty × X
inv-pr1-prod-empty X ()

issec-inv-pr1-prod-empty :
  {l : Level} (X : UU l) → (pr1 ∘ (inv-pr1-prod-empty X)) ~ id
issec-inv-pr1-prod-empty X ()

isretr-inv-pr1-prod-empty :
  {l : Level} (X : UU l) → ((inv-pr1-prod-empty X) ∘ pr1) ~ id
isretr-inv-pr1-prod-empty X (pair () x)

is-equiv-pr1-prod-empty :
  {l : Level} (X : UU l) → is-equiv (pr1 {A = empty} {B = λ t → X})
is-equiv-pr1-prod-empty X =
  is-equiv-has-inverse
    ( inv-pr1-prod-empty X)
    ( issec-inv-pr1-prod-empty X)
    ( isretr-inv-pr1-prod-empty X)

left-zero-law-prod :
  {l : Level} (X : UU l) → (empty × X) ≃ empty
left-zero-law-prod X =
  pair pr1 (is-equiv-pr1-prod-empty X)

{- We prove the right zero law for cartesian products. -}

inv-pr2-prod-empty :
  {l : Level} (X : UU l) → empty → (X × empty)
inv-pr2-prod-empty X ()

issec-inv-pr2-prod-empty :
  {l : Level} (X : UU l) → (pr2 ∘ (inv-pr2-prod-empty X)) ~ id
issec-inv-pr2-prod-empty X ()

isretr-inv-pr2-prod-empty :
  {l : Level} (X : UU l) → ((inv-pr2-prod-empty X) ∘ pr2) ~ id
isretr-inv-pr2-prod-empty X (pair x ())

is-equiv-pr2-prod-empty :
  {l : Level} (X : UU l) → is-equiv (pr2 {A = X} {B = λ x → empty})
is-equiv-pr2-prod-empty X =
  is-equiv-has-inverse
    ( inv-pr2-prod-empty X)
    ( issec-inv-pr2-prod-empty X)
    ( isretr-inv-pr2-prod-empty X)

right-zero-law-prod :
  {l : Level} (X : UU l) → (X × empty) ≃ empty
right-zero-law-prod X =
  pair pr2 (is-equiv-pr2-prod-empty X)

-- Exercise 7.5

-- Exercise 7.5(a)

-- Exercise 7.5(c)

-- Exercise 7.6

-- Exercise 7.7

{- In this exercise we construct an equivalence from A + B to B + A, showing 
   that the coproduct is commutative. -}

swap-coprod :
  {i j : Level} (A : UU i) (B : UU j) → coprod A B → coprod B A
swap-coprod A B (inl x) = inr x
swap-coprod A B (inr x) = inl x

swap-swap-coprod :
  {i j : Level} (A : UU i) (B : UU j) →
  ((swap-coprod B A) ∘ (swap-coprod A B)) ~ id
swap-swap-coprod A B (inl x) = refl
swap-swap-coprod A B (inr x) = refl

abstract
  is-equiv-swap-coprod :
    {i j : Level} (A : UU i) (B : UU j) → is-equiv (swap-coprod A B)
  is-equiv-swap-coprod A B =
    is-equiv-has-inverse
      ( swap-coprod B A)
      ( swap-swap-coprod B A)
      ( swap-swap-coprod A B)

equiv-swap-coprod :
  {i j : Level} (A : UU i) (B : UU j) → coprod A B ≃ coprod B A
equiv-swap-coprod A B = pair (swap-coprod A B) (is-equiv-swap-coprod A B)

swap-prod :
  {i j : Level} (A : UU i) (B : UU j) → prod A B → prod B A
swap-prod A B t = pair (pr2 t) (pr1 t)

swap-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) →
  ((swap-prod B A) ∘ (swap-prod A B)) ~ id
swap-swap-prod A B (pair x y) = refl

abstract
  is-equiv-swap-prod :
    {i j : Level} (A : UU i) (B : UU j) →
    is-equiv (swap-prod A B)
  is-equiv-swap-prod A B =
    is-equiv-has-inverse
      ( swap-prod B A)
      ( swap-swap-prod B A)
      ( swap-swap-prod A B)

equiv-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) → (A × B) ≃ (B × A)
equiv-swap-prod A B = pair (swap-prod A B) (is-equiv-swap-prod A B)

-- Exercise 7.8

{- In this exercise we show that if A is a retract of B, then so are its 
   identity types. -}

ap-retraction :
  {i j : Level} {A : UU i} {B : UU j}
  (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
  (x y : A) → Id (i x) (i y) → Id x y
ap-retraction i r H x y p =
    ( inv (H x)) ∙ ((ap r p) ∙ (H y))

isretr-ap-retraction :
  {i j : Level} {A : UU i} {B : UU j}
  (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
  (x y : A) → ((ap-retraction i r H x y) ∘ (ap i {x} {y})) ~ id
isretr-ap-retraction i r H x .x refl = left-inv (H x)

retr-ap :
  {i j : Level} {A : UU i} {B : UU j} (i : A → B) →
  retr i → (x y : A) → retr (ap i {x} {y})
retr-ap i (pair r H) x y =
  pair (ap-retraction i r H x y) (isretr-ap-retraction i r H x y)

Id-retract-of-Id :
  {i j : Level} {A : UU i} {B : UU j} (R : A retract-of B) →
  (x y : A) → (Id x y) retract-of (Id (pr1 R x) (pr1 R y))
Id-retract-of-Id (pair i (pair r H)) x y =
  pair
    ( ap i {x} {y})
    ( retr-ap i (pair r H) x y)

-- Exercise 7.9

Σ-assoc :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ (Σ A B) C → Σ A (λ x → Σ (B x) (λ y → C (pair x y)))
Σ-assoc A B C (pair (pair x y) z) = pair x (pair y z)

Σ-assoc' :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ A (λ x → Σ (B x) (λ y → C (pair x y))) → Σ (Σ A B) C
Σ-assoc' A B C t = pair (pair (pr1 t) (pr1 (pr2 t))) (pr2 (pr2 t))

Σ-assoc-assoc :
  {i j k : Level} (A : UU i) (B : A → UU j)
  (C : (Σ A B) → UU k) → ((Σ-assoc' A B C) ∘ (Σ-assoc A B C)) ~ id
Σ-assoc-assoc A B C (pair (pair x y) z) = refl

Σ-assoc-assoc' :
  {i j k : Level} (A : UU i) (B : A → UU j)
  (C : (Σ A B) → UU k) → ((Σ-assoc A B C) ∘ (Σ-assoc' A B C)) ~ id
Σ-assoc-assoc' A B C (pair x (pair y z)) = refl

abstract
  is-equiv-Σ-assoc :
    {i j k : Level} (A : UU i) (B : A → UU j)
    (C : (Σ A B) → UU k) → is-equiv (Σ-assoc A B C)
  is-equiv-Σ-assoc A B C =
    is-equiv-has-inverse
      ( Σ-assoc' A B C)
      ( Σ-assoc-assoc' A B C)
      ( Σ-assoc-assoc A B C)

equiv-Σ-assoc :
  {i j k : Level} (A : UU i) (B : A → UU j) (C : (Σ A B) → UU k) →
  Σ (Σ A B) C ≃ Σ A (λ x → Σ (B x) (λ y → C (pair x y)))
equiv-Σ-assoc A B C =
  pair (Σ-assoc A B C) (is-equiv-Σ-assoc A B C)

-- Exercise 7.10

Σ-swap :
  {i j k : Level} (A : UU i) (B : UU j) (C : A → B → UU k) →
  Σ A (λ x → Σ B (C x)) → Σ B (λ y → Σ A (λ x → C x y))
Σ-swap A B C t = pair (pr1 (pr2 t)) (pair (pr1 t) (pr2 (pr2 t)))

Σ-swap' :
  {i j k : Level} (A : UU i) (B : UU j) (C : A → B → UU k) →
  Σ B (λ y → Σ A (λ x → C x y)) → Σ A (λ x → Σ B (C x))
Σ-swap' A B C = Σ-swap B A (λ y x → C x y)

Σ-swap-swap :
  {i j k : Level} (A : UU i) (B : UU j) (C : A → B → UU k) →
  ((Σ-swap' A B C) ∘ (Σ-swap A B C)) ~ id
Σ-swap-swap A B C (pair x (pair y z)) = refl

abstract
  is-equiv-Σ-swap :
    {i j k : Level} (A : UU i) (B : UU j) (C : A → B → UU k) →
    is-equiv (Σ-swap A B C)
  is-equiv-Σ-swap A B C =
    is-equiv-has-inverse
      ( Σ-swap' A B C)
      ( Σ-swap-swap B A (λ y x → C x y))
      ( Σ-swap-swap A B C)

-- Exercise 7.11

abstract
  is-equiv-add-ℤ-right :
    (x : ℤ) → is-equiv (add-ℤ x)
  is-equiv-add-ℤ-right x =
    is-equiv-has-inverse
      ( add-ℤ (neg-ℤ x))
      ( λ y →
        ( inv (associative-add-ℤ x (neg-ℤ x) y)) ∙
        ( ap (λ t → add-ℤ t y) (right-inverse-law-add-ℤ x)))
      ( λ y →
        ( inv (associative-add-ℤ (neg-ℤ x) x y)) ∙
        ( ap (λ t → add-ℤ t y) (left-inverse-law-add-ℤ x)))

abstract
  is-equiv-add-ℤ-left :
    (y : ℤ) → is-equiv (λ x → add-ℤ x y)
  is-equiv-add-ℤ-left y =
    is-equiv-htpy (add-ℤ y)
      ( λ x → commutative-add-ℤ x y)
      ( is-equiv-add-ℤ-right y)

-- Exercise 7.12

-- Exercise 7.13

{- We construct the functoriality of coproducts. -}

htpy-functor-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f f' : A → A'} (H : f ~ f') {g g' : B → B'} (K : g ~ g') →
  (functor-coprod f g) ~ (functor-coprod f' g')
htpy-functor-coprod H K (inl x) = ap inl (H x)
htpy-functor-coprod H K (inr y) = ap inr (K y)

id-functor-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (functor-coprod (id {A = A}) (id {A = B})) ~ id
id-functor-coprod A B (inl x) = refl
id-functor-coprod A B (inr x) = refl

compose-functor-coprod :
  {l1 l2 l1' l2' l1'' l2'' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {A'' : UU l1''} {B'' : UU l2''}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'') →
  (functor-coprod (f' ∘ f) (g' ∘ g)) ~
  ((functor-coprod f' g') ∘ (functor-coprod f g))
compose-functor-coprod f f' g g' (inl x) = refl
compose-functor-coprod f f' g g' (inr y) = refl

abstract
  is-equiv-functor-coprod :
    {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
    {f : A → A'} {g : B → B'} →
    is-equiv f → is-equiv g → is-equiv (functor-coprod f g)
  is-equiv-functor-coprod {A = A} {B = B} {A' = A'} {B' = B'} {f = f} {g = g}
    (pair (pair sf issec-sf) (pair rf isretr-rf))
    (pair (pair sg issec-sg) (pair rg isretr-rg)) =
    pair
      ( pair
        ( functor-coprod sf sg)
        ( ( ( htpy-inv (compose-functor-coprod sf f sg g)) ∙h
            ( htpy-functor-coprod issec-sf issec-sg)) ∙h
          ( id-functor-coprod A' B')))
      ( pair
        ( functor-coprod rf rg)
        ( ( ( htpy-inv (compose-functor-coprod f rf g rg)) ∙h
            ( htpy-functor-coprod isretr-rf isretr-rg)) ∙h
          ( id-functor-coprod A B)))
  
equiv-functor-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'} →
  (A ≃ A') → (B ≃ B') → ((coprod A B) ≃ (coprod A' B'))
equiv-functor-coprod (pair e is-equiv-e) (pair f is-equiv-f) =
  pair
    ( functor-coprod e f)
    ( is-equiv-functor-coprod is-equiv-e is-equiv-f)

-- Extra material

abstract
  is-equiv-inv-con :
    {i : Level} {A : UU i} {x y z : A} (p : Id x y)
    (q : Id y z) (r : Id x z) → is-equiv (inv-con p q r)
  is-equiv-inv-con refl q r = is-equiv-id (Id q r)

equiv-inv-con :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) (q : Id y z) (r : Id x z) →
  Id (p ∙ q) r ≃ Id q ((inv p) ∙ r)
equiv-inv-con p q r = pair (inv-con p q r) (is-equiv-inv-con p q r)

abstract
  is-equiv-con-inv :
    {i : Level} {A : UU i} {x y z : A} (p : Id x y)
    (q : Id y z) (r : Id x z) → is-equiv (con-inv p q r)
  is-equiv-con-inv p refl r =
    is-equiv-comp'
      ( concat' p (inv right-unit))
      ( concat (inv right-unit) r)
      ( is-equiv-concat (inv right-unit) r)
      ( is-equiv-concat' p (inv right-unit))

equiv-con-inv :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) (q : Id y z) (r : Id x z) →
  Id (p ∙ q) r ≃ Id p (r ∙ (inv q))
equiv-con-inv p q r = pair (con-inv p q r) (is-equiv-con-inv p q r)

-- Extra constructions with homotopies

htpy-inv-con :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K : g ~ h) (L : f ~ h) →
  (H ∙h K) ~ L → K ~ ((htpy-inv H) ∙h L)
htpy-inv-con H K L M x = inv-con (H x) (K x) (L x) (M x)

htpy-con-inv :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K : g ~ h) (L : f ~ h) →
  (H ∙h K) ~ L → H ~ (L ∙h (htpy-inv K))
htpy-con-inv H K L M x = con-inv (H x) (K x) (L x) (M x)

htpy-ap-concat :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K K' : g ~ h) →
  K ~ K' → (H ∙h K) ~ (H ∙h K')
htpy-ap-concat {g = g} {h} H K K' L x =
  ap (concat (H x) (h x)) (L x)

htpy-ap-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H H' : f ~ g) (K : g ~ h) →
  H ~ H' → (H ∙h K) ~ (H' ∙h K)
htpy-ap-concat' H H' K L x =
  ap (concat' _ (K x)) (L x)

htpy-distributive-inv-concat :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K : g ~ h) →
  (htpy-inv (H ∙h K)) ~ ((htpy-inv K) ∙h (htpy-inv H))
htpy-distributive-inv-concat H K x = distributive-inv-concat (H x) (K x)

htpy-ap-inv :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  {H H' : f ~ g} →
  H ~ H' → (htpy-inv H) ~ (htpy-inv H')
htpy-ap-inv K x = ap inv (K x)

htpy-left-whisk-htpy-inv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f f' : A → B} (g : B → C) (H : f ~ f') →
  (g ·l (htpy-inv H)) ~ htpy-inv (g ·l H)
htpy-left-whisk-htpy-inv g H x = ap-inv g (H x)

htpy-right-whisk-htpy-inv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g g' : B → C} (H : g ~ g') (f : A → B) →
  ((htpy-inv H) ·r f) ~ (htpy-inv (H ·r f))
htpy-right-whisk-htpy-inv H f = refl-htpy


-- Old stuff

element :
  {i : Level} {A : UU i} → A → unit → A
element a star = a

htpy-element-constant :
  {i : Level} {A : UU i} (a : A) →
  (element a) ~ (const unit A a)
htpy-element-constant a star = refl

ap-const :
  {i j : Level} {A : UU i} {B : UU j} (b : B) (x y : A) →
  (ap (const A B b) {x} {y}) ~ const (Id x y) (Id b b) refl
ap-const b x .x refl = refl
