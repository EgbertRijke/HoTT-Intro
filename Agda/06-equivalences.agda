{-# OPTIONS --without-K #-}

module 06-equivalences where

import 05-identity-types
open 05-identity-types public

-- Section 5.1 Homotopies
_~_ :
  {i j : Level} {A : UU i} {B : A → UU j} (f g : (x : A) → B x) → UU (i ⊔ j)
f ~ g = (x : _) → Id (f x) (g x)

htpy-refl :
  {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → f ~ f
htpy-refl f x = refl

htpy-inv :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) → (g ~ f)
htpy-inv H x = inv (H x)

htpy-concat :
  {i j : Level} {A : UU i} {B : A → UU j} {f : (x : A) → B x}
  (g : (x : A) → B x) {h : (x : A) → B x} → (f ~ g) → (g ~ h) → (f ~ h)
htpy-concat g H K x = concat (g x) (H x) (K x)

_∙h_ :
  {i j : Level} {A : UU i} {B : A → UU j} {f g h : (x : A) → B x} →
  (f ~ g) → (g ~ h) → (f ~ h)
_∙h_ {g = g} = htpy-concat g

htpy-assoc :
  {i j : Level} {A : UU i} {B : A → UU j} {f g h k : (x : A) → B x} →
  (H : f ~ g) → (K : g ~ h) → (L : h ~ k) →
  ((H ∙h K) ∙h L) ~ (H ∙h (K ∙h L))
htpy-assoc H K L x = assoc (H x) (K x) (L x)

htpy-left-unit :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → (htpy-concat f (htpy-refl f) H) ~ H
htpy-left-unit H x = left-unit (H x)

htpy-right-unit :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → (htpy-concat g H (htpy-refl g)) ~ H
htpy-right-unit H x = right-unit (H x)

htpy-left-inv :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → htpy-concat f (htpy-inv H) H ~ htpy-refl g
htpy-left-inv H x = left-inv (H x)

htpy-right-inv :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → htpy-concat g H (htpy-inv H) ~ htpy-refl f
htpy-right-inv H x = right-inv (H x)

htpy-left-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  (h : B → C) {f g : A → B} → (f ~ g) → ((h ∘ f) ~ (h ∘ g))
htpy-left-whisk h H x = ap h (H x)

_·l_ = htpy-left-whisk

htpy-right-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  {g h : B → C} (H : g ~ h) (f : A → B) → ((g ∘ f) ~ (h ∘ f))
htpy-right-whisk H f x = H (f x)

_·r_ = htpy-right-whisk

-- Section 5.2 Bi-invertible maps
sec :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
sec {i} {j} {A} {B} f = Σ (B → A) (λ g → (f ∘ g) ~ id)

retr :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
retr {i} {j} {A} {B} f = Σ (B → A) (λ g → (g ∘ f) ~ id)

_retract-of_ :
  {i j : Level} → UU i → UU j → UU (i ⊔ j)
A retract-of B = Σ (A → B) retr

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

sec-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → sec f
sec-is-equiv is-equiv-f = pr1 is-equiv-f

map-sec-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → B → A
map-sec-is-equiv is-equiv-f = pr1 (sec-is-equiv is-equiv-f)

issec-map-sec-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → ((f ∘ map-sec-is-equiv is-equiv-f) ~ id)
issec-map-sec-is-equiv is-equiv-f = pr2 (sec-is-equiv is-equiv-f)

retr-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → retr f
retr-is-equiv is-equiv-f = pr2 is-equiv-f

map-retr-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → B → A
map-retr-is-equiv is-equiv-f = pr1 (retr-is-equiv is-equiv-f)

isretr-map-retr-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → (((map-retr-is-equiv is-equiv-f) ∘ f) ~ id)
isretr-map-retr-is-equiv is-equiv-f = pr2 (retr-is-equiv is-equiv-f)

has-inverse :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
has-inverse {i} {j} {A} {B} f =
  Σ (B → A) (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

abstract
  is-equiv-has-inverse :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    has-inverse f → is-equiv f
  is-equiv-has-inverse (pair g (pair H K)) = pair (pair g H) (pair g K)

abstract
  is-equiv-has-inverse' :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    (g : B → A) (H : (f ∘ g) ~ id) (K : (g ∘ f) ~ id) → is-equiv f
  is-equiv-has-inverse' g H K =
    is-equiv-has-inverse (pair g (pair H K))

htpy-secf-retrf :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (is-equiv-f : is-equiv f) →
  (map-sec-is-equiv is-equiv-f ~ map-retr-is-equiv is-equiv-f)
htpy-secf-retrf {i} {j} {A} {B} {f} (pair (pair g issec) (pair h isretr)) =
  htpy-concat
    ( h ∘ (f ∘ g))
    ( htpy-inv (htpy-right-whisk isretr g))
    ( htpy-left-whisk h issec)

-- For some reason Agda takes significantly longer to type-check the files if
-- the following definition is given directly in terms of E : is-equiv-f.
has-inverse-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-equiv f → has-inverse f
has-inverse-is-equiv
  {i} {j} {A} {B} {f} (pair (pair g issec) (pair h isretr)) =
  pair g
    ( pair issec
      ( htpy-concat
        ( h ∘ f)
        ( htpy-right-whisk
          ( htpy-secf-retrf ( pair (pair g issec) (pair h isretr)))
          ( f))
        ( isretr)))

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

abstract
  is-equiv-inv-is-equiv :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    (is-equiv-f : is-equiv f) → is-equiv (inv-is-equiv is-equiv-f)
  is-equiv-inv-is-equiv {i} {j} {A} {B} {f} is-equiv-f =
    is-equiv-has-inverse' f
      ( isretr-inv-is-equiv is-equiv-f)
      ( issec-inv-is-equiv is-equiv-f)

inv-map-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (B → A)
inv-map-equiv e = inv-is-equiv (is-equiv-map-equiv e)

abstract
  is-equiv-inv-map-equiv :
    {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) → is-equiv (inv-map-equiv e)
  is-equiv-inv-map-equiv e =
    is-equiv-inv-is-equiv (is-equiv-map-equiv e)

inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (B ≃ A)
inv-equiv e = pair (inv-map-equiv e) (is-equiv-inv-map-equiv e)

is-equiv-id :
  {i : Level} (A : UU i) → is-equiv (id {i} {A})
is-equiv-id A = pair (pair id (htpy-refl id)) (pair id (htpy-refl id))

equiv-id :
  {i : Level} (A : UU i) → A ≃ A
equiv-id A = pair id (is-equiv-id A)

inv-Π-swap :
  {i j k : Level} {A : UU i} {B : UU j} (C : A → B → UU k) →
  ((y : B) (x : A) → C x y) → ((x : A) (y : B) → C x y)
inv-Π-swap C g x y = g y x

abstract
  is-equiv-Π-swap :
    {i j k : Level} {A : UU i} {B : UU j} (C : A → B → UU k) →
    is-equiv (Π-swap {i} {j} {k} {A} {B} {C})
  is-equiv-Π-swap C =
    is-equiv-has-inverse'
      ( inv-Π-swap C)
      ( htpy-refl id)
      ( htpy-refl id)

-- Section 5.3 The identity type of a Σ-type

eq-pair' :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  (Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))) → Id s t
eq-pair' (pair x y) (pair x' y') (pair refl refl) = refl

eq-pair :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  (Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))) → Id s t
eq-pair {i} {j} {A} {B} {s} {t} = eq-pair' s t

pair-eq' :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  (Id s t) → Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))
pair-eq' s t refl = pair refl refl

pair-eq  :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  (Id s t) → Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))
pair-eq {i} {j} {A} {B} {s} {t} = pair-eq' s t

isretr-pair-eq :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  (((pair-eq' s t) ∘ (eq-pair' s t)) ~ id)
isretr-pair-eq (pair x y) (pair x' y') (pair refl refl) = refl

issec-pair-eq :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  (((eq-pair' s t) ∘ (pair-eq' s t)) ~ id)
issec-pair-eq (pair x y) .(pair x y) refl = refl

abstract
  is-equiv-eq-pair' :
    {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
    is-equiv (eq-pair' s t)
  is-equiv-eq-pair' s t =
    is-equiv-has-inverse'
      ( pair-eq' s t)
      ( issec-pair-eq s t)
      ( isretr-pair-eq s t)

abstract
  is-equiv-eq-pair :
    {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
    is-equiv (eq-pair {i} {j} {A} {B} {s} {t})
  is-equiv-eq-pair {s = s} {t} = is-equiv-eq-pair' s t

abstract
  is-equiv-pair-eq' :
    {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
    is-equiv (pair-eq' s t)
  is-equiv-pair-eq' s t =
    is-equiv-has-inverse'
      ( eq-pair {s = s} {t = t})
      ( isretr-pair-eq s t)
      ( issec-pair-eq s t)

abstract
  is-equiv-pair-eq :
    {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
    is-equiv (pair-eq {s = s} {t})
  is-equiv-pair-eq {s = s} {t} = is-equiv-pair-eq' s t

-- We also define a function eq-pair-triv, which is like eq-pair but simplified for the case where B is just a type.

eq-pair-triv' :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  prod (Id (pr1 s) (pr1 t)) (Id (pr2 s) (pr2 t)) → Id s t
eq-pair-triv' (pair x y) (pair .x .y) (pair refl refl) = refl

eq-pair-triv :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  prod (Id (pr1 s) (pr1 t)) (Id (pr2 s) (pr2 t)) → Id s t
eq-pair-triv {s = s} {t} = eq-pair-triv' s t

-- Ideally, we would use the 3-for-2 property of equivalences to show that eq-pair-triv is an equivalence, using that eq-pair is an equivalence. Indeed, there is an equivalence (Id x x') × (Id y y') → Σ (Id x x') (λ p → Id (tr (λ x → B) p y) y'). However, to show that this map is an equivalence we either give a direct proof (in which case we might as well have given a direct proof that eq-pair-triv is an equivalence), or we use the fact that it is the induced map on total spaces of a fiberwise equivalence (the topic of Lecture 7). Thus it seems that a direct proof showing that eq-pair-triv is an equivalence is quickest for now. 

pair-eq-triv' :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  Id s t → prod (Id (pr1 s) (pr1 t)) (Id (pr2 s) (pr2 t))
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
    is-equiv-has-inverse'
      ( pair-eq-triv' s t)
      ( issec-pair-eq-triv' s t)
      ( isretr-pair-eq-triv' s t)

-- Exercises

-- Exercise 5.1
element :
  {i : Level} {A : UU i} → A → unit → A
element a star = a 

htpy-element-constant :
  {i : Level} {A : UU i} (a : A) →
  (element a) ~ (const unit A a)
htpy-element-constant a star = refl

-- Exercise 5.2
ap-const :
  {i j : Level} {A : UU i} {B : UU j} (b : B) (x y : A) →
  (ap (const A B b) {x} {y}) ~ const (Id x y) (Id b b) refl
ap-const b x .x refl = refl

-- Exercise 5.3
inv-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (inv (inv p)) p
inv-inv refl = refl

abstract
  is-equiv-inv :
    {i : Level} {A : UU i} (x y : A) →
    is-equiv (λ (p : Id x y) → inv p)
  is-equiv-inv x y = pair (pair inv inv-inv) (pair inv inv-inv)

equiv-inv :
  {i : Level} {A : UU i} (x y : A) → (Id x y) ≃ (Id y x)
equiv-inv x y = pair inv (is-equiv-inv x y)

inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  (Id x z) → (Id y z)
inv-concat p z = concat _ (inv p)

left-inv-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  ((inv-concat p z) ∘ (concat y {z} p)) ~ id
left-inv-inv-concat refl z q = refl

right-inv-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  ((concat y {z} p) ∘ (inv-concat p z)) ~ id
right-inv-inv-concat refl z refl = refl

abstract
  is-equiv-concat :
    {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
    is-equiv (concat y {z} p)
  is-equiv-concat p z =
    is-equiv-has-inverse'
      ( inv-concat p z)
      ( right-inv-inv-concat p z)
      ( left-inv-inv-concat p z)

equiv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  Id y z ≃ Id x z
equiv-concat p z = pair (concat _ p) (is-equiv-concat p z)

concat' :
  {i : Level} {A : UU i} {x : A} (y : A) {z : A} → Id y z → Id x y → Id x z
concat' y q p = concat y p q

inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} → Id y z →
  Id x z → Id x y
inv-concat' x q = concat' _ (inv q)

left-inv-inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  ((inv-concat' x q) ∘ (concat' y q)) ~ id
left-inv-inv-concat' x q p =
  concat
    ( concat _ p (concat _ q (inv q)))
    ( assoc p q (inv q))
    ( concat
      ( concat _ p refl)
      ( ap (concat _ p) (right-inv q))
      ( right-unit p))

right-inv-inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  ((concat' y q) ∘ (inv-concat' x q)) ~ id
right-inv-inv-concat' x q r =
  concat
    ( concat _ r (concat _ (inv q) q))
    ( assoc r (inv q) q)
    ( concat
      ( concat _ r refl)
      ( ap (concat _ r) (left-inv q))
      ( right-unit r))

abstract
  is-equiv-concat' :
    {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
    is-equiv (concat' {x = x} y q)
  is-equiv-concat' x q =
    is-equiv-has-inverse'
      ( inv-concat' x q)
      ( right-inv-inv-concat' x q)
      ( left-inv-inv-concat' x q)

equiv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  Id x y ≃ Id x z
equiv-concat' x q = pair (concat' _ q) (is-equiv-concat' x q)

inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A} →
  Id x y → B y → B x
inv-tr B p = tr B (inv p)

left-inv-inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → ((inv-tr B p ) ∘ (tr B p)) ~ id
left-inv-inv-tr B refl b = refl

right-inv-inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → ((tr B p) ∘ (inv-tr B p)) ~ id
right-inv-inv-tr B refl b = refl

abstract
  is-equiv-tr :
    {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
    (p : Id x y) → is-equiv (tr B p)
  is-equiv-tr B p =
    is-equiv-has-inverse'
      ( inv-tr B p)
      ( right-inv-inv-tr B p)
      ( left-inv-inv-tr B p)

equiv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → (B x) ≃ (B y)
equiv-tr B p = pair (tr B p) (is-equiv-tr B p)

-- Exercise 5.4

abstract
  is-equiv-htpy :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} (g : A → B) →
    f ~ g → is-equiv g → is-equiv f
  is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)) =
    pair
      ( pair gs (htpy-concat _ (htpy-right-whisk H gs) issec))
      ( pair gr (htpy-concat (gr ∘ _) (htpy-left-whisk gr H) isretr))

abstract
  is-equiv-htpy' :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) {g : A → B} →
    f ~ g → is-equiv f → is-equiv g
  is-equiv-htpy' f H = is-equiv-htpy f (htpy-inv H)

htpy-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f f' : A → B} (H : f ~ f') →
  (is-equiv-f : is-equiv f) (is-equiv-f' : is-equiv f') →
  (inv-is-equiv is-equiv-f) ~ (inv-is-equiv is-equiv-f')
htpy-inv-is-equiv H is-equiv-f is-equiv-f' b =
  ( inv (isretr-inv-is-equiv is-equiv-f' (inv-is-equiv is-equiv-f b))) ∙
  ( ap (inv-is-equiv is-equiv-f')
    ( ( inv (H (inv-is-equiv is-equiv-f b))) ∙
      ( issec-inv-is-equiv is-equiv-f b)))

-- Exercise 5.5

-- Exercise 5.5 (a) asks to show that, given a commuting triangle f ~ g ∘ h and a section s of h, we get a new commuting triangle g ~ f ∘ s. Moreover, under the same assumptions it follows that f has a section if and only if g has a section.

triangle-section :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (S : sec h) →
  g ~ (f ∘ (pr1 S))
triangle-section f g h H (pair s issec) =
  htpy-inv
    ( htpy-concat
      ( g ∘ (h ∘ s))
      ( htpy-right-whisk H s)
      ( htpy-left-whisk g issec))

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

-- Exercise 5.5 (b) is dual to exercise 5.5 (a). It asks to show that, given a commuting triangle f ~ g ∘ h and a retraction r of g, we get a new commuting triangle h ~ r ∘ f. Moreover, under these assumptions it also follows that f has a retraction if and only if h has a retraction.

triangle-retraction :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (R : retr g) →
  h ~ ((pr1 R) ∘ f)
triangle-retraction f g h H (pair r isretr) =
  htpy-inv
    ( htpy-concat
      ( r ∘ (g ∘ h))
      ( htpy-left-whisk r H)
      ( htpy-right-whisk isretr h))

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

-- In Exercise 5.5 (c) we use the constructions of parts (a) and (b) to derive the 3-for-2 property of equivalences.

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
  is-equiv-comp' g h = is-equiv-comp (g ∘ h) g h (htpy-refl _)

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
    is-equiv-left-factor (g ∘ h) g h (htpy-refl _)

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
    is-equiv-right-factor (g ∘ h) g h (htpy-refl _)

-- Exercise 5.6

-- In this exercise we show that the negation function on the booleans is an equivalence. Moreover, we show that any constant function on the booleans is not an equivalence.

neg-𝟚 : bool → bool
neg-𝟚 true = false
neg-𝟚 false = true

neg-neg-𝟚 : (neg-𝟚 ∘ neg-𝟚) ~ id
neg-neg-𝟚 true = refl
neg-neg-𝟚 false = refl

abstract
  is-equiv-neg-𝟚 : is-equiv neg-𝟚
  is-equiv-neg-𝟚 = pair (pair neg-𝟚 neg-neg-𝟚) (pair neg-𝟚 neg-neg-𝟚)

equiv-neg-𝟚 : bool ≃ bool
equiv-neg-𝟚 = pair neg-𝟚 is-equiv-neg-𝟚

abstract
  not-true-is-false : ¬ (Id true false)
  not-true-is-false p =
    ( ind-Id true
      ( λ b p → Eq-𝟚 true b)
      ( reflexive-Eq-𝟚 true)
      false
      p)

abstract
  not-equiv-const :
    (b : bool) → ¬ (is-equiv (const bool bool b))
  not-equiv-const true (pair (pair s issec) (pair r isretr)) =
    not-true-is-false (issec false)
  not-equiv-const false (pair (pair s issec) (pair r isretr)) =
    not-true-is-false (inv (issec true))

-- Exercise 5.7

-- In this exercise we show that the successor function on the integers is an equivalence. 

abstract
  left-inverse-pred-ℤ :
    (k : ℤ) → Id (pred-ℤ (succ-ℤ k)) k
  left-inverse-pred-ℤ (inl zero-ℕ) = refl
  left-inverse-pred-ℤ (inl (succ-ℕ x)) = refl
  left-inverse-pred-ℤ (inr (inl star)) = refl
  left-inverse-pred-ℤ (inr (inr zero-ℕ)) = refl
  left-inverse-pred-ℤ (inr (inr (succ-ℕ x))) = refl
  
  right-inverse-pred-ℤ :
    (k : ℤ) → Id (succ-ℤ (pred-ℤ k)) k
  right-inverse-pred-ℤ (inl zero-ℕ) = refl
  right-inverse-pred-ℤ (inl (succ-ℕ x)) = refl
  right-inverse-pred-ℤ (inr (inl star)) = refl
  right-inverse-pred-ℤ (inr (inr zero-ℕ)) = refl
  right-inverse-pred-ℤ (inr (inr (succ-ℕ x))) = refl
  
  is-equiv-succ-ℤ : is-equiv succ-ℤ
  is-equiv-succ-ℤ =
    pair
    ( pair pred-ℤ right-inverse-pred-ℤ)
    ( pair pred-ℤ left-inverse-pred-ℤ)
  
equiv-succ-ℤ : ℤ ≃ ℤ
equiv-succ-ℤ = pair succ-ℤ is-equiv-succ-ℤ

-- Exercise 5.8

-- In this exercise we construct an equivalence from A + B to B + A, showing that the coproduct is commutative.

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
    is-equiv-has-inverse'
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
    is-equiv-has-inverse'
      ( swap-prod B A)
      ( swap-swap-prod B A)
      ( swap-swap-prod A B)

equiv-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) → (A × B) ≃ (B × A)
equiv-swap-prod A B = pair (swap-prod A B) (is-equiv-swap-prod A B)

-- Exercise 5.9

-- In this exercise we show that if A is a retract of B, then so are its identity types.

ap-retraction :
  {i j : Level} {A : UU i} {B : UU j}
  (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
  (x y : A) → Id (i x) (i y) → Id x y
ap-retraction i r H x y p =
    ( inv (H x)) ∙ (concat (r (i y)) (ap r p) (H y))

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

-- Exercise 5.10
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
    is-equiv-has-inverse'
      ( Σ-assoc' A B C)
      ( Σ-assoc-assoc' A B C)
      ( Σ-assoc-assoc A B C)

-- Exercise 5.11
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
    is-equiv-has-inverse'
      ( Σ-swap' A B C)
      ( Σ-swap-swap B A (λ y x → C x y))
      ( Σ-swap-swap A B C)

-- Exercise 5.12

-- Exercise 5.12 (a) simply asks to prove the unit laws. The left unit law holds by judgmental equality.

abstract
  left-unit-law-add-ℤ :
    (k : ℤ) → Id (add-ℤ zero-ℤ k) k
  left-unit-law-add-ℤ k = refl
  
  right-unit-law-add-ℤ :
    (k : ℤ) → Id (add-ℤ k zero-ℤ) k
  right-unit-law-add-ℤ (inl zero-ℕ) = refl
  right-unit-law-add-ℤ (inl (succ-ℕ x)) =
    ap pred-ℤ (right-unit-law-add-ℤ (inl x))
  right-unit-law-add-ℤ (inr (inl star)) = refl
  right-unit-law-add-ℤ (inr (inr zero-ℕ)) = refl
  right-unit-law-add-ℤ (inr (inr (succ-ℕ x))) =
    ap succ-ℤ (right-unit-law-add-ℤ (inr (inr x)))

-- Exercise 5.12 (b) asks to show the left and right predecessor and successor laws. These are helpful to give proofs of associativity and commutativity.

abstract
  left-predecessor-law-add-ℤ :
    (x y : ℤ) → Id (add-ℤ (pred-ℤ x) y) (pred-ℤ (add-ℤ x y))
  left-predecessor-law-add-ℤ (inl n) y = refl
  left-predecessor-law-add-ℤ (inr (inl star)) y = refl
  left-predecessor-law-add-ℤ (inr (inr zero-ℕ)) y =
    concat
      ( y)
      ( ap (λ t → add-ℤ t y) (left-inverse-pred-ℤ zero-ℤ))
      ( inv (left-inverse-pred-ℤ y))
  left-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) y =
    concat
      ( add-ℤ (inr (inr x)) y)
      ( ap (λ t → (add-ℤ t y)) (left-inverse-pred-ℤ (inr (inr x))))
      ( inv (left-inverse-pred-ℤ (add-ℤ (inr (inr x)) y)))

  right-predecessor-law-add-ℤ :
    (x y : ℤ) → Id (add-ℤ x (pred-ℤ y)) (pred-ℤ (add-ℤ x y))
  right-predecessor-law-add-ℤ (inl zero-ℕ) n = refl
  right-predecessor-law-add-ℤ (inl (succ-ℕ m)) n =
    ap pred-ℤ (right-predecessor-law-add-ℤ (inl m) n)
  right-predecessor-law-add-ℤ (inr (inl star)) n = refl
  right-predecessor-law-add-ℤ (inr (inr zero-ℕ)) n =
    concat n (right-inverse-pred-ℤ n) (inv (left-inverse-pred-ℤ n))
  right-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) n =
    concat
      ( succ-ℤ (pred-ℤ (add-ℤ (inr (inr x)) n)))
      ( ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) n))
      ( concat
        ( add-ℤ (inr (inr x)) n)
        ( right-inverse-pred-ℤ (add-ℤ (inr (inr x)) n))
        ( inv (left-inverse-pred-ℤ (add-ℤ (inr (inr x)) n))))

abstract
  left-successor-law-add-ℤ :
    (x y : ℤ) → Id (add-ℤ (succ-ℤ x) y) (succ-ℤ (add-ℤ x y))
  left-successor-law-add-ℤ (inl zero-ℕ) y =
    concat
      ( y)
      ( ap (λ t → add-ℤ t y) (right-inverse-pred-ℤ zero-ℤ))
      ( inv (right-inverse-pred-ℤ y))
  left-successor-law-add-ℤ (inl (succ-ℕ x)) y =
    concat
      ( succ-ℤ (pred-ℤ (add-ℤ (inl x) y)))
      ( inv (right-inverse-pred-ℤ (add-ℤ (inl x) y)))
      ( ap succ-ℤ (inv (left-predecessor-law-add-ℤ (inl x) y)))
  left-successor-law-add-ℤ (inr (inl star)) y = refl
  left-successor-law-add-ℤ (inr (inr x)) y = refl

  right-successor-law-add-ℤ :
    (x y : ℤ) → Id (add-ℤ x (succ-ℤ y)) (succ-ℤ (add-ℤ x y))
  right-successor-law-add-ℤ (inl zero-ℕ) y =
    concat y (left-inverse-pred-ℤ y) (inv (right-inverse-pred-ℤ y))
  right-successor-law-add-ℤ (inl (succ-ℕ x)) y =
    concat
      ( pred-ℤ (succ-ℤ (add-ℤ (inl x) y)))
      ( ap pred-ℤ (right-successor-law-add-ℤ (inl x) y))
      ( concat
        ( add-ℤ (inl x) y)
        ( left-inverse-pred-ℤ (add-ℤ (inl x) y))
        ( inv (right-inverse-pred-ℤ (add-ℤ (inl x) y))))
  right-successor-law-add-ℤ (inr (inl star)) y = refl
  right-successor-law-add-ℤ (inr (inr zero-ℕ)) y = refl
  right-successor-law-add-ℤ (inr (inr (succ-ℕ x))) y =
    ap succ-ℤ (right-successor-law-add-ℤ (inr (inr x)) y)

-- Exercise 5.12 (c) asks to prove associativity and commutativity. Note that we avoid an unwieldy amount of cases by only using induction on the first argument. The resulting proof term is fairly short, and we don't have to present ℤ as a certain quotient of ℕ × ℕ.

abstract
  associative-add-ℤ :
    (x y z : ℤ) → Id (add-ℤ (add-ℤ x y) z) (add-ℤ x (add-ℤ y z))
  associative-add-ℤ (inl zero-ℕ) y z =
    concat
      ( add-ℤ (pred-ℤ y) z)
      ( ap (λ t → add-ℤ t z) (left-predecessor-law-add-ℤ zero-ℤ y))
      ( concat
        ( pred-ℤ (add-ℤ y z))
        ( left-predecessor-law-add-ℤ y z)
        ( inv (left-predecessor-law-add-ℤ zero-ℤ (add-ℤ y z))))
  associative-add-ℤ (inl (succ-ℕ x)) y z =
    concat
      ( add-ℤ (pred-ℤ (add-ℤ (inl x) y)) z)
      ( ap (λ t → add-ℤ t z) (left-predecessor-law-add-ℤ (inl x) y))
      ( concat
        ( pred-ℤ (add-ℤ (add-ℤ (inl x) y) z))
        ( left-predecessor-law-add-ℤ (add-ℤ (inl x) y) z)
        ( concat
          ( pred-ℤ (add-ℤ (inl x) (add-ℤ y z)))
          ( ap pred-ℤ (associative-add-ℤ (inl x) y z))
          ( inv (left-predecessor-law-add-ℤ (inl x) (add-ℤ y z)))))
  associative-add-ℤ (inr (inl star)) y z = refl
  associative-add-ℤ (inr (inr zero-ℕ)) y z =
    concat
      ( add-ℤ (succ-ℤ y) z)
      ( ap (λ t → add-ℤ t z) (left-successor-law-add-ℤ zero-ℤ y))
      ( concat
        ( succ-ℤ (add-ℤ y z))
        ( left-successor-law-add-ℤ y z)
        ( inv (left-successor-law-add-ℤ zero-ℤ (add-ℤ y z))))
  associative-add-ℤ (inr (inr (succ-ℕ x))) y z =
    concat
      ( add-ℤ (succ-ℤ (add-ℤ (inr (inr x)) y)) z)
      ( ap (λ t → add-ℤ t z) (left-successor-law-add-ℤ (inr (inr x)) y))
      ( concat
        ( succ-ℤ (add-ℤ (add-ℤ (inr (inr x)) y) z))
        ( left-successor-law-add-ℤ (add-ℤ (inr (inr x)) y) z)
        ( concat
          ( succ-ℤ (add-ℤ (inr (inr x)) (add-ℤ y z)))
          ( ap succ-ℤ (associative-add-ℤ (inr (inr x)) y z))
          ( inv (left-successor-law-add-ℤ (inr (inr x)) (add-ℤ y z)))))

abstract
  commutative-add-ℤ :
    (x y : ℤ) → Id (add-ℤ x y) (add-ℤ y x)
  commutative-add-ℤ (inl zero-ℕ) y =
    concat
      ( pred-ℤ y)
      ( left-predecessor-law-add-ℤ zero-ℤ y)
      ( inv
        ( concat
          ( pred-ℤ (add-ℤ y zero-ℤ))
          ( right-predecessor-law-add-ℤ y zero-ℤ)
          ( ap pred-ℤ (right-unit-law-add-ℤ y))))
  commutative-add-ℤ (inl (succ-ℕ x)) y =
    concat
      ( pred-ℤ (add-ℤ y (inl x)))
      ( ap pred-ℤ (commutative-add-ℤ (inl x) y))
      ( inv (right-predecessor-law-add-ℤ y (inl x)))
  commutative-add-ℤ (inr (inl star)) y = inv (right-unit-law-add-ℤ y)
  commutative-add-ℤ (inr (inr zero-ℕ)) y =
    inv ( concat
      ( succ-ℤ (add-ℤ y zero-ℤ))
      ( right-successor-law-add-ℤ y zero-ℤ)
      ( ap succ-ℤ (right-unit-law-add-ℤ y)))
  commutative-add-ℤ (inr (inr (succ-ℕ x))) y =
    concat
      ( succ-ℤ (add-ℤ y (inr (inr (x)))))
      ( ap succ-ℤ (commutative-add-ℤ (inr (inr x)) y))
      ( inv (right-successor-law-add-ℤ y (inr (inr x))))

-- Exercise 5.12 (d) finally asks to show the inverse laws, completing the verification of the group laws. Combined with associativity and commutativity we conclude that (add-ℤ x) and (λ x → add-ℤ x y) are equivalences, for every x : ℤ and y : ℤ, respectively.

abstract
  left-inverse-law-add-ℤ :
    (x : ℤ) → Id (add-ℤ (neg-ℤ x) x) zero-ℤ
  left-inverse-law-add-ℤ (inl zero-ℕ) = refl
  left-inverse-law-add-ℤ (inl (succ-ℕ x)) =
    concat
      ( succ-ℤ (pred-ℤ (add-ℤ (inr (inr x)) (inl x))))
      ( ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) (inl x)))
      ( concat
        ( add-ℤ (inr (inr x)) (inl x))
        ( right-inverse-pred-ℤ (add-ℤ (inr (inr x)) (inl x)))
        ( left-inverse-law-add-ℤ (inl x))) 
  left-inverse-law-add-ℤ (inr (inl star)) = refl
  left-inverse-law-add-ℤ (inr (inr x)) =
    concat
      ( add-ℤ (inr (inr x)) (inl x))
      ( commutative-add-ℤ (inl x) (inr (inr x)))
      ( left-inverse-law-add-ℤ (inl x))
  
  right-inverse-law-add-ℤ :
    (x : ℤ) → Id (add-ℤ x (neg-ℤ x)) zero-ℤ
  right-inverse-law-add-ℤ x =
    concat
      ( add-ℤ (neg-ℤ x) x)
      ( commutative-add-ℤ x (neg-ℤ x))
      ( left-inverse-law-add-ℤ x)

abstract
  is-equiv-add-ℤ-right :
    (x : ℤ) → is-equiv (add-ℤ x)
  is-equiv-add-ℤ-right x =
    is-equiv-has-inverse'
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

-- Extra material

abstract
  is-equiv-inv-con :
    {i : Level} {A : UU i} {x y z : A} (p : Id x y)
    (q : Id y z) (r : Id x z) → is-equiv (inv-con p q r)
  is-equiv-inv-con refl q r = is-equiv-id (Id q r)

abstract
  is-equiv-con-inv :
    {i : Level} {A : UU i} {x y z : A} (p : Id x y)
    (q : Id y z) (r : Id x z) → is-equiv (con-inv p q r)
  is-equiv-con-inv p refl r =
    is-equiv-comp'
      ( concat' r (inv (right-unit r)))
      ( concat (concat _ p refl) (inv (right-unit p)))
      ( is-equiv-concat (inv (right-unit p)) r)
      ( is-equiv-concat' p (inv (right-unit r)))

-- Exercise 5.13

-- We construct the functoriality of coproducts

functor-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'} →
  (A → A') → (B → B') → coprod A B → coprod A' B'
functor-coprod f g (inl x) = inl (f x)
functor-coprod f g (inr y) = inr (g y)

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
  ap (concat (g x) {z = h x} (H x)) (L x)

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
htpy-right-whisk-htpy-inv H f = htpy-refl _
