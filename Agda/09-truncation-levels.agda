{-# OPTIONS --without-K #-}

module 09-truncation-levels where

import 08-fundamental-theorem
open 08-fundamental-theorem public

-- Section 8.1 Propositions

is-prop :
  {i : Level} (A : UU i) → UU i
is-prop A = (x y : A) → is-contr (Id x y)

hProp :
  (l : Level) → UU (lsuc l)
hProp l = Σ (UU l) is-prop

abstract
  is-prop-empty : is-prop empty
  is-prop-empty ()

abstract
  is-prop-unit : is-prop unit
  is-prop-unit = is-prop-is-contr is-contr-unit

is-prop' :
  {i : Level} (A : UU i) → UU i
is-prop' A = (x y : A) → Id x y

abstract
  is-prop-is-prop' :
    {i : Level} {A : UU i} → is-prop' A → is-prop A
  is-prop-is-prop' {i} {A} H x y =
    pair
      ( (inv (H x x)) ∙ (H x y))
      ( ind-Id x
        ( λ z p → Id ((inv (H x x)) ∙ (H x z)) p)
        ( left-inv (H x x)) y)

abstract
  is-prop'-is-prop :
    {i : Level} {A : UU i} → is-prop A → is-prop' A
  is-prop'-is-prop H x y = pr1 (H x y)

abstract
  is-contr-is-prop-inh :
    {i : Level} {A : UU i} → is-prop A → A → is-contr A
  is-contr-is-prop-inh H a = pair a (is-prop'-is-prop H a)

abstract
  is-prop-is-contr-if-inh :
    {i : Level} {A : UU i} → (A → is-contr A) → is-prop A
  is-prop-is-contr-if-inh H x y = is-prop-is-contr (H x) x y

is-subtype :
  {i j : Level} {A : UU i} (B : A → UU j) → UU (i ⊔ j)
is-subtype B = (x : _) → is-prop (B x)

-- Section 8.2 Sets

is-set :
  {i : Level} → UU i → UU i
is-set A = (x y : A) → is-prop (Id x y)

hSet :
  (i : Level) → UU (lsuc i)
hSet i = Σ (UU i) is-set

axiom-K :
  {i : Level} → UU i → UU i
axiom-K A = (x : A) (p : Id x x) → Id refl p

abstract
  is-set-axiom-K :
    {i : Level} (A : UU i) → axiom-K A → is-set A
  is-set-axiom-K A H x y =
    is-prop-is-prop' (ind-Id x (λ z p → (q : Id x z) → Id p q) (H x) y)

abstract
  axiom-K-is-set :
    {i : Level} (A : UU i) → is-set A → axiom-K A
  axiom-K-is-set A H x p =
    ( inv (contraction (is-contr-is-prop-inh (H x x) refl) refl)) ∙ 
    ( contraction (is-contr-is-prop-inh (H x x) refl) p)

abstract
  is-equiv-prop-in-id :
    {i j : Level} {A : UU i}
    (R : A → A → UU j)
    (p : (x y : A) → is-prop (R x y))
    (ρ : (x : A) → R x x)
    (i : (x y : A) → R x y → Id x y) →
    (x y : A) → is-equiv (i x y)
  is-equiv-prop-in-id R p ρ i x =
    fundamental-theorem-id-retr x (i x)
      (λ y → pair
        (ind-Id x (λ z p → R x z) (ρ x) y)
        ((λ r → is-prop'-is-prop (p x y) _ r)))

abstract
  is-prop-is-equiv :
    {i j : Level} {A : UU i} (B : UU j) (f : A → B) (E : is-equiv f) →
    is-prop B → is-prop A
  is-prop-is-equiv B f E H x y =
    is-contr-is-equiv _ (ap f {x} {y}) (is-emb-is-equiv f E x y) (H (f x) (f y))

abstract
  is-prop-is-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (f : A → B) (E : is-equiv f) →
    is-prop A → is-prop B
  is-prop-is-equiv' A f E H =
    is-prop-is-equiv _ (inv-is-equiv E) (is-equiv-inv-is-equiv E) H

abstract
  is-set-prop-in-id :
    {i j : Level} {A : UU i} (R : A → A → UU j)
    (p : (x y : A) → is-prop (R x y))
    (ρ : (x : A) → R x x)
    (i : (x y : A) → R x y → Id x y) →
    is-set A
  is-set-prop-in-id R p ρ i x y =
    is-prop-is-equiv' (R x y) (i x y) (is-equiv-prop-in-id R p ρ i x y) (p x y)

abstract
  is-prop-Eq-ℕ :
    (n m : ℕ) → is-prop (Eq-ℕ n m)
  is-prop-Eq-ℕ zero-ℕ zero-ℕ = is-prop-unit
  is-prop-Eq-ℕ zero-ℕ (succ-ℕ m) = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) zero-ℕ = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) (succ-ℕ m) = is-prop-Eq-ℕ n m

abstract
  eq-Eq-ℕ : (n m : ℕ) → Eq-ℕ n m → Id n m
  eq-Eq-ℕ = least-reflexive-Eq-ℕ Id (λ n → refl)

abstract
  is-set-ℕ : is-set ℕ
  is-set-ℕ = is-set-prop-in-id Eq-ℕ is-prop-Eq-ℕ refl-Eq-ℕ eq-Eq-ℕ

set-ℕ : hSet lzero
set-ℕ = pair ℕ is-set-ℕ

-- Section 8.3 General truncation levels

data 𝕋 : UU lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋

neg-one-𝕋 : 𝕋
neg-one-𝕋 = succ-𝕋 (neg-two-𝕋)

zero-𝕋 : 𝕋
zero-𝕋 = succ-𝕋 (neg-one-𝕋)

one-𝕋 : 𝕋
one-𝕋 = succ-𝕋 (zero-𝕋)

ℕ-in-𝕋 : ℕ → 𝕋
ℕ-in-𝕋 zero-ℕ = zero-𝕋
ℕ-in-𝕋 (succ-ℕ n) = succ-𝕋 (ℕ-in-𝕋 n)

-- Probably it is better to define this where we first need it.
add-𝕋 : 𝕋 → 𝕋 → 𝕋
add-𝕋 neg-two-𝕋 neg-two-𝕋 = neg-two-𝕋
add-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = neg-two-𝕋
add-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 y)) = y
add-𝕋 (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = neg-two-𝕋
add-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 y) = y
add-𝕋 (succ-𝕋 (succ-𝕋 neg-two-𝕋)) y = y
add-𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 x))) y = succ-𝕋 (add-𝕋 (succ-𝕋 (succ-𝕋 x)) y)

is-trunc : {i : Level} (k : 𝕋) → UU i → UU i
is-trunc neg-two-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (Id x y)

abstract
  is-trunc-succ-is-trunc :
    {i : Level} (k : 𝕋) (A : UU i) →
    is-trunc k A → is-trunc (succ-𝕋 k) A
  is-trunc-succ-is-trunc neg-two-𝕋 A H = is-prop-is-contr H
  is-trunc-succ-is-trunc (succ-𝕋 k) A H =
    λ x y → is-trunc-succ-is-trunc k (Id x y) (H x y)

abstract
  is-trunc-is-equiv :
    {i j : Level} (k : 𝕋) {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
    is-trunc k B → is-trunc k A
  is-trunc-is-equiv neg-two-𝕋 B f is-equiv-f H =
    is-contr-is-equiv B f is-equiv-f H
  is-trunc-is-equiv (succ-𝕋 k) B f is-equiv-f H x y =
    is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y})
      (is-emb-is-equiv f is-equiv-f x y) (H (f x) (f y))

is-trunc-equiv :
  {i j : Level} (k : 𝕋) {A : UU i} (B : UU  j) (e : A ≃ B) →
  is-trunc k B → is-trunc k A
is-trunc-equiv k B (pair f is-equiv-f) =
  is-trunc-is-equiv k B f is-equiv-f

abstract
  is-trunc-is-equiv' :
    {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (f : A → B) →
    is-equiv f → is-trunc k A → is-trunc k B
  is-trunc-is-equiv' k A  f is-equiv-f is-trunc-A =
    is-trunc-is-equiv k A
      ( inv-is-equiv is-equiv-f)
      ( is-equiv-inv-is-equiv is-equiv-f)
      ( is-trunc-A)

is-trunc-equiv' :
  {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (e : A ≃ B) →
  is-trunc k A → is-trunc k B
is-trunc-equiv' k A (pair f is-equiv-f) =
  is-trunc-is-equiv' k A f is-equiv-f

abstract
  is-trunc-succ-is-emb : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j}
    (f : A → B) → is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-succ-is-emb k f Ef H x y =
    is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y}) (Ef x y) (H (f x) (f y))

is-trunc-map : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} →
  (A → B) → UU (i ⊔ j)
is-trunc-map k f = (y : _) → is-trunc k (fib f y)

abstract
  is-trunc-pr1-is-trunc-fam : {i j : Level} (k : 𝕋) {A : UU i} (B : A → UU j) →
    ((x : A) → is-trunc k (B x)) → is-trunc-map k (pr1 {i} {j} {A} {B})
  is-trunc-pr1-is-trunc-fam k B H x =
    is-trunc-is-equiv k
      ( B x)
      ( fib-fam-fib-pr1 B x)
      ( is-equiv-fib-fam-fib-pr1 B x)
      ( H x)

abstract
  is-trunc-fam-is-trunc-pr1 : {i j : Level} (k : 𝕋) {A : UU i} (B : A → UU j) →
    is-trunc-map k (pr1 {i} {j} {A} {B}) → ((x : A) → is-trunc k (B x))
  is-trunc-fam-is-trunc-pr1 k B is-trunc-pr1 x =
    is-trunc-is-equiv k
      ( fib pr1 x)
      ( fib-pr1-fib-fam B x)
      ( is-equiv-fib-pr1-fib-fam B x)
      ( is-trunc-pr1 x)

abstract
  is-trunc-map-is-trunc-ap : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j}
    (f : A → B) → ((x y : A) → is-trunc-map k (ap f {x = x} {y = y})) →
    is-trunc-map (succ-𝕋 k) f
  is-trunc-map-is-trunc-ap k f is-trunc-ap-f b (pair x p) (pair x' p') =
    is-trunc-is-equiv k
      ( fib (ap f) (p ∙ (inv p')))
      ( fib-ap-eq-fib f (pair x p) (pair x' p'))
      ( is-equiv-fib-ap-eq-fib f (pair x p) (pair x' p'))
      ( is-trunc-ap-f x x' (p ∙ (inv p')))

abstract
  is-trunc-ap-is-trunc-map : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j}
    (f : A → B) → is-trunc-map (succ-𝕋 k) f →
    (x y : A) → is-trunc-map k (ap f {x = x} {y = y})
  is-trunc-ap-is-trunc-map k f is-trunc-map-f x y p =
    is-trunc-is-equiv' k
      ( Id (pair x p) (pair y refl))
      ( eq-fib-fib-ap f x y p)
      ( is-equiv-eq-fib-fib-ap f x y p)
      ( is-trunc-map-f (f y) (pair x p) (pair y refl))

is-prop-map : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-prop-map f = (b : _) → is-trunc neg-one-𝕋 (fib f b)

abstract
  is-emb-is-prop-map : {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
    is-prop-map f → is-emb f
  is-emb-is-prop-map f is-prop-map-f x y =
    is-equiv-is-contr-map
      ( is-trunc-ap-is-trunc-map neg-two-𝕋 f is-prop-map-f x y)

abstract
  is-prop-map-is-emb : {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
    is-emb f → is-prop-map f
  is-prop-map-is-emb f is-emb-f =
    is-trunc-map-is-trunc-ap neg-two-𝕋 f
      ( λ x y → is-contr-map-is-equiv (is-emb-f x y))

abstract
  is-emb-pr1-is-subtype : {i j : Level} {A : UU i} {B : A → UU j} →
    is-subtype B → is-emb (pr1 {B = B})
  is-emb-pr1-is-subtype {B = B} is-subtype-B =
    is-emb-is-prop-map pr1
      ( λ x → is-trunc-is-equiv neg-one-𝕋
        ( B x)
        ( fib-fam-fib-pr1 _ x)
        ( is-equiv-fib-fam-fib-pr1 _ x)
        ( is-subtype-B x))

abstract
  is-subtype-is-emb-pr1 : {i j : Level} {A : UU i} {B : A → UU j} →
    is-emb (pr1 {B = B}) → is-subtype B
  is-subtype-is-emb-pr1 is-emb-pr1-B x =
    is-trunc-is-equiv neg-one-𝕋
      ( fib pr1 x)
      ( fib-pr1-fib-fam _ x)
      ( is-equiv-fib-pr1-fib-fam _ x)
      ( is-prop-map-is-emb pr1 is-emb-pr1-B x)

is-fiberwise-trunc : {l1 l2 l3 : Level} (k : 𝕋)  {A : UU l1} {B : A → UU l2}
  {C : A → UU l3} (f : (x : A) → B x → C x) → UU (l1 ⊔ (l2 ⊔ l3))
is-fiberwise-trunc k f = (x : _) → is-trunc-map k (f x)

abstract
  is-trunc-tot-is-fiberwise-trunc : {l1 l2 l3 : Level} (k : 𝕋)
    {A : UU l1} {B : A → UU l2} {C : A → UU l3} (f : (x : A) → B x → C x) →
    is-fiberwise-trunc k f → is-trunc-map k (tot f)
  is-trunc-tot-is-fiberwise-trunc k f is-fiberwise-trunc-f (pair x z) =
    is-trunc-is-equiv k
      ( fib (f x) z)
      ( fib-ftr-fib-tot f (pair x z))
      ( is-equiv-fib-ftr-fib-tot f (pair x z))
      ( is-fiberwise-trunc-f x z)

abstract
  is-fiberwise-trunc-is-trunc-tot : {l1 l2 l3 : Level} (k : 𝕋)
    {A : UU l1} {B : A → UU l2} {C : A → UU l3} (f : (x : A) → B x → C x) →
    is-trunc-map k (tot f) → is-fiberwise-trunc k f
  is-fiberwise-trunc-is-trunc-tot k f is-trunc-tot-f x z =
    is-trunc-is-equiv k
      ( fib (tot f) (pair x z))
      ( fib-tot-fib-ftr f (pair x z))
      ( is-equiv-fib-tot-fib-ftr f (pair x z))
      ( is-trunc-tot-f (pair x z))

-- Exercises

-- Exercise 8.1

diagonal : {l : Level} (A : UU l) → A → A × A
diagonal A x = pair x x

abstract
  is-prop-is-equiv-diagonal : {l : Level} (A : UU l) →
    is-equiv (diagonal A) → is-prop A
  is-prop-is-equiv-diagonal A is-equiv-d =
    is-prop-is-prop' ( λ x y →
      let α = issec-inv-is-equiv is-equiv-d (pair x y) in
      ( inv (ap pr1 α)) ∙ (ap pr2 α))

eq-fib-diagonal : {l : Level} (A : UU l) (t : A × A) →
  fib (diagonal A) t → Id (pr1 t) (pr2 t)
eq-fib-diagonal A (pair x y) (pair z α) = (inv (ap pr1 α)) ∙ (ap pr2 α)

fib-diagonal-eq : {l : Level} (A : UU l) (t : A × A) →
  Id (pr1 t) (pr2 t) → fib (diagonal A) t
fib-diagonal-eq A (pair x y) β =
  pair x (eq-pair-triv (pair refl β))

issec-fib-diagonal-eq : {l : Level} (A : UU l) (t : A × A) →
  ((eq-fib-diagonal A t) ∘ (fib-diagonal-eq A t)) ~ id
issec-fib-diagonal-eq A (pair x .x) refl = refl

isretr-fib-diagonal-eq : {l : Level} (A : UU l) (t : A × A) →
  ((fib-diagonal-eq A t) ∘ (eq-fib-diagonal A t)) ~ id
isretr-fib-diagonal-eq A .(pair z z) (pair z refl) = refl

abstract
  is-equiv-eq-fib-diagonal : {l : Level} (A : UU l) (t : A × A) →
    is-equiv (eq-fib-diagonal A t)
  is-equiv-eq-fib-diagonal A t =
    is-equiv-has-inverse
      ( fib-diagonal-eq A t)
      ( issec-fib-diagonal-eq A t)
      ( isretr-fib-diagonal-eq A t)

abstract
  is-trunc-is-trunc-diagonal : {l : Level} (k : 𝕋) (A : UU l) →
    is-trunc-map k (diagonal A) → is-trunc (succ-𝕋 k) A
  is-trunc-is-trunc-diagonal k A is-trunc-d x y =
    is-trunc-is-equiv' k
      ( fib (diagonal A) (pair x y))
      ( eq-fib-diagonal A (pair x y))
      ( is-equiv-eq-fib-diagonal A (pair x y))
      ( is-trunc-d (pair x y))

abstract
  is-trunc-diagonal-is-trunc : {l : Level} (k : 𝕋) (A : UU l) →
    is-trunc (succ-𝕋 k) A → is-trunc-map k (diagonal A)
  is-trunc-diagonal-is-trunc k A is-trunc-A t =
    is-trunc-is-equiv k
      ( Id (pr1 t) (pr2 t))
      ( eq-fib-diagonal A t)
      ( is-equiv-eq-fib-diagonal A t)
      ( is-trunc-A (pr1 t) (pr2 t))

-- Exercise 8.2

-- Exercise 8.2(a)

abstract
  is-trunc-Σ : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    is-trunc k A → ((x : A) → is-trunc k (B x)) → is-trunc k (Σ A B)
  is-trunc-Σ neg-two-𝕋 is-trunc-A is-trunc-B =
    is-contr-Σ is-trunc-A is-trunc-B
  is-trunc-Σ (succ-𝕋 k) {B = B} is-trunc-A is-trunc-B s t =
    is-trunc-is-equiv k
      ( Σ (Id (pr1 s) (pr1 t)) (λ p → Id (tr B p (pr2 s)) (pr2 t)))
      ( pair-eq)
      ( is-equiv-pair-eq s t)
      ( is-trunc-Σ k
        ( is-trunc-A (pr1 s) (pr1 t))
        ( λ p → is-trunc-B (pr1 t) (tr B p (pr2 s)) (pr2 t)))

abstract
  is-trunc-prod : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k A → is-trunc k B → is-trunc k (A × B)
  is-trunc-prod k is-trunc-A is-trunc-B =
    is-trunc-Σ k is-trunc-A (λ x → is-trunc-B)

abstract
  is-prop-Σ : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-prop A → is-subtype B → is-prop (Σ A B)
  is-prop-Σ = is-trunc-Σ neg-one-𝕋

abstract
  is-prop-prod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop A → is-prop B → is-prop (A × B)
  is-prop-prod = is-trunc-prod neg-one-𝕋

abstract
  is-set-Σ : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → ((x : A) → is-set (B x)) → is-set (Σ A B)
  is-set-Σ = is-trunc-Σ zero-𝕋

set-Σ :
  {l1 l2 : Level} (A : hSet l1) (B : pr1 A → hSet l2) → hSet (l1 ⊔ l2)
set-Σ (pair A is-set-A) B =
  pair
    ( Σ A (λ x → (pr1 (B x))))
    ( is-set-Σ is-set-A (λ x → pr2 (B x)))

abstract
  is-set-prod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A × B)
  is-set-prod = is-trunc-prod zero-𝕋

set-prod :
  {l1 l2 : Level} (A : hSet l1) (B : hSet l2) → hSet (l1 ⊔ l2)
set-prod (pair A is-set-A) (pair B is-set-B) =
  pair (A × B) (is-set-prod is-set-A is-set-B)

-- Exercise 8.2 (b)

abstract
  is-trunc-Id : {l : Level} (k : 𝕋) {A : UU l} →
    is-trunc k A → (x y : A) → is-trunc k (Id x y)
  is-trunc-Id neg-two-𝕋 is-trunc-A = is-prop-is-contr is-trunc-A
  is-trunc-Id (succ-𝕋 k) is-trunc-A x y =
    is-trunc-succ-is-trunc k (Id x y) (is-trunc-A x y)

-- Exercise 8.2 (c)

abstract
  is-trunc-map-is-trunc-domain-codomain : {l1 l2 : Level} (k : 𝕋) {A : UU l1}
    {B : UU l2} {f : A → B} → is-trunc k A → is-trunc k B → is-trunc-map k f
  is-trunc-map-is-trunc-domain-codomain k {f = f} is-trunc-A is-trunc-B b =
    is-trunc-Σ k is-trunc-A (λ x → is-trunc-Id k is-trunc-B (f x) b)

-- Exercise 8.2 (d)

abstract
  is-trunc-fam-is-trunc-Σ :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    is-trunc k A → is-trunc k (Σ A B) → (x : A) → is-trunc k (B x)
  is-trunc-fam-is-trunc-Σ k {B = B} is-trunc-A is-trunc-ΣAB x =
    is-trunc-is-equiv' k
      ( fib pr1 x)
      ( fib-fam-fib-pr1 B x)
      ( is-equiv-fib-fam-fib-pr1 B x)
      ( is-trunc-map-is-trunc-domain-codomain k is-trunc-ΣAB is-trunc-A x)

-- Exercise 8.3

abstract
  is-prop-Eq-𝟚 : (x y : bool) → is-prop (Eq-𝟚 x y)
  is-prop-Eq-𝟚 true true = is-prop-unit
  is-prop-Eq-𝟚 true false = is-prop-empty
  is-prop-Eq-𝟚 false true = is-prop-empty
  is-prop-Eq-𝟚 false false = is-prop-unit

abstract
  eq-Eq-𝟚 : (x y : bool) → Eq-𝟚 x y → Id x y
  eq-Eq-𝟚 true true star = refl
  eq-Eq-𝟚 true false ()
  eq-Eq-𝟚 false true ()
  eq-Eq-𝟚 false false star = refl

abstract
  is-set-bool : is-set bool
  is-set-bool = is-set-prop-in-id Eq-𝟚 is-prop-Eq-𝟚 reflexive-Eq-𝟚 eq-Eq-𝟚

set-bool : hSet lzero
set-bool = pair bool is-set-bool

-- Exercise 8.4

abstract
  is-trunc-succ-empty : (k : 𝕋) → is-trunc (succ-𝕋 k) empty
  is-trunc-succ-empty k = ind-empty

abstract
  is-trunc-coprod : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc (succ-𝕋 (succ-𝕋 k)) A → is-trunc (succ-𝕋 (succ-𝕋 k)) B →
    is-trunc (succ-𝕋 (succ-𝕋 k)) (coprod A B)
  is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inl x) (inl y) =
    is-trunc-is-equiv (succ-𝕋 k)
      ( Eq-coprod A B (inl x) (inl y))
      ( Eq-coprod-eq A B (inl x) (inl y))
      ( is-equiv-Eq-coprod-eq A B (inl x) (inl y))
      ( is-trunc-is-equiv' (succ-𝕋 k)
        ( Id x y)
        ( map-raise _ (Id x y))
        ( is-equiv-map-raise _ (Id x y))
        ( is-trunc-A x y))
  is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inl x) (inr y) =
    is-trunc-is-equiv (succ-𝕋 k)
      ( Eq-coprod A B (inl x) (inr y))
      ( Eq-coprod-eq A B (inl x) (inr y))
      ( is-equiv-Eq-coprod-eq A B (inl x) (inr y))
      ( is-trunc-is-equiv' (succ-𝕋 k)
        ( empty)
        ( map-raise _ empty)
        ( is-equiv-map-raise _ empty)
        ( is-trunc-succ-empty k))
  is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inr x) (inl y) =
    is-trunc-is-equiv (succ-𝕋 k)
      ( Eq-coprod A B (inr x) (inl y))
      ( Eq-coprod-eq A B (inr x) (inl y))
      ( is-equiv-Eq-coprod-eq A B (inr x) (inl y))
      ( is-trunc-is-equiv' (succ-𝕋 k)
        ( empty)
        ( map-raise _ empty)
        ( is-equiv-map-raise _ empty)
        ( is-trunc-succ-empty k))
  is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inr x) (inr y) =
    is-trunc-is-equiv (succ-𝕋 k)
      ( Eq-coprod A B (inr x) (inr y))
      ( Eq-coprod-eq A B (inr x) (inr y))
      ( is-equiv-Eq-coprod-eq A B (inr x) (inr y))
      ( is-trunc-is-equiv' (succ-𝕋 k)
        ( Id x y)
        ( map-raise _ (Id x y))
        ( is-equiv-map-raise _ (Id x y))
        ( is-trunc-B x y))

abstract
  is-set-coprod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (coprod A B)
  is-set-coprod = is-trunc-coprod neg-two-𝕋

set-coprod :
  {l1 l2 : Level} (A : hSet l1) (B : hSet l2) → hSet (l1 ⊔ l2)
set-coprod (pair A is-set-A) (pair B is-set-B) =
  pair (coprod A B) (is-set-coprod is-set-A is-set-B)

abstract
  is-set-unit : is-set unit
  is-set-unit = is-trunc-succ-is-trunc neg-one-𝕋 unit is-prop-unit

set-unit : hSet lzero
set-unit = pair unit is-set-unit

abstract
  is-set-ℤ : is-set ℤ
  is-set-ℤ = is-set-coprod is-set-ℕ (is-set-coprod is-set-unit is-set-ℕ)

set-ℤ : hSet lzero
set-ℤ = pair ℤ is-set-ℤ

-- Exercise 8.5

decide : {l : Level} (A : UU l) → UU l
decide A = coprod A (¬ A)

has-decidable-equality : {l : Level} (A : UU l) → UU l
has-decidable-equality A = (x y : A) → decide (Id x y)

splitting-decidable-equality : {l : Level} (A : UU l) (x y : A) →
  decide (Id x y) → UU lzero
splitting-decidable-equality A x y (inl p) = unit
splitting-decidable-equality A x y (inr f) = empty

abstract
  is-prop-splitting-decidable-equality : {l : Level} (A : UU l) (x y : A) →
    (t : decide (Id x y)) →
    is-prop (splitting-decidable-equality A x y t)
  is-prop-splitting-decidable-equality A x y (inl p) = is-prop-unit
  is-prop-splitting-decidable-equality A x y (inr f) = is-prop-empty

reflexive-splitting-decidable-equality : {l : Level} (A : UU l) (x : A) →
  (t : decide (Id x x)) → splitting-decidable-equality A x x t
reflexive-splitting-decidable-equality A x (inl p) = star
reflexive-splitting-decidable-equality A x (inr f) =
  ind-empty {P = λ t → splitting-decidable-equality A x x (inr f)} (f refl)

eq-splitting-decidable-equality : {l : Level} (A : UU l) (x y : A) →
  (t : decide (Id x y)) →
  splitting-decidable-equality A x y t → Id x y
eq-splitting-decidable-equality A x y (inl p) t = p
eq-splitting-decidable-equality A x y (inr f) t =
  ind-empty {P = λ s → Id x y} t 

abstract
  is-set-has-decidable-equality : {l : Level} (A : UU l) →
    has-decidable-equality A → is-set A
  is-set-has-decidable-equality A d =
    is-set-prop-in-id
      ( λ x y → splitting-decidable-equality A x y (d x y))
      ( λ x y → is-prop-splitting-decidable-equality A x y (d x y))
      ( λ x → reflexive-splitting-decidable-equality A x (d x x))
      ( λ x y → eq-splitting-decidable-equality A x y (d x y))

-- Exercise 8.6

-- Exercise 8.6.a

Eq-𝟚-eq : (x y : bool) → Id x y → Eq-𝟚 x y
Eq-𝟚-eq x .x refl = reflexive-Eq-𝟚 x

abstract
  has-decidable-equality-𝟚 : has-decidable-equality bool
  has-decidable-equality-𝟚 true true = inl refl
  has-decidable-equality-𝟚 true false = inr (Eq-𝟚-eq true false)
  has-decidable-equality-𝟚 false true = inr (Eq-𝟚-eq false true)
  has-decidable-equality-𝟚 false false = inl refl

Eq-ℕ-eq : (x y : ℕ) → Id x y → Eq-ℕ x y
Eq-ℕ-eq x .x refl = refl-Eq-ℕ x

abstract
  injective-succ-ℕ : (x y : ℕ) → Id (succ-ℕ x) (succ-ℕ y) → Id x y
  injective-succ-ℕ zero-ℕ zero-ℕ p = refl
  injective-succ-ℕ zero-ℕ (succ-ℕ y) p =
    ind-empty
      { P = λ t → Id zero-ℕ (succ-ℕ y)}
      ( Eq-ℕ-eq one-ℕ (succ-ℕ (succ-ℕ y)) p)
  injective-succ-ℕ (succ-ℕ x) zero-ℕ p =
    ind-empty
      { P = λ t → Id (succ-ℕ x) zero-ℕ}
      ( Eq-ℕ-eq (succ-ℕ (succ-ℕ x)) one-ℕ p)
  injective-succ-ℕ (succ-ℕ x) (succ-ℕ y) p =
    ap succ-ℕ (eq-Eq-ℕ x y (Eq-ℕ-eq (succ-ℕ (succ-ℕ x)) (succ-ℕ (succ-ℕ y)) p))

abstract
  has-decidable-equality-ℕ : has-decidable-equality ℕ
  has-decidable-equality-ℕ zero-ℕ zero-ℕ = inl refl
  has-decidable-equality-ℕ zero-ℕ (succ-ℕ y) = inr (Eq-ℕ-eq zero-ℕ (succ-ℕ y))
  has-decidable-equality-ℕ (succ-ℕ x) zero-ℕ = inr (Eq-ℕ-eq (succ-ℕ x) zero-ℕ)
  has-decidable-equality-ℕ (succ-ℕ x) (succ-ℕ y) =
    functor-coprod
      ( ap succ-ℕ)
      ( λ (f : ¬ (Id x y)) p → f (injective-succ-ℕ x y p))
      ( has-decidable-equality-ℕ x y)

-- Exercise 8.6.b

abstract
  has-decidable-equality-coprod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    has-decidable-equality A → has-decidable-equality B →
    has-decidable-equality (coprod A B)
  has-decidable-equality-coprod dec-A dec-B (inl x) (inl y) =
    functor-coprod
      ( ap inl)
      ( λ f p → f (inv-is-equiv (is-emb-inl _ _ x y) p))
      ( dec-A x y)
  has-decidable-equality-coprod {A = A} {B = B} dec-A dec-B (inl x) (inr y) =
    inr
      ( λ p →
        inv-is-equiv
          ( is-equiv-map-raise _ empty)
          ( Eq-coprod-eq A B (inl x) (inr y) p))
  has-decidable-equality-coprod {A = A} {B = B} dec-A dec-B (inr x) (inl y) =
    inr
      ( λ p →
        inv-is-equiv
          ( is-equiv-map-raise _ empty)
          ( Eq-coprod-eq A B (inr x) (inl y) p))
  has-decidable-equality-coprod dec-A dec-B (inr x) (inr y) =
    functor-coprod
      ( ap inr)
      ( λ f p → f (inv-is-equiv (is-emb-inr _ _ x y) p))
      ( dec-B x y)

abstract
  has-decidable-equality-prod-aux : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    (x x' : A) (y y' : B) → decide (Id x x') → decide (Id y y') →
    decide (Id (pair x y) (pair x' y'))
  has-decidable-equality-prod-aux x x' y y' (inl p) (inl q) =
    inl (eq-pair-triv (pair p q))
  has-decidable-equality-prod-aux x x' y y' (inl p) (inr g) =
    inr (λ h → g (ap pr2 h))
  has-decidable-equality-prod-aux x x' y y' (inr f) (inl q) =
    inr (λ h → f (ap pr1 h))
  has-decidable-equality-prod-aux x x' y y' (inr f) (inr g) =
    inr (λ h → f (ap pr1 h))

abstract
  has-decidable-equality-prod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    has-decidable-equality A → has-decidable-equality B →
    has-decidable-equality (A × B)
  has-decidable-equality-prod dec-A dec-B (pair x y) (pair x' y') =
    has-decidable-equality-prod-aux x x' y y' (dec-A x x') (dec-B y y')

-- Exercise 8.6.c

decide-retract-of :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → decide B → decide A
decide-retract-of (pair i (pair r H)) (inl b) = inl (r b)
decide-retract-of (pair i (pair r H)) (inr f) = inr (f ∘ i)

abstract
  has-decidable-equality-retract-of :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    A retract-of B → has-decidable-equality B → has-decidable-equality A
  has-decidable-equality-retract-of (pair i (pair r H)) d x y =
    decide-retract-of
      ( Id-retract-of-Id (pair i (pair r H)) x y)
      ( d (i x) (i y))

-- Exercise 8.7

abstract
  is-trunc-retract-of : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    A retract-of B → is-trunc k B → is-trunc k A
  is-trunc-retract-of neg-two-𝕋 (pair i (pair r H)) is-trunc-B =
    is-contr-retract-of _ (pair i (pair r H)) is-trunc-B
  is-trunc-retract-of (succ-𝕋 k) (pair i retr-i) is-trunc-B x y =
    is-trunc-retract-of k
      ( pair (ap i) (retr-ap i retr-i x y))
      ( is-trunc-B (i x) (i y))

-- Exercise 8.8

is-injective : {l1 l2 : Level} {A : UU l1} (is-set-A : is-set A) {B : UU l2}
  (is-set-B : is-set B) (f : A → B) → UU (l1 ⊔ l2)
is-injective {A = A} is-set-A is-set-B f = (x y : A) → Id (f x) (f y) → Id x y

is-injective-const-true : is-injective is-set-unit is-set-bool
  (const unit bool true)
is-injective-const-true x y p = center (is-prop-unit x y)

is-injective-const-false : is-injective is-set-unit is-set-bool
  (const unit bool false)
is-injective-const-false x y p = center (is-prop-unit x y)

abstract
  is-equiv-is-prop : {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-prop A →
    is-prop B → {f : A → B} → (B → A) → is-equiv f
  is-equiv-is-prop is-prop-A is-prop-B {f} g =
    is-equiv-has-inverse
      ( g)
      ( λ y → center (is-prop-B (f (g y)) y))
      ( λ x → center (is-prop-A (g (f x)) x))

abstract
  is-emb-is-injective : {l1 l2 : Level} {A : UU l1} (is-set-A : is-set A)
    {B : UU l2} (is-set-B : is-set B) (f : A → B) →
    is-injective is-set-A is-set-B f → is-emb f
  is-emb-is-injective is-set-A is-set-B f is-injective-f x y =
    is-equiv-is-prop
      ( is-set-A x y)
      ( is-set-B (f x) (f y))
      ( is-injective-f x y)

abstract
  is-injective-is-emb : {l1 l2 : Level} {A : UU l1} {is-set-A : is-set A}
    {B : UU l2} {is-set-B : is-set B} {f : A → B} →
    is-emb f → is-injective is-set-A is-set-B f
  is-injective-is-emb is-emb-f x y = inv-is-equiv (is-emb-f x y)

-- Exercise 8.9

abstract
  is-trunc-const-is-trunc : {l : Level} (k : 𝕋) {A : UU l} →
    is-trunc (succ-𝕋 k) A → (x : A) → is-trunc-map k (const unit A x)
  is-trunc-const-is-trunc k is-trunc-A x y =
    is-trunc-is-equiv' k
      ( Id x y)
      ( left-unit-law-Σ-map (λ t → Id x y) is-contr-unit)
      ( is-equiv-left-unit-law-Σ-map (λ t → Id x y) is-contr-unit)
      ( is-trunc-A x y)

abstract
  is-trunc-is-trunc-const : {l : Level} (k : 𝕋) {A : UU l} →
    ((x : A) → is-trunc-map k (const unit A x)) → is-trunc (succ-𝕋 k) A
  is-trunc-is-trunc-const k is-trunc-const x y =
    is-trunc-is-equiv k
      ( Σ unit (λ t → Id x y))
      ( left-unit-law-Σ-map (λ t → Id x y) is-contr-unit)
      ( is-equiv-left-unit-law-Σ-map (λ t → Id x y) is-contr-unit)
      ( is-trunc-const x y)

-- Exercise 8.10

map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) → fib (g ∘ h) x → Σ (fib g x) (λ t → fib h (pr1 t))
map-fib-comp g h x (pair a p) =
  pair
    ( pair (h a) p)
    ( pair a refl)

inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) → Σ (fib g x) (λ t → fib h (pr1 t)) → fib (g ∘ h) x
inv-map-fib-comp g h c t =
  pair (pr1 (pr2 t)) ((ap g (pr2 (pr2 t))) ∙ (pr2 (pr1 t)))

issec-inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) →
  ((map-fib-comp g h x) ∘ (inv-map-fib-comp g h x)) ~ id
issec-inv-map-fib-comp g h x
  (pair (pair .(h a) refl) (pair a refl)) = refl

isretr-inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) (x : X) →
  ((inv-map-fib-comp g h x) ∘ (map-fib-comp g h x)) ~ id
isretr-inv-map-fib-comp g h .(g (h a)) (pair a refl) = refl

abstract
  is-equiv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) (x : X) →
    is-equiv (map-fib-comp g h x)
  is-equiv-map-fib-comp g h x =
    is-equiv-has-inverse
      ( inv-map-fib-comp g h x)
      ( issec-inv-map-fib-comp g h x)
      ( isretr-inv-map-fib-comp g h x)

abstract
  is-equiv-inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) (x : X) →
    is-equiv (inv-map-fib-comp g h x)
  is-equiv-inv-map-fib-comp g h x =
    is-equiv-has-inverse
      ( map-fib-comp g h x)
      ( isretr-inv-map-fib-comp g h x)
      ( issec-inv-map-fib-comp g h x)

abstract
  is-trunc-map-htpy : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    (f g : A → B) → f ~ g → is-trunc-map k g → is-trunc-map k f
  is-trunc-map-htpy k {A} f g H is-trunc-g b =
    is-trunc-is-equiv k
      ( Σ A (λ z → Id (g z) b))
      ( fib-triangle f g id H b)
      ( is-fiberwise-equiv-is-equiv-triangle f g id H (is-equiv-id _) b)
      ( is-trunc-g b)

abstract
  is-trunc-map-comp : {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k h → is-trunc-map k f
  is-trunc-map-comp k f g h H is-trunc-g is-trunc-h =
    is-trunc-map-htpy k f (g ∘ h) H
      ( λ x → is-trunc-is-equiv k
        ( Σ (fib g x) (λ t → fib h (pr1 t)))
        ( map-fib-comp g h x)
        ( is-equiv-map-fib-comp g h x)
        ( is-trunc-Σ k
          ( is-trunc-g x)
          ( λ t → is-trunc-h (pr1 t))))

abstract
  is-trunc-map-right-factor : {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k f → is-trunc-map k h
  is-trunc-map-right-factor k {A} f g h H is-trunc-g is-trunc-f b =
    is-trunc-fam-is-trunc-Σ k
      ( is-trunc-g (g b))
      ( is-trunc-is-equiv' k
        ( Σ A (λ z → Id (g (h z)) (g b)))
        ( map-fib-comp g h (g b))
        ( is-equiv-map-fib-comp g h (g b))
        ( is-trunc-map-htpy k (g ∘ h) f (htpy-inv H) is-trunc-f (g b)))
      ( pair b refl)

abstract
  is-trunc-map-succ-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    (f : A → B) → is-trunc-map k f → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-succ-is-trunc-map k f is-trunc-f b =
    is-trunc-succ-is-trunc k (fib f b) (is-trunc-f b)

{- Elementary number theory -} 

abstract
  is-decidable-leq-ℕ :
    (m n : ℕ) → decide (leq-ℕ m n)
  is-decidable-leq-ℕ zero-ℕ zero-ℕ = inl star
  is-decidable-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
  is-decidable-leq-ℕ (succ-ℕ m) zero-ℕ = inr id
  is-decidable-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-leq-ℕ m n

abstract
  is-decidable-le-ℕ :
    (m n : ℕ) → decide (le-ℕ m n)
  is-decidable-le-ℕ zero-ℕ zero-ℕ = inr id
  is-decidable-le-ℕ zero-ℕ (succ-ℕ n) = inl star
  is-decidable-le-ℕ (succ-ℕ m) zero-ℕ = inr id
  is-decidable-le-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-le-ℕ m n
