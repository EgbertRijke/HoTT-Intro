{-# OPTIONS --without-K --exact-split #-}

module hott-i where

import 04-inductive-types
open 04-inductive-types public

data 𝕀 : UU lzero where
  left : 𝕀

postulate right : 𝕀

data Path {l : Level} (A : 𝕀 → UU l) : (a : A left) (a' : A right) → UU l where
  pcon : (f : (x : 𝕀) → A x) → Path A (f left) (f right)

apply-path :
  {l : Level} (A : 𝕀 → UU l) (a : A left) (a' : A right) →
  Path A a a' → (x : 𝕀) → A x
apply-path A .(f left) .(f right) (pcon f) x = f x

refl-path :
  {l : Level} (A : UU l) (a : A) → Path (λ x → A) a a
refl-path A a = pcon (λ x → a)

apply-path-pcon :
  {l : Level} (A : 𝕀 → UU l) (f : (x : 𝕀) → A x) →
  (x : 𝕀) → Path (λ y → A x) (apply-path A (f left) (f right) (pcon f) x) (f x)
apply-path-pcon A f x = refl-path (A x) (f x)

left-apply-path :
  {l : Level} (A : 𝕀 → UU l) (a : A left) (a' : A right) (p : Path A a a') →
  Path (λ y → A left) (apply-path A a a' p left) a
left-apply-path A .(f left) .(f right) (pcon f) = refl-path (A left) (f left)

right-apply-path :
  {l : Level} (A : 𝕀 → UU l) (a : A left) (a' : A right) (p : Path A a a') →
  Path (λ y → A right) (apply-path A a a' p right) a'
right-apply-path A .(f left) .(f right) (pcon f) = refl-path (A right) (f right)

free-transport-path :
  {l : Level} (A : 𝕀 → UU l) → A left → (x : 𝕀) → A x
free-transport-path A a left = a

transport-path :
  {l : Level} (A : 𝕀 → UU l) → A left → A right
transport-path A a = free-transport-path A a right

elim-path-lemma :
  {l : Level} {A : UU l} (f : (x : 𝕀) → A) →
  (i : 𝕀) → Path (λ j → A) (f left) (f i)
elim-path-lemma {A = A} f left = refl-path A (f left)

elim-path :
  {l1 l2 : Level} (A : UU l1) (a : A)
  (B : (x : A) (p : Path (λ i → A) a x) → UU l2) →
  B a (refl-path A a) →
  (x : A) (p : Path (λ i → A) a x) → B x p
elim-path A .(f left) B b .(f right) (pcon f) =
  transport-path (λ i → B (f i) {!elim-path-lemma f i!}) b
  

concat-path :
  {l : Level} {A : UU l} {x y z : A} →
  Path (λ i → A) x y → Path (λ i → A) y z → Path (λ i → A) x z
concat-path {l} {A} {x} p (pcon f) =
  transport-path (λ i → Path (λ j → A) x (f i)) p

function-extensionality' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  (H : (x : A) → Path (λ i → B x) (f x) (g x)) →
  (i : 𝕀) (x : A) → B x
function-extensionality' {B = B} {f} {g} H i x =
  apply-path (λ j → B x) (f x) (g x) (H x) i

function-extensionality :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  (H : (x : A) → Path (λ i → B x) (f x) (g x)) →
  Path (λ j → (x : A) → B x) f g
function-extensionality {l1} {l2} {A} {B} {f} {g} H =
  concat-path
    ( concat-path
      {!!}
      ( pcon (function-extensionality' H)))
    ( {!!})

{-
pcon-apply-path :
  {l : Level} (A : 𝕀 → UU l) (a : A left) (a' : A right) (p : Path A a a') →
  Path (λ y → Path A a a') (pcon (apply-path A a a' p)) ?
pcon-apply-path A a a' p = ?
-}
