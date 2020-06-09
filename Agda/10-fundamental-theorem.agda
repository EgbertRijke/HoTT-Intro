{-# OPTIONS --without-K --exact-split --safe #-}

module 10-fundamental-theorem where

import 09-contractible-types
open 09-contractible-types public

--------------------------------------------------------------------------------

-- Section 8.1 Families of equivalences

{- Any family of maps induces a map on the total spaces. -}

tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x → C x) → ( Σ A B → Σ A C)
tot f t = pair (pr1 t) (f (pr1 t) (pr2 t))

{- We show that for any family of maps, the fiber of the induced map on total
   spaces are equivalent to the fibers of the maps in the family. -}
   
fib-ftr-fib-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  fib (tot f) t → fib (f (pr1 t)) (pr2 t)
fib-ftr-fib-tot f .(pair x (f x y)) (pair (pair x y) refl) = pair y refl

fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  fib (f (pr1 t)) (pr2 t) → fib (tot f) t
fib-tot-fib-ftr F (pair a .(F a y)) (pair y refl) = pair (pair a y) refl

issec-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  ((fib-ftr-fib-tot f t) ∘ (fib-tot-fib-ftr f t)) ~ id
issec-fib-tot-fib-ftr f (pair x .(f x y)) (pair y refl) = refl

isretr-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  ((fib-tot-fib-ftr f t) ∘ (fib-ftr-fib-tot f t)) ~ id
isretr-fib-tot-fib-ftr f .(pair x (f x y)) (pair (pair x y) refl) = refl

abstract
  is-equiv-fib-ftr-fib-tot :
    {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
    (f : (x : A) → B x → C x) → (t : Σ A C) →
    is-equiv (fib-ftr-fib-tot f t)
  is-equiv-fib-ftr-fib-tot f t =
    is-equiv-has-inverse
      ( fib-tot-fib-ftr f t)
      ( issec-fib-tot-fib-ftr f t)
      ( isretr-fib-tot-fib-ftr f t)

abstract
  is-equiv-fib-tot-fib-ftr :
    {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
    (f : (x : A) → B x → C x) → (t : Σ A C) →
    is-equiv (fib-tot-fib-ftr f t)
  is-equiv-fib-tot-fib-ftr f t =
    is-equiv-has-inverse
      ( fib-ftr-fib-tot f t)
      ( isretr-fib-tot-fib-ftr f t)
      ( issec-fib-tot-fib-ftr f t)

{- Now that we have shown that the fibers of the induced map on total spaces
   are equivalent to the fibers of the maps in the family, it follows that
   the induced map on total spaces is an equivalence if and only if each map
   in the family is an equivalence. -}

is-fiberwise-equiv :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x → C x) → UU (i ⊔ (j ⊔ k))
is-fiberwise-equiv f = (x : _) → is-equiv (f x)

abstract
  is-equiv-tot-is-fiberwise-equiv :
    {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
    {f : (x : A) → B x → C x} → is-fiberwise-equiv f →
    is-equiv (tot f )
  is-equiv-tot-is-fiberwise-equiv {f = f} H =
    is-equiv-is-contr-map
      ( λ t → is-contr-is-equiv _
        ( fib-ftr-fib-tot f t)
        ( is-equiv-fib-ftr-fib-tot f t)
        ( is-contr-map-is-equiv (H _) (pr2 t)))

abstract
  is-fiberwise-equiv-is-equiv-tot :
    {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
    (f : (x : A) → B x → C x) → is-equiv (tot f) →
    is-fiberwise-equiv f
  is-fiberwise-equiv-is-equiv-tot {A = A} {B} {C} f is-equiv-tot-f x =
    is-equiv-is-contr-map
      ( λ z → is-contr-is-equiv'
        ( fib (tot f) (pair x z))
        ( fib-ftr-fib-tot f (pair x z))
        ( is-equiv-fib-ftr-fib-tot f (pair x z))
        ( is-contr-map-is-equiv is-equiv-tot-f (pair x z)))

equiv-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x ≃ C x) → (Σ A B) ≃ (Σ A C)
equiv-tot e =
  pair
    ( tot (λ x → map-equiv (e x)))
    ( is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-map-equiv (e x)))

{- In the second part of this section we show that any equivalence f on base 
   types also induces an equivalence on total spaces. -}

Σ-map-base-map :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  Σ A (λ x → C (f x)) → Σ B C
Σ-map-base-map f C s = pair (f (pr1 s)) (pr2 s)

{- The proof is similar to the previous part: we show that the fibers of f
   and Σ-kap-base-map f C are equivalent. -}

fib-Σ-map-base-map-fib :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → fib f (pr1 t) → fib (Σ-map-base-map f C) t
fib-Σ-map-base-map-fib f C (pair .(f x) z) (pair x refl) =
  pair (pair x z) refl

fib-fib-Σ-map-base-map :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → fib (Σ-map-base-map f C) t → fib f (pr1 t)
fib-fib-Σ-map-base-map f C .(pair (f x) z) (pair (pair x z) refl) =
  pair x refl

issec-fib-fib-Σ-map-base-map :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) →
  ( (fib-Σ-map-base-map-fib f C t) ∘ (fib-fib-Σ-map-base-map f C t)) ~ id
issec-fib-fib-Σ-map-base-map f C .(pair (f x) z) (pair (pair x z) refl) =
  refl

isretr-fib-fib-Σ-map-base-map :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) →
  ( (fib-fib-Σ-map-base-map f C t) ∘ (fib-Σ-map-base-map-fib f C t)) ~ id
isretr-fib-fib-Σ-map-base-map f C (pair .(f x) z) (pair x refl) = refl

abstract
  is-equiv-fib-Σ-map-base-map-fib :
    { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
    ( t : Σ B C) → is-equiv (fib-Σ-map-base-map-fib f C t)
  is-equiv-fib-Σ-map-base-map-fib f C t =
    is-equiv-has-inverse
      ( fib-fib-Σ-map-base-map f C t)
      ( issec-fib-fib-Σ-map-base-map f C t)
      ( isretr-fib-fib-Σ-map-base-map f C t)

equiv-fib-Σ-map-base-map-fib :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → (fib f (pr1 t)) ≃ (fib (Σ-map-base-map f C) t)
equiv-fib-Σ-map-base-map-fib f C t =
  pair ( fib-Σ-map-base-map-fib f C t)
       ( is-equiv-fib-Σ-map-base-map-fib f C t)

abstract
  is-contr-map-Σ-map-base-map :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (f : A → B) →
    is-contr-map f → is-contr-map (Σ-map-base-map f C)
  is-contr-map-Σ-map-base-map C f is-contr-f (pair y z) =
    is-contr-is-equiv'
      ( fib f y)
      ( fib-Σ-map-base-map-fib f C (pair y z))
      ( is-equiv-fib-Σ-map-base-map-fib f C (pair y z))
      ( is-contr-f y)

abstract
  is-equiv-Σ-map-base-map :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (f : A → B) →
    is-equiv f → is-equiv (Σ-map-base-map f C)
  is-equiv-Σ-map-base-map C f is-equiv-f =
    is-equiv-is-contr-map
      ( is-contr-map-Σ-map-base-map C f (is-contr-map-is-equiv is-equiv-f))

{- Now we combine the two parts of this section. -}

toto :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  Σ A C → Σ B D
toto D f g t = pair (f (pr1 t)) (g (pr1 t) (pr2 t))

{- A special case of toto is the functoriality of the cartesian product. -}

{- We construct the functoriality of cartesian products. -}

functor-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (A × B) → (C × D)
functor-prod f g (pair a b) = pair (f a) (g b)

functor-prod-pr1 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (pr1 ∘ (functor-prod f g)) ~ (f ∘ pr1)
functor-prod-pr1 f g (pair a b) = refl

functor-prod-pr2 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (pr2 ∘ (functor-prod f g)) ~ (g ∘ pr2)
functor-prod-pr2 f g (pair a b) = refl

{- For our convenience we show that the functorial action of cartesian products
   preserves identity maps, compositions, homotopies, and equivalences. -}

functor-prod-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (functor-prod (id {A = A}) (id {A = B})) ~ id
functor-prod-id (pair a b) = refl

functor-prod-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : UU l5} {F : UU l6} (f : A → C) (g : B → D) (h : C → E) (k : D → F) →
  functor-prod (h ∘ f) (k ∘ g) ~ ((functor-prod h k) ∘ (functor-prod f g))
functor-prod-comp f g h k (pair a b) = refl

functor-prod-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f f' : A → C} (H : f ~ f') {g g' : B → D} (K : g ~ g') →
  functor-prod f g ~ functor-prod f' g'
functor-prod-htpy {f = f} {f'} H {g} {g'} K (pair a b) =
  eq-pair-triv (pair (H a) (K b))

abstract
  is-equiv-functor-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) →
    is-equiv f → is-equiv g → is-equiv (functor-prod f g)
  is-equiv-functor-prod f g
    ( pair (pair sf issec-sf) (pair rf isretr-rf))
    ( pair (pair sg issec-sg) (pair rg isretr-rg)) =
    pair
      ( pair
        ( functor-prod sf sg)
        ( ( htpy-inv (functor-prod-comp sf sg f g)) ∙h
          ( (functor-prod-htpy issec-sf issec-sg) ∙h functor-prod-id)))
      ( pair
        ( functor-prod rf rg)
        ( ( htpy-inv (functor-prod-comp f g rf rg)) ∙h
          ( (functor-prod-htpy isretr-rf isretr-rg) ∙h functor-prod-id)))

{- triangle -}

triangle-toto :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  (toto D f g) ~ ((Σ-map-base-map f D) ∘ (tot g))
triangle-toto D f g t = refl

abstract
  is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
    (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
    is-equiv f → (is-fiberwise-equiv g) →
    is-equiv (toto D f g)
  is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map
    D f g is-equiv-f is-fiberwise-equiv-g =
    is-equiv-comp
      ( toto D f g)
      ( Σ-map-base-map f D)
      ( tot g)
      ( triangle-toto D f g)
      ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-g)
      ( is-equiv-Σ-map-base-map D f is-equiv-f)

equiv-toto :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (e : A ≃ B) (g : (x : A) → C x ≃ D (map-equiv e x)) →
  Σ A C ≃ Σ B D
equiv-toto D e g =
  pair
    ( toto D (map-equiv e) (λ x → map-equiv (g x)))
    ( is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map D
      ( map-equiv e)
      ( λ x → map-equiv (g x))
      ( is-equiv-map-equiv e)
      ( λ x → is-equiv-map-equiv (g x)))

abstract
  is-fiberwise-equiv-is-equiv-toto-is-equiv-base-map :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
    (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
    is-equiv f → is-equiv (toto D f g) → is-fiberwise-equiv g
  is-fiberwise-equiv-is-equiv-toto-is-equiv-base-map
    D f g is-equiv-f is-equiv-toto-fg =
    is-fiberwise-equiv-is-equiv-tot g
      ( is-equiv-right-factor
        ( toto D f g)
        ( Σ-map-base-map f D)
        ( tot g)
        ( triangle-toto D f g)
        ( is-equiv-Σ-map-base-map D f is-equiv-f)
        ( is-equiv-toto-fg))

--------------------------------------------------------------------------------

-- Section 8.2 The fundamental theorem

-- The general form of the fundamental theorem of identity types

abstract
  fundamental-theorem-id :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    is-contr (Σ A B) → (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f
  fundamental-theorem-id {A = A} a b is-contr-AB f =
    is-fiberwise-equiv-is-equiv-tot f
      ( is-equiv-is-contr (tot f) (is-contr-total-path a) is-contr-AB)

abstract
  fundamental-theorem-id' :
    {i j : Level} {A : UU i} {B : A → UU j}
    (a : A) (b : B a) (f : (x : A) → Id a x → B x) →
    is-fiberwise-equiv f → is-contr (Σ A B)
  fundamental-theorem-id' {A = A} {B = B} a b f is-fiberwise-equiv-f =
    is-contr-is-equiv'
      ( Σ A (Id a))
      ( tot f)
      ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-f)
      ( is-contr-total-path a)

-- The canonical form of the fundamental theorem of identity types

abstract 
  fundamental-theorem-id-J :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    is-contr (Σ A B) → is-fiberwise-equiv (ind-Id a (λ x p → B x) b)
  fundamental-theorem-id-J {i} {j} {A} {B} a b is-contr-AB =
    fundamental-theorem-id a b is-contr-AB (ind-Id a (λ x p → B x) b)

-- The converse of the fundamental theorem of identity types

abstract
  fundamental-theorem-id-J' :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    (is-fiberwise-equiv (ind-Id a (λ x p → B x) b)) → is-contr (Σ A B)
  fundamental-theorem-id-J' {i} {j} {A} {B} a b H =
    is-contr-is-equiv'
      ( Σ A (Id a))
      ( tot (ind-Id a (λ x p → B x) b))
      ( is-equiv-tot-is-fiberwise-equiv H)
      ( is-contr-total-path a)

-- We characterize the identity type of the natural numbers.

center-total-Eq-ℕ :
  (m : ℕ) → Σ ℕ (Eq-ℕ m)
center-total-Eq-ℕ m = pair m (refl-Eq-ℕ m)

map-total-Eq-ℕ :
  (m : ℕ) → Σ ℕ (Eq-ℕ m) → Σ ℕ (Eq-ℕ (succ-ℕ m))
map-total-Eq-ℕ m (pair n e) = pair (succ-ℕ n) e

contraction-total-Eq-ℕ :
  (m : ℕ) (x : Σ ℕ (Eq-ℕ m)) → Id (center-total-Eq-ℕ m) x
contraction-total-Eq-ℕ zero-ℕ (pair zero-ℕ star) = refl
contraction-total-Eq-ℕ (succ-ℕ m) (pair (succ-ℕ n) e) =
  ap (map-total-Eq-ℕ m) (contraction-total-Eq-ℕ m (pair n e))

is-contr-total-Eq-ℕ :
  (m : ℕ) → is-contr (Σ ℕ (Eq-ℕ m))
is-contr-total-Eq-ℕ m =
  pair (center-total-Eq-ℕ m) (contraction-total-Eq-ℕ m)

is-equiv-Eq-ℕ-eq :
  {m n : ℕ} → is-equiv (Eq-ℕ-eq {m} {n})
is-equiv-Eq-ℕ-eq {m} {n} =
  fundamental-theorem-id m
    ( refl-Eq-ℕ m)
    ( is-contr-total-Eq-ℕ m)
    ( λ y → Eq-ℕ-eq {m} {y})
    ( n)

-- As an application we show that equivalences are embeddings.
is-emb :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-emb f = (x y : _) → is-equiv (ap f {x} {y})

_↪_ :
  {i j : Level} → UU i → UU j → UU (i ⊔ j)
A ↪ B = Σ (A → B) is-emb

map-emb :
  {i j : Level} {A : UU i} {B : UU j} → A ↪ B → A → B
map-emb f = pr1 f

is-emb-map-emb :
  { i j : Level} {A : UU i} {B : UU j} (f : A ↪ B) → is-emb (map-emb f)
is-emb-map-emb f = pr2 f

eq-emb :
  {i j : Level} {A : UU i} {B : UU j} (f : A ↪ B) →
  {x y : A} → Id (map-emb f x) (map-emb f y) → Id x y
eq-emb f {x} {y} = inv-is-equiv (is-emb-map-emb f x y)

abstract
  is-emb-is-equiv :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) → is-equiv f → is-emb f
  is-emb-is-equiv {i} {j} {A} {B} f is-equiv-f x =
    fundamental-theorem-id x refl
      ( is-contr-equiv
        ( fib f (f x))
        ( equiv-tot (λ y → equiv-inv (f x) (f y)))
        ( is-contr-map-is-equiv is-equiv-f (f x)))
      ( λ y p → ap f p)

emb-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (A ↪ B)
emb-equiv e =
  pair (map-equiv e) (is-emb-is-equiv (map-equiv e) (is-equiv-map-equiv e))

emb-id :
  {i : Level} {A : UU i} → (A ↪ A)
emb-id {i} {A} = emb-equiv (equiv-id A)

equiv-ap :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) (x y : A) →
  (Id x y) ≃ (Id (map-equiv e x) (map-equiv e y))
equiv-ap e x y =
  pair
    ( ap (map-equiv e) {x} {y})
    ( is-emb-is-equiv (map-equiv e) (is-equiv-map-equiv e) x y)

-- Section 7.3 Identity systems

IND-identity-system :
  {i j : Level} (k : Level) {A : UU i} (B : A → UU j) (a : A) (b : B a) → UU _
IND-identity-system k {A} B a b =
  ( P : (x : A) (y : B x) → UU k) →
    sec (λ (h : (x : A) (y : B x) → P x y) → h a b)

fam-Σ :
  {i j k : Level} {A : UU i} {B : A → UU j} (C : (x : A) → B x → UU k) →
  Σ A B → UU k
fam-Σ C (pair x y) = C x y

abstract
  ind-identity-system :
    {i j k : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    (is-contr-AB : is-contr (Σ A B)) (P : (x : A) → B x → UU k) →
    P a b → (x : A) (y : B x) → P x y
  ind-identity-system a b is-contr-AB P p x y =
    tr
      ( fam-Σ P)
      ( eq-is-contr is-contr-AB (pair a b) (pair x y))
      ( p)

  comp-identity-system :
    {i j k : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    (is-contr-AB : is-contr (Σ A B)) →
    (P : (x : A) → B x → UU k) (p : P a b) →
    Id (ind-identity-system a b is-contr-AB P p a b) p
  comp-identity-system a b is-contr-AB P p =
    ap
      ( λ t → tr (fam-Σ P) t p)
      ( eq-is-contr
        ( is-prop-is-contr is-contr-AB (pair a b) (pair a b))
        ( eq-is-contr is-contr-AB (pair a b) (pair a b))
        ( refl))

  Ind-identity-system :
    {i j : Level} (k : Level) {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    (is-contr-AB : is-contr (Σ A B)) →
    IND-identity-system k B a b
  Ind-identity-system k a b is-contr-AB P =
    pair
      ( ind-identity-system a b is-contr-AB P)
      ( comp-identity-system a b is-contr-AB P)
  
contraction-total-space-IND-identity-system :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  IND-identity-system (i ⊔ j) B a b →
  (t : Σ A B) → Id (pair a b) t
contraction-total-space-IND-identity-system a b ind (pair x y) =
  pr1 (ind (λ x' y' → Id (pair a b) (pair x' y'))) refl x y

abstract
  is-contr-total-space-IND-identity-system :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    IND-identity-system (i ⊔ j) B a b → is-contr (Σ A B)
  is-contr-total-space-IND-identity-system a b ind =
    pair
      ( pair a b)
      ( contraction-total-space-IND-identity-system a b ind)

abstract
  fundamental-theorem-id-IND-identity-system :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    IND-identity-system (i ⊔ j) B a b →
    (f : (x : A) → Id a x → B x) → (x : A) → is-equiv (f x)
  fundamental-theorem-id-IND-identity-system a b ind f =
    fundamental-theorem-id a b (is-contr-total-space-IND-identity-system a b ind) f

--------------------------------------------------------------------------------

-- Section 7.4 Disjointness of coproducts

-- Raising universe levels

data raise (l : Level) {l1 : Level} (A : UU l1) : UU (l1 ⊔ l) where
  map-raise : A → raise l A

inv-map-raise :
  {l l1 : Level} {A : UU l1} → raise l A → A
inv-map-raise (map-raise x) = x

issec-inv-map-raise :
  {l l1 : Level} {A : UU l1} (x : raise l A) →
  Id (map-raise (inv-map-raise x)) x
issec-inv-map-raise (map-raise x) = refl

isretr-inv-map-raise :
  {l l1 : Level} {A : UU l1} (x : A) →
  Id (inv-map-raise {l} (map-raise x)) x
isretr-inv-map-raise x = refl

is-equiv-map-raise :
  (l : Level) {l1 : Level} (A : UU l1) → is-equiv (map-raise {l} {l1} {A})
is-equiv-map-raise l A =
  is-equiv-has-inverse
    inv-map-raise
    ( issec-inv-map-raise)
    ( isretr-inv-map-raise {l})

equiv-raise :
  (l : Level) {l1 : Level} (A : UU l1) → A ≃ raise l A
equiv-raise l A = pair map-raise (is-equiv-map-raise l A)

Raise :
  (l : Level) {l1 : Level} (A : UU l1) → Σ (UU (l1 ⊔ l)) (λ X → A ≃ X)
Raise l A = pair (raise l A) (equiv-raise l A)

-- Lemmas about coproducts

left-distributive-coprod-Σ-map :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2)
  (C : coprod A B → UU l3) → Σ (coprod A B) C →
  coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
left-distributive-coprod-Σ-map A B C (pair (inl x) z) = inl (pair x z)
left-distributive-coprod-Σ-map A B C (pair (inr y) z) = inr (pair y z)

inv-left-distributive-coprod-Σ-map :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2)
  (C : coprod A B → UU l3) →
  coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y))) → Σ (coprod A B) C
inv-left-distributive-coprod-Σ-map A B C (inl (pair x z)) = pair (inl x) z
inv-left-distributive-coprod-Σ-map A B C (inr (pair y z)) = pair (inr y) z

issec-inv-left-distributive-coprod-Σ-map :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  ( (left-distributive-coprod-Σ-map A B C) ∘
    (inv-left-distributive-coprod-Σ-map A B C)) ~ id
issec-inv-left-distributive-coprod-Σ-map A B C (inl (pair x z)) = refl
issec-inv-left-distributive-coprod-Σ-map A B C (inr (pair y z)) = refl

isretr-inv-left-distributive-coprod-Σ-map :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  ( (inv-left-distributive-coprod-Σ-map A B C) ∘
    (left-distributive-coprod-Σ-map A B C)) ~ id
isretr-inv-left-distributive-coprod-Σ-map A B C (pair (inl x) z) = refl
isretr-inv-left-distributive-coprod-Σ-map A B C (pair (inr y) z) = refl

abstract
  is-equiv-left-distributive-coprod-Σ-map :
    {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
    is-equiv (left-distributive-coprod-Σ-map A B C)
  is-equiv-left-distributive-coprod-Σ-map A B C =
    is-equiv-has-inverse
      ( inv-left-distributive-coprod-Σ-map A B C)
      ( issec-inv-left-distributive-coprod-Σ-map A B C)
      ( isretr-inv-left-distributive-coprod-Σ-map A B C)

equiv-left-distributive-coprod-Σ :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  Σ (coprod A B) C ≃ coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
equiv-left-distributive-coprod-Σ A B C =
  pair ( left-distributive-coprod-Σ-map A B C)
       ( is-equiv-left-distributive-coprod-Σ-map A B C)

abstract
  is-equiv-map-to-empty :
    {l : Level} {A : UU l} (f : A → empty) → is-equiv f
  is-equiv-map-to-empty f =
    is-equiv-has-inverse
      ind-empty
      ind-empty
      ( λ x → ind-empty {P = λ t → Id (ind-empty (f x)) x} (f x))

map-Σ-empty-fam :
  {l : Level} (A : UU l) → Σ A (λ x → empty) → empty
map-Σ-empty-fam A (pair x ()) 

abstract
  is-equiv-map-Σ-empty-fam :
    {l : Level} (A : UU l) → is-equiv (map-Σ-empty-fam A)
  is-equiv-map-Σ-empty-fam A = is-equiv-map-to-empty (map-Σ-empty-fam A)

equiv-Σ-empty-fam :
  {l : Level} (A : UU l) → Σ A (λ x → empty) ≃ empty
equiv-Σ-empty-fam A =
  pair (map-Σ-empty-fam A) (is-equiv-map-Σ-empty-fam A)

-- The identity types of coproducts

Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  coprod A B → coprod A B → UU (l1 ⊔ l2)
Eq-coprod {l1} {l2} A B (inl x) (inl y) = raise (l1 ⊔ l2) (Id x y)
Eq-coprod {l1} {l2} A B (inl x) (inr y) = raise (l1 ⊔ l2) empty
Eq-coprod {l1} {l2} A B (inr x) (inl y) = raise (l1 ⊔ l2) empty
Eq-coprod {l1} {l2} A B (inr x) (inr y) = raise (l1 ⊔ l2) (Id x y)

reflexive-Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (t : coprod A B) → Eq-coprod A B t t
reflexive-Eq-coprod {l1} {l2} A B (inl x) = map-raise refl
reflexive-Eq-coprod {l1} {l2} A B (inr x) = map-raise refl

Eq-coprod-eq :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (s t : coprod A B) → Id s t → Eq-coprod A B s t
Eq-coprod-eq A B s .s refl = reflexive-Eq-coprod A B s

abstract
  is-contr-total-Eq-coprod-inl :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : A) →
    is-contr (Σ (coprod A B) (Eq-coprod A B (inl x)))
  is-contr-total-Eq-coprod-inl A B x =
    is-contr-equiv
      ( coprod
        ( Σ A (λ y → Eq-coprod A B (inl x) (inl y)))
        ( Σ B (λ y → Eq-coprod A B (inl x) (inr y))))
      ( equiv-left-distributive-coprod-Σ A B (Eq-coprod A B (inl x)))
      ( is-contr-equiv'
        ( coprod
          ( Σ A (Id x))
          ( Σ B (λ y → empty)))
        ( equiv-functor-coprod
          ( equiv-tot (λ y → equiv-raise _ (Id x y)))
          ( equiv-tot (λ y → equiv-raise _ empty)))
        ( is-contr-equiv
          ( coprod (Σ A (Id x)) empty)
          ( equiv-functor-coprod
            ( equiv-id (Σ A (Id x)))
            ( equiv-Σ-empty-fam B))
          ( is-contr-equiv'
            ( Σ A (Id x))
            ( right-unit-law-coprod (Σ A (Id x)))
            ( is-contr-total-path x))))

abstract
  is-contr-total-Eq-coprod-inr :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : B) →
    is-contr (Σ (coprod A B) (Eq-coprod A B (inr x)))
  is-contr-total-Eq-coprod-inr A B x =
    is-contr-equiv
      ( coprod
        ( Σ A (λ y → Eq-coprod A B (inr x) (inl y)))
        ( Σ B (λ y → Eq-coprod A B (inr x) (inr y))))
      ( equiv-left-distributive-coprod-Σ A B (Eq-coprod A B (inr x)))
      ( is-contr-equiv'
        ( coprod (Σ A (λ y → empty)) (Σ B (Id x)))
        ( equiv-functor-coprod
          ( equiv-tot (λ y → equiv-raise _ empty))
          ( equiv-tot (λ y → equiv-raise _ (Id x y))))
        ( is-contr-equiv
          ( coprod empty (Σ B (Id x)))
          ( equiv-functor-coprod
            ( equiv-Σ-empty-fam A)
            ( equiv-id (Σ B (Id x))))
          ( is-contr-equiv'
            ( Σ B (Id x))
            ( left-unit-law-coprod (Σ B (Id x)))
            ( is-contr-total-path x))))

abstract
  is-equiv-Eq-coprod-eq-inl :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : A) →
    is-fiberwise-equiv (Eq-coprod-eq A B (inl x))
  is-equiv-Eq-coprod-eq-inl A B x =
    fundamental-theorem-id
      ( inl x)
      ( reflexive-Eq-coprod A B (inl x))
      ( is-contr-total-Eq-coprod-inl A B x)
      ( Eq-coprod-eq A B (inl x))

abstract
  is-equiv-Eq-coprod-eq-inr :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : B) →
    is-fiberwise-equiv (Eq-coprod-eq A B (inr x))
  is-equiv-Eq-coprod-eq-inr A B x =
    fundamental-theorem-id
      ( inr x)
      ( reflexive-Eq-coprod A B (inr x))
      ( is-contr-total-Eq-coprod-inr A B x)
      ( Eq-coprod-eq A B (inr x))

abstract
  is-equiv-Eq-coprod-eq :
    {l1 l2 : Level} (A : UU l1) (B : UU l2)
    (s : coprod A B) → is-fiberwise-equiv (Eq-coprod-eq A B s)
  is-equiv-Eq-coprod-eq A B (inl x) = is-equiv-Eq-coprod-eq-inl A B x
  is-equiv-Eq-coprod-eq A B (inr x) = is-equiv-Eq-coprod-eq-inr A B x

map-compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → Id (inl {B = B} x) (inl {B = B} x') → Id x x'
map-compute-eq-coprod-inl-inl x x' =
  ( inv-is-equiv (is-equiv-map-raise _ (Id x x'))) ∘
    ( Eq-coprod-eq _ _ (inl x) (inl x')) 

abstract
  is-equiv-map-compute-eq-coprod-inl-inl :
    {l1 l2 : Level} {A : UU l1} {B : UU l2}
    (x x' : A) → is-equiv (map-compute-eq-coprod-inl-inl {B = B} x x')
  is-equiv-map-compute-eq-coprod-inl-inl x x' =
    is-equiv-comp
      ( map-compute-eq-coprod-inl-inl x x')
      ( inv-is-equiv (is-equiv-map-raise _ (Id x x')))
      ( Eq-coprod-eq _ _ (inl x) (inl x'))
      ( refl-htpy)
      ( is-equiv-Eq-coprod-eq _ _ (inl x) (inl x'))
      ( is-equiv-inv-is-equiv (is-equiv-map-raise _ (Id x x')))

compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → (Id (inl {B = B} x) (inl x')) ≃ (Id x x')
compute-eq-coprod-inl-inl x x' =
  pair
    ( map-compute-eq-coprod-inl-inl x x')
    ( is-equiv-map-compute-eq-coprod-inl-inl x x')

map-compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → Id (inl x) (inr y') → empty
map-compute-eq-coprod-inl-inr x y' =
  ( inv-is-equiv (is-equiv-map-raise _ empty)) ∘
    ( Eq-coprod-eq _ _ (inl x) (inr y'))

abstract
  is-equiv-map-compute-eq-coprod-inl-inr :
    {l1 l2 : Level} {A : UU l1} {B : UU l2}
    (x : A) (y' : B) → is-equiv (map-compute-eq-coprod-inl-inr x y')
  is-equiv-map-compute-eq-coprod-inl-inr x y' =
    is-equiv-comp
      ( map-compute-eq-coprod-inl-inr x y')
      ( inv-is-equiv (is-equiv-map-raise _ empty))
      ( Eq-coprod-eq _ _ (inl x) (inr y'))
      ( refl-htpy)
      ( is-equiv-Eq-coprod-eq _ _ (inl x) (inr y'))
      ( is-equiv-inv-is-equiv (is-equiv-map-raise _ empty))
  
compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → (Id (inl x) (inr y')) ≃ empty
compute-eq-coprod-inl-inr x y' =
  pair
    ( map-compute-eq-coprod-inl-inr x y')
    ( is-equiv-map-compute-eq-coprod-inl-inr x y')

map-compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → (Id (inr {A = A} y) (inl x')) → empty
map-compute-eq-coprod-inr-inl y x' =
   ( inv-is-equiv (is-equiv-map-raise _ empty)) ∘
     ( Eq-coprod-eq _ _ (inr y) (inl x'))

abstract
  is-equiv-map-compute-eq-coprod-inr-inl :
    {l1 l2 : Level} {A : UU l1} {B : UU l2}
    (y : B) (x' : A) → is-equiv (map-compute-eq-coprod-inr-inl y x')
  is-equiv-map-compute-eq-coprod-inr-inl y x' =
    is-equiv-comp
      ( map-compute-eq-coprod-inr-inl y x')
      ( inv-is-equiv (is-equiv-map-raise _ empty))
      ( Eq-coprod-eq _ _ (inr y) (inl x'))
      ( refl-htpy)
      ( is-equiv-Eq-coprod-eq _ _ (inr y) (inl x'))
      ( is-equiv-inv-is-equiv (is-equiv-map-raise _ empty))

compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → (Id (inr y) (inl x')) ≃ empty
compute-eq-coprod-inr-inl y x' =
  pair
    ( map-compute-eq-coprod-inr-inl y x')
    ( is-equiv-map-compute-eq-coprod-inr-inl y x')

map-compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → (Id (inr {A = A} y) (inr y')) → Id y y'
map-compute-eq-coprod-inr-inr y y' =
  ( inv-is-equiv (is-equiv-map-raise _ (Id y y'))) ∘
    ( Eq-coprod-eq _ _ (inr y) (inr y'))

abstract
  is-equiv-map-compute-eq-coprod-inr-inr :
    {l1 l2 : Level} {A : UU l1} {B : UU l2}
    (y y' : B) → is-equiv (map-compute-eq-coprod-inr-inr {A = A} y y')
  is-equiv-map-compute-eq-coprod-inr-inr y y' =
    is-equiv-comp
      ( map-compute-eq-coprod-inr-inr y y')
      ( inv-is-equiv (is-equiv-map-raise _ (Id y y')))
      ( Eq-coprod-eq _ _ (inr y) (inr y'))
      ( refl-htpy)
      ( is-equiv-Eq-coprod-eq _ _ (inr y) (inr y'))
      ( is-equiv-inv-is-equiv (is-equiv-map-raise _ (Id y y')))

compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → (Id (inr {A = A} y) (inr y')) ≃ (Id y y')
compute-eq-coprod-inr-inr y y' =
  pair
    ( map-compute-eq-coprod-inr-inr y y')
    ( is-equiv-map-compute-eq-coprod-inr-inr y y')

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 7.1

abstract
  is-emb-empty :
    {i : Level} (A : UU i) → is-emb (ind-empty {P = λ x → A})
  is-emb-empty A = ind-empty

-- Exercise 7.2

path-adjointness-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) (x : A) (y : B) →
  (Id (map-equiv e x) y) ≃ (Id x (inv-map-equiv e y))
path-adjointness-equiv e x y =
  ( inv-equiv (equiv-ap e x (inv-map-equiv e y))) ∘e
  ( equiv-concat'
    ( map-equiv e x)
    ( inv (issec-inv-is-equiv (is-equiv-map-equiv e) y)))

-- Exercise 7.3

abstract
  is-equiv-top-is-equiv-left-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
    is-equiv i → is-equiv f → is-equiv g → is-equiv h
  is-equiv-top-is-equiv-left-square f g h i H Ei Ef Eg =
    is-equiv-right-factor (i ∘ f) g h H Eg
      ( is-equiv-comp (i ∘ f) i f refl-htpy Ef Ei)

abstract
  is-emb-htpy :
    {i j : Level} {A : UU i} {B : UU j} (f g : A → B) → (f ~ g) →
    is-emb g → is-emb f
  is-emb-htpy f g H is-emb-g x y =
    is-equiv-top-is-equiv-left-square
      ( ap g)
      ( concat' (f x) (H y))
      ( ap f)
      ( concat (H x) (g y))
      ( htpy-nat H)
      ( is-equiv-concat (H x) (g y))
      ( is-emb-g x y)
      ( is-equiv-concat' (f x) (H y))

abstract
  is-emb-htpy' :
    {i j : Level} {A : UU i} {B : UU j} (f g : A → B) → (f ~ g) →
    is-emb f → is-emb g
  is-emb-htpy' f g H is-emb-f =
    is-emb-htpy g f (htpy-inv H) is-emb-f

-- Exercise 7.4

abstract
  is-emb-comp :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
    is-emb h → is-emb f
  is-emb-comp f g h H is-emb-g is-emb-h =
    is-emb-htpy f (g ∘ h) H
      ( λ x y → is-equiv-comp (ap (g ∘ h)) (ap g) (ap h) (ap-comp g h)
        ( is-emb-h x y)
        ( is-emb-g (h x) (h y)))

abstract
  is-emb-comp' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (g : B → X) (h : A → B) → is-emb g → is-emb h → is-emb (g ∘ h)
  is-emb-comp' g h = is-emb-comp (g ∘ h) g h refl-htpy

abstract
  is-emb-right-factor :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
    is-emb f → is-emb h
  is-emb-right-factor f g h H is-emb-g is-emb-f x y =
    is-equiv-right-factor
      ( ap (g ∘ h))
      ( ap g)
      ( ap h)
      ( ap-comp g h)
      ( is-emb-g (h x) (h y))
      ( is-emb-htpy (g ∘ h) f (htpy-inv H) is-emb-f x y)

abstract
  is-emb-triangle-is-equiv :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (e : A → B) (H : f ~ (g ∘ e)) →
    is-equiv e → is-emb g → is-emb f
  is-emb-triangle-is-equiv f g e H is-equiv-e is-emb-g =
    is-emb-comp f g e H is-emb-g (is-emb-is-equiv e is-equiv-e)

abstract
  is-emb-triangle-is-equiv' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (e : A → B) (H : f ~ (g ∘ e)) →
    is-equiv e → is-emb f → is-emb g
  is-emb-triangle-is-equiv' f g e H is-equiv-e is-emb-f =
    is-emb-triangle-is-equiv g f
      ( inv-is-equiv is-equiv-e)
      ( triangle-section f g e H
        ( pair
          ( inv-is-equiv is-equiv-e)
          ( issec-inv-is-equiv is-equiv-e)))
      ( is-equiv-inv-is-equiv is-equiv-e)
      ( is-emb-f)

-- Exercise 7.5

abstract
  is-emb-inl :
    {i j : Level} (A : UU i) (B : UU j) → is-emb (inl {A = A} {B = B})
  is-emb-inl A B x =
    fundamental-theorem-id x refl
      ( is-contr-is-equiv
        ( Σ A (λ y → Eq-coprod A B (inl x) (inl y)))
        ( tot (λ y → Eq-coprod-eq A B (inl x) (inl y)))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ y → is-equiv-Eq-coprod-eq A B (inl x) (inl y)))
        ( is-contr-equiv'
          ( Σ A (Id x))
          ( equiv-tot (λ y → equiv-raise _ (Id x y)))
          ( is-contr-total-path x)))
      ( λ y → ap inl)

abstract
  is-emb-inr :
    {i j : Level} (A : UU i) (B : UU j) → is-emb (inr {A = A} {B = B})
  is-emb-inr A B x =
    fundamental-theorem-id x refl
      ( is-contr-is-equiv
        ( Σ B (λ y → Eq-coprod A B (inr x) (inr y)))
        ( tot (λ y → Eq-coprod-eq A B (inr x) (inr y)))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ y → is-equiv-Eq-coprod-eq A B (inr x) (inr y)))
        ( is-contr-equiv'
          ( Σ B (Id x))
          ( equiv-tot (λ y → equiv-raise _ (Id x y)))
          ( is-contr-total-path x)))
      ( λ y → ap inr)

-- Exercise 7.6

-- Exercise 7.7

tot-htpy :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k}
  {f g : (x : A) → B x → C x} → (H : (x : A) → f x ~ g x) → tot f ~ tot g
tot-htpy H (pair x y) = eq-pair refl (H x y)

tot-id :
  {i j : Level} {A : UU i} (B : A → UU j) →
  (tot (λ x (y : B x) → y)) ~ id
tot-id B (pair x y) = refl

tot-comp :
  {i j j' j'' : Level}
  {A : UU i} {B : A → UU j} {B' : A → UU j'} {B'' : A → UU j''}
  (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  tot (λ x → (g x) ∘ (f x)) ~ ((tot g) ∘ (tot f))
tot-comp f g (pair x y) = refl

-- Exercise 7.8

abstract
  fundamental-theorem-id-retr :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A) →
    (i : (x : A) → B x → Id a x) → (R : (x : A) → retr (i x)) →
    is-fiberwise-equiv i
  fundamental-theorem-id-retr {_} {_} {A} {B} a i R =
    is-fiberwise-equiv-is-equiv-tot i
      ( is-equiv-is-contr (tot i)
        ( is-contr-retract-of (Σ _ (λ y → Id a y))
          ( pair (tot i)
            ( pair (tot λ x → pr1 (R x))
              ( ( htpy-inv (tot-comp i (λ x → pr1 (R x)))) ∙h
                ( ( tot-htpy λ x → pr2 (R x)) ∙h (tot-id B)))))
          ( is-contr-total-path a))
        ( is-contr-total-path a))

abstract
  is-equiv-sec-is-equiv :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) (sec-f : sec f) →
    is-equiv (pr1 sec-f) → is-equiv f
  is-equiv-sec-is-equiv {A = A} {B = B} f (pair g issec-g) is-equiv-sec-f =
    let h : A → B
        h = inv-is-equiv is-equiv-sec-f
    in
    is-equiv-htpy h
      ( ( htpy-left-whisk f (htpy-inv (issec-inv-is-equiv is-equiv-sec-f))) ∙h
        ( htpy-right-whisk issec-g h))
      ( is-equiv-inv-is-equiv is-equiv-sec-f)

abstract
  fundamental-theorem-id-sec :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A)
    (f : (x : A) → Id a x → B x) → ((x : A) → sec (f x)) →
    is-fiberwise-equiv f
  fundamental-theorem-id-sec {A = A} {B = B} a f sec-f x =
    let i : (x : A) → B x → Id a x
        i = λ x → pr1 (sec-f x)
        retr-i : (x : A) → retr (i x)
        retr-i = λ x → pair (f x) (pr2 (sec-f x))
        is-fiberwise-equiv-i : is-fiberwise-equiv i
        is-fiberwise-equiv-i = fundamental-theorem-id-retr a i retr-i
    in is-equiv-sec-is-equiv (f x) (sec-f x) (is-fiberwise-equiv-i x)

-- Exercise 7.9

abstract
  is-emb-sec-ap :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
    ((x y : A) → sec (ap f {x = x} {y = y})) → is-emb f
  is-emb-sec-ap f sec-ap-f x =
    fundamental-theorem-id-sec x (λ y → ap f {y = y}) (sec-ap-f x)

-- Exercise 7.10

coherence-is-half-adjoint-equivalence :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  (G : (f ∘ g) ~ id) (H : (g ∘ f) ~ id) → UU (l1 ⊔ l2)
coherence-is-half-adjoint-equivalence f g G H =
  ( htpy-right-whisk G f) ~ (htpy-left-whisk f H)

is-half-adjoint-equivalence :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-half-adjoint-equivalence {A = A} {B = B} f =
  Σ (B → A)
    ( λ g → Σ ((f ∘ g) ~ id)
      ( λ G → Σ ((g ∘ f) ~ id) (coherence-is-half-adjoint-equivalence f g G)))

is-path-split :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-path-split {A = A} {B = B} f =
  sec f × ((x y : A) → sec (ap f {x = x} {y = y}))

abstract
  is-path-split-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv f → is-path-split f
  is-path-split-is-equiv f is-equiv-f =
    pair (pr1 is-equiv-f) (λ x y → pr1 (is-emb-is-equiv f is-equiv-f x y))

abstract
  is-half-adjoint-equivalence-is-path-split :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-path-split f → is-half-adjoint-equivalence f
  is-half-adjoint-equivalence-is-path-split {A = A} {B = B} f
    ( pair (pair g issec-g) sec-ap-f) =
    let φ : ((x : A) → fib (ap f) (issec-g (f x))) →
                Σ ((g ∘ f) ~ id)
                ( λ H → (htpy-right-whisk issec-g f) ~ (htpy-left-whisk f H))
        φ =  ( tot (λ H' → htpy-inv)) ∘
               ( λ s → pair (λ x → pr1 (s x)) (λ x → pr2 (s x)))
    in
    pair g
      ( pair issec-g
        ( φ (λ x → pair
          ( pr1 (sec-ap-f (g (f x)) x) (issec-g (f x)))
          ( pr2 (sec-ap-f (g (f x)) x) (issec-g (f x))))))

abstract
  is-equiv-is-half-adjoint-equivalence :
    { l1 l2 : Level} {A : UU l1} {B : UU l2}
    (f : A → B) → is-half-adjoint-equivalence f → is-equiv f
  is-equiv-is-half-adjoint-equivalence f (pair g (pair G (pair H K))) =
    is-equiv-has-inverse g G H

abstract
  is-equiv-is-path-split :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-path-split f → is-equiv f
  is-equiv-is-path-split f =
    ( is-equiv-is-half-adjoint-equivalence f) ∘
    ( is-half-adjoint-equivalence-is-path-split f)

abstract
  is-half-adjoint-equivalence-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv f → is-half-adjoint-equivalence f
  is-half-adjoint-equivalence-is-equiv f =
    ( is-half-adjoint-equivalence-is-path-split f) ∘ (is-path-split-is-equiv f)

-- Exercise 7.11

abstract
  is-equiv-top-is-equiv-bottom-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
    (is-equiv f) → (is-equiv g) → (is-equiv i) → (is-equiv h)
  is-equiv-top-is-equiv-bottom-square
    f g h i H is-equiv-f is-equiv-g is-equiv-i =
    is-equiv-right-factor (i ∘ f) g h H is-equiv-g
      ( is-equiv-comp' i f is-equiv-f is-equiv-i)

abstract
  is-equiv-bottom-is-equiv-top-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
    (is-equiv f) → (is-equiv g) → (is-equiv h) → (is-equiv i)
  is-equiv-bottom-is-equiv-top-square
    f g h i H is-equiv-f is-equiv-g is-equiv-h = 
    is-equiv-left-factor' i f
      ( is-equiv-comp (i ∘ f) g h H is-equiv-h is-equiv-g) is-equiv-f

abstract
  is-equiv-left-is-equiv-right-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
    (is-equiv h) → (is-equiv i) → (is-equiv g) → (is-equiv f)
  is-equiv-left-is-equiv-right-square
    f g h i H is-equiv-h is-equiv-i is-equiv-g =
    is-equiv-right-factor' i f is-equiv-i
      ( is-equiv-comp (i ∘ f) g h H is-equiv-h is-equiv-g)

abstract
  is-equiv-right-is-equiv-left-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
    (is-equiv h) → (is-equiv i) → (is-equiv f) → (is-equiv g)
  is-equiv-right-is-equiv-left-square
    f g h i H is-equiv-h is-equiv-i is-equiv-f =
    is-equiv-left-factor (i ∘ f) g h H
      ( is-equiv-comp' i f is-equiv-f is-equiv-i)
      ( is-equiv-h)

fib-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  (x : X) → (fib f x) → (fib g x)
fib-triangle f g h H .(f a) (pair a refl) = pair (h a) (inv (H a))

square-tot-fib-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (h ∘ (Σ-fib-to-domain f)) ~
  ((Σ-fib-to-domain g) ∘ (tot (fib-triangle f g h H)))
square-tot-fib-triangle f g h H (pair .(f a) (pair a refl)) = refl

abstract
  is-fiberwise-equiv-is-equiv-triangle :
    {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    (E : is-equiv h) → is-fiberwise-equiv (fib-triangle f g h H)
  is-fiberwise-equiv-is-equiv-triangle f g h H E =
    is-fiberwise-equiv-is-equiv-tot
      ( fib-triangle f g h H)
      ( is-equiv-top-is-equiv-bottom-square
        ( Σ-fib-to-domain f)
        ( Σ-fib-to-domain g)
        ( tot (fib-triangle f g h H))
        ( h)
        ( square-tot-fib-triangle f g h H)
        ( is-equiv-Σ-fib-to-domain f)
        ( is-equiv-Σ-fib-to-domain g)
        ( E))

abstract
  is-equiv-triangle-is-fiberwise-equiv :
    {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    (E : is-fiberwise-equiv (fib-triangle f g h H)) → is-equiv h
  is-equiv-triangle-is-fiberwise-equiv f g h H E =
    is-equiv-bottom-is-equiv-top-square
      ( Σ-fib-to-domain f)
      ( Σ-fib-to-domain g)
      ( tot (fib-triangle f g h H))
      ( h)
      ( square-tot-fib-triangle f g h H)
      ( is-equiv-Σ-fib-to-domain f)
      ( is-equiv-Σ-fib-to-domain g)
      ( is-equiv-tot-is-fiberwise-equiv E)

-- Extra material

{- In order to show that the total space of htpy-cone is contractible, we give
   a general construction that helps us characterize the identity type of
   a structure. This construction is called 

   is-contr-total-Eq-structure.

   We first give some definitions that help us with the construction of
   is-contr-total-Eq-structure. -}

swap-total-Eq-structure :
  {l1 l2 l3 l4 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
  (D : (x : A) → B x → C x → UU l4) →
  Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) →
  Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
swap-total-Eq-structure B C D (pair (pair a b) (pair c d)) =
  pair (pair a c) (pair b d)

htpy-swap-total-Eq-structure :
  {l1 l2 l3 l4 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
  (D : (x : A) → B x → C x → UU l4) →
  ( ( swap-total-Eq-structure B C D) ∘
    ( swap-total-Eq-structure C B (λ x z y → D x y z))) ~ id
htpy-swap-total-Eq-structure B C D (pair (pair a b) (pair c d)) = refl

abstract
  is-equiv-swap-total-Eq-structure :
    {l1 l2 l3 l4 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
    (D : (x : A) → B x → C x → UU l4) →
    is-equiv (swap-total-Eq-structure B C D)
  is-equiv-swap-total-Eq-structure B C D =
    is-equiv-has-inverse
      ( swap-total-Eq-structure C B (λ x z y → D x y z))
      ( htpy-swap-total-Eq-structure B C D)
      ( htpy-swap-total-Eq-structure C B (λ x z y → D x y z))

abstract
  is-contr-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-contr A → ((x : A) → is-contr (B x)) → is-contr (Σ A B)
  is-contr-Σ {A = A} {B = B} is-contr-A is-contr-B =
    is-contr-equiv'
      ( B (center is-contr-A))
      ( left-unit-law-Σ B is-contr-A)
      ( is-contr-B (center is-contr-A))

abstract
  is-contr-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-contr A → (a : A) → is-contr (B a) → is-contr (Σ A B)
  is-contr-Σ' {A = A} {B} is-contr-A a is-contr-B =
    is-contr-is-equiv'
      ( B a)
      ( left-unit-law-Σ-map-gen B is-contr-A a)
      ( is-equiv-left-unit-law-Σ-map-gen B is-contr-A a)
      ( is-contr-B)

abstract
  is-contr-total-Eq-structure :
    { l1 l2 l3 l4 : Level} { A : UU l1} {B : A → UU l2} {C : A → UU l3}
    ( D : (x : A) → B x → C x → UU l4) →
    ( is-contr-AC : is-contr (Σ A C)) →
    ( t : Σ A C) →
    is-contr (Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
    is-contr (Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))))
  is-contr-total-Eq-structure
    {A = A} {B = B} {C = C} D is-contr-AC t is-contr-BD =
    is-contr-is-equiv
      ( Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))))
      ( swap-total-Eq-structure B C D)
      ( is-equiv-swap-total-Eq-structure B C D)
      ( is-contr-Σ' is-contr-AC t is-contr-BD)

-- Characterizing the identity type of a fiber as the fiber of the action on
-- paths

fib-ap-eq-fib-fiberwise :
  {i j : Level} {A : UU i} {B : UU j}
  (f : A → B) {b : B} (s t : fib f b) (p : Id (pr1 s) (pr1 t)) →
  (Id (tr (λ (a : A) → Id (f a) b) p (pr2 s)) (pr2 t)) →
  (Id (ap f p) ((pr2 s) ∙ (inv (pr2 t))))
fib-ap-eq-fib-fiberwise f (pair .x' p) (pair x' refl) refl =
  inv ∘ (concat right-unit refl)

abstract
  is-fiberwise-equiv-fib-ap-eq-fib-fiberwise :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) {b : B} (s t : fib f b) →
    is-fiberwise-equiv (fib-ap-eq-fib-fiberwise f s t)
  is-fiberwise-equiv-fib-ap-eq-fib-fiberwise
    f (pair x y) (pair .x refl) refl =
    is-equiv-comp
      ( fib-ap-eq-fib-fiberwise f (pair x y) (pair x refl) refl)
      ( inv)
      ( concat right-unit refl)
      ( refl-htpy)
      ( is-equiv-concat right-unit refl)
      ( is-equiv-inv (y ∙ refl) refl)

fib-ap-eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {b : B}
  (s t : fib f b) → Id s t →
  fib (ap f {x = pr1 s} {y = pr1 t}) ((pr2 s) ∙ (inv (pr2 t)))
fib-ap-eq-fib f s .s refl = pair refl (inv (right-inv (pr2 s)))

triangle-fib-ap-eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B)
  {b : B} (s t : fib f b) →
  (fib-ap-eq-fib f s t) ~ ((tot (fib-ap-eq-fib-fiberwise f s t)) ∘ (pair-eq {s = s} {t}))
triangle-fib-ap-eq-fib f (pair x refl) .(pair x refl) refl = refl

abstract
  is-equiv-fib-ap-eq-fib :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) {b : B}
    (s t : fib f b) → is-equiv (fib-ap-eq-fib f s t)
  is-equiv-fib-ap-eq-fib f s t =
    is-equiv-comp
      ( fib-ap-eq-fib f s t)
      ( tot (fib-ap-eq-fib-fiberwise f s t))
      ( pair-eq {s = s} {t})
      ( triangle-fib-ap-eq-fib f s t)
      ( is-equiv-pair-eq s t)
      ( is-equiv-tot-is-fiberwise-equiv
        ( is-fiberwise-equiv-fib-ap-eq-fib-fiberwise f s t))

eq-fib-fib-ap :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (x y : A)
  (q : Id (f x) (f y)) →
  Id (pair x q) (pair y (refl {x = f y})) → fib (ap f {x = x} {y = y}) q
eq-fib-fib-ap f x y q = (tr (fib (ap f)) right-unit) ∘ (fib-ap-eq-fib f (pair x q) (pair y refl))

abstract
  is-equiv-eq-fib-fib-ap :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) (x y : A)
    (q : Id (f x) (f y)) → is-equiv (eq-fib-fib-ap f x y q)
  is-equiv-eq-fib-fib-ap f x y q =
    is-equiv-comp
      ( eq-fib-fib-ap f x y q)
      ( tr (fib (ap f)) right-unit)
      ( fib-ap-eq-fib f (pair x q) (pair y refl))
      ( refl-htpy)
      ( is-equiv-fib-ap-eq-fib f (pair x q) (pair y refl))
      ( is-equiv-tr (fib (ap f)) right-unit)

-- Comparing fib and fib'

fib'-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  fib f y → fib' f y
fib'-fib f y t = tot (λ x → inv) t

abstract
  is-equiv-fib'-fib :
    {i j : Level} {A : UU i} {B : UU j}
    (f : A → B) → is-fiberwise-equiv (fib'-fib f)
  is-equiv-fib'-fib f y =
    is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-inv (f x) y)

{-
-- Equivalent finite sets have the same cardinality

skip-Fin :
  {n : ℕ} → Fin (succ-ℕ n) → Fin n → Fin (succ-ℕ n)
skip-Fin {succ-ℕ n} (inl x) (inl y) = inl (skip-Fin x y)
skip-Fin {succ-ℕ n} (inl x) (inr y) = inr star
skip-Fin {succ-ℕ n} (inr x) y = inl y

swap-top-two-Fin :
  {n : ℕ} → Fin (succ-ℕ (succ-ℕ n)) → Fin (succ-ℕ (succ-ℕ n))
swap-top-two-Fin (inl (inl x)) = inl (inl x)
swap-top-two-Fin (inl (inr star)) = inr star
swap-top-two-Fin (inr star) = inl (inr star)

idempotent-top-two-Fin :
  {n : ℕ} (x : Fin (succ-ℕ (succ-ℕ n))) →
  Id (swap-top-two-Fin (swap-top-two-Fin x)) x
idempotent-top-two-Fin (inl (inl x)) = refl
idempotent-top-two-Fin (inl (inr star)) = refl
idempotent-top-two-Fin (inr star) = refl

is-equiv-swap-top-two-Fin :
  {n : ℕ} → is-equiv (swap-top-two-Fin {n})
is-equiv-swap-top-two-Fin =
  is-equiv-has-inverse
    swap-top-two-Fin
    idempotent-top-two-Fin
    idempotent-top-two-Fin

{-
swap-top-Fin :
  {n : ℕ} → Fin (succ-ℕ n) → Fin (succ-ℕ n) → Fin (succ-ℕ n)
swap-top-Fin {zero-ℕ} x y = x
swap-top-Fin {succ-ℕ n} (inl (inl x)) (inl (inl y)) = swap-top-two-Fin (inl (swap-top-Fin (inl x) (inl y)))
swap-top-Fin {succ-ℕ n} (inl (inr x)) (inl (inl y)) = inl (inl y)
swap-top-Fin {succ-ℕ n} (inl (inl x)) (inl (inr star)) = inl (inr star)
swap-top-Fin {succ-ℕ n} (inl (inr x)) (inl (inr star)) = inr star
swap-top-Fin {succ-ℕ n} (inl x) (inr y) = inl x
swap-top-Fin {succ-ℕ n} (inr x) y = y

idempotent-swap-top-Fin :
  {n : ℕ} (x : Fin (succ-ℕ n)) →
  ((swap-top-Fin x) ∘ (swap-top-Fin x)) ~ id
idempotent-swap-top-Fin {zero-ℕ} (inr star) (inr star) = refl
idempotent-swap-top-Fin {succ-ℕ n} (inl x) (inl y) = {!!}
idempotent-swap-top-Fin {succ-ℕ n} (inl (inl x)) (inr star) = {!!}
idempotent-swap-top-Fin {succ-ℕ n} (inl (inr star)) (inr star) = refl
idempotent-swap-top-Fin {succ-ℕ n} (inr x) (inl y) = refl
idempotent-swap-top-Fin {succ-ℕ n} (inr x) (inr y) = refl

eq-ℕ-equiv-Fin :
  {m n : ℕ} → (Fin m ≃ Fin n) → Id m n
eq-ℕ-equiv-Fin {zero-ℕ} {zero-ℕ} e = refl
eq-ℕ-equiv-Fin {zero-ℕ} {succ-ℕ n} e = ind-empty (inv-map-equiv e (inr star))
eq-ℕ-equiv-Fin {succ-ℕ m} {zero-ℕ} e = ind-empty (map-equiv e (inr star))
eq-ℕ-equiv-Fin {succ-ℕ m} {succ-ℕ n} e = {!!}
-}
-}
