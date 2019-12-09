{-# OPTIONS --without-K #-}

module combinatorial-objects where

import 12-univalence
open 12-univalence public

{- The type ℍ of hereditarily finite types is introduces as an inductive type.

   Note that this is the type of 'planar' combinatorial objects, because Fin n
   is a linearly ordered finite set with n elements.

   For a non-planar type of hereditarily finite types, we need to use the type
   𝔽, which is the image of (Fin : ℕ → UU lzero). This latter type probably has
   the correct identity type, and is more interesting from the perspective of
   homotopy type theory.

   Planar hereditarily finite types are easier to handle though, so we study
   them first.
   -}
   
data ℍ : UU lzero where
  join-ℍ : (n : ℕ) → (Fin n → ℍ) → ℍ

width-ℍ : ℍ → ℕ
width-ℍ (join-ℍ n x) = n

branch-ℍ : (x : ℍ) → (Fin (width-ℍ x) → ℍ)
branch-ℍ (join-ℍ n x) = x

empty-ℍ : ℍ
empty-ℍ = join-ℍ zero-ℕ ind-empty

Fin-ℍ : ℕ → ℍ
Fin-ℍ n = join-ℍ n (const (Fin n) ℍ empty-ℍ) 

unit-ℍ : ℍ
unit-ℍ = Fin-ℍ one-ℕ

{- Logical morphisms of hereditarily finite types. -}

hom-ℍ : ℍ → ℍ → UU lzero
hom-ℍ (join-ℍ m x) (join-ℍ n y) =
  Σ (Fin m → Fin n) (λ h → (i : Fin m) → hom-ℍ (x i) (y (h i)))

map-base-hom-ℍ : (x y : ℍ) (f : hom-ℍ x y) →
  Fin (width-ℍ x) → Fin (width-ℍ y)
map-base-hom-ℍ (join-ℍ m x) (join-ℍ n y) = pr1

hom-branch-hom-ℍ : (x y : ℍ) (f : hom-ℍ x y) (i : Fin (width-ℍ x)) →
  hom-ℍ (branch-ℍ x i) (branch-ℍ y (map-base-hom-ℍ x y f i))
hom-branch-hom-ℍ (join-ℍ m x) (join-ℍ n y) = pr2

htpy-hom-ℍ : {x y : ℍ} (f g : hom-ℍ x y) → UU lzero
htpy-hom-ℍ {join-ℍ m x} {join-ℍ n y} (pair f F) g =
  Σ ( f ~ (map-base-hom-ℍ (join-ℍ m x) (join-ℍ n y) g))
    ( λ H →
      ( i : Fin m) →
        htpy-hom-ℍ
          ( tr (λ t → hom-ℍ (x i) (y t)) (H i) (F i))
          ( hom-branch-hom-ℍ (join-ℍ m x) (join-ℍ n y) g i))

refl-htpy-hom-ℍ : {x y : ℍ} {f : hom-ℍ x y} → htpy-hom-ℍ f f
refl-htpy-hom-ℍ {join-ℍ m x} {join-ℍ n y} {pair f F} =
  pair refl-htpy (λ i → refl-htpy-hom-ℍ)

htpy-hom-ℍ-eq : {x y : ℍ} {f g : hom-ℍ x y} → (Id f g) → htpy-hom-ℍ f g
htpy-hom-ℍ-eq refl = refl-htpy-hom-ℍ

is-contr-total-htpy-hom-ℍ : {x y : ℍ} (f : hom-ℍ x y) →
  is-contr (Σ (hom-ℍ x y) (htpy-hom-ℍ f))
is-contr-total-htpy-hom-ℍ {join-ℍ m x} {join-ℍ n y} (pair f F) =
  is-contr-total-Eq-structure
    ( λ g G (H : f ~ g) →
      ( i : Fin m) →
        htpy-hom-ℍ
          ( tr (λ t → hom-ℍ (x i) (y t)) (H i) (F i))
          ( G i))
    ( is-contr-total-htpy f)
    ( pair f refl-htpy)
    ( is-contr-total-Eq-Π
      ( λ i G → htpy-hom-ℍ (F i) G)
      ( λ i → is-contr-total-htpy-hom-ℍ (F i))
      ( λ i → F i))

is-equiv-htpy-hom-ℍ-eq : {x y : ℍ} (f g : hom-ℍ x y) →
  is-equiv (htpy-hom-ℍ-eq {x} {y} {f} {g})
is-equiv-htpy-hom-ℍ-eq f =
  fundamental-theorem-id f
    ( refl-htpy-hom-ℍ)
    ( is-contr-total-htpy-hom-ℍ f)
    ( λ g → htpy-hom-ℍ-eq)

eq-htpy-hom-ℍ : {x y : ℍ} {f g : hom-ℍ x y} → htpy-hom-ℍ f g → Id f g
eq-htpy-hom-ℍ {x} {y} {f} {g} =
  inv-is-equiv (is-equiv-htpy-hom-ℍ-eq f g)

id-ℍ : {x : ℍ} → hom-ℍ x x
id-ℍ {join-ℍ n x} = pair id (λ i → id-ℍ)

comp-ℍ :
  {x y z : ℍ} (g : hom-ℍ y z) (f : hom-ℍ x y) → hom-ℍ x z
comp-ℍ {join-ℍ m x} {join-ℍ n y} {join-ℍ k z} (pair g G) (pair f F) =
  pair (g ∘ f) (λ i → comp-ℍ (G (f i)) (F i))

left-unit-law-htpy-hom-ℍ :
  {x y : ℍ} (f : hom-ℍ x y) → htpy-hom-ℍ (comp-ℍ id-ℍ f) f
left-unit-law-htpy-hom-ℍ {join-ℍ m x} {join-ℍ n y} (pair f F) =
  pair refl-htpy (λ i → left-unit-law-htpy-hom-ℍ (F i))

left-unit-law-hom-ℍ :
  {x y : ℍ} (f : hom-ℍ x y) → Id (comp-ℍ id-ℍ f) f
left-unit-law-hom-ℍ f = eq-htpy-hom-ℍ (left-unit-law-htpy-hom-ℍ f)

right-unit-law-htpy-hom-ℍ :
  {x y : ℍ} (g : hom-ℍ x y) → htpy-hom-ℍ (comp-ℍ g id-ℍ) g
right-unit-law-htpy-hom-ℍ {join-ℍ m x} {join-ℍ n y} (pair g G) =
  pair refl-htpy (λ i → right-unit-law-htpy-hom-ℍ (G i))

right-unit-law-hom-ℍ :
  {x y : ℍ} (g : hom-ℍ x y) → Id (comp-ℍ g id-ℍ) g
right-unit-law-hom-ℍ g = eq-htpy-hom-ℍ (right-unit-law-htpy-hom-ℍ g)

associative-htpy-comp-ℍ :
  {x y z w : ℍ} (h : hom-ℍ z w) (g : hom-ℍ y z) (f : hom-ℍ x y) →
  htpy-hom-ℍ (comp-ℍ (comp-ℍ h g) f) (comp-ℍ h (comp-ℍ g f))
associative-htpy-comp-ℍ
  {join-ℍ n1 x1} {join-ℍ n2 x2} {join-ℍ n3 x3} {join-ℍ n4 x4} (pair h H) (pair g G) (pair f F) =
  pair refl-htpy (λ i → associative-htpy-comp-ℍ (H (g (f i))) (G (f i)) (F i))

associative-comp-ℍ :
  {x y z w : ℍ} (h : hom-ℍ z w) (g : hom-ℍ y z) (f : hom-ℍ x y) →
  Id (comp-ℍ (comp-ℍ h g) f) (comp-ℍ h (comp-ℍ g f))
associative-comp-ℍ h g f = eq-htpy-hom-ℍ (associative-htpy-comp-ℍ h g f)

{-
{- Union of planar hereditarily finite sets -}

{-
map-add-Fin : {m n : ℕ} → Fin (add-ℕ m n) → coprod (Fin m) (Fin n)
map-add-Fin {zero-ℕ} {n} x = inr x
map-add-Fin {succ-ℕ m} {n} (inl x) = {!!}
map-add-Fin {succ-ℕ m} {n} (inr star) = ?
-}

{-
union-ℍ : ℍ → ℍ → ℍ
union-ℍ (join-ℍ n f) (join-ℍ m g) = join-ℍ (add-ℕ n m) ((ind-coprod (λ x → ℍ) f g) ∘ map-add-Fin)
-}

{- We define the Rado graph to be the graph with set of vertices ℍ, and for each   (f : Fin n → ℍ) and each (i : Fin n), an edge from (join-ℍ n f) to (f i).
   
   Note that in this definition of the Rado graph, there can be multiple edges 
   from x to y. -}

data Rado-ℍ : ℍ → ℍ → UU lzero where
  edge-Rado-ℍ : (n : ℕ) (f : Fin n → ℍ) (i : Fin n) → Rado-ℍ (join-ℍ n f) (f i)

{- Next, we define the Ackermann bijection from ℍ to ℕ. -}

finite-sum-ℕ : (n : ℕ) → (f : Fin n → ℕ) → ℕ
finite-sum-ℕ zero-ℕ f = zero-ℕ
finite-sum-ℕ (succ-ℕ n) f = add-ℕ (f (inr star)) (finite-sum-ℕ n (f ∘ inl))

map-Ackermann-ℍ : ℍ → ℕ
map-Ackermann-ℍ (join-ℍ n f) =
  finite-sum-ℕ n (λ i → pow-ℕ (succ-ℕ (succ-ℕ zero-ℕ)) (map-Ackermann-ℍ (f i)))

{- In order to construct the inverse of the Ackermann map, we need to show
   first that every natural number can be uniquely represented as a list of
   booleans. -}

ℕ-list-bool : list bool → ℕ
ℕ-list-bool nil = zero-ℕ
ℕ-list-bool (cons false l) = pow-ℕ (succ-ℕ (succ-ℕ zero-ℕ)) (ℕ-list-bool l)
ℕ-list-bool (cons true l) = succ-ℕ (pow-ℕ (succ-ℕ (succ-ℕ zero-ℕ)) (ℕ-list-bool l))

list-bool-ℕ : ℕ → list bool
list-bool-ℕ zero-ℕ = nil
list-bool-ℕ (succ-ℕ n) = {!!}

inv-Ackermann-ℍ : ℕ → ℍ
inv-Ackermann-ℍ n = {!!}
-}
