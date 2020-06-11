{-# OPTIONS --without-K --exact-split #-}

module 15-groups where

import 14-univalence
open 14-univalence public

--------------------------------------------------------------------------------

-- Section 12.3 Groups in univalent mathematics

{- We first introduce semi-groups, and then groups. We do this because the
   category of groups is a full subcategory of the category of semi-groups.
   In particular, it is a proposition for a semi-group to be a group. Therefore
   this approach gives us in a straightforward way that equality of groups is 
   equality of semi-groups. This will be useful in showing that group 
   isomorphisms are equivalent to identifications of groups. -}

has-associative-bin-op :
  {l : Level} (X : UU-Set l) → UU l
has-associative-bin-op X =
  Σ ( ( type-Set X) →
      ( ( type-Set X) → (type-Set X))) (λ μ →
    ( x y z : type-Set X) → Id (μ (μ x y) z) (μ x (μ y z)))

Semi-Group :
  (l : Level) → UU (lsuc l)
Semi-Group l = Σ (UU-Set l) has-associative-bin-op

--------------------------------------------------------------------------------

{- Bureaucracy of semi-groups. -}

set-Semi-Group :
  {l : Level} → Semi-Group l → UU-Set l
set-Semi-Group G = pr1 G

type-Semi-Group :
  {l : Level} → Semi-Group l → UU l
type-Semi-Group G = pr1 (set-Semi-Group G)

is-set-type-Semi-Group :
  {l : Level} (G : Semi-Group l) → is-set (type-Semi-Group G)
is-set-type-Semi-Group G = pr2 (set-Semi-Group G)

associative-mul-Semi-Group :
  {l : Level} (G : Semi-Group l) →
  has-associative-bin-op (set-Semi-Group G)
associative-mul-Semi-Group G = pr2 G

mul-Semi-Group :
  {l : Level} (G : Semi-Group l) →
  type-Semi-Group G →
    type-Semi-Group G → type-Semi-Group G
mul-Semi-Group G = pr1 (associative-mul-Semi-Group G)

is-associative-mul-Semi-Group :
  {l : Level} (G : Semi-Group l) (x y z : type-Semi-Group G) →
  Id ( mul-Semi-Group G (mul-Semi-Group G x y) z)
     ( mul-Semi-Group G x (mul-Semi-Group G y z))
is-associative-mul-Semi-Group G = pr2 (associative-mul-Semi-Group G)

--------------------------------------------------------------------------------

{- The property that a semi-group is a monoid is just that the semi-group 
   possesses a unit that satisfies the left and right unit laws. -}

is-unital :
  {l : Level} → Semi-Group l → UU l
is-unital G =
  Σ ( type-Semi-Group G)
    ( λ e →
      ( (y : type-Semi-Group G) → Id (mul-Semi-Group G e y) y) ×
      ( (x : type-Semi-Group G) → Id (mul-Semi-Group G x e) x))

Monoid :
  (l : Level) → UU (lsuc l)
Monoid l = Σ (Semi-Group l) is-unital

semi-group-Monoid :
  {l : Level} (M : Monoid l) → Semi-Group l
semi-group-Monoid M = pr1 M

type-Monoid :
  {l : Level} (M : Monoid l) → UU l
type-Monoid M = type-Semi-Group (semi-group-Monoid M)

is-set-type-Monoid :
  {l : Level} (M : Monoid l) → is-set (type-Monoid M)
is-set-type-Monoid M = is-set-type-Semi-Group (semi-group-Monoid M)

mul-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M → type-Monoid M → type-Monoid M
mul-Monoid M = mul-Semi-Group (semi-group-Monoid M)

is-associative-mul-Monoid :
  {l : Level} (M : Monoid l) (x y z : type-Monoid M) →
  Id (mul-Monoid M (mul-Monoid M x y) z) (mul-Monoid M x (mul-Monoid M y z))
is-associative-mul-Monoid M =
  is-associative-mul-Semi-Group (semi-group-Monoid M)

unit-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M
unit-Monoid M = pr1 (pr2 M)

left-unit-law-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  Id (mul-Monoid M (unit-Monoid M) x) x
left-unit-law-Monoid M = pr1 (pr2 (pr2 M))

right-unit-law-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  Id (mul-Monoid M x (unit-Monoid M)) x
right-unit-law-Monoid M = pr2 (pr2 (pr2 M))

--------------------------------------------------------------------------------

{- We show that is-unital is a proposition. -}

abstract
  is-prop-is-unital' :
    {l : Level} (G : Semi-Group l) → is-prop' (is-unital G)
  is-prop-is-unital' (pair (pair X is-set-X) (pair μ assoc-μ))
    (pair e (pair left-unit-e right-unit-e))
    (pair e' (pair left-unit-e' right-unit-e')) =
    eq-subtype
      ( λ e → is-prop-prod
        ( is-prop-Π (λ y → is-set-X (μ e y) y))
        ( is-prop-Π (λ x → is-set-X (μ x e) x)))
      ( (inv (left-unit-e' e)) ∙ (right-unit-e e'))

abstract
  is-prop-is-unital :
    {l : Level} (G : Semi-Group l) → is-prop (is-unital G)
  is-prop-is-unital G = is-prop-is-prop' (is-prop-is-unital' G)

--------------------------------------------------------------------------------

{- We introduce invertible elements of a monoid -}

is-invertible-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M → UU l
is-invertible-Monoid M x =
  Σ ( type-Monoid M)
    ( λ y →
      Id (mul-Monoid M y x) (unit-Monoid M) ×
      Id (mul-Monoid M x y) (unit-Monoid M))

is-prop-is-invertible-Monoid' :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  is-prop' (is-invertible-Monoid M x)
is-prop-is-invertible-Monoid' M x (pair y (pair p q)) (pair y' (pair p' q')) =
  eq-subtype
    ( ( λ z →
      is-prop-prod
        ( is-set-type-Monoid M (mul-Monoid M z x) (unit-Monoid M))
        ( is-set-type-Monoid M (mul-Monoid M x z) (unit-Monoid M))))
    ( ( inv (left-unit-law-Monoid M y)) ∙
      ( ( inv (ap (λ z → mul-Monoid M z y) p')) ∙
        ( ( is-associative-mul-Monoid M y' x y) ∙
          ( ( ap (mul-Monoid M y') q) ∙
            ( right-unit-law-Monoid M y')))))

is-prop-is-invertible-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  is-prop (is-invertible-Monoid M x)
is-prop-is-invertible-Monoid M x =
  is-prop-is-prop' (is-prop-is-invertible-Monoid' M x)

--------------------------------------------------------------------------------

{- The property that a monoid is a group is just the property that the monoid
   that every element is invertible, i.e., it comes equipped with an inverse
   operation that satisfies the left and right inverse laws. -}

is-group' :
  {l : Level} (G : Semi-Group l) → is-unital G → UU l
is-group' G is-unital-G =
  Σ ( type-Semi-Group G → type-Semi-Group G)
    ( λ i →
      ( (x : type-Semi-Group G) →
        Id (mul-Semi-Group G (i x) x) (pr1 is-unital-G)) ×
      ( (x : type-Semi-Group G) →
        Id (mul-Semi-Group G x (i x)) (pr1 is-unital-G)))

is-group :
  {l : Level} (G : Semi-Group l) → UU l
is-group G =
  Σ (is-unital G) (is-group' G)

Group :
  (l : Level) → UU (lsuc l)
Group l = Σ (Semi-Group l) is-group

--------------------------------------------------------------------------------

{- Some bureaucracy of Groups. -}

semi-group-Group :
  {l : Level} → Group l → Semi-Group l
semi-group-Group G = pr1 G

set-Group :
  {l : Level} → Group l → UU-Set l
set-Group G = pr1 (semi-group-Group G)

type-Group :
  {l : Level} → Group l → UU l
type-Group G = pr1 (set-Group G)

is-set-type-Group :
  {l : Level} (G : Group l) → is-set (type-Group G)
is-set-type-Group G = pr2 (set-Group G)

associative-mul-Group :
  {l : Level} (G : Group l) → has-associative-bin-op (set-Group G)
associative-mul-Group G = pr2 (semi-group-Group G)

mul-Group :
  {l : Level} (G : Group l) →
  type-Group G → type-Group G → type-Group G
mul-Group G = pr1 (associative-mul-Group G)

mul-Group' :
  {l : Level} (G : Group l) →
  type-Group G → type-Group G → type-Group G
mul-Group' G x y = mul-Group G y x

is-associative-mul-Group :
  {l : Level} (G : Group l) (x y z : type-Group G) →
  Id (mul-Group G (mul-Group G x y) z) (mul-Group G x (mul-Group G y z))
is-associative-mul-Group G = pr2 (associative-mul-Group G)

is-group-Group :
  {l : Level} (G : Group l) → is-group (semi-group-Group G)
is-group-Group G = pr2 G

is-unital-Group :
  {l : Level} (G : Group l) → is-unital (semi-group-Group G)
is-unital-Group G = pr1 (is-group-Group G)

unit-Group :
  {l : Level} (G : Group l) → type-Group G
unit-Group G = pr1 (is-unital-Group G)

left-unit-law-Group :
  {l : Level} (G : Group l) (x : type-Group G) →
  Id (mul-Group G (unit-Group G) x) x
left-unit-law-Group G = pr1 (pr2 (is-unital-Group G))

right-unit-law-Group :
  {l : Level} (G : Group l) (x : type-Group G) →
  Id (mul-Group G x (unit-Group G)) x
right-unit-law-Group G = pr2 (pr2 (is-unital-Group G))

has-inverses-Group :
  {l : Level} (G : Group l) →
  is-group' (semi-group-Group G) (is-unital-Group G)
has-inverses-Group G = pr2 (is-group-Group G)

inv-Group :
  {l : Level} (G : Group l) →
  type-Group G → type-Group G
inv-Group G = pr1 (has-inverses-Group G)

left-inverse-law-Group :
  {l : Level} (G : Group l) (x : type-Group G) →
  Id (mul-Group G (inv-Group G x) x) (unit-Group G)
left-inverse-law-Group G = pr1 (pr2 (has-inverses-Group G))

right-inverse-law-Group :
  {l : Level} (G : Group l) (x : type-Group G) →
  Id (mul-Group G x (inv-Group G x)) (unit-Group G)
right-inverse-law-Group G = pr2 (pr2 (has-inverses-Group G))

is-equiv-mul-Group :
  {l : Level} (G : Group l) (x : type-Group G) →
  is-equiv (mul-Group G x)
is-equiv-mul-Group G x =
  is-equiv-has-inverse
    ( mul-Group G (inv-Group G x))
    ( λ y →
      ( inv (is-associative-mul-Group G _ _ _)) ∙
      ( ( ap (mul-Group' G y) (right-inverse-law-Group G x)) ∙
        ( left-unit-law-Group G y)))
    ( λ y →
      ( inv (is-associative-mul-Group G _ _ _)) ∙
      ( ( ap (mul-Group' G y) (left-inverse-law-Group G x)) ∙
        ( left-unit-law-Group G y)))

is-equiv-mul-Group' :
  {l : Level} (G : Group l) (x : type-Group G) →
  is-equiv (mul-Group' G x)
is-equiv-mul-Group' G x =
  is-equiv-has-inverse
    ( mul-Group' G (inv-Group G x))
    ( λ y →
      ( is-associative-mul-Group G _ _ _) ∙
      ( ( ap (mul-Group G y) (left-inverse-law-Group G x)) ∙
        ( right-unit-law-Group G y)))
    ( λ y →
      ( is-associative-mul-Group G _ _ _) ∙
      ( ( ap (mul-Group G y) (right-inverse-law-Group G x)) ∙
        ( right-unit-law-Group G y)))

--------------------------------------------------------------------------------

{- We show that being a group is a proposition. -}

abstract
  is-prop-is-group' :
    {l : Level} (G : Semi-Group l) (e : is-unital G) → is-prop' (is-group' G e)
  is-prop-is-group'
    ( pair (pair G is-set-G) (pair μ assoc-G))
    ( pair e (pair left-unit-G right-unit-G))
    ( pair i (pair left-inv-i right-inv-i))
    ( pair i' (pair left-inv-i' right-inv-i')) =
    eq-subtype
      ( λ i →
        is-prop-prod
          ( is-prop-Π (λ x → is-set-G (μ (i x) x) e))
          ( is-prop-Π (λ x → is-set-G (μ x (i x)) e)))
      ( eq-htpy
        ( λ x →                                             -- ix
          ( inv (left-unit-G (i x))) ∙                      -- = 1·(ix)
          ( ( ap (λ y → μ y (i x)) (inv (left-inv-i' x))) ∙ -- = (i'x·x)·(ix)
            ( ( assoc-G (i' x) x (i x)) ∙                   -- = (i'x)·(x·ix)
              ( ( ap (μ (i' x)) (right-inv-i x)) ∙          -- = (i'x)·1
                ( right-unit-G (i' x)))))))                 -- = i'x

abstract
  is-prop-is-group :
    {l : Level} (G : Semi-Group l) → is-prop (is-group G)
  is-prop-is-group G =
    is-prop-Σ
      ( is-prop-is-unital G)
      ( λ e → is-prop-is-prop' (is-prop-is-group' G e))

--------------------------------------------------------------------------------

{- We give two examples of groups. The first is the group ℤ of integers. The
   second is the loop space of a pointed 1-type.  -}

{- The group of integers. -}

semi-group-ℤ : Semi-Group lzero
semi-group-ℤ = pair set-ℤ (pair add-ℤ associative-add-ℤ)

group-ℤ : Group lzero
group-ℤ =
  pair
    ( semi-group-ℤ)
    ( pair
      ( pair zero-ℤ (pair left-unit-law-add-ℤ right-unit-law-add-ℤ))
      ( pair neg-ℤ (pair left-inverse-law-add-ℤ right-inverse-law-add-ℤ)))

--------------------------------------------------------------------------------

{- The loop space of a 1-type as a group. -}

loop-space :
  {l : Level} {A : UU l} → A → UU l
loop-space a = Id a a

set-loop-space :
  {l : Level} (A : UU l) (a : A) (is-set-Ω : is-set (Id a a)) → UU-Set l
set-loop-space A a is-set-Ω = pair (Id a a) is-set-Ω

semi-group-loop-space :
  {l : Level} (A : UU l) (a : A) (is-set-Ω : is-set (Id a a)) → Semi-Group l
semi-group-loop-space A a is-set-Ω =
  pair
    ( set-loop-space A a is-set-Ω)
    ( pair (λ p q → p ∙ q) assoc)

group-loop-space :
  {l : Level} (A : UU l) (a : A) (is-set-Ω : is-set (Id a a)) → Group l
group-loop-space A a is-set-Ω =
  pair
    ( semi-group-loop-space A a is-set-Ω)
    ( pair
      ( pair refl (pair (λ q → left-unit) (λ p → right-unit)))
      ( pair inv (pair left-inv right-inv)))

set-loop-space-1-type :
  {l : Level} (A : 1-type l) (a : pr1 A) → UU-Set l
set-loop-space-1-type (pair A is-1-type-A) a =
  set-loop-space A a (is-1-type-A a a)

semi-group-loop-space-1-type :
  {l : Level} (A : 1-type l) (a : pr1 A) → Semi-Group l
semi-group-loop-space-1-type (pair A is-1-type-A) a =
  semi-group-loop-space A a (is-1-type-A a a)

group-loop-space-1-type :
  {l : Level} (A : 1-type l) (a : pr1 A) → Group l
group-loop-space-1-type (pair A is-1-type-A) a =
  group-loop-space A a (is-1-type-A a a)

--------------------------------------------------------------------------------

{- We introduce the automorphism group on a set X. -}

aut-Set :
  {l : Level} (X : UU-Set l) → UU-Set l
aut-Set X = set-equiv X X

associative-comp-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} →
  (e : A ≃ B) (f : B ≃ C) (g : C ≃ D) →
  Id ((g ∘e f) ∘e e) (g ∘e (f ∘e e))
associative-comp-equiv e f g = eq-htpy-equiv refl-htpy

has-associative-mul-aut-Set :
  {l : Level} (X : UU-Set l) → has-associative-bin-op (aut-Set X)
has-associative-mul-aut-Set X =
  pair
    ( λ e f → f ∘e e)
    ( λ e f g → inv (associative-comp-equiv e f g))

aut-Semi-Group :
  {l : Level} (X : UU-Set l) → Semi-Group l
aut-Semi-Group X =
  pair
    ( aut-Set X)
    ( has-associative-mul-aut-Set X)

left-unit-law-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  Id ((equiv-id Y) ∘e e) e
left-unit-law-equiv e = eq-htpy-equiv refl-htpy

right-unit-law-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  Id (e ∘e (equiv-id X)) e
right-unit-law-equiv e = eq-htpy-equiv refl-htpy

is-unital-aut-Semi-Group :
  {l : Level} (X : UU-Set l) → is-unital (aut-Semi-Group X)
is-unital-aut-Semi-Group X =
  pair
    ( equiv-id (type-Set X))
    ( pair
      ( right-unit-law-equiv)
      ( left-unit-law-equiv))

left-inverse-law-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  Id ((inv-equiv e) ∘e e) (equiv-id X)
left-inverse-law-equiv e =
  eq-htpy-equiv (isretr-inv-is-equiv (is-equiv-map-equiv e))

right-inverse-law-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  Id (e ∘e (inv-equiv e)) (equiv-id Y)
right-inverse-law-equiv e =
  eq-htpy-equiv (issec-inv-is-equiv (is-equiv-map-equiv e))

is-group-aut-Semi-Group' :
  {l : Level} (X : UU-Set l) →
  is-group' (aut-Semi-Group X) (is-unital-aut-Semi-Group X)
is-group-aut-Semi-Group' X =
  pair
    ( inv-equiv)
    ( pair right-inverse-law-equiv left-inverse-law-equiv)

aut-Group :
  {l : Level} → UU-Set l → Group l
aut-Group X =
  pair
    ( aut-Semi-Group X)
    ( pair (is-unital-aut-Semi-Group X) (is-group-aut-Semi-Group' X))

--------------------------------------------------------------------------------

{- Now we introduce homomorphisms of semi-groups. Group homomorphisms are just
   homomorphisms between their underlying semi-groups. -}

preserves-mul :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  (type-Semi-Group G → type-Semi-Group H) → UU (l1 ⊔ l2)
preserves-mul G H f =
  (x y : type-Semi-Group G) →
      Id (f (mul-Semi-Group G x y)) (mul-Semi-Group H (f x) (f y))

abstract
  is-prop-preserves-mul :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f : type-Semi-Group G → type-Semi-Group H) →
    is-prop (preserves-mul G H f)
  is-prop-preserves-mul G (pair (pair H is-set-H) (pair μ-H assoc-H)) f =
    is-prop-Π (λ x →
      is-prop-Π (λ y →
        is-set-H (f (mul-Semi-Group G x y)) (μ-H (f x) (f y))))

hom-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) → UU (l1 ⊔ l2)
hom-Semi-Group G H =
  Σ ( type-Semi-Group G → type-Semi-Group H)
    ( preserves-mul G H)

--------------------------------------------------------------------------------

{- Bureaucracy of homomorphisms of semi-groups. -}

map-hom-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  ( hom-Semi-Group G H) →
  ( type-Semi-Group G) → (type-Semi-Group H)
map-hom-Semi-Group G H f = pr1 f

preserves-mul-hom-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  ( f : hom-Semi-Group G H) →
  preserves-mul G H (map-hom-Semi-Group G H f)
preserves-mul-hom-Semi-Group G H f = pr2 f

--------------------------------------------------------------------------------

{- We characterize the identity type of the semi-group homomorphisms. -}

htpy-hom-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2)
  (f g : hom-Semi-Group G H) → UU (l1 ⊔ l2)
htpy-hom-Semi-Group G H f g =
  (map-hom-Semi-Group G H f) ~ (map-hom-Semi-Group G H g)

reflexive-htpy-hom-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  ( f : hom-Semi-Group G H) → htpy-hom-Semi-Group G H f f
reflexive-htpy-hom-Semi-Group G H f = refl-htpy

htpy-hom-Semi-Group-eq :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  ( f g : hom-Semi-Group G H) → Id f g → htpy-hom-Semi-Group G H f g
htpy-hom-Semi-Group-eq G H f .f refl = reflexive-htpy-hom-Semi-Group G H f 

abstract
  is-contr-total-htpy-hom-Semi-Group :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f : hom-Semi-Group G H) →
    is-contr (Σ (hom-Semi-Group G H) (htpy-hom-Semi-Group G H f))
  is-contr-total-htpy-hom-Semi-Group G H f =
    is-contr-total-Eq-substructure
      ( is-contr-total-htpy (map-hom-Semi-Group G H f))
      ( is-prop-preserves-mul G H)
      ( map-hom-Semi-Group G H f)
      ( refl-htpy)
      ( preserves-mul-hom-Semi-Group G H f)

abstract
  is-equiv-htpy-hom-Semi-Group-eq :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f g : hom-Semi-Group G H) → is-equiv (htpy-hom-Semi-Group-eq G H f g)
  is-equiv-htpy-hom-Semi-Group-eq G H f =
    fundamental-theorem-id f
      ( reflexive-htpy-hom-Semi-Group G H f)
      ( is-contr-total-htpy-hom-Semi-Group G H f)
      ( htpy-hom-Semi-Group-eq G H f)

eq-htpy-hom-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  { f g : hom-Semi-Group G H} → htpy-hom-Semi-Group G H f g → Id f g
eq-htpy-hom-Semi-Group G H {f} {g} =
  inv-is-equiv (is-equiv-htpy-hom-Semi-Group-eq G H f g)

--------------------------------------------------------------------------------

{- We show that the type of semi-group homomorphisms between two semi-groups is
   a set. -}

is-set-hom-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  is-set (hom-Semi-Group G H)
is-set-hom-Semi-Group G H (pair f μ-f) (pair g μ-g) =
  is-prop-is-equiv
    ( htpy-hom-Semi-Group G H (pair f μ-f) (pair g μ-g))
    ( htpy-hom-Semi-Group-eq G H (pair f μ-f) (pair g μ-g))
    ( is-equiv-htpy-hom-Semi-Group-eq G H (pair f μ-f) (pair g μ-g))
    ( is-prop-Π (λ x → is-set-type-Semi-Group H (f x) (g x)))

--------------------------------------------------------------------------------

{- We introduce monoid homomorphisms. -}

preserves-unit-hom-Semi-Group :
  { l1 l2 : Level} (M1 : Monoid l1) (M2 : Monoid l2) →
  ( hom-Semi-Group (semi-group-Monoid M1) (semi-group-Monoid M2)) → UU l2
preserves-unit-hom-Semi-Group M1 M2 f =
  Id ( map-hom-Semi-Group
       ( semi-group-Monoid M1)
       ( semi-group-Monoid M2)
       ( f)
       ( unit-Monoid M1))
     ( unit-Monoid M2)

hom-Monoid :
  { l1 l2 : Level} (M1 : Monoid l1) (M2 : Monoid l2) → UU (l1 ⊔ l2)
hom-Monoid M1 M2 =
  Σ ( hom-Semi-Group (semi-group-Monoid M1) (semi-group-Monoid M2))
    ( preserves-unit-hom-Semi-Group M1 M2)

--------------------------------------------------------------------------------

{- We introduce group homomorphisms. -}

preserves-mul-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  (type-Group G → type-Group H) → UU (l1 ⊔ l2)
preserves-mul-Group G H f =
  preserves-mul (semi-group-Group G) (semi-group-Group H) f

hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) → UU (l1 ⊔ l2)
hom-Group G H =
  hom-Semi-Group
    ( semi-group-Group G)
    ( semi-group-Group H)

--------------------------------------------------------------------------------

{- Bureaucracy of group homomorphisms. -}

map-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( hom-Group G H) →
  ( type-Group G) → (type-Group H)
map-hom-Group G H = pr1

preserves-mul-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : hom-Group G H) →
  preserves-mul
    ( semi-group-Group G)
    ( semi-group-Group H)
    ( map-hom-Group G H f)
preserves-mul-hom-Group G H = pr2

--------------------------------------------------------------------------------

{- We characterize the identity type of the group homomorphisms. -}

htpy-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2)
  (f g : hom-Group G H) → UU (l1 ⊔ l2)
htpy-hom-Group G H =
  htpy-hom-Semi-Group
    ( semi-group-Group G)
    ( semi-group-Group H)

reflexive-htpy-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : hom-Group G H) → htpy-hom-Group G H f f
reflexive-htpy-hom-Group G H =
  reflexive-htpy-hom-Semi-Group
    ( semi-group-Group G)
    ( semi-group-Group H)

htpy-hom-Group-eq :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f g : hom-Group G H) → Id f g → htpy-hom-Group G H f g
htpy-hom-Group-eq G H =
  htpy-hom-Semi-Group-eq
    ( semi-group-Group G)
    ( semi-group-Group H)

abstract
  is-contr-total-htpy-hom-Group :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f : hom-Group G H) →
    is-contr (Σ (hom-Group G H) (htpy-hom-Group G H f))
  is-contr-total-htpy-hom-Group G H =
    is-contr-total-htpy-hom-Semi-Group
      ( semi-group-Group G)
      ( semi-group-Group H)

abstract
  is-equiv-htpy-hom-Group-eq :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f g : hom-Group G H) → is-equiv (htpy-hom-Group-eq G H f g)
  is-equiv-htpy-hom-Group-eq G H =
    is-equiv-htpy-hom-Semi-Group-eq
      ( semi-group-Group G)
      ( semi-group-Group H)

eq-htpy-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  { f g : hom-Group G H} → htpy-hom-Group G H f g → Id f g
eq-htpy-hom-Group G H =
  eq-htpy-hom-Semi-Group (semi-group-Group G) (semi-group-Group H)

is-set-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  is-set (hom-Group G H)
is-set-hom-Group G H =
  is-set-hom-Semi-Group (semi-group-Group G) (semi-group-Group H)

--------------------------------------------------------------------------------

{- Next, we construct the identity group homomorphism, and we show that
   compositions of group homomorphisms are again group homomorphisms. -}

preserves-mul-id :
  {l : Level} (G : Semi-Group l) → preserves-mul G G id
preserves-mul-id (pair (pair G is-set-G) (pair μ-G assoc-G)) x y = refl

id-hom-Semi-Group :
  {l : Level} (G : Semi-Group l) → hom-Semi-Group G G
id-hom-Semi-Group G =
  pair id (preserves-mul-id G)

preserves-unit-id-hom-Semi-Group :
  { l : Level} (M : Monoid l) →
  preserves-unit-hom-Semi-Group M M (id-hom-Semi-Group (semi-group-Monoid M))
preserves-unit-id-hom-Semi-Group M = refl

id-Monoid :
  {l : Level} (M : Monoid l) → hom-Monoid M M
id-Monoid M =
  pair ( id-hom-Semi-Group (semi-group-Monoid M))
       ( preserves-unit-id-hom-Semi-Group M)

id-Group :
  {l : Level} (G : Group l) → hom-Group G G
id-Group G = id-hom-Semi-Group (semi-group-Group G)

comp-Semi-Group :
  {l1 l2 l3 : Level} →
  (G : Semi-Group l1) (H : Semi-Group l2) (K : Semi-Group l3) →
  (hom-Semi-Group H K) → (hom-Semi-Group G H) → (hom-Semi-Group G K)
comp-Semi-Group G H K g f =
  pair
    ( (map-hom-Semi-Group H K g) ∘ (map-hom-Semi-Group G H f))
    ( λ x y →
      ( ap ( map-hom-Semi-Group H K g)
           ( preserves-mul-hom-Semi-Group G H f x y)) ∙
      ( preserves-mul-hom-Semi-Group H K g
        ( map-hom-Semi-Group G H f x)
        ( map-hom-Semi-Group G H f y)))

comp-Group :
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3) →
  (hom-Group H K) → (hom-Group G H) → (hom-Group G K)
comp-Group G H K =
  comp-Semi-Group
    ( semi-group-Group G)
    ( semi-group-Group H)
    ( semi-group-Group K)

--------------------------------------------------------------------------------

{- Next, we prove the that the laws for a category hold for group homomorphisms,
   i.e., we show that composition is associative and satisfies the left and
   right unit laws. Before we show that these laws hold, we will characterize
   the identity type of the types of semi-group homomorphisms and group 
   homomorphisms. -}

associative-Semi-Group :
  { l1 l2 l3 l4 : Level} (G : Semi-Group l1) (H : Semi-Group l2)
  ( K : Semi-Group l3) (L : Semi-Group l4) (h : hom-Semi-Group K L) →
  ( g : hom-Semi-Group H K) (f : hom-Semi-Group G H) →
  Id ( comp-Semi-Group G H L
       ( comp-Semi-Group H K L h g) f)
     ( comp-Semi-Group G K L h
       ( comp-Semi-Group G H K g f))
associative-Semi-Group G H K L (pair h μ-h) (pair g μ-g) (pair f μ-f) =
  eq-htpy-hom-Semi-Group G L refl-htpy

left-unit-law-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2)
  ( f : hom-Semi-Group G H) →
  Id ( comp-Semi-Group G H H (id-hom-Semi-Group H) f) f
left-unit-law-Semi-Group G
  (pair (pair H is-set-H) (pair μ-H assoc-H)) (pair f μ-f) =
  eq-htpy-hom-Semi-Group G
    ( pair (pair H is-set-H) (pair μ-H assoc-H))
    ( refl-htpy)

right-unit-law-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2)
  ( f : hom-Semi-Group G H) →
  Id ( comp-Semi-Group G G H f (id-hom-Semi-Group G)) f
right-unit-law-Semi-Group
  (pair (pair G is-set-G) (pair μ-G assoc-G)) H (pair f μ-f) =
  eq-htpy-hom-Semi-Group
    ( pair (pair G is-set-G) (pair μ-G assoc-G)) H refl-htpy

--------------------------------------------------------------------------------

{- Now we introduce the notion of group isomorphism. Finally, we will show that
   isomorphic groups are equal. -}

is-iso-hom-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  ( f : hom-Semi-Group G H) → UU (l1 ⊔ l2)
is-iso-hom-Semi-Group G H f =
  Σ ( hom-Semi-Group H G) (λ g →
    ( Id (comp-Semi-Group H G H f g) (id-hom-Semi-Group H)) ×
    ( Id (comp-Semi-Group G H G g f) (id-hom-Semi-Group G)))

inv-is-iso-hom-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  ( f : hom-Semi-Group G H) →
  is-iso-hom-Semi-Group G H f → hom-Semi-Group H G
inv-is-iso-hom-Semi-Group G H f = pr1

iso-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) → UU (l1 ⊔ l2)
iso-Semi-Group G H =
  Σ (hom-Semi-Group G H) (is-iso-hom-Semi-Group G H)

hom-iso-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  iso-Semi-Group G H → hom-Semi-Group G H
hom-iso-Semi-Group G H = pr1

is-iso-hom-iso-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2)
  ( f : iso-Semi-Group G H) →
  is-iso-hom-Semi-Group G H (hom-iso-Semi-Group G H f)
is-iso-hom-iso-Semi-Group G H = pr2

inv-hom-iso-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  iso-Semi-Group G H → hom-Semi-Group H G
inv-hom-iso-Semi-Group G H f =
  inv-is-iso-hom-Semi-Group G H
    ( hom-iso-Semi-Group G H f)
    ( is-iso-hom-iso-Semi-Group G H f)

abstract
  is-prop-is-iso-hom-Semi-Group' :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f : hom-Semi-Group G H) → is-prop' (is-iso-hom-Semi-Group G H f)
  is-prop-is-iso-hom-Semi-Group' G H f
    (pair g (pair issec isretr)) (pair g' (pair issec' isretr')) =
    eq-subtype
      ( λ h →
        is-prop-prod
          ( is-set-hom-Semi-Group H H
            ( comp-Semi-Group H G H f h)
            ( id-hom-Semi-Group H))
          ( is-set-hom-Semi-Group G G
            ( comp-Semi-Group G H G h f)
            ( id-hom-Semi-Group G)))
      ( ( inv (left-unit-law-Semi-Group H G g)) ∙
        ( ( inv (ap (λ h → comp-Semi-Group H G G h g) isretr')) ∙
          ( ( associative-Semi-Group H G H G g' f g) ∙
            ( ( ap (comp-Semi-Group H H G g') issec) ∙
              ( right-unit-law-Semi-Group H G g')))))

abstract
  is-prop-is-iso-hom-Semi-Group :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f : hom-Semi-Group G H) → is-prop (is-iso-hom-Semi-Group G H f)
  is-prop-is-iso-hom-Semi-Group G H f =
    is-prop-is-prop' (is-prop-is-iso-hom-Semi-Group' G H f)

abstract
  preserves-mul-inv-is-equiv-Semi-Group :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f : hom-Semi-Group G H)
    ( is-equiv-f : is-equiv (map-hom-Semi-Group G H f)) →
    preserves-mul H G (inv-is-equiv is-equiv-f)
  preserves-mul-inv-is-equiv-Semi-Group
    ( pair (pair G is-set-G) (pair μ-G assoc-G))
    ( pair (pair H is-set-H) (pair μ-H assoc-H))
    ( pair f μ-f) is-equiv-f x y =
    inv-is-equiv
      ( is-emb-is-equiv f is-equiv-f
        ( inv-is-equiv is-equiv-f (μ-H x y))
        ( μ-G (inv-is-equiv is-equiv-f x) (inv-is-equiv is-equiv-f y)))
      ( ( ( issec-inv-is-equiv is-equiv-f (μ-H x y)) ∙
          ( ( ap (λ t → μ-H t y) (inv (issec-inv-is-equiv is-equiv-f x))) ∙
            ( ap
              ( μ-H (f (inv-is-equiv is-equiv-f x)))
              ( inv (issec-inv-is-equiv is-equiv-f y))))) ∙
        ( inv (μ-f (inv-is-equiv is-equiv-f x) (inv-is-equiv is-equiv-f y))))

abstract
  is-iso-is-equiv-hom-Semi-Group :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f : hom-Semi-Group G H) (is-equiv-f : is-equiv (pr1 f)) →
    is-iso-hom-Semi-Group G H f
  is-iso-is-equiv-hom-Semi-Group
    ( pair (pair G is-set-G) (pair μ-G assoc-G))
    ( pair (pair H is-set-H) (pair μ-H assoc-H))
    ( pair f μ-f) is-equiv-f =
    pair
      ( pair
        ( inv-is-equiv is-equiv-f)
        ( preserves-mul-inv-is-equiv-Semi-Group
          ( pair (pair G is-set-G) (pair μ-G assoc-G))
          ( pair (pair H is-set-H) (pair μ-H assoc-H))
          ( pair f μ-f) is-equiv-f))
      ( pair
        ( eq-htpy-hom-Semi-Group
          ( pair (pair H is-set-H) (pair μ-H assoc-H))
          ( pair (pair H is-set-H) (pair μ-H assoc-H))
          ( issec-inv-is-equiv is-equiv-f))
        ( eq-htpy-hom-Semi-Group
          ( pair (pair G is-set-G) (pair μ-G assoc-G))
          ( pair (pair G is-set-G) (pair μ-G assoc-G))
          ( isretr-inv-is-equiv is-equiv-f)))

abstract
  is-equiv-hom-is-iso-hom-Semi-Group :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f : hom-Semi-Group G H) (is-iso-f : is-iso-hom-Semi-Group G H f) →
    ( is-equiv (pr1 f))
  is-equiv-hom-is-iso-hom-Semi-Group
    ( pair (pair G is-set-G) (pair μ-G assoc-G))
    ( pair (pair H is-set-H) (pair μ-H assoc-H))
    ( pair f μ-f)
    ( pair (pair g μ-g) (pair issec isretr)) =
    is-equiv-has-inverse g
      ( htpy-eq (ap pr1 issec))
      ( htpy-eq (ap pr1 isretr))

equiv-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) → UU (l1 ⊔ l2)
equiv-Semi-Group G H =
  Σ ( type-Semi-Group G ≃ type-Semi-Group H)
    ( λ e → preserves-mul G H (map-equiv e))

total-is-equiv-hom-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) → UU (l1 ⊔ l2)
total-is-equiv-hom-Semi-Group G H =
  Σ (hom-Semi-Group G H) (λ f → is-equiv (map-hom-Semi-Group G H f))

preserves-mul' :
  { l1 l2 : Level} (G : Semi-Group l1) (H : UU-Set l2)
  ( μ-H : has-associative-bin-op H) →
  ( e : (type-Semi-Group G) ≃ (type-Set H)) →
  UU (l1 ⊔ l2)
preserves-mul' G H μ-H e = preserves-mul G (pair H μ-H) (map-equiv e)

equiv-Semi-Group' :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) → UU (l1 ⊔ l2)
equiv-Semi-Group' G H = equiv-Semi-Group G (pair (pr1 H) (pr2 H))

abstract
  equiv-iso-Semi-Group-equiv-Semi-Group :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    equiv-Semi-Group' G H ≃ iso-Semi-Group G H
  equiv-iso-Semi-Group-equiv-Semi-Group G H =
    ( ( ( equiv-total-subtype
          ( λ f → is-subtype-is-equiv (map-hom-Semi-Group G H f))
          ( is-prop-is-iso-hom-Semi-Group G H)
          ( is-iso-is-equiv-hom-Semi-Group G H)
          ( is-equiv-hom-is-iso-hom-Semi-Group G H)) ∘e
        ( ( inv-equiv
            ( equiv-Σ-assoc
              ( type-Semi-Group G → type-Semi-Group H)
              ( preserves-mul G H)
              ( λ f → is-equiv (map-hom-Semi-Group G H f)))) ∘e
          ( equiv-tot
            ( λ f → equiv-swap-prod (is-equiv f) (preserves-mul G H f))))) ∘e
      ( equiv-Σ-assoc
        ( type-Semi-Group G → type-Semi-Group H)
        ( is-equiv)
        ( λ e → preserves-mul G H (map-equiv e)))) ∘e
    ( equiv-tr (equiv-Semi-Group G) (η-pair H))

center-total-preserves-mul-id :
  { l1 : Level} (G : Semi-Group l1) →
  Σ (has-associative-bin-op (pr1 G)) (λ μ → preserves-mul G (pair (pr1 G) μ) id)
center-total-preserves-mul-id (pair (pair G is-set-G) (pair μ-G assoc-G)) =
  pair (pair μ-G assoc-G) (λ x y → refl)

contraction-total-preserves-mul-id :
  { l1 : Level} (G : Semi-Group l1) →
  ( t : Σ ( has-associative-bin-op (pr1 G))
          ( λ μ → preserves-mul G (pair (pr1 G) μ) id)) →
  Id (center-total-preserves-mul-id G) t
contraction-total-preserves-mul-id
  ( pair (pair G is-set-G) (pair μ-G assoc-G))
  ( pair (pair μ-G' assoc-G') μ-id) =
  eq-subtype
    ( λ μ →
      is-prop-preserves-mul
        ( pair (pair G is-set-G) (pair μ-G assoc-G))
        ( pair (pair G is-set-G) μ) id)
    ( eq-subtype
      ( λ μ →
        is-prop-Π (λ x →
          is-prop-Π (λ y →
            is-prop-Π (λ z →
              is-set-G (μ (μ x y) z) (μ x (μ y z))))))
      ( eq-htpy (λ x → eq-htpy (λ y → μ-id x y))))

is-contr-total-preserves-mul-id :
  { l1 : Level} (G : Semi-Group l1) →
  is-contr (Σ (has-associative-bin-op (pr1 G)) (λ μ → preserves-mul G (pair (pr1 G) μ) id))
is-contr-total-preserves-mul-id G =
  pair
    ( center-total-preserves-mul-id G)
    ( contraction-total-preserves-mul-id G)

is-contr-total-equiv-Semi-Group :
  { l1 : Level} (G : Semi-Group l1) →
  is-contr (Σ (Semi-Group l1) (λ H → equiv-Semi-Group' G H))
is-contr-total-equiv-Semi-Group {l1} G =
  is-contr-total-Eq-structure
    ( preserves-mul' G)
    ( is-contr-total-Eq-substructure
      ( is-contr-total-equiv (type-Semi-Group G))
      ( is-prop-is-set)
      ( type-Semi-Group G)
      ( equiv-id (type-Semi-Group G))
      ( is-set-type-Semi-Group G))
    ( pair (pr1 G) (equiv-id (type-Semi-Group G)))
    ( is-contr-total-preserves-mul-id G)

is-contr-total-iso-Semi-Group :
  { l1 : Level} (G : Semi-Group l1) →
  is-contr (Σ (Semi-Group l1) (iso-Semi-Group G))
is-contr-total-iso-Semi-Group {l1} G =
  is-contr-equiv'
    ( Σ (Semi-Group l1) (λ H → equiv-Semi-Group' G H))
    ( equiv-tot (λ H → equiv-iso-Semi-Group-equiv-Semi-Group G H))
    ( is-contr-total-equiv-Semi-Group G)

iso-id-Semi-Group :
  { l1 : Level} (G : Semi-Group l1) → iso-Semi-Group G G
iso-id-Semi-Group G =
  pair
    ( id-hom-Semi-Group G)
    ( pair
      ( id-hom-Semi-Group G)
      ( pair
        ( left-unit-law-Semi-Group G G (id-hom-Semi-Group G))
        ( right-unit-law-Semi-Group G G (id-hom-Semi-Group G))))

iso-eq-Semi-Group :
  { l1 : Level} (G H : Semi-Group l1) → Id G H → iso-Semi-Group G H
iso-eq-Semi-Group G .G refl = iso-id-Semi-Group G

is-equiv-iso-eq-Semi-Group :
  { l1 : Level} (G H : Semi-Group l1) → is-equiv (iso-eq-Semi-Group G H)
is-equiv-iso-eq-Semi-Group G =
  fundamental-theorem-id G
    ( iso-id-Semi-Group G)
    ( is-contr-total-iso-Semi-Group G)
    ( iso-eq-Semi-Group G)

equiv-iso-eq-Semi-Group :
  { l1 : Level} (G H : Semi-Group l1) → Id G H ≃ iso-Semi-Group G H
equiv-iso-eq-Semi-Group G H =
  pair (iso-eq-Semi-Group G H) (is-equiv-iso-eq-Semi-Group G H)

eq-iso-Semi-Group :
  { l1 : Level} (G H : Semi-Group l1) → iso-Semi-Group G H → Id G H
eq-iso-Semi-Group G H = inv-is-equiv (is-equiv-iso-eq-Semi-Group G H)

--------------------------------------------------------------------------------

{- Finally we show that isomorphic groups are equal. -}

is-iso-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  hom-Group G H → UU (l1 ⊔ l2)
is-iso-hom-Group G H =
  is-iso-hom-Semi-Group
    ( semi-group-Group G)
    ( semi-group-Group H)

inv-is-iso-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : hom-Group G H) → is-iso-hom-Group G H f → hom-Group H G
inv-is-iso-hom-Group G H f = pr1

iso-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) → UU (l1 ⊔ l2)
iso-Group G H =
  iso-Semi-Group
    ( semi-group-Group G)
    ( semi-group-Group H)

hom-iso-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  iso-Group G H → hom-Group G H
hom-iso-Group G H = pr1

is-iso-hom-iso-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : iso-Group G H) → is-iso-hom-Group G H (hom-iso-Group G H f)
is-iso-hom-iso-Group G H = pr2

inv-hom-iso-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  iso-Group G H → hom-Group H G
inv-hom-iso-Group G H f =
  inv-is-iso-hom-Group G H
    ( hom-iso-Group G H f)
    ( is-iso-hom-iso-Group G H f)

iso-id-Group :
  { l1 : Level} (G : Group l1) → iso-Group G G
iso-id-Group G = iso-id-Semi-Group (semi-group-Group G)

iso-eq-Group :
  { l1 : Level} (G H : Group l1) → Id G H → iso-Group G H
iso-eq-Group G .G refl = iso-id-Group G

abstract
  equiv-iso-eq-Group' :
    { l1 : Level} (G H : Group l1) → Id G H ≃ iso-Group G H
  equiv-iso-eq-Group' G H =
    ( equiv-iso-eq-Semi-Group
      ( semi-group-Group G)
      ( semi-group-Group H)) ∘e
    ( equiv-ap-pr1-is-subtype is-prop-is-group {s = G} {t = H})

abstract
  is-contr-total-iso-Group :
    { l1 : Level} (G : Group l1) → is-contr (Σ (Group l1) (iso-Group G))
  is-contr-total-iso-Group {l1} G =
    is-contr-equiv'
      ( Σ (Group l1) (Id G))
      ( equiv-tot (λ H → equiv-iso-eq-Group' G H))
      ( is-contr-total-path G)

is-equiv-iso-eq-Group :
  { l1 : Level} (G H : Group l1) → is-equiv (iso-eq-Group G H)
is-equiv-iso-eq-Group G =
  fundamental-theorem-id G
    ( iso-id-Group G)
    ( is-contr-total-iso-Group G)
    ( iso-eq-Group G)

eq-iso-Group :
  { l1 : Level} (G H : Group l1) → iso-Group G H → Id G H
eq-iso-Group G H = inv-is-equiv (is-equiv-iso-eq-Group G H)

--------------------------------------------------------------------------------

-- Categories

underlying-type-Set :
  {l : Level} → UU-Set l → UU l
underlying-type-Set A = pr1 A

is-set-underlying-type-Set :
  {l : Level} (A : UU-Set l) → is-set (underlying-type-Set A)
is-set-underlying-type-Set A = pr2 A

associative-composition-structure :
  {l1 l2 : Level} (A : UU l1) (hom : A → A → UU-Set l2) → UU (l1 ⊔ l2)
associative-composition-structure A hom =
  Σ ( (x y z : A)
      → underlying-type-Set (hom x y)
      → underlying-type-Set (hom y z)
      → underlying-type-Set (hom x z))
    ( λ μ → (x y z w : A) (f : underlying-type-Set (hom x y)) (g : underlying-type-Set (hom y z)) (h : underlying-type-Set (hom z w)) →
      Id (μ x z w (μ x y z f g) h) (μ x y w f (μ y z w g h)))

is-unital-composition-structure :
  {l1 l2 : Level} (A : UU l1) (hom : A → A → UU-Set l2) →
  associative-composition-structure A hom → UU _
is-unital-composition-structure A hom (pair μ assoc-μ) =
  Σ ( (x : A) → underlying-type-Set (hom x x))
    ( λ e →
      ( (x y : A) (f : underlying-type-Set (hom x y)) → Id (μ x x y (e x) f) f)
      × ( (x y : A) (f : underlying-type-Set (hom x y)) → Id (μ x y y f (e y)) f))

is-prop-is-unital-composition-structure' :
  {l1 l2 : Level} (A : UU l1) (hom : A → A → UU-Set l2) →
  ( μ : associative-composition-structure A hom) →
  is-prop' (is-unital-composition-structure A hom μ)
is-prop-is-unital-composition-structure' A hom
  ( pair μ assoc-μ)
  ( pair e (pair left-unit-law-e right-unit-law-e))
  ( pair e' (pair left-unit-law-e' right-unit-law-e')) =
  eq-subtype
    ( λ x →
      is-prop-prod
        ( is-prop-Π
          ( λ a → is-prop-Π
            ( λ b → is-prop-Π
              ( λ f' →
                is-set-underlying-type-Set (hom a b) (μ a a b (x a) f') f'))))
        ( is-prop-Π
          ( λ a → is-prop-Π
            ( λ b → is-prop-Π
              ( λ f' →
                is-set-underlying-type-Set (hom a b) (μ a b b f' (x b)) f')))))
    ( eq-htpy
      ( λ x → (inv (left-unit-law-e' x x (e x))) ∙ right-unit-law-e x x (e' x)))

Precategory :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Precategory l1 l2 =
  Σ ( UU l1) (λ A →
    Σ (A → A → UU-Set l2) (λ hom →
      Σ ( associative-composition-structure A hom)
        ( is-unital-composition-structure A hom)))

obj-Precat :
  {l1 l2 : Level} → Precategory l1 l2 → UU l1
obj-Precat C = pr1 C

hom-Set-Precat :
  {l1 l2 : Level} (C : Precategory l1 l2) (x y : obj-Precat C) → UU-Set l2
hom-Set-Precat C = pr1 (pr2 C)

hom-Precat :
  {l1 l2 : Level} (C : Precategory l1 l2) (x y : obj-Precat C) → UU l2
hom-Precat C x y = pr1 (hom-Set-Precat C x y)

is-set-hom-Precat :
  {l1 l2 : Level} (C : Precategory l1 l2) (x y : obj-Precat C) →
  is-set (hom-Precat C x y)
is-set-hom-Precat C x y = pr2 (hom-Set-Precat C x y)

associative-composition-Precat :
  {l1 l2 : Level} (C : Precategory l1 l2) →
  associative-composition-structure (obj-Precat C) (hom-Set-Precat C)
associative-composition-Precat C = pr1 (pr2 (pr2 C))

composition-Precat :
  {l1 l2 : Level} (C : Precategory l1 l2) {x y z : obj-Precat C} →
  hom-Precat C x y → hom-Precat C y z → hom-Precat C x z
composition-Precat C {x} {y} {z} =
  pr1 (associative-composition-Precat C) x y z

is-associative-composition-Precat :
  { l1 l2 : Level} (C : Precategory l1 l2) {x y z w : obj-Precat C} →
  ( f : hom-Precat C x y) (g : hom-Precat C y z) (h : hom-Precat C z w) →
  Id (composition-Precat C (composition-Precat C f g) h)
     (composition-Precat C f (composition-Precat C g h))
is-associative-composition-Precat C {x} {y} {z} {w} =
  pr2 (associative-composition-Precat C) x y z w

is-unital-Precat :
  { l1 l2 : Level} (C : Precategory l1 l2) →
  is-unital-composition-structure
    ( obj-Precat C)
    ( hom-Set-Precat C)
    ( associative-composition-Precat C)
is-unital-Precat C = pr2 (pr2 (pr2 C))

{-
id-Precat :
  { l1 l2 : Level} (C : Precategory l1 l2) {x : obj-Precat C} →
  hom-Precat C x x
id-Precat (pair A (pair hom (pair (pair μ assoc-μ) t))) {x} =
  pr1 (is-unital-Precat {!!}) x
-}

--------------------------------------------------------------------------------

-- Exercises

--------------------------------------------------------------------------------

-- Exercise

{- We show that group homomorphisms preserve the unit. -}

preserves-unit :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : hom-Semi-Group
    ( semi-group-Group G)
    ( semi-group-Group H)) →
  UU l2
preserves-unit G H f =
  Id (map-hom-Group G H f (unit-Group G)) (unit-Group H)

abstract
  preserves-unit-group-hom :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f : hom-Group G H) → preserves-unit G H f
  preserves-unit-group-hom
    ( pair ( pair (pair G is-set-G) (pair μ-G assoc-G))
           ( pair ( pair e-G (pair left-unit-G right-unit-G))
                  ( pair i-G (pair left-inv-G right-inv-G))))
    ( pair ( pair (pair H is-set-H) (pair μ-H assoc-H))
           ( pair ( pair e-H (pair left-unit-H right-unit-H))
                  ( pair i-H (pair left-inv-H right-inv-H))))
    ( pair f μ-f) =
    ( inv (left-unit-H (f e-G))) ∙
    ( ( ap (λ x → μ-H x (f e-G)) (inv (left-inv-H (f e-G)))) ∙
      ( ( assoc-H (i-H (f e-G)) (f e-G) (f e-G)) ∙
        ( ( ap (μ-H (i-H (f e-G))) (inv (μ-f e-G e-G))) ∙
          ( ( ap (λ x → μ-H (i-H (f e-G)) (f x)) (left-unit-G e-G)) ∙
            ( left-inv-H (f e-G))))))

{- We show that group homomorphisms preserve inverses. -}

preserves-inverses :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : hom-Group G H) → UU (l1 ⊔ l2)
preserves-inverses G H f =
  ( x : type-Group G) →
  Id ( map-hom-Group G H f (inv-Group G x))
     ( inv-Group H (map-hom-Group G H f x))

abstract
  preserves-inverses-group-hom' :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f : hom-Group G H) →
    preserves-unit G H f → preserves-inverses G H f
  preserves-inverses-group-hom'
    ( pair ( pair (pair G is-set-G) (pair μ-G assoc-G))
           ( pair ( pair e-G (pair left-unit-G right-unit-G))
                  ( pair i-G (pair left-inv-G right-inv-G))))
    ( pair ( pair (pair H is-set-H) (pair μ-H assoc-H))
           ( pair ( pair e-H (pair left-unit-H right-unit-H))
                  ( pair i-H (pair left-inv-H right-inv-H))))
    ( pair f μ-f) preserves-unit-f x =
    ( inv ( right-unit-H (f (i-G x)))) ∙
    ( ( ap (μ-H (f (i-G x))) (inv (right-inv-H (f x)))) ∙
      ( ( inv (assoc-H (f (i-G x)) (f x) (i-H (f x)))) ∙
        ( ( inv (ap (λ y → μ-H y (i-H (f x))) (μ-f (i-G x) x))) ∙
          ( ( ap (λ y → μ-H (f y) (i-H (f x))) (left-inv-G x)) ∙
            ( ( ap
                ( λ y → μ-H y (i-H (f x)))
                ( preserves-unit-f)) ∙
              ( left-unit-H (i-H (f x))))))))

abstract
  preserves-inverses-group-hom :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f : hom-Group G H) → preserves-inverses G H f
  preserves-inverses-group-hom G H f =
    preserves-inverses-group-hom' G H f (preserves-unit-group-hom G H f)

hom-Group' :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) → UU (l1 ⊔ l2)
hom-Group' G H =
  Σ ( hom-Group G H) (λ f →
    ( preserves-unit G H f) × (preserves-inverses G H f))

preserves-all-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  hom-Group G H → hom-Group' G H
preserves-all-hom-Group G H f =
  pair f
    ( pair
      ( preserves-unit-group-hom G H f)
      ( preserves-inverses-group-hom G H f))

--------------------------------------------------------------------------------

