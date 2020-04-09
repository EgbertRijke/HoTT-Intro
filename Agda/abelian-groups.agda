{-# OPTIONS --without-K --exact-split #-}

module abelian-groups where

import 16-number-theory
open 16-number-theory public

is-abelian-Group :
  {l : Level} (G : Group l) → UU l
is-abelian-Group G =
  (x y : type-Group G) → Id (mul-Group G x y) (mul-Group G y x)

Ab : (l : Level) → UU (lsuc l)
Ab l = Σ (Group l) is-abelian-Group

group-Ab :
  {l : Level} (A : Ab l) → Group l
group-Ab A = pr1 A

set-Ab :
  {l : Level} (A : Ab l) → UU-Set l
set-Ab A = set-Group (group-Ab A)

type-Ab :
  {l : Level} (A : Ab l) → UU l
type-Ab A = type-Group (group-Ab A)

is-set-type-Ab :
  {l : Level} (A : Ab l) → is-set (type-Ab A)
is-set-type-Ab A = is-set-type-Group (group-Ab A)

associative-add-Ab :
  {l : Level} (A : Ab l) → has-associative-bin-op (set-Ab A)
associative-add-Ab A = associative-mul-Group (group-Ab A)

add-Ab :
  {l : Level} (A : Ab l) → type-Ab A → type-Ab A → type-Ab A
add-Ab A = mul-Group (group-Ab A)

is-associative-add-Ab :
  {l : Level} (A : Ab l) (x y z : type-Ab A) →
  Id (add-Ab A (add-Ab A x y) z) (add-Ab A x (add-Ab A y z))
is-associative-add-Ab A = is-associative-mul-Group (group-Ab A)

semi-group-Ab :
  {l : Level} (A : Ab l) → Semi-Group l
semi-group-Ab A = semi-group-Group (group-Ab A)

is-group-Ab :
  {l : Level} (A : Ab l) → is-group (semi-group-Ab A)
is-group-Ab A = is-group-Group (group-Ab A)

has-zero-Ab :
  {l : Level} (A : Ab l) → is-unital (semi-group-Ab A)
has-zero-Ab A = is-unital-Group (group-Ab A)

zero-Ab :
  {l : Level} (A : Ab l) → type-Ab A
zero-Ab A = unit-Group (group-Ab A)

left-zero-law-Ab :
  {l : Level} (A : Ab l) → (x : type-Ab A) →
  Id (add-Ab A (zero-Ab A) x) x
left-zero-law-Ab A = left-unit-law-Group (group-Ab A)

right-zero-law-Ab :
  {l : Level} (A : Ab l) → (x : type-Ab A) →
  Id (add-Ab A x (zero-Ab A)) x
right-zero-law-Ab A = right-unit-law-Group (group-Ab A)

has-negatives-Ab :
  {l : Level} (A : Ab l) → is-group' (semi-group-Ab A) (has-zero-Ab A)
has-negatives-Ab A = has-inverses-Group (group-Ab A)

neg-Ab :
  {l : Level} (A : Ab l) → type-Ab A → type-Ab A
neg-Ab A = inv-Group (group-Ab A)

left-negative-law-Ab :
  {l : Level} (A : Ab l) (x : type-Ab A) →
  Id (add-Ab A (neg-Ab A x) x) (zero-Ab A)
left-negative-law-Ab A = left-inverse-law-Group (group-Ab A)

right-negative-law-Ab :
  {l : Level} (A : Ab l) (x : type-Ab A) →
  Id (add-Ab A x (neg-Ab A x)) (zero-Ab A)
right-negative-law-Ab A = right-inverse-law-Group (group-Ab A)

is-commutative-add-Ab :
  {l : Level} (A : Ab l) (x y : type-Ab A) →
  Id (add-Ab A x y) (add-Ab A y x)
is-commutative-add-Ab A = pr2 A

{- So far the basic interface of abelian groups. -}

is-prop-is-abelian-Group :
  {l : Level} (G : Group l) → is-prop (is-abelian-Group G)
is-prop-is-abelian-Group G =
  is-prop-Π (λ x → is-prop-Π (λ y → is-set-type-Group G _ _))

{- Homomorphisms of abelian groups -}

preserves-add :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  (type-Ab A → type-Ab B) → UU (l1 ⊔ l2)
preserves-add A B = preserves-mul (semi-group-Ab A) (semi-group-Ab B)

hom-Ab :
  {l1 l2 : Level} → Ab l1 → Ab l2 → UU (l1 ⊔ l2)
hom-Ab A B = hom-Group (group-Ab A) (group-Ab B)

map-hom-Ab :
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  hom-Ab A B → type-Ab A → type-Ab B
map-hom-Ab A B = map-hom-Group (group-Ab A) (group-Ab B)

preserves-add-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  ( f : hom-Ab A B) → preserves-add A B (map-hom-Ab A B f)
preserves-add-Ab A B f = preserves-mul-hom-Group (group-Ab A) (group-Ab B) f

{- We characterize the identity type of the abelian group homomorphisms. -}

htpy-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f g : hom-Ab A B) → UU (l1 ⊔ l2)
htpy-hom-Ab A B f g = htpy-hom-Group (group-Ab A) (group-Ab B) f g

reflexive-htpy-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  ( f : hom-Ab A B) → htpy-hom-Ab A B f f
reflexive-htpy-hom-Ab A B f =
  reflexive-htpy-hom-Group (group-Ab A) (group-Ab B) f

htpy-hom-Ab-eq :
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  (f g : hom-Ab A B) → Id f g → htpy-hom-Ab A B f g
htpy-hom-Ab-eq A B f g = htpy-hom-Group-eq (group-Ab A) (group-Ab B) f g

abstract
  is-contr-total-htpy-hom-Ab :
    { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
    ( f : hom-Ab A B) →
    is-contr (Σ (hom-Ab A B) (htpy-hom-Ab A B f))
  is-contr-total-htpy-hom-Ab A B f =
    is-contr-total-htpy-hom-Group (group-Ab A) (group-Ab B) f

abstract
  is-equiv-htpy-hom-Ab-eq :
    { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
    ( f g : hom-Ab A B) → is-equiv (htpy-hom-Ab-eq A B f g)
  is-equiv-htpy-hom-Ab-eq A B f g =
    is-equiv-htpy-hom-Group-eq (group-Ab A) (group-Ab B) f g

eq-htpy-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  { f g : hom-Ab A B} → htpy-hom-Ab A B f g → Id f g
eq-htpy-hom-Ab A B =
  eq-htpy-hom-Group (group-Ab A) (group-Ab B)

is-set-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  is-set (hom-Ab A B)
is-set-hom-Ab A B = is-set-hom-Group (group-Ab A) (group-Ab B)

preserves-add-id :
  {l : Level} (A : Ab l) → preserves-add A A id
preserves-add-id A = preserves-mul-id (semi-group-Ab A)

id-hom-Ab :
  { l1 : Level} (A : Ab l1) → hom-Ab A A
id-hom-Ab A = id-Group (group-Ab A)

comp-hom-Ab :
  { l1 l2 l3 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3) →
  ( hom-Ab B C) → (hom-Ab A B) → (hom-Ab A C)
comp-hom-Ab A B C =
  comp-Group (group-Ab A) (group-Ab B) (group-Ab C)

is-associative-comp-hom-Ab :
  { l1 l2 l3 l4 : Level} (A : Ab l1) (B : Ab l2) (C : Ab l3) (D : Ab l4) →
  ( h : hom-Ab C D) (g : hom-Ab B C) (f : hom-Ab A B) →
  Id (comp-hom-Ab A B D (comp-hom-Ab B C D h g) f)
     (comp-hom-Ab A C D h (comp-hom-Ab A B C g f))
is-associative-comp-hom-Ab A B C D =
  associative-Semi-Group
    ( semi-group-Ab A)
    ( semi-group-Ab B)
    ( semi-group-Ab C)
    ( semi-group-Ab D)

left-unit-law-comp-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f : hom-Ab A B) → Id (comp-hom-Ab A B B (id-hom-Ab B) f) f
left-unit-law-comp-hom-Ab A B =
  left-unit-law-Semi-Group (semi-group-Ab A) (semi-group-Ab B)

right-unit-law-comp-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2)
  ( f : hom-Ab A B) → Id (comp-hom-Ab A A B f (id-hom-Ab A)) f
right-unit-law-comp-hom-Ab A B =
  right-unit-law-Semi-Group (semi-group-Ab A) (semi-group-Ab B)

{- Isomorphisms of abelian groups -}

is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  ( f : hom-Ab A B) → UU (l1 ⊔ l2)
is-iso-hom-Ab A B =
  is-iso-hom-Semi-Group (semi-group-Ab A) (semi-group-Ab B)

inv-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : hom-Ab A B) →
  is-iso-hom-Ab A B f → hom-Ab B A
inv-is-iso-hom-Ab A B f = pr1

map-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : hom-Ab A B) →
  is-iso-hom-Ab A B f → type-Ab B → type-Ab A
map-inv-is-iso-hom-Ab A B f is-iso-f =
  map-hom-Ab B A (inv-is-iso-hom-Ab A B f is-iso-f)

is-sec-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : hom-Ab A B) →
  ( is-iso-f : is-iso-hom-Ab A B f) →
  Id (comp-hom-Ab B A B f (inv-is-iso-hom-Ab A B f is-iso-f)) (id-hom-Ab B)
is-sec-inv-is-iso-hom-Ab A B f is-iso-f = pr1 (pr2 is-iso-f)

is-sec-map-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : hom-Ab A B) →
  ( is-iso-f : is-iso-hom-Ab A B f) →
  ( (map-hom-Ab A B f) ∘ (map-hom-Ab B A (inv-is-iso-hom-Ab A B f is-iso-f))) ~
  id
is-sec-map-inv-is-iso-hom-Ab A B f is-iso-f =
  htpy-hom-Ab-eq B B
    ( comp-hom-Ab B A B f (inv-is-iso-hom-Ab A B f is-iso-f))
    ( id-hom-Ab B)
    ( is-sec-inv-is-iso-hom-Ab A B f is-iso-f)

is-retr-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : hom-Ab A B) →
  ( is-iso-f : is-iso-hom-Ab A B f) →
  Id (comp-hom-Ab A B A (inv-is-iso-hom-Ab A B f is-iso-f) f) (id-hom-Ab A)
is-retr-inv-is-iso-hom-Ab A B f is-iso-f = pr2 (pr2 is-iso-f)

is-retr-map-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : hom-Ab A B) →
  ( is-iso-f : is-iso-hom-Ab A B f) →
  ( (map-inv-is-iso-hom-Ab A B f is-iso-f) ∘ (map-hom-Ab A B f)) ~ id
is-retr-map-inv-is-iso-hom-Ab A B f is-iso-f =
  htpy-hom-Ab-eq A A
    ( comp-hom-Ab A B A (inv-is-iso-hom-Ab A B f is-iso-f) f)
    ( id-hom-Ab A)
    ( is-retr-inv-is-iso-hom-Ab A B f is-iso-f)

is-prop-is-iso-hom-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : hom-Ab A B) →
  is-prop (is-iso-hom-Ab A B f)
is-prop-is-iso-hom-Ab A B f =
  is-prop-is-iso-hom-Semi-Group (semi-group-Ab A) (semi-group-Ab B) f

iso-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) → UU (l1 ⊔ l2)
iso-Ab A B = Σ (hom-Ab A B) (is-iso-hom-Ab A B)

hom-iso-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  iso-Ab A B → hom-Ab A B
hom-iso-Ab A B = pr1

is-iso-hom-iso-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  ( f : iso-Ab A B) → is-iso-hom-Ab A B (hom-iso-Ab A B f)
is-iso-hom-iso-Ab A B = pr2

inv-hom-iso-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) →
  iso-Ab A B → hom-Ab B A
inv-hom-iso-Ab A B f =
  inv-is-iso-hom-Ab A B
    ( hom-iso-Ab A B f)
    ( is-iso-hom-iso-Ab A B f)

id-iso-Ab :
  {l1 : Level} (A : Ab l1) → iso-Ab A A
id-iso-Ab A = iso-id-Group (group-Ab A)

iso-eq-Ab :
  { l1 : Level} (A B : Ab l1) → Id A B → iso-Ab A B
iso-eq-Ab A .A refl = id-iso-Ab A

abstract
  equiv-iso-eq-Ab' :
    {l1 : Level} (A B : Ab l1) → Id A B ≃ iso-Ab A B
  equiv-iso-eq-Ab' A B =
    ( equiv-iso-eq-Group' (group-Ab A) (group-Ab B)) ∘e
    ( equiv-ap-pr1-is-subtype is-prop-is-abelian-Group {A} {B})

abstract
  is-contr-total-iso-Ab :
    { l1 : Level} (A : Ab l1) → is-contr (Σ (Ab l1) (iso-Ab A))
  is-contr-total-iso-Ab {l1} A =
    is-contr-equiv'
      ( Σ (Ab l1) (Id A))
      ( equiv-tot (equiv-iso-eq-Ab' A))
      ( is-contr-total-path A)

is-equiv-iso-eq-Ab :
  { l1 : Level} (A B : Ab l1) → is-equiv (iso-eq-Ab A B)
is-equiv-iso-eq-Ab A =
  fundamental-theorem-id A
    ( id-iso-Ab A)
    ( is-contr-total-iso-Ab A)
    ( iso-eq-Ab A)

eq-iso-Ab :
  { l1 : Level} (A B : Ab l1) → iso-Ab A B → Id A B
eq-iso-Ab A B = inv-is-equiv (is-equiv-iso-eq-Ab A B)
