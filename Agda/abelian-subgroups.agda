{-# OPTIONS --without-K --exact-split #-}

module abelian-subgroups where

import abelian-groups
import subgroups
open abelian-groups public
open subgroups public

{- Subsets of abelian groups -}

subset-Ab :
  (l : Level) {l1 : Level} (A : Ab l1) → UU ((lsuc l) ⊔ l1)
subset-Ab l A = subset-Group l (group-Ab A)

is-set-subset-Ab :
  (l : Level) {l1 : Level} (A : Ab l1) → is-set (subset-Ab l A)
is-set-subset-Ab l A = is-set-subset-Group l (group-Ab A)

{- Defining subgroups -}

contains-zero-subset-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : subset-Ab l2 A) → UU l2
contains-zero-subset-Ab A = contains-unit-subset-Group (group-Ab A)

is-prop-contains-zero-subset-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : subset-Ab l2 A) →
  is-prop (contains-zero-subset-Ab A P)
is-prop-contains-zero-subset-Ab A =
  is-prop-contains-unit-subset-Group (group-Ab A)

closed-under-add-subset-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : subset-Ab l2 A) → UU (l1 ⊔ l2)
closed-under-add-subset-Ab A =
  closed-under-mul-subset-Group (group-Ab A)

is-prop-closed-under-add-subset-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : subset-Ab l2 A) →
  is-prop (closed-under-add-subset-Ab A P)
is-prop-closed-under-add-subset-Ab A =
  is-prop-closed-under-mul-subset-Group (group-Ab A)

closed-under-neg-subset-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : subset-Ab l2 A) → UU (l1 ⊔ l2)
closed-under-neg-subset-Ab A =
  closed-under-inv-subset-Group (group-Ab A)

is-prop-closed-under-neg-subset-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : subset-Ab l2 A) →
  is-prop (closed-under-neg-subset-Ab A P)
is-prop-closed-under-neg-subset-Ab A =
  is-prop-closed-under-inv-subset-Group (group-Ab A)
  
is-subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : subset-Ab l2 A) → UU (l1 ⊔ l2)
is-subgroup-Ab A = is-subgroup-Group (group-Ab A)

is-prop-is-subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : subset-Ab l2 A) →
  is-prop (is-subgroup-Ab A P)
is-prop-is-subgroup-Ab A = is-prop-is-subgroup-Group (group-Ab A)

{- Introducing the type of all subgroups of a group G -}

Subgroup-Ab :
  (l : Level) {l1 : Level} (A : Ab l1) → UU ((lsuc l) ⊔ l1)
Subgroup-Ab l A = Subgroup l (group-Ab A)

subset-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) →
  ( Subgroup-Ab l2 A) → ( subset-Ab l2 A)
subset-Subgroup-Ab A = subset-Subgroup (group-Ab A)

is-emb-subset-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) → is-emb (subset-Subgroup-Ab {l2 = l2} A)
is-emb-subset-Subgroup-Ab A = is-emb-subset-Subgroup (group-Ab A)

type-subset-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  (type-Ab A → UU l2)
type-subset-Subgroup-Ab A = type-subset-Subgroup (group-Ab A)

is-prop-type-subset-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  (x : type-Ab A) → is-prop (type-subset-Subgroup-Ab A P x)
is-prop-type-subset-Subgroup-Ab A =
  is-prop-type-subset-Subgroup (group-Ab A)

is-subgroup-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  is-subgroup-Ab A (subset-Subgroup-Ab A P)
is-subgroup-Subgroup-Ab A = is-subgroup-Subgroup (group-Ab A)

contains-zero-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  contains-zero-subset-Ab A (subset-Subgroup-Ab A P)
contains-zero-Subgroup-Ab A = contains-unit-Subgroup (group-Ab A)

closed-under-add-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  closed-under-add-subset-Ab A (subset-Subgroup-Ab A P)
closed-under-add-Subgroup-Ab A = closed-under-mul-Subgroup (group-Ab A)

closed-under-neg-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  closed-under-neg-subset-Ab A (subset-Subgroup-Ab A P)
closed-under-neg-Subgroup-Ab A = closed-under-inv-Subgroup (group-Ab A)

{- Given a subgroup of an abelian group, we construct an abelian group -}

type-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) → UU (l1 ⊔ l2)
type-ab-Subgroup-Ab A =  type-group-Subgroup (group-Ab A)

incl-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  type-ab-Subgroup-Ab A P → type-Ab A
incl-ab-Subgroup-Ab A = incl-group-Subgroup (group-Ab A)

is-emb-incl-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  is-emb (incl-ab-Subgroup-Ab A P)
is-emb-incl-ab-Subgroup-Ab A = is-emb-incl-group-Subgroup (group-Ab A)

eq-subgroup-ab-eq-ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  {x y : type-ab-Subgroup-Ab A P} →
  Id (incl-ab-Subgroup-Ab A P x) (incl-ab-Subgroup-Ab A P y) → Id x y
eq-subgroup-ab-eq-ab A =
  eq-subgroup-eq-group (group-Ab A)

set-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) → Subgroup-Ab l2 A → UU-Set (l1 ⊔ l2)
set-ab-Subgroup-Ab A = set-group-Subgroup (group-Ab A)

zero-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) → type-ab-Subgroup-Ab A P
zero-ab-Subgroup-Ab A = unit-group-Subgroup (group-Ab A)

add-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  ( x y : type-ab-Subgroup-Ab A P) → type-ab-Subgroup-Ab A P
add-ab-Subgroup-Ab A = mul-group-Subgroup (group-Ab A)

neg-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  type-ab-Subgroup-Ab A P → type-ab-Subgroup-Ab A P
neg-ab-Subgroup-Ab A = inv-group-Subgroup (group-Ab A)

is-associative-add-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  ( x y z : type-ab-Subgroup-Ab A P) →
  Id (add-ab-Subgroup-Ab A P (add-ab-Subgroup-Ab A P x y) z)
     (add-ab-Subgroup-Ab A P x (add-ab-Subgroup-Ab A P y z))
is-associative-add-ab-Subgroup-Ab A =
  is-associative-mul-group-Subgroup (group-Ab A)

left-zero-law-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  ( x : type-ab-Subgroup-Ab A P) →
  Id (add-ab-Subgroup-Ab A P (zero-ab-Subgroup-Ab A P) x) x
left-zero-law-ab-Subgroup-Ab A =
  left-unit-law-group-Subgroup (group-Ab A)

right-zero-law-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  ( x : type-ab-Subgroup-Ab A P) →
  Id (add-ab-Subgroup-Ab A P x (zero-ab-Subgroup-Ab A P)) x
right-zero-law-ab-Subgroup-Ab A =
  right-unit-law-group-Subgroup (group-Ab A)

left-neg-law-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  ( x : type-ab-Subgroup-Ab A P) →
  Id ( add-ab-Subgroup-Ab A P (neg-ab-Subgroup-Ab A P x) x)
     ( zero-ab-Subgroup-Ab A P)
left-neg-law-ab-Subgroup-Ab A =
  left-inverse-law-group-Subgroup (group-Ab A)

right-neg-law-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  ( x : type-ab-Subgroup-Ab A P) →
  Id ( add-ab-Subgroup-Ab A P x (neg-ab-Subgroup-Ab A P x))
     ( zero-ab-Subgroup-Ab A P)
right-neg-law-ab-Subgroup-Ab A = right-inverse-law-group-Subgroup (group-Ab A)

is-commutative-add-ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  ( x y : type-ab-Subgroup-Ab A P) →
  Id ( add-ab-Subgroup-Ab A P x y) (add-ab-Subgroup-Ab A P y x)
is-commutative-add-ab-Subgroup-Ab A P (pair x p) (pair y q) =
  eq-subgroup-ab-eq-ab A P (is-commutative-add-Ab A x y)

ab-Subgroup-Ab :
  {l1 l2 : Level} (A : Ab l1) → Subgroup-Ab l2 A → Ab (l1 ⊔ l2)
ab-Subgroup-Ab A P =
  pair
    (group-Subgroup (group-Ab A) P) (is-commutative-add-ab-Subgroup-Ab A P)

{- We show that the inclusion from ab-Subgroup-Ab A P → A is a group 
   homomorphism -}

preserves-add-incl-ab-Subgroup-Ab :
  { l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  preserves-add (ab-Subgroup-Ab A P) A (incl-ab-Subgroup-Ab A P)
preserves-add-incl-ab-Subgroup-Ab A =
  preserves-mul-incl-group-Subgroup (group-Ab A)

hom-ab-Subgroup-Ab :
  { l1 l2 : Level} (A : Ab l1) (P : Subgroup-Ab l2 A) →
  hom-Ab (ab-Subgroup-Ab A P) A
hom-ab-Subgroup-Ab A = hom-group-Subgroup (group-Ab A)

{- We define another type of subgroups of A as the type of group inclusions -}

emb-Ab :
  { l1 l2 : Level} (A : Ab l1) (B : Ab l2) → UU (l1 ⊔ l2)
emb-Ab A B = emb-Group (group-Ab A) (group-Ab B)

emb-Ab-Slice :
  (l : Level) {l1 : Level} (A : Ab l1) → UU ((lsuc l) ⊔ l1)
emb-Ab-Slice l A = emb-Group-Slice l (group-Ab A)

emb-ab-slice-Subgroup-Ab :
  { l1 l2 : Level} (A : Ab l1) →
  Subgroup-Ab l2 A → emb-Ab-Slice (l1 ⊔ l2) A
emb-ab-slice-Subgroup-Ab A = emb-group-slice-Subgroup (group-Ab A)
