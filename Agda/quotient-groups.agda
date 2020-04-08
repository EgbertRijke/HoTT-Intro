{-# OPTIONS --without-K --exact-split #-}

module quotient-groups where

import subgroups
open subgroups public

{- The left and right coset relation -}

left-coset-relation :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  (x y : type-Group G) → UU (l1 ⊔ l2)
left-coset-relation G H x y =
  Σ ( type-group-Subgroup G H)
    ( λ z → Id (mul-Group G x (incl-group-Subgroup G H z)) y)

right-coset-relation :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  (x y : type-Group G) → UU (l1 ⊔ l2)
right-coset-relation G H x y =
  Σ ( type-group-Subgroup G H)
    ( λ z → Id (mul-Group G (incl-group-Subgroup G H z) x) y)

{- We show that the left coset relation is an equivalence relation -}

is-reflexive-left-coset-relation :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  (x : type-Group G) → left-coset-relation G H x x
is-reflexive-left-coset-relation G H x =
  pair ( unit-group-Subgroup G H)
       ( right-unit-law-Group G x)

is-symmetric-left-coset-relation :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  (x y : type-Group G) →
  left-coset-relation G H x y → left-coset-relation G H y x
is-symmetric-left-coset-relation G H x y (pair z p) =
  pair ( inv-group-Subgroup G H z)
       (  ap ( λ t → mul-Group G t
                      ( incl-group-Subgroup G H
                        ( inv-group-Subgroup G H z)))
             ( inv p) ∙
         ( ( is-associative-mul-Group G _ _ _) ∙
           ( ( ap (mul-Group G x) (right-inverse-law-Group G _)) ∙
             ( right-unit-law-Group G x))))

is-transitive-left-coset-relation :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  (x y z : type-Group G) →
  left-coset-relation G H x y → left-coset-relation G H y z →
  left-coset-relation G H x z
is-transitive-left-coset-relation G H x y z (pair h1 p1) (pair h2 p2) =
  pair ( mul-group-Subgroup G H h1 h2)
       ( ( inv (is-associative-mul-Group G _ _ _)) ∙
         ( ( ap (λ t → mul-Group G t (incl-group-Subgroup G H h2)) p1) ∙ p2))

{- We show that the right coset relation is an equivalence relation -}

is-reflexive-right-coset-relation :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  (x : type-Group G) → right-coset-relation G H x x
is-reflexive-right-coset-relation G H x =
  pair ( unit-group-Subgroup G H)
       ( left-unit-law-Group G x)

is-symmetric-right-coset-relation :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  (x y : type-Group G) →
  right-coset-relation G H x y → right-coset-relation G H y x
is-symmetric-right-coset-relation G H x y (pair z p) =
  pair ( inv-group-Subgroup G H z)
       ( ( ap
           ( mul-Group G (incl-group-Subgroup G H (inv-group-Subgroup G H z)))
           ( inv p)) ∙
         ( ( inv (is-associative-mul-Group G _ _ _)) ∙
           ( ( ap (λ t → mul-Group G t x) (left-inverse-law-Group G _)) ∙
             ( left-unit-law-Group G x))))

is-transitive-right-coset-relation :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  (x y z : type-Group G) →
  right-coset-relation G H x y → right-coset-relation G H y z →
  right-coset-relation G H x z
is-transitive-right-coset-relation G H x y z (pair h1 p1) (pair h2 p2) =
  pair ( mul-group-Subgroup G H h2 h1)
       ( ( is-associative-mul-Group G _ _ _) ∙
         ( ( ap (mul-Group G (incl-group-Subgroup G H h2)) p1) ∙ p2))
