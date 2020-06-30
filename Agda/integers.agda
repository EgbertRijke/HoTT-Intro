{-# OPTIONS --without-K --exact-split #-}

module integers where

import rings-with-properties
open rings-with-properties public

--------------------------------------------------------------------------------

{- We give a self-contained proof that ℤ is the initial pointed type with an
   automorphism. -}

-- We first introduce the type of pointed types with an automorphism

UU-Pointed-Type-With-Aut :
  (l : Level) → UU (lsuc l)
UU-Pointed-Type-With-Aut l =
  Σ (UU l) (λ X → X × (X ≃ X))

-- Some trivial bureaucracy for the type of pointed types with an automorphism

type-Pointed-Type-With-Aut :
  {l : Level} → UU-Pointed-Type-With-Aut l → UU l
type-Pointed-Type-With-Aut X = pr1 X

point-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) → type-Pointed-Type-With-Aut X
point-Pointed-Type-With-Aut X = pr1 (pr2 X)

aut-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  type-Pointed-Type-With-Aut X ≃ type-Pointed-Type-With-Aut X
aut-Pointed-Type-With-Aut X = pr2 (pr2 X)

map-aut-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  type-Pointed-Type-With-Aut X → type-Pointed-Type-With-Aut X
map-aut-Pointed-Type-With-Aut X =
  map-equiv (aut-Pointed-Type-With-Aut X)

inv-map-aut-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  type-Pointed-Type-With-Aut X → type-Pointed-Type-With-Aut X
inv-map-aut-Pointed-Type-With-Aut X =
  inv-map-equiv (aut-Pointed-Type-With-Aut X)

issec-inv-map-aut-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  ((map-aut-Pointed-Type-With-Aut X) ∘ (inv-map-aut-Pointed-Type-With-Aut X))
  ~ id
issec-inv-map-aut-Pointed-Type-With-Aut X =
  issec-inv-map-equiv (aut-Pointed-Type-With-Aut X)

isretr-inv-map-aut-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  ((inv-map-aut-Pointed-Type-With-Aut X) ∘ (map-aut-Pointed-Type-With-Aut X))
  ~ id
isretr-inv-map-aut-Pointed-Type-With-Aut X =
  isretr-inv-map-equiv (aut-Pointed-Type-With-Aut X)

-- ℤ is a pointed type with an automorphism

ℤ-Pointed-Type-With-Aut : UU-Pointed-Type-With-Aut lzero
ℤ-Pointed-Type-With-Aut =
  pair ℤ (pair zero-ℤ equiv-succ-ℤ)

-- We introduce the type of morphisms of pointed types with an automorphism

hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} →
  UU-Pointed-Type-With-Aut l1 → UU-Pointed-Type-With-Aut l2 → UU (l1 ⊔ l2)
hom-Pointed-Type-With-Aut {l1} {l2} X Y =
  Σ ( type-Pointed-Type-With-Aut X → type-Pointed-Type-With-Aut Y)
    ( λ f →
      Id (f (point-Pointed-Type-With-Aut X)) (point-Pointed-Type-With-Aut Y)
      ×
      ( ( f ∘ (map-aut-Pointed-Type-With-Aut X)) ~
        ( (map-aut-Pointed-Type-With-Aut Y) ∘ f)))

-- Some trivial bureaucracy about morphisms of pointed types with an
-- automorphism

map-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) → hom-Pointed-Type-With-Aut X Y →
  type-Pointed-Type-With-Aut X → type-Pointed-Type-With-Aut Y
map-hom-Pointed-Type-With-Aut X Y f = pr1 f

preserves-point-map-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (f : hom-Pointed-Type-With-Aut X Y) →
  Id ( map-hom-Pointed-Type-With-Aut X Y f (point-Pointed-Type-With-Aut X))
     ( point-Pointed-Type-With-Aut Y)
preserves-point-map-hom-Pointed-Type-With-Aut X Y f = pr1 (pr2 f)

preserves-aut-map-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (f : hom-Pointed-Type-With-Aut X Y) →
  ( ( map-hom-Pointed-Type-With-Aut X Y f) ∘ (map-aut-Pointed-Type-With-Aut X))
    ~
  ( ( map-aut-Pointed-Type-With-Aut Y) ∘ (map-hom-Pointed-Type-With-Aut X Y f))
preserves-aut-map-hom-Pointed-Type-With-Aut X Y f = pr2 (pr2 f)

-- We characterize the identity type of hom-Pointed-Type-With-Aut

htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (h1 h2 : hom-Pointed-Type-With-Aut X Y) →
  UU (l1 ⊔ l2)
htpy-hom-Pointed-Type-With-Aut X Y h1 h2 =
  Σ ( map-hom-Pointed-Type-With-Aut X Y h1
      ~ map-hom-Pointed-Type-With-Aut X Y h2)
    ( λ H →
      ( Id ( preserves-point-map-hom-Pointed-Type-With-Aut X Y h1)
           ( ( H (point-Pointed-Type-With-Aut X)) ∙
             ( preserves-point-map-hom-Pointed-Type-With-Aut X Y h2)))
      ×
      ( ( x : type-Pointed-Type-With-Aut X) →
        ( Id ( ( preserves-aut-map-hom-Pointed-Type-With-Aut X Y h1 x) ∙
               ( ap (map-aut-Pointed-Type-With-Aut Y) (H x)))
             ( ( H (map-aut-Pointed-Type-With-Aut X x)) ∙
               ( preserves-aut-map-hom-Pointed-Type-With-Aut X Y h2 x)))))

refl-htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (h : hom-Pointed-Type-With-Aut X Y) →
  htpy-hom-Pointed-Type-With-Aut X Y h h
refl-htpy-hom-Pointed-Type-With-Aut X Y h =
  pair refl-htpy (pair refl (λ x → right-unit))

htpy-hom-Pointed-Type-With-Aut-eq :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (h1 h2 : hom-Pointed-Type-With-Aut X Y) →
  Id h1 h2 → htpy-hom-Pointed-Type-With-Aut X Y h1 h2
htpy-hom-Pointed-Type-With-Aut-eq X Y h1 .h1 refl =
  refl-htpy-hom-Pointed-Type-With-Aut X Y h1

-- This is the meat of the characterization of the type of morphisms of pointed
-- types with an equivalence. The only hard part is feeding the families
-- explicitly to Agda over and over again, because Agda is apparently not that
-- good at figuring out what the correct family is.

is-contr-total-htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (h1 : hom-Pointed-Type-With-Aut X Y) →
  is-contr
    ( Σ ( hom-Pointed-Type-With-Aut X Y)
        ( htpy-hom-Pointed-Type-With-Aut X Y h1))
is-contr-total-htpy-hom-Pointed-Type-With-Aut X Y h1 =
  is-contr-total-Eq-structure
    ( λ ( map-h2 : type-Pointed-Type-With-Aut X → type-Pointed-Type-With-Aut Y)
        ( str-h2 : ( Id ( map-h2 (point-Pointed-Type-With-Aut X))
                        ( point-Pointed-Type-With-Aut Y)) ×
                   ( ( x : type-Pointed-Type-With-Aut X) →
                     Id ( map-h2 (map-aut-Pointed-Type-With-Aut X x))
                        ( map-aut-Pointed-Type-With-Aut Y (map-h2 x))))
        ( H : map-hom-Pointed-Type-With-Aut X Y h1 ~ map-h2)
      → ( Id ( preserves-point-map-hom-Pointed-Type-With-Aut X Y h1)
             ( ( H (point-Pointed-Type-With-Aut X)) ∙
               ( pr1 str-h2)))
        ×
        ( ( x : type-Pointed-Type-With-Aut X) →
          ( Id ( ( preserves-aut-map-hom-Pointed-Type-With-Aut X Y h1 x) ∙
                 ( ap (map-aut-Pointed-Type-With-Aut Y) (H x)))
               ( ( H (map-aut-Pointed-Type-With-Aut X x)) ∙
                 ( pr2 str-h2 x)))))
    ( is-contr-total-htpy (map-hom-Pointed-Type-With-Aut X Y h1))
    ( pair (map-hom-Pointed-Type-With-Aut X Y h1) refl-htpy)
    ( is-contr-total-Eq-structure
      ( λ ( pt-h2 : Id ( map-hom-Pointed-Type-With-Aut X Y h1
                         ( point-Pointed-Type-With-Aut X))
                       ( point-Pointed-Type-With-Aut Y))
          ( aut-h2 : ( x : type-Pointed-Type-With-Aut X) →
                     Id ( map-hom-Pointed-Type-With-Aut X Y h1
                          ( map-aut-Pointed-Type-With-Aut X x))
                        ( map-aut-Pointed-Type-With-Aut Y
                          ( map-hom-Pointed-Type-With-Aut X Y h1 x)))
          ( α : Id ( preserves-point-map-hom-Pointed-Type-With-Aut X Y h1)
                   ( pt-h2))
        → ( ( x : type-Pointed-Type-With-Aut X) →
            Id ( ( preserves-aut-map-hom-Pointed-Type-With-Aut X Y h1 x) ∙
                 ( refl))
               ( aut-h2 x)))
      ( is-contr-total-path
        ( preserves-point-map-hom-Pointed-Type-With-Aut X Y h1))
      ( pair (preserves-point-map-hom-Pointed-Type-With-Aut X Y h1) refl)
      ( is-contr-equiv'
        ( Σ ( ( x : type-Pointed-Type-With-Aut X) →
              Id ( map-hom-Pointed-Type-With-Aut X Y h1
                   ( map-aut-Pointed-Type-With-Aut X x))
                 ( map-aut-Pointed-Type-With-Aut Y
                   ( map-hom-Pointed-Type-With-Aut X Y h1 x)))
            ( λ aut-h2 →
              ( x : type-Pointed-Type-With-Aut X) →
              Id ( preserves-aut-map-hom-Pointed-Type-With-Aut X Y h1 x)
                 ( aut-h2 x)))
        ( equiv-tot (equiv-htpy-concat htpy-right-unit))
        ( is-contr-total-htpy
          ( preserves-aut-map-hom-Pointed-Type-With-Aut X Y h1))))

-- We complete the characterization of the identity type of the type of
-- morphisms of types with a point and an automorphism

is-equiv-htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (h1 h2 : hom-Pointed-Type-With-Aut X Y) →
  is-equiv (htpy-hom-Pointed-Type-With-Aut-eq X Y h1 h2)
is-equiv-htpy-hom-Pointed-Type-With-Aut X Y h1 =
  fundamental-theorem-id h1
    ( refl-htpy-hom-Pointed-Type-With-Aut X Y h1)
    ( is-contr-total-htpy-hom-Pointed-Type-With-Aut X Y h1)
    ( htpy-hom-Pointed-Type-With-Aut-eq X Y h1)

eq-htpy-hom-Pointed-Type-With-Aut :
  {l1 l2 : Level} (X : UU-Pointed-Type-With-Aut l1)
  (Y : UU-Pointed-Type-With-Aut l2) (h1 h2 : hom-Pointed-Type-With-Aut X Y) →
  htpy-hom-Pointed-Type-With-Aut X Y h1 h2 → Id h1 h2
eq-htpy-hom-Pointed-Type-With-Aut X Y h1 h2 =
  inv-is-equiv (is-equiv-htpy-hom-Pointed-Type-With-Aut X Y h1 h2)

-- We show that from ℤ there is a morphism of pointed types with automorphism
-- to any pointed type with automorphisms

map-initial-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  ℤ → type-Pointed-Type-With-Aut X
map-initial-Pointed-Type-With-Aut X (inl zero-ℕ) =
  inv-map-aut-Pointed-Type-With-Aut X (point-Pointed-Type-With-Aut X)
map-initial-Pointed-Type-With-Aut X (inl (succ-ℕ k)) =
  inv-map-aut-Pointed-Type-With-Aut X
    ( map-initial-Pointed-Type-With-Aut X (inl k))
map-initial-Pointed-Type-With-Aut X (inr (inl star)) =
  point-Pointed-Type-With-Aut X
map-initial-Pointed-Type-With-Aut X (inr (inr zero-ℕ)) =
  map-aut-Pointed-Type-With-Aut X (point-Pointed-Type-With-Aut X)
map-initial-Pointed-Type-With-Aut X (inr (inr (succ-ℕ k))) =
  map-aut-Pointed-Type-With-Aut X
    ( map-initial-Pointed-Type-With-Aut X (inr (inr k)))

preserves-point-map-initial-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  Id ( map-initial-Pointed-Type-With-Aut X zero-ℤ)
     ( point-Pointed-Type-With-Aut X)
preserves-point-map-initial-Pointed-Type-With-Aut X = refl

preserves-aut-map-initial-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) (k : ℤ) →
  Id ( map-initial-Pointed-Type-With-Aut X (succ-ℤ k))
     ( map-aut-Pointed-Type-With-Aut X
       ( map-initial-Pointed-Type-With-Aut X k))
preserves-aut-map-initial-Pointed-Type-With-Aut X (inl zero-ℕ) =
  inv
    ( issec-inv-map-aut-Pointed-Type-With-Aut X (point-Pointed-Type-With-Aut X))
preserves-aut-map-initial-Pointed-Type-With-Aut X (inl (succ-ℕ k)) =
  inv
    ( issec-inv-map-aut-Pointed-Type-With-Aut X
      ( map-initial-Pointed-Type-With-Aut X (inl k)))
preserves-aut-map-initial-Pointed-Type-With-Aut X (inr (inl star)) =
  refl
preserves-aut-map-initial-Pointed-Type-With-Aut X (inr (inr zero-ℕ)) =
  refl
preserves-aut-map-initial-Pointed-Type-With-Aut X (inr (inr (succ-ℕ x))) =
  refl

hom-initial-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X
hom-initial-Pointed-Type-With-Aut X =
  pair
    ( map-initial-Pointed-Type-With-Aut X)
    ( pair
      ( preserves-point-map-initial-Pointed-Type-With-Aut X)
      ( preserves-aut-map-initial-Pointed-Type-With-Aut X))

-- We now show that the morphism from ℤ to a pointed type with an automorphism
-- is unique, using our characterization of the identity type of the type of
-- morphisms of pointed types with an automorphism

htpy-initial-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l)
  (h : hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X) →
  map-initial-Pointed-Type-With-Aut X ~
  map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X h
htpy-initial-Pointed-Type-With-Aut X h (inl zero-ℕ) =
  map-eq-transpose-equiv'
    ( aut-Pointed-Type-With-Aut X)
    ( ( inv
        ( preserves-point-map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut
          X h)) ∙
      ( preserves-aut-map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut
        X h neg-one-ℤ))
htpy-initial-Pointed-Type-With-Aut X h (inl (succ-ℕ k)) =
  map-eq-transpose-equiv'
    ( aut-Pointed-Type-With-Aut X)
    ( ( htpy-initial-Pointed-Type-With-Aut X h (inl k)) ∙
      ( preserves-aut-map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut
        X h (inl (succ-ℕ k))))
htpy-initial-Pointed-Type-With-Aut X h (inr (inl star)) =
  inv
    ( preserves-point-map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X h)
htpy-initial-Pointed-Type-With-Aut X h (inr (inr zero-ℕ)) =
  ( ap ( map-aut-Pointed-Type-With-Aut X)
       ( htpy-initial-Pointed-Type-With-Aut X h (inr (inl star)))) ∙
  ( inv
    ( preserves-aut-map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut
      X h (inr (inl star))))
htpy-initial-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k))) =
  ( ap ( map-aut-Pointed-Type-With-Aut X)
       ( htpy-initial-Pointed-Type-With-Aut X h (inr (inr k)))) ∙
  ( inv
    ( preserves-aut-map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut
      X h (inr (inr k))))

-- The following two steps become trivial if X is a set

coh-point-htpy-initial-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l)
  (h : hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X) →
  Id ( preserves-point-map-initial-Pointed-Type-With-Aut X)
     ( ( htpy-initial-Pointed-Type-With-Aut X h zero-ℤ) ∙
       ( preserves-point-map-hom-Pointed-Type-With-Aut
         ℤ-Pointed-Type-With-Aut X h))
coh-point-htpy-initial-Pointed-Type-With-Aut X h =
  inv
    ( left-inv
      ( preserves-point-map-hom-Pointed-Type-With-Aut
        ℤ-Pointed-Type-With-Aut X h))

coh-aut-htpy-initial-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l)
  (h : hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X)
  (k : ℤ) →
  Id ( ( preserves-aut-map-initial-Pointed-Type-With-Aut X k) ∙
       ( ap ( map-aut-Pointed-Type-With-Aut X)
            ( htpy-initial-Pointed-Type-With-Aut X h k)))
     ( ( htpy-initial-Pointed-Type-With-Aut X h (succ-ℤ k)) ∙
       ( preserves-aut-map-hom-Pointed-Type-With-Aut
         ℤ-Pointed-Type-With-Aut X h k))
coh-aut-htpy-initial-Pointed-Type-With-Aut X h (inl zero-ℕ) =
  inv
    ( inv-con
      ( issec-inv-map-equiv
        ( aut-Pointed-Type-With-Aut X)
        ( point-Pointed-Type-With-Aut X))
      ( ( htpy-initial-Pointed-Type-With-Aut X h zero-ℤ) ∙
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h neg-one-ℤ))
      ( ap ( map-equiv (aut-Pointed-Type-With-Aut X))
           ( htpy-initial-Pointed-Type-With-Aut X h neg-one-ℤ))
      ( triangle-eq-transpose-equiv'
        ( aut-Pointed-Type-With-Aut X)
        ( ( inv
            ( preserves-point-map-hom-Pointed-Type-With-Aut
              ℤ-Pointed-Type-With-Aut X h)) ∙
          ( preserves-aut-map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h neg-one-ℤ))))
coh-aut-htpy-initial-Pointed-Type-With-Aut X h (inl (succ-ℕ k)) =
  inv
    ( inv-con
      ( issec-inv-map-equiv
        ( aut-Pointed-Type-With-Aut X)
        ( map-initial-Pointed-Type-With-Aut X (inl k)))
      ( ( htpy-initial-Pointed-Type-With-Aut X h (inl k)) ∙
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h (inl (succ-ℕ k))))
      ( ap ( map-equiv (aut-Pointed-Type-With-Aut X))
           ( htpy-initial-Pointed-Type-With-Aut X h (inl (succ-ℕ k))))
      ( triangle-eq-transpose-equiv'
        ( aut-Pointed-Type-With-Aut X)
        ( ( htpy-initial-Pointed-Type-With-Aut X h (inl k)) ∙
          ( preserves-aut-map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h (inl (succ-ℕ k))))))
coh-aut-htpy-initial-Pointed-Type-With-Aut X h (inr (inl star)) =
  ( inv right-unit) ∙
  ( ( ap ( concat
           ( ap
             ( map-aut-Pointed-Type-With-Aut X)
             ( htpy-initial-Pointed-Type-With-Aut X h zero-ℤ))
           ( map-aut-Pointed-Type-With-Aut X
             ( map-hom-Pointed-Type-With-Aut
               ℤ-Pointed-Type-With-Aut X h zero-ℤ)))
         ( inv (left-inv
           ( preserves-aut-map-hom-Pointed-Type-With-Aut
             ℤ-Pointed-Type-With-Aut X h zero-ℤ)))) ∙
    ( inv
      ( assoc
        ( ap
          ( map-aut-Pointed-Type-With-Aut X)
          ( htpy-initial-Pointed-Type-With-Aut X h zero-ℤ))
        ( inv
          ( preserves-aut-map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h zero-ℤ))
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h zero-ℤ))))
coh-aut-htpy-initial-Pointed-Type-With-Aut X h (inr (inr zero-ℕ)) =
  ( inv right-unit) ∙
  ( ( ap ( concat
           ( ap
             ( map-aut-Pointed-Type-With-Aut X)
             ( htpy-initial-Pointed-Type-With-Aut X h one-ℤ))
           ( map-aut-Pointed-Type-With-Aut X
             ( map-hom-Pointed-Type-With-Aut
               ℤ-Pointed-Type-With-Aut X h one-ℤ)))
         ( inv (left-inv
           ( preserves-aut-map-hom-Pointed-Type-With-Aut
             ℤ-Pointed-Type-With-Aut X h one-ℤ)))) ∙
    ( inv
      ( assoc
        ( ap
          ( map-aut-Pointed-Type-With-Aut X)
          ( htpy-initial-Pointed-Type-With-Aut X h one-ℤ))
        ( inv
          ( preserves-aut-map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h one-ℤ))
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h one-ℤ))))
coh-aut-htpy-initial-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k))) =
  ( inv right-unit) ∙
  ( ( ap ( concat
           ( ap
             ( map-aut-Pointed-Type-With-Aut X)
             ( htpy-initial-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k)))))
           ( map-aut-Pointed-Type-With-Aut X
             ( map-hom-Pointed-Type-With-Aut
               ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k))))))
         ( inv (left-inv
           ( preserves-aut-map-hom-Pointed-Type-With-Aut
             ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k))))))) ∙
    ( inv
      ( assoc
        ( ap
          ( map-aut-Pointed-Type-With-Aut X)
          ( htpy-initial-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k)))))
        ( inv
          ( preserves-aut-map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k)))))
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k)))))))

is-initial-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : UU-Pointed-Type-With-Aut l) →
  is-contr (hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X)
is-initial-ℤ-Pointed-Type-With-Aut X =
  pair
    ( hom-initial-Pointed-Type-With-Aut X)
    ( λ h →
      eq-htpy-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X
        ( hom-initial-Pointed-Type-With-Aut X)
        ( h)
        ( pair
          ( htpy-initial-Pointed-Type-With-Aut X h)
          ( pair
            ( coh-point-htpy-initial-Pointed-Type-With-Aut X h)
            ( coh-aut-htpy-initial-Pointed-Type-With-Aut X h))))

--------------------------------------------------------------------------------

{- We exhibit ℤ as an abelian group, and as a ring. -}

add-ℤ-Semi-Group : Semi-Group lzero
add-ℤ-Semi-Group = pair ℤ-Set (pair add-ℤ associative-add-ℤ)

is-unital-add-ℤ-Semi-Group : is-unital add-ℤ-Semi-Group
is-unital-add-ℤ-Semi-Group = pair zero-ℤ (pair left-unit-law-add-ℤ right-unit-law-add-ℤ)

add-ℤ-Monoid : Monoid lzero
add-ℤ-Monoid = pair add-ℤ-Semi-Group is-unital-add-ℤ-Semi-Group

has-inverses-add-ℤ-Monoid : is-group' add-ℤ-Semi-Group is-unital-add-ℤ-Semi-Group
has-inverses-add-ℤ-Monoid = pair neg-ℤ (pair left-inverse-law-add-ℤ right-inverse-law-add-ℤ)

is-group-add-ℤ-Semi-Group : is-group add-ℤ-Semi-Group
is-group-add-ℤ-Semi-Group = pair is-unital-add-ℤ-Semi-Group has-inverses-add-ℤ-Monoid

ℤ-Group : Group lzero
ℤ-Group = pair add-ℤ-Semi-Group is-group-add-ℤ-Semi-Group

ℤ-Ab : Ab lzero
ℤ-Ab = pair ℤ-Group commutative-add-ℤ

has-mul-ℤ-Ab : has-mul-Ab ℤ-Ab
has-mul-ℤ-Ab =
  pair
    ( pair mul-ℤ associative-mul-ℤ)
    ( pair
      ( pair one-ℤ (pair left-unit-law-mul-ℤ right-unit-law-mul-ℤ))
      ( pair left-distributive-mul-add-ℤ right-distributive-mul-add-ℤ))

ℤ-Ring : Ring lzero
ℤ-Ring = pair ℤ-Ab has-mul-ℤ-Ab

ℤ-Comm-Ring : Comm-Ring lzero
ℤ-Comm-Ring = pair ℤ-Ring commutative-mul-ℤ

mul-ℤ-Semi-Group : Semi-Group lzero
mul-ℤ-Semi-Group = pair ℤ-Set (pair mul-ℤ associative-mul-ℤ)

mul-ℤ-Monoid : Monoid lzero
mul-ℤ-Monoid =
  pair
    ( mul-ℤ-Semi-Group)
    ( pair one-ℤ (pair left-unit-law-mul-ℤ right-unit-law-mul-ℤ))

--------------------------------------------------------------------------------

{- We characterize the identity type of ℤ. -}

Eq-ℤ : ℤ → ℤ → UU lzero
Eq-ℤ (inl x) (inl y) = Eq-ℕ x y
Eq-ℤ (inl x) (inr y) = empty
Eq-ℤ (inr x) (inl x₁) = empty
Eq-ℤ (inr (inl x)) (inr (inl y)) = unit
Eq-ℤ (inr (inl x)) (inr (inr y)) = empty
Eq-ℤ (inr (inr x)) (inr (inl y)) = empty
Eq-ℤ (inr (inr x)) (inr (inr y)) = Eq-ℕ x y

is-prop-Eq-ℤ :
  (x y : ℤ) → is-prop (Eq-ℤ x y)
is-prop-Eq-ℤ (inl x) (inl y) = is-prop-Eq-ℕ x y
is-prop-Eq-ℤ (inl x) (inr y) = is-prop-empty
is-prop-Eq-ℤ (inr x) (inl x₁) = is-prop-empty
is-prop-Eq-ℤ (inr (inl x)) (inr (inl y)) = is-prop-unit
is-prop-Eq-ℤ (inr (inl x)) (inr (inr y)) = is-prop-empty
is-prop-Eq-ℤ (inr (inr x)) (inr (inl y)) = is-prop-empty
is-prop-Eq-ℤ (inr (inr x)) (inr (inr y)) = is-prop-Eq-ℕ x y

refl-Eq-ℤ :
  (x : ℤ) → Eq-ℤ x x
refl-Eq-ℤ (inl x) = refl-Eq-ℕ x
refl-Eq-ℤ (inr (inl x)) = star
refl-Eq-ℤ (inr (inr x)) = refl-Eq-ℕ x

Eq-ℤ-eq :
  {x y : ℤ} → Id x y → Eq-ℤ x y
Eq-ℤ-eq {x} {.x} refl = refl-Eq-ℤ x

contraction-total-Eq-ℤ :
  (x : ℤ) (y : Σ ℤ (Eq-ℤ x)) → Id (pair x (refl-Eq-ℤ x)) y
contraction-total-Eq-ℤ (inl x) (pair (inl y) e) =
  eq-pair
    ( ap inl (eq-Eq-ℕ x y e))
    ( is-prop'-is-prop
      ( is-prop-Eq-ℕ x y)
      ( tr
        ( Eq-ℤ (inl x))
        ( ap inl (eq-Eq-ℕ x y e))
        ( refl-Eq-ℤ (inl x)))
      ( e))
contraction-total-Eq-ℤ (inr (inl star)) (pair (inr (inl star)) e) =
  eq-pair refl (is-prop'-is-prop is-prop-unit (refl-Eq-ℤ zero-ℤ) e)
contraction-total-Eq-ℤ (inr (inr x)) (pair (inr (inr y)) e) =
  eq-pair
    ( ap (inr ∘ inr) (eq-Eq-ℕ x y e))
    ( is-prop'-is-prop
      ( is-prop-Eq-ℕ x y)
      ( tr
        ( Eq-ℤ (inr (inr x)))
        ( ap (inr ∘ inr) (eq-Eq-ℕ x y e))
        ( refl-Eq-ℤ (inr (inr x))))
      ( e))

is-contr-total-Eq-ℤ :
  (x : ℤ) → is-contr (Σ ℤ (Eq-ℤ x))
is-contr-total-Eq-ℤ x =
  pair (pair x (refl-Eq-ℤ x)) (contraction-total-Eq-ℤ x)

is-equiv-Eq-ℤ-eq :
  (x y : ℤ) → is-equiv (Eq-ℤ-eq {x} {y})
is-equiv-Eq-ℤ-eq x =
  fundamental-theorem-id x
    ( refl-Eq-ℤ x)
    ( is-contr-total-Eq-ℤ x)
    ( λ y → Eq-ℤ-eq {x} {y})

eq-Eq-ℤ :
  {x y : ℤ} → Eq-ℤ x y → Id x y
eq-Eq-ℤ {x} {y} = inv-is-equiv (is-equiv-Eq-ℤ-eq x y)

--------------------------------------------------------------------------------

{- We prove some basic arithmetic properties of the integers. -}

--------------------------------------------------------------------------------

{- We show that addition from the left and from the right are both equivalences.
   We conclude that they are both injective maps. -}

is-emb-add-ℤ :
  (x : ℤ) → is-emb (add-ℤ x)
is-emb-add-ℤ x =
  is-emb-is-equiv (add-ℤ x) (is-equiv-add-ℤ x)

is-injective-add-ℤ :
  (x y z : ℤ) → Id (add-ℤ x y) (add-ℤ x z) → Id y z
is-injective-add-ℤ x y z = inv-is-equiv (is-emb-add-ℤ x y z)

is-emb-add-ℤ' :
  (y : ℤ) → is-emb (add-ℤ' y)
is-emb-add-ℤ' y = is-emb-is-equiv (add-ℤ' y) (is-equiv-add-ℤ' y)

is-injective-add-ℤ' :
  (y x w : ℤ) → Id (add-ℤ x y) (add-ℤ w y) → Id x w
is-injective-add-ℤ' y x w = inv-is-equiv (is-emb-add-ℤ' y x w)

--------------------------------------------------------------------------------

{- We show that multiplication by neg-one-ℤ is an equivalence. -}

is-emb-neg-ℤ : is-emb neg-ℤ
is-emb-neg-ℤ = is-emb-is-equiv neg-ℤ is-equiv-neg-ℤ

is-injective-neg-ℤ :
  (x y : ℤ) → Id (neg-ℤ x) (neg-ℤ y) → Id x y
is-injective-neg-ℤ x y = inv-is-equiv (is-emb-neg-ℤ x y)

--------------------------------------------------------------------------------

{- We show that if x = mul-ℤ x y for some non-zero integer x, then y = 1. -}

--------------------------------------------------------------------------------

{- We show that multiplication by a non-zero integer is an embedding. -}

{-
is-injective-mul-ℤ :
  (x y z : ℤ) → ¬ (Id zero-ℤ x) → Id (mul-ℤ x y) (mul-ℤ x z) → Id y z
is-injective-mul-ℤ (inl zero-ℕ) y z p q = is-injective-neg-ℤ y z q
is-injective-mul-ℤ (inl (succ-ℕ x)) y z p q = {!!}
is-injective-mul-ℤ (inr x) y z p q = {!x!}

neq-zero-mul-ℤ :
  (x y : ℤ) → ¬ (Id zero-ℤ x) → ¬ (Id zero-ℤ y) → ¬ (Id zero-ℤ (mul-ℤ x y))
neq-zero-mul-ℤ x y Hx Hy = {!!}
-}

--------------------------------------------------------------------------------

{- We prove some interchange laws and moves on iterated multiplications. -}

interchange-2-3-mul-ℤ :
  {a b c d : ℤ} →
  Id (mul-ℤ (mul-ℤ a b) (mul-ℤ c d)) (mul-ℤ (mul-ℤ a c) (mul-ℤ b d))
interchange-2-3-mul-ℤ {a} {b} {c} {d} =
  ( associative-mul-ℤ a b (mul-ℤ c d)) ∙
  ( ( ap ( mul-ℤ a)
         ( ( inv (associative-mul-ℤ b c d)) ∙
           ( ( ap (λ t → mul-ℤ t d) (commutative-mul-ℤ b c)) ∙
             ( associative-mul-ℤ c b d)))) ∙
    ( inv (associative-mul-ℤ a c (mul-ℤ b d))))

interchange-1-3-mul-ℤ :
  {a b c d : ℤ} →
  Id (mul-ℤ (mul-ℤ a b) (mul-ℤ c d)) (mul-ℤ (mul-ℤ c b) (mul-ℤ a d))
interchange-1-3-mul-ℤ {a} {b} {c} {d} =
  ( ap (λ t → mul-ℤ t (mul-ℤ c d)) (commutative-mul-ℤ a b)) ∙
  ( ( interchange-2-3-mul-ℤ {b}) ∙
    ( ap (λ t → mul-ℤ t (mul-ℤ a d)) (commutative-mul-ℤ b c)))

move-four-mul-ℤ :
  {a b c d : ℤ} →
  Id (mul-ℤ (mul-ℤ a b) (mul-ℤ c d)) (mul-ℤ (mul-ℤ a d) (mul-ℤ b c))
move-four-mul-ℤ {a} {b} {c} {d} =
   ( associative-mul-ℤ a b (mul-ℤ c d)) ∙
   ( ( ap ( mul-ℤ a)
          ( ( inv (associative-mul-ℤ b c d)) ∙
            ( commutative-mul-ℤ (mul-ℤ b c) d))) ∙
     ( inv (associative-mul-ℤ a d (mul-ℤ b c))))

move-five-mul-ℤ :
  {a b c d : ℤ} →
  Id (mul-ℤ (mul-ℤ a b) (mul-ℤ c d)) (mul-ℤ (mul-ℤ b c) (mul-ℤ a d))
move-five-mul-ℤ {a} {b} {c} {d} =
  ( interchange-2-3-mul-ℤ {a} {b} {c} {d}) ∙
  ( ( ap (λ t → mul-ℤ t (mul-ℤ b d)) (commutative-mul-ℤ a c)) ∙
    ( ( interchange-2-3-mul-ℤ {c}) ∙
      ( ap (λ t → mul-ℤ t (mul-ℤ a d)) (commutative-mul-ℤ c b))))
