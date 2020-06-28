{-# OPTIONS --without-K --exact-split #-}

module free-group where

import 15-groups
open 15-groups public

{- We state the universal property of the free group on a set X -}

precomp-universal-property-free-group :
  {l1 l2 l3 : Level} (X : UU-Set l1) (F : Group l2) (G : Group l3)
  (f : type-hom-Set X (set-Group F)) →
  hom-Group F G → type-hom-Set X (set-Group G)
precomp-universal-property-free-group X F G f g = (map-hom-Group F G g) ∘ f

universal-property-free-group :
  (l : Level) {l1 l2 : Level} (X : UU-Set l1) (F : Group l2)
  (f : type-hom-Set X (set-Group F)) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-free-group l X F f =
  (G : Group l) → is-equiv (precomp-universal-property-free-group X F G f)

{- We state the universal property of the initial set equipped with a point
   and an automorphism for each x : X. -}

universal-property-initial-pset-with-automorphisms :
  (l : Level) {l1 l2 : Level} (X : UU-Set l1) (Y : UU-Set l2)
  (pt-Y : type-Set Y) (f : type-Set X → (type-Set Y ≃ type-Set Y)) →
  UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-initial-pset-with-automorphisms l X Y pt-Y f =
  (Z : UU-Set l) (pt-Z : type-Set Z) (g : type-Set X → (type-Set Z ≃ type-Set Z)) →
  is-contr
    ( Σ ( type-hom-Set Y Z)
        ( λ h →
          ( Id (h pt-Y) pt-Z) ×
          ( (x : type-Set X) (y : type-Set Y) →
            Id (h (map-equiv (f x) y)) (map-equiv (g x) (h y)))))

map-initial-pset-with-automorphisms :
  { l1 l2 l3 : Level} (X : UU-Set l1) (Y : UU-Set l2) (pt-Y : type-Set Y)
  ( f : type-Set X → (type-Set Y ≃ type-Set Y)) →
  ( {l : Level} →
    universal-property-initial-pset-with-automorphisms l X Y pt-Y f) →
  ( Z : UU-Set l3) (pt-Z : type-Set Z)
  ( g : type-Set X → (type-Set Z ≃ type-Set Z)) →
  type-hom-Set Y Z
map-initial-pset-with-automorphisms
  X Y pt-Y f up-Y Z pt-Z g = pr1 (center (up-Y Z pt-Z g))

preserves-point-map-initial-pset-with-automorphisms :
  { l1 l2 l3 : Level} (X : UU-Set l1) (Y : UU-Set l2) (pt-Y : type-Set Y)
  ( f : type-Set X → (type-Set Y ≃ type-Set Y)) →
  ( up-Y : {l : Level} →
    universal-property-initial-pset-with-automorphisms l X Y pt-Y f) →
  ( Z : UU-Set l3) (pt-Z : type-Set Z)
  ( g : type-Set X → (type-Set Z ≃ type-Set Z)) →
  Id (map-initial-pset-with-automorphisms X Y pt-Y f up-Y Z pt-Z g pt-Y) pt-Z
preserves-point-map-initial-pset-with-automorphisms X Y pt-Y f up-Y Z pt-Z g =
  pr1 (pr2 (center (up-Y Z pt-Z g)))

htpy-map-initial-pset-with-automorphisms :
  { l1 l2 l3 : Level} (X : UU-Set l1) (Y : UU-Set l2) (pt-Y : type-Set Y)
  ( f : type-Set X → (type-Set Y ≃ type-Set Y)) →
  ( up-Y : {l : Level} →
    universal-property-initial-pset-with-automorphisms l X Y pt-Y f) →
  ( Z : UU-Set l3) (pt-Z : type-Set Z)
  ( g : type-Set X → (type-Set Z ≃ type-Set Z)) →
  ( x : type-Set X) (y : type-Set Y) →
  Id ( map-initial-pset-with-automorphisms X Y pt-Y f up-Y Z pt-Z g
       ( map-equiv (f x) y))
     ( map-equiv (g x)
       ( map-initial-pset-with-automorphisms X Y pt-Y f up-Y Z pt-Z g y))
htpy-map-initial-pset-with-automorphisms X Y pt-Y f up-Y Z pt-Z g =
  pr2 (pr2 (center (up-Y Z pt-Z g)))

{- We show a dependent elimination property for the initial pointed set with
   an automorphism for each x : X. -}

dependent-up-initial-pset-with-automorphisms :
  { l1 l2 l3 l4 : Level} (X : UU-Set l1) (Y : UU-Set l2) (pt-Y : type-Set Y)
  ( f : type-Set X → (type-Set Y ≃ type-Set Y)) →
  ( up-Y : {l : Level} →
    universal-property-initial-pset-with-automorphisms l X Y pt-Y f) →
  ( Z : UU-Set l3) (pt-Z : type-Set Z)
  ( g : type-Set X → (type-Set Z ≃ type-Set Z)) →
  ( P : type-Set Z → UU-Set l4)
  ( p : type-Set (P pt-Z))
  ( e : (x : type-Set X) (z : type-Set Z) →
        type-Set (P z) ≃ type-Set (P (map-equiv (g x) z))) →
  ( y : type-Set Y) →
  type-Set (P (map-initial-pset-with-automorphisms X Y pt-Y f up-Y Z pt-Z g y))
dependent-up-initial-pset-with-automorphisms X Y pt-Y f up-Y Z pt-Z g P p e =
  {!!}
        
  
{- We show that the initial set equipped with a point and an automorphism for
   each x : X is a group. -}

mul-initial-pset-with-automorphisms :
  {l1 l2 : Level} (X : UU-Set l1) (Y : UU-Set l2)
  (pt-Y : type-Set Y) (f : type-Set X → (type-Set Y ≃ type-Set Y)) →
  ( {l : Level} →
    universal-property-initial-pset-with-automorphisms l X Y pt-Y f) →
  type-Set Y → type-Set Y → type-Set Y
mul-initial-pset-with-automorphisms {l1} {l2} X Y pt-Y f up-Y =
  map-initial-pset-with-automorphisms
    X Y pt-Y f up-Y (hom-Set Y Y) id
    ( λ x → equiv-postcomp (type-Set Y) (f x))

associative-mul-initial-pset-with-automorphisms :
  {l1 l2 : Level} (X : UU-Set l1) (Y : UU-Set l2)
  (pt-Y : type-Set Y) (f : type-Set X → (type-Set Y ≃ type-Set Y)) →
  ( up-Y : {l : Level} →
    universal-property-initial-pset-with-automorphisms l X Y pt-Y f) →
  ( x y z : type-Set Y) →
  Id ( mul-initial-pset-with-automorphisms X Y pt-Y f up-Y
       ( mul-initial-pset-with-automorphisms X Y pt-Y f up-Y x y) z)
     ( mul-initial-pset-with-automorphisms X Y pt-Y f up-Y x
       ( mul-initial-pset-with-automorphisms X Y pt-Y f up-Y y z))
associative-mul-initial-pset-with-automorphisms X Y pt-Y f up-Y x y z = {!refl!}
