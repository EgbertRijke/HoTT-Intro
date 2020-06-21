{-# OPTIONS --without-K --exact-split #-}

module localizations-rings where

import subrings
open subrings public

is-invertible-Ring :
  {l1 : Level} (R : Ring l1) (x : type-Ring R) → UU l1
is-invertible-Ring R =
  is-invertible-Monoid (multiplicative-monoid-Ring R)

is-prop-is-invertible-Ring :
  {l1 : Level} (R : Ring l1) (x : type-Ring R) →
  is-prop (is-invertible-Ring R x)
is-prop-is-invertible-Ring R =
  is-prop-is-invertible-Monoid (multiplicative-monoid-Ring R)

--------------------------------------------------------------------------------

{- We introduce homomorphism that invert specific elements -}

inverts-element-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (x : type-Ring R1) →
  (f : hom-Ring R1 R2) → UU l2
inverts-element-hom-Ring R1 R2 x f =
  is-invertible-Ring R2 (map-hom-Ring R1 R2 f x)

is-prop-inverts-element-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (x : type-Ring R)
  (f : hom-Ring R S) → is-prop (inverts-element-hom-Ring R S x f)
is-prop-inverts-element-hom-Ring R S x f =
  is-prop-is-invertible-Ring S (map-hom-Ring R S f x)

inv-inverts-element-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (x : type-Ring R)
  (f : hom-Ring R S) → inverts-element-hom-Ring R S x f → type-Ring S
inv-inverts-element-hom-Ring R S x f H = pr1 H

is-left-inverse-inv-inverts-element-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  Id ( mul-Ring S
       ( inv-inverts-element-hom-Ring R S x f H)
       ( map-hom-Ring R S f x))
     ( unit-Ring S)
is-left-inverse-inv-inverts-element-hom-Ring R S x f H = pr1 (pr2 H)

is-right-inverse-inv-inverts-element-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  Id ( mul-Ring S
       ( map-hom-Ring R S f x)
       ( inv-inverts-element-hom-Ring R S x f H))
     ( unit-Ring S)
is-right-inverse-inv-inverts-element-hom-Ring R S x f H = pr2 (pr2 H)

inverts-element-comp-hom-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (g : hom-Ring S T) (f : hom-Ring R S) → inverts-element-hom-Ring R S x f →
  inverts-element-hom-Ring R T x (comp-hom-Ring R S T g f)
inverts-element-comp-hom-Ring R S T x g f H =
  pair
    ( map-hom-Ring S T g (inv-inverts-element-hom-Ring R S x f H))
    ( pair
      ( ( inv
          ( preserves-mul-hom-Ring S T g
            ( inv-inverts-element-hom-Ring R S x f H)
            ( map-hom-Ring R S f x))) ∙
        ( ( ap
            ( map-hom-Ring S T g)
            ( is-left-inverse-inv-inverts-element-hom-Ring R S x f H)) ∙
          ( preserves-unit-hom-Ring S T g)))
      ( ( inv
          ( preserves-mul-hom-Ring S T g
            ( map-hom-Ring R S f x)
            ( inv-inverts-element-hom-Ring R S x f H))) ∙
        ( ( ap
            ( map-hom-Ring S T g)
            ( is-right-inverse-inv-inverts-element-hom-Ring R S x f H)) ∙
          ( preserves-unit-hom-Ring S T g))))

{- We state the universal property of the localization of a Ring at a single
   element x ∈ R. -}

precomp-universal-property-localization-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  hom-Ring S T → Σ (hom-Ring R T) (inverts-element-hom-Ring R T x)
precomp-universal-property-localization-Ring R S T x f H g =
  pair (comp-hom-Ring R S T g f) (inverts-element-comp-hom-Ring R S T x g f H)

universal-property-localization-Ring :
  (l : Level) {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (x : type-Ring R)
  (f : hom-Ring R S) → inverts-element-hom-Ring R S x f → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-localization-Ring l R S x f H =
  (T : Ring l) →
  is-equiv (precomp-universal-property-localization-Ring R S T x f H)

unique-extension-universal-property-localization-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  universal-property-localization-Ring l3 R S x f H →
  (h : hom-Ring R T) (K : inverts-element-hom-Ring R T x h) →
  is-contr
    (Σ (hom-Ring S T) (λ g → htpy-hom-Ring R T (comp-hom-Ring R S T g f) h))
unique-extension-universal-property-localization-Ring R S T x f H up-f h K =
  is-contr-equiv'
    ( fib (precomp-universal-property-localization-Ring R S T x f H) (pair h K))
    ( equiv-tot ( λ g →
      ( equiv-htpy-hom-Ring-eq R T (comp-hom-Ring R S T g f) h) ∘e
      ( equiv-Eq-total-subtype-eq
        ( is-prop-inverts-element-hom-Ring R T x)
        ( precomp-universal-property-localization-Ring R S T x f H g)
        ( pair h K))))
    ( is-contr-map-is-equiv (up-f T) (pair h K))

center-unique-extension-universal-property-localization-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  universal-property-localization-Ring l3 R S x f H →
  (h : hom-Ring R T) (K : inverts-element-hom-Ring R T x h) →
  Σ (hom-Ring S T) (λ g → htpy-hom-Ring R T (comp-hom-Ring R S T g f) h)
center-unique-extension-universal-property-localization-Ring R S T x f H up-f h K =
  center
    ( unique-extension-universal-property-localization-Ring
      R S T x f H up-f h K)

map-universal-property-localization-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  universal-property-localization-Ring l3 R S x f H →
  (h : hom-Ring R T) (K : inverts-element-hom-Ring R T x h) → hom-Ring S T
map-universal-property-localization-Ring R S T x f H up-f h K =
  pr1 ( center-unique-extension-universal-property-localization-Ring
        R S T x f H up-f h K)

htpy-universal-property-localization-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (f : hom-Ring R S) (H : inverts-element-hom-Ring R S x f) →
  (up-f : universal-property-localization-Ring l3 R S x f H) →
  (h : hom-Ring R T) (K : inverts-element-hom-Ring R T x h) →
  htpy-hom-Ring R T (comp-hom-Ring R S T (map-universal-property-localization-Ring R S T x f H up-f h K) f) h
htpy-universal-property-localization-Ring R S T x f H up-f h K =
  pr2 ( center-unique-extension-universal-property-localization-Ring
        R S T x f H up-f h K)

{- We show that the type of localizations of a ring R at an element x is
   contractible. -}

is-equiv-up-localization-up-localization-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) (x : type-Ring R)
  (f : hom-Ring R S) (inverts-f : inverts-element-hom-Ring R S x f) →
  (g : hom-Ring R T) (inverts-g : inverts-element-hom-Ring R T x g) →
  (h : hom-Ring S T) (H : htpy-hom-Ring R T (comp-hom-Ring R S T h f) g) →
  ({l : Level} → universal-property-localization-Ring l R S x f inverts-f) →
  ({l : Level} → universal-property-localization-Ring l R T x g inverts-g) →
  is-iso-hom-Ring S T h
is-equiv-up-localization-up-localization-Ring R S T x f inverts-f g inverts-g h H up-f up-g = {!is-iso-is-equiv-hom-Ring!}

--------------------------------------------------------------------------------

{- We introduce homomorphisms that invert all elements of a subset of a ring -}

inverts-subset-hom-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (P : subset-Ring l3 R) →
  (f : hom-Ring R S) → UU (l1 ⊔ l2 ⊔ l3)
inverts-subset-hom-Ring R S P f =
  (x : type-Ring R) (p : type-Prop (P x)) → inverts-element-hom-Ring R S x f

is-prop-inverts-subset-hom-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (P : subset-Ring l3 R) →
  (f : hom-Ring R S) → is-prop (inverts-subset-hom-Ring R S P f)
is-prop-inverts-subset-hom-Ring R S P f =
  is-prop-Π (λ x → is-prop-Π (λ p → is-prop-inverts-element-hom-Ring R S x f))

inv-inverts-subset-hom-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (P : subset-Ring l3 R)
  (f : hom-Ring R S) (H : inverts-subset-hom-Ring R S P f)
  (x : type-Ring R) (p : type-Prop (P x)) → type-Ring S
inv-inverts-subset-hom-Ring R S P f H x p =
  inv-inverts-element-hom-Ring R S x f (H x p)

is-left-inverse-inv-inverts-subset-hom-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (P : subset-Ring l3 R)
  (f : hom-Ring R S) (H : inverts-subset-hom-Ring R S P f)
  (x : type-Ring R) (p : type-Prop (P x)) →
  Id (mul-Ring S (inv-inverts-subset-hom-Ring R S P f H x p) (map-hom-Ring R S f x)) (unit-Ring S)
is-left-inverse-inv-inverts-subset-hom-Ring R S P f H x p =
  is-left-inverse-inv-inverts-element-hom-Ring R S x f (H x p)

is-right-inverse-inv-inverts-subset-hom-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (P : subset-Ring l3 R)
  (f : hom-Ring R S) (H : inverts-subset-hom-Ring R S P f)
  (x : type-Ring R) (p : type-Prop (P x)) →
  Id (mul-Ring S (map-hom-Ring R S f x) (inv-inverts-subset-hom-Ring R S P f H x p)) (unit-Ring S)
is-right-inverse-inv-inverts-subset-hom-Ring R S P f H x p =
  is-right-inverse-inv-inverts-element-hom-Ring R S x f (H x p)
  
inverts-subset-comp-hom-Ring :
  {l1 l2 l3 l4 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3)
  (P : subset-Ring l4 R) (g : hom-Ring S T) (f : hom-Ring R S) →
  inverts-subset-hom-Ring R S P f →
  inverts-subset-hom-Ring R T P (comp-hom-Ring R S T g f)
inverts-subset-comp-hom-Ring R S T P g f H x p =
  inverts-element-comp-hom-Ring R S T x g f (H x p)

{- We state the universal property of the localization of a Ring at a subset
   of R. -}

precomp-universal-property-localization-subset-Ring :
  {l1 l2 l3 l4 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3)
  (P : subset-Ring l4 R) →
  (f : hom-Ring R S) (H : inverts-subset-hom-Ring R S P f) →
  hom-Ring S T → Σ (hom-Ring R T) (inverts-subset-hom-Ring R T P)
precomp-universal-property-localization-subset-Ring R S T P f H g =
  pair (comp-hom-Ring R S T g f) (inverts-subset-comp-hom-Ring R S T P g f H)

universal-property-localization-subset-Ring :
  (l : Level) {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2)
  (P : subset-Ring l3 R) (f : hom-Ring R S) →
  inverts-subset-hom-Ring R S P f → UU (lsuc l ⊔ l1 ⊔ l2 ⊔ l3)
universal-property-localization-subset-Ring l R S P f H =
  (T : Ring l) →
  is-equiv (precomp-universal-property-localization-subset-Ring R S T P f H)


