{-# OPTIONS --without-K #-}

module 12-univalence where

import 11-function-extensionality
open 11-function-extensionality public

-- Section 10.1 Type extensionality

equiv-eq : {i : Level} {A : UU i} {B : UU i} → Id A B → A ≃ B
equiv-eq {A = A} refl = pair id (is-equiv-id A)

UNIVALENCE : {i : Level} (A B : UU i) → UU (lsuc i)
UNIVALENCE A B = is-equiv (equiv-eq {A = A} {B = B})


is-contr-total-equiv-UNIVALENCE : {i : Level} (A : UU i) →
  ((B : UU i) → UNIVALENCE A B) → is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv-UNIVALENCE A UA =
  fundamental-theorem-id' A
    ( pair id (is-equiv-id A))
    ( λ B → equiv-eq {B = B})
    ( UA)

UNIVALENCE-is-contr-total-equiv : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X)) → (B : UU i) → UNIVALENCE A B
UNIVALENCE-is-contr-total-equiv A c =
  fundamental-theorem-id A
    ( pair id (is-equiv-id A))
    ( c)
    ( λ B → equiv-eq {B = B})

ev-id : {i j : Level} {A : UU i} (P : (B : UU i) → (A ≃ B) → UU j) →
  ((B : UU i) (e : A ≃ B) → P B e) → P A (pair id (is-equiv-id A))
ev-id {A = A} P f = f A (pair id (is-equiv-id A))

IND-EQUIV : {i j : Level} {A : UU i} → ((B : UU i) (e : A ≃ B) → UU j) → UU _
IND-EQUIV P = sec (ev-id P)

triangle-ev-id : {i j : Level} {A : UU i}
  (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) →
  (ev-pt (Σ (UU i) (λ X → A ≃ X)) (pair A (pair id (is-equiv-id A))) P)
  ~ ((ev-id (λ X e → P (pair X e))) ∘ (ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P}))
triangle-ev-id P f = refl

abstract
  IND-EQUIV-is-contr-total-equiv : {i j : Level} (A : UU i) →
    is-contr (Σ (UU i) (λ X → A ≃ X)) →
    (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) → IND-EQUIV (λ B e → P (pair B e))
  IND-EQUIV-is-contr-total-equiv {i} {j} A c P =
    section-comp
      ( ev-pt (Σ (UU i) (λ X → A ≃ X)) (pair A (pair id (is-equiv-id A))) P)
      ( ev-id (λ X e → P (pair X e)))
      ( ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P})
      ( triangle-ev-id P)
      ( sec-ev-pair (UU i) (λ X → A ≃ X) P)
      ( is-sing-is-contr (Σ (UU i) (λ X → A ≃ X))
        ( pair
          ( pair A (pair id (is-equiv-id A)))
          ( λ t → 
            ( inv (contraction c (pair A (pair id (is-equiv-id A))))) ∙
            ( contraction c t)))
        ( P)
        ( pair A (equiv-id A)))

abstract
  is-contr-total-equiv-IND-EQUIV : {i : Level} (A : UU i) →
    ( {j : Level} (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) →
      IND-EQUIV (λ B e → P (pair B e))) →
    is-contr (Σ (UU i) (λ X → A ≃ X))
  is-contr-total-equiv-IND-EQUIV {i} A ind =
    is-contr-is-sing
      ( Σ (UU i) (λ X → A ≃ X))
      ( pair A (pair id (is-equiv-id A)))
      ( λ P → section-comp'
        ( ev-pt (Σ (UU i) (λ X → A ≃ X)) (pair A (pair id (is-equiv-id A))) P)
        ( ev-id (λ X e → P (pair X e)))
        ( ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P})
        ( triangle-ev-id P)
        ( sec-ev-pair (UU i) (λ X → A ≃ X) P)
        ( ind P))

-- The univalence axiom

postulate univalence : {i : Level} (A B : UU i) → UNIVALENCE A B

eq-equiv : {i : Level} (A B : UU i) → (A ≃ B) → Id A B
eq-equiv A B = inv-is-equiv (univalence A B)

abstract
  is-contr-total-equiv : {i : Level} (A : UU i) →
    is-contr (Σ (UU i) (λ X → A ≃ X))
  is-contr-total-equiv A = is-contr-total-equiv-UNIVALENCE A (univalence A)

abstract
  Ind-equiv : {i j : Level} (A : UU i) (P : (B : UU i) (e : A ≃ B) → UU j) →
    sec (ev-id P)
  Ind-equiv A P =
    IND-EQUIV-is-contr-total-equiv A
    ( is-contr-total-equiv A)
    ( λ t → P (pr1 t) (pr2 t))

ind-equiv : {i j : Level} (A : UU i) (P : (B : UU i) (e : A ≃ B) → UU j) →
  P A (pair id (is-equiv-id A)) → (B : UU i) (e : A ≃ B) → P B e
ind-equiv A P = pr1 (Ind-equiv A P)

-- Subuniverses

is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU ((lsuc l1) ⊔ l2)
is-subuniverse P = is-subtype P

subuniverse :
  (l1 l2 : Level) → UU ((lsuc l1) ⊔ (lsuc l2))
subuniverse l1 l2 = Σ (UU l1 → UU l2) is-subuniverse

{- By univalence, subuniverses are closed under equivalences. -}
in-subuniverse-equiv :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P X → P Y
in-subuniverse-equiv P e = tr P (eq-equiv _ _ e)

in-subuniverse-equiv' :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P Y → P X
in-subuniverse-equiv' P e = tr P (inv (eq-equiv _ _ e))

total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU ((lsuc l1) ⊔ l2)
total-subuniverse {l1} P = Σ (UU l1) (pr1 P)

{- We also introduce the notion of 'global subuniverse'. The handling of 
   universe levels is a bit more complicated here, since (l : Level) → A l are 
   kinds but not types. -}
   
is-global-subuniverse :
  (α : Level → Level) (P : (l : Level) → subuniverse l (α l)) →
  (l1 l2 : Level) → UU _
is-global-subuniverse α P l1 l2 =
  (X : UU l1) (Y : UU l2) → X ≃ Y → (pr1 (P l1)) X → (pr1 (P l2)) Y

{- Next we characterize the identity type of a subuniverse. -}

Eq-total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → UU l1
Eq-total-subuniverse (pair P H) (pair X p) t = X ≃ (pr1 t)

Eq-total-subuniverse-eq :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → Id s t → Eq-total-subuniverse P s t
Eq-total-subuniverse-eq (pair P H) (pair X p) .(pair X p) refl = equiv-id X

abstract
  is-contr-total-Eq-total-subuniverse :
    {l1 l2 : Level} (P : subuniverse l1 l2)
    (s : total-subuniverse P) →
    is-contr (Σ (total-subuniverse P) (λ t → Eq-total-subuniverse P s t))
  is-contr-total-Eq-total-subuniverse (pair P H) (pair X p) =
    is-contr-total-Eq-substructure (is-contr-total-equiv X) H X (equiv-id X) p

abstract
  is-equiv-Eq-total-subuniverse-eq :
    {l1 l2 : Level} (P : subuniverse l1 l2)
    (s t : total-subuniverse P) → is-equiv (Eq-total-subuniverse-eq P s t)
  is-equiv-Eq-total-subuniverse-eq (pair P H) (pair X p) =
    fundamental-theorem-id
      ( pair X p)
      ( equiv-id X)
      ( is-contr-total-Eq-total-subuniverse (pair P H) (pair X p))
      ( Eq-total-subuniverse-eq (pair P H) (pair X p))

eq-Eq-total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  {s t : total-subuniverse P} → Eq-total-subuniverse P s t → Id s t
eq-Eq-total-subuniverse P {s} {t} =
  inv-is-equiv (is-equiv-Eq-total-subuniverse-eq P s t)

-- Section 12.2 Groups in univalent mathematics

{- We first introduce semi-groups, then monoids, and finally groups. We do this
   because for a monoid to be a group is a proposition, and similarly for a
   semi-group to be a monoid is a proposition. Therefore this approach gives us
   in a straightforward way that equality of groups is equality of semi-groups.
   This will be useful in showing that group isomorphisms are equivalent to
   identifications of groups. -}

has-associative-mul :
  {l : Level} (X : hSet l) → UU l
has-associative-mul (pair X is-set-X) =
  Σ ( X → (X → X)) (λ μ →
    ( x y z : X) → Id (μ (μ x y) z) (μ x (μ y z)))

Semi-Group :
  (l : Level) → UU (lsuc l)
Semi-Group l = Σ (hSet l) has-associative-mul

underlying-type-semi-group :
  {l : Level} → Semi-Group l → UU l
underlying-type-semi-group (pair (pair G is-set-G) μ) = G

mul-semi-group :
  {l : Level} (G : Semi-Group l) →
  underlying-type-semi-group G →
    underlying-type-semi-group G → underlying-type-semi-group G
mul-semi-group (pair (pair G is-set-G) (pair μ assoc-G)) = μ

{- The property that a semi-group is a monoid is just that the semi-group 
   possesses a unit that satisfies the left and right unit laws. -}

is-monoid :
  {l : Level} → Semi-Group l → UU l
is-monoid (pair (pair X is-set-X) (pair μ assoc-μ)) =
  Σ X (λ e → ((y : X) → Id (μ e y) y) × ((x : X) → Id (μ x e) x))

Monoid :
  (l : Level) → UU (lsuc l)
Monoid l = Σ (Semi-Group l) is-monoid

semi-group-monoid :
  {l : Level} → Monoid l → Semi-Group l
semi-group-monoid G = pr1 G

{- We show that is-monoid is a proposition. -}

abstract
  is-prop-is-monoid' :
    {l : Level} (G : Semi-Group l) → is-prop' (is-monoid G)
  is-prop-is-monoid' (pair (pair X is-set-X) (pair μ assoc-μ))
    (pair e (pair left-unit-e right-unit-e))
    (pair e' (pair left-unit-e' right-unit-e')) =
    eq-subtype
      ( λ e → is-prop-prod
        ( is-prop-Π (λ y → is-set-X (μ e y) y))
        ( is-prop-Π (λ x → is-set-X (μ x e) x)))
      ( (inv (left-unit-e' e)) ∙ (right-unit-e e'))

abstract
  is-prop-is-monoid :
    {l : Level} (G : Semi-Group l) → is-prop (is-monoid G)
  is-prop-is-monoid G = is-prop-is-prop' (is-prop-is-monoid' G)

{- The property that a monoid is a group is just the property that the monoid
   that every element is invertible, i.e., it comes equipped with an inverse
   operation that satisfies the left and right inverse laws. -}

is-group :
  {l : Level} (G : Monoid l) → UU l
is-group (pair (pair (pair X is-set-X) (pair μ assoc-μ)) (pair e laws-e)) =
  Σ (X → X) (λ i → ((x : X) → Id (μ (i x) x) e) × ((x : X) → Id (μ x (i x)) e))

Group :
  (l : Level) → UU (lsuc l)
Group l = Σ (Monoid l) is-group

monoid-group :
  {l : Level} → Group l → Monoid l
monoid-group G = pr1 G

underlying-semi-group :
  {l : Level} → Group l → Semi-Group l
underlying-semi-group G = pr1 (pr1 G)

{- We show that being a group is a proposition. -}

abstract
  is-prop-is-group' :
    {l : Level} (G : Monoid l) → is-prop' (is-group G)
  is-prop-is-group'
    ( pair
      ( pair (pair X is-set-X) (pair μ assoc-μ))
      ( pair e (pair left-unit-e right-unit-e)))
    ( pair i (pair left-inv-i right-inv-i))
    ( pair i' (pair left-inv-i' right-inv-i')) =
    eq-subtype
      ( λ i →
        is-prop-prod
          ( is-prop-Π (λ x → is-set-X (μ (i x) x) e))
          ( is-prop-Π (λ x → is-set-X (μ x (i x)) e)))
      ( eq-htpy
        ( λ x →                                             -- ix
          ( inv (left-unit-e (i x))) ∙                      -- = 1·(ix)
          ( ( ap (λ y → μ y (i x)) (inv (left-inv-i' x))) ∙ -- = (i'x·x)·(ix)
            ( ( assoc-μ (i' x) x (i x)) ∙                   -- = (i'x)·(x·i'x)
              ( ( ap (μ (i' x)) (right-inv-i x)) ∙          -- = (i'x)·1
                ( right-unit-e (i' x)))))))                 -- = i'x

abstract
  is-prop-is-group :
    {l : Level} (G : Monoid l) → is-prop (is-group G)
  is-prop-is-group G = is-prop-is-prop' (is-prop-is-group' G)

{- We give two examples of groups. The first is the group ℤ of integers. The
   second is the loop space of a pointed 1-type.  -}

{- The group of integers. -}

semi-group-ℤ : Semi-Group lzero
semi-group-ℤ = pair set-ℤ (pair add-ℤ associative-add-ℤ)

monoid-ℤ : Monoid lzero
monoid-ℤ =
  pair
    ( semi-group-ℤ)
    ( pair zero-ℤ (pair left-unit-law-add-ℤ right-unit-law-add-ℤ))

group-ℤ : Group lzero
group-ℤ =
  pair
    ( monoid-ℤ)
    ( pair neg-ℤ (pair left-inverse-law-add-ℤ right-inverse-law-add-ℤ))

{- The loop space of a 1-type as a group. -}

loop-space :
  {l : Level} {A : UU l} → A → UU l
loop-space a = Id a a

set-loop-space :
  {l : Level} (A : 1-type l) (a : pr1 A) → hSet l
set-loop-space (pair A is-1-type-A) a =
  pair (loop-space a) (is-1-type-A a a)

semi-group-loop-space :
  {l : Level} (A : 1-type l) (a : pr1 A) → Semi-Group l
semi-group-loop-space (pair A is-1-type-A) a =
  pair
    ( set-loop-space (pair A is-1-type-A) a)
    ( pair (λ p q → p ∙ q) assoc)

monoid-loop-space :
  {l : Level} (A : 1-type l) (a : pr1 A) → Monoid l
monoid-loop-space (pair A is-1-type-A) a =
  pair
    ( semi-group-loop-space (pair A is-1-type-A) a)
    ( pair refl
      ( pair (λ q → left-unit) (λ p → right-unit)))

group-loop-space :
  {l : Level} (A : 1-type l) (a : pr1 A) → Group l
group-loop-space (pair A is-1-type-A) a =
  pair
    ( monoid-loop-space (pair A is-1-type-A) a)
    ( pair inv (pair left-inv right-inv))

{- We now work our way up from semi-group homomorphisms to group homomorphisms.
   Indeed, every semi-group homomorphism between groups preserves the unit and
   the inverses. -}

preserves-mul :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  (underlying-type-semi-group G → underlying-type-semi-group H) → UU (l1 ⊔ l2)
preserves-mul G H f =
  (x y : underlying-type-semi-group G) →
      Id (f (mul-semi-group G x y)) (mul-semi-group H (f x) (f y))

is-prop-preserves-mul :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  ( f : underlying-type-semi-group G → underlying-type-semi-group H) →
  is-prop (preserves-mul G H f)
is-prop-preserves-mul G (pair (pair H is-set-H) (pair μ-H assoc-H)) f =
  is-prop-Π (λ x →
    is-prop-Π (λ y →
      is-set-H (f (mul-semi-group G x y)) (μ-H (f x) (f y))))

Semi-Group-Hom :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) → UU (l1 ⊔ l2)
Semi-Group-Hom G H =
  Σ ( underlying-type-semi-group G → underlying-type-semi-group H) (λ f →
    ( (x y : underlying-type-semi-group G) →
      Id (f (mul-semi-group G x y)) (mul-semi-group H (f x) (f y))))

underlying-map-semi-group-hom :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  ( Semi-Group-Hom G H) →
  ( underlying-type-semi-group G) → (underlying-type-semi-group H)
underlying-map-semi-group-hom G H f = pr1 f

preserves-mul-semi-group-hom :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  ( f : Semi-Group-Hom G H) →
  preserves-mul G H (underlying-map-semi-group-hom G H f)
preserves-mul-semi-group-hom G H f = pr2 f

preserves-unit-monoid :
  { l1 l2 : Level} (G : Monoid l1) (H : Monoid l2) →
  (f : Semi-Group-Hom (semi-group-monoid G) (semi-group-monoid H)) → UU l2
preserves-unit-monoid
  ( pair ( pair (pair G is-set-G) (pair μ-G assoc-G))
         ( pair e-G (pair left-unit-G right-unit-G)))
  ( pair ( pair (pair H is-set-H) (pair μ-H assoc-H))
         ( pair e-H (pair left-unit-H right-unit-H)))
  ( pair f μ-f) =
  Id (f e-G) e-H

Monoid-Hom :
  { l1 l2 : Level} (G : Monoid l1) (H : Monoid l2) → UU (l1 ⊔ l2)
Monoid-Hom G H =
  Σ ( Semi-Group-Hom (semi-group-monoid G) (semi-group-monoid H))
    ( preserves-unit-monoid G H)

Group-Hom :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) → UU (l1 ⊔ l2)
Group-Hom G H = Semi-Group-Hom (underlying-semi-group G) (underlying-semi-group H)

preserves-unit :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : Group-Hom G H) → UU l2
preserves-unit G H f =
  preserves-unit-monoid (monoid-group G) (monoid-group H) f

abstract
  preserves-unit-group-hom :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f : Group-Hom G H) → preserves-unit G H f
  preserves-unit-group-hom
    ( pair ( pair ( pair (pair G is-set-G) (pair μ-G assoc-G))
                  ( pair e-G (pair left-unit-G right-unit-G)))
           ( pair i-G (pair left-inv-G right-inv-G)))
    ( pair ( pair ( pair (pair H is-set-H) (pair μ-H assoc-H))
                  ( pair e-H (pair left-unit-H right-unit-H)))
           ( pair i-H (pair left-inv-H right-inv-H)))
    ( pair f μ-f) =
    ( inv (left-unit-H (f e-G))) ∙
    ( ( ap (λ x → μ-H x (f e-G)) (inv (left-inv-H (f e-G)))) ∙
      ( ( assoc-H (i-H (f e-G)) (f e-G) (f e-G)) ∙
        ( ( ap (μ-H (i-H (f e-G))) (inv (μ-f e-G e-G))) ∙
          ( ( ap (λ x → μ-H (i-H (f e-G)) (f x)) (left-unit-G e-G)) ∙
            ( left-inv-H (f e-G))))))

preserves-inverses :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : Group-Hom G H) → UU (l1 ⊔ l2)
preserves-inverses
  ( pair ( pair ( pair (pair G is-set-G) (pair μ-G assoc-G))
                ( pair e-G (pair left-unit-G right-unit-G)))
         ( pair i-G (pair left-inv-G right-inv-G)))
  ( pair ( pair ( pair (pair H is-set-H) (pair μ-H assoc-H))
                ( pair e-H (pair left-unit-H right-unit-H)))
         ( pair i-H (pair left-inv-H right-inv-H)))
  ( pair f μ-f) =
  ( x : G) → Id (f (i-G x)) (i-H (f x))

abstract
  preserves-inverses-group-hom' :
    { l1 l2 : Level} (G : Group l1) (H : Group l2) →
    ( f : Group-Hom G H) →
    preserves-unit G H f → preserves-inverses G H f
  preserves-inverses-group-hom'
    ( pair ( pair ( pair (pair G is-set-G) (pair μ-G assoc-G))
                  ( pair e-G (pair left-unit-G right-unit-G)))
           ( pair i-G (pair left-inv-G right-inv-G)))
    ( pair ( pair ( pair (pair H is-set-H) (pair μ-H assoc-H))
                  ( pair e-H (pair left-unit-H right-unit-H)))
           ( pair i-H (pair left-inv-H right-inv-H)))
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
    ( f : Group-Hom G H) → preserves-inverses G H f
  preserves-inverses-group-hom G H f =
    preserves-inverses-group-hom' G H f (preserves-unit-group-hom G H f)

Group-Hom' :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) → UU (l1 ⊔ l2)
Group-Hom' G H =
  Σ ( Group-Hom G H) (λ f →
    ( preserves-unit G H f) × (preserves-inverses G H f))

preserves-all-Group-Hom :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  Group-Hom G H → Group-Hom' G H
preserves-all-Group-Hom G H f =
  pair f
    ( pair
      ( preserves-unit-group-hom G H f)
      ( preserves-inverses-group-hom G H f))

{- Next, we construct the identity group homomorphism, and we show that
   compositions of group homomorphisms are again group homomorphisms. -}

id-semi-group-hom :
  {l : Level} (G : Semi-Group l) → Semi-Group-Hom G G
id-semi-group-hom (pair (pair G is-set-G) (pair μ assoc-G)) =
  pair id (λ x y → refl)

id-group-hom :
  {l : Level} (G : Group l) → Group-Hom G G
id-group-hom G = id-semi-group-hom (underlying-semi-group G)

composition-Semi-Group-Hom :
  {l1 l2 l3 : Level} →
  (G : Semi-Group l1) (H : Semi-Group l2) (K : Semi-Group l3) →
  (Semi-Group-Hom H K) → (Semi-Group-Hom G H) → (Semi-Group-Hom G K)
composition-Semi-Group-Hom G H K (pair g μ-g) (pair f μ-f) =
  pair
    ( g ∘ f)
    ( λ x y → (ap g (μ-f x y)) ∙ (μ-g (f x) (f y)))

composition-Group-Hom :
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3) →
  (Group-Hom H K) → (Group-Hom G H) → (Group-Hom G K)
composition-Group-Hom G H K =
  composition-Semi-Group-Hom
    ( underlying-semi-group G)
    ( underlying-semi-group H)
    ( underlying-semi-group K)

{- Next, we prove the that the laws for a category hold for group homomorphisms,
   i.e., we show that composition is associative and satisfies the left and
   right unit laws. Before we show that these laws hold, we will characterize
   the identity type of the types of semi-group homomorphisms and group 
   homomorphisms. -}

{- First we characterize the identity type of the semi-group homomorphisms. -}

htpy-Semi-Group-Hom :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2)
  (f g : Semi-Group-Hom G H) → UU (l1 ⊔ l2)
htpy-Semi-Group-Hom G H f g = (pr1 f) ~ (pr1 g)

reflexive-htpy-Semi-Group-Hom :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  ( f : Semi-Group-Hom G H) → htpy-Semi-Group-Hom G H f f
reflexive-htpy-Semi-Group-Hom G H f = htpy-refl

htpy-Semi-Group-Hom-eq :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  ( f g : Semi-Group-Hom G H) → Id f g → htpy-Semi-Group-Hom G H f g
htpy-Semi-Group-Hom-eq G H f .f refl = reflexive-htpy-Semi-Group-Hom G H f 

abstract
  is-contr-total-htpy-Semi-Group-Hom :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f : Semi-Group-Hom G H) →
    is-contr (Σ (Semi-Group-Hom G H) (htpy-Semi-Group-Hom G H f))
  is-contr-total-htpy-Semi-Group-Hom G H f =
    is-contr-total-Eq-substructure
      ( is-contr-total-htpy (underlying-map-semi-group-hom G H f))
      ( is-prop-preserves-mul G H)
      ( underlying-map-semi-group-hom G H f)
      ( htpy-refl)
      ( preserves-mul-semi-group-hom G H f)

abstract
  is-equiv-htpy-Semi-Group-Hom-eq :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f g : Semi-Group-Hom G H) → is-equiv (htpy-Semi-Group-Hom-eq G H f g)
  is-equiv-htpy-Semi-Group-Hom-eq G H f =
    fundamental-theorem-id f
      ( reflexive-htpy-Semi-Group-Hom G H f)
      ( is-contr-total-htpy-Semi-Group-Hom G H f)
      ( htpy-Semi-Group-Hom-eq G H f)

eq-htpy-Semi-Group-Hom :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  { f g : Semi-Group-Hom G H} → htpy-Semi-Group-Hom G H f g → Id f g
eq-htpy-Semi-Group-Hom G H {f} {g} =
  inv-is-equiv (is-equiv-htpy-Semi-Group-Hom-eq G H f g)

associative-comp-Semi-Group-Hom :
  { l1 l2 l3 l4 : Level} (G : Semi-Group l1) (H : Semi-Group l2)
  ( K : Semi-Group l3) (L : Semi-Group l4) (h : Semi-Group-Hom K L) →
  ( g : Semi-Group-Hom H K) (f : Semi-Group-Hom G H) →
  Id ( composition-Semi-Group-Hom G H L
       ( composition-Semi-Group-Hom H K L h g) f)
     ( composition-Semi-Group-Hom G K L h
       ( composition-Semi-Group-Hom G H K g f))
associative-comp-Semi-Group-Hom G H K L (pair h μ-h) (pair g μ-g) (pair f μ-f) =
  eq-htpy-Semi-Group-Hom G L htpy-refl

{- Now we characterize the identity type of group homomorphisms. -}

htpy-Group-Hom :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f g : Group-Hom G H) → UU (l1 ⊔ l2)
htpy-Group-Hom G H f g =
  htpy-Semi-Group-Hom (underlying-semi-group G) (underlying-semi-group H) f g

reflexive-htpy-Group-Hom :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : Group-Hom G H) → htpy-Group-Hom G H f f
reflexive-htpy-Group-Hom G H =
  reflexive-htpy-Semi-Group-Hom
    ( underlying-semi-group G)
    ( underlying-semi-group H)

htpy-Group-Hom-eq :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f g : Group-Hom G H) → Id f g → htpy-Group-Hom G H f g
htpy-Group-Hom-eq G H =
  htpy-Semi-Group-Hom-eq
    ( underlying-semi-group G)
    ( underlying-semi-group H)

is-contr-total-htpy-Group-Hom :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) (f : Group-Hom G H) →
  is-contr (Σ (Group-Hom G H) (htpy-Group-Hom G H f))
is-contr-total-htpy-Group-Hom G H =
  is-contr-total-htpy-Semi-Group-Hom
    ( underlying-semi-group G)
    ( underlying-semi-group H)

is-equiv-htpy-Group-Hom-eq :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f g : Group-Hom G H) → is-equiv (htpy-Group-Hom-eq G H f g)
is-equiv-htpy-Group-Hom-eq G H =
  is-equiv-htpy-Semi-Group-Hom-eq
    ( underlying-semi-group G)
    ( underlying-semi-group H)

{- Now we introduce the notion of group isomorphism. Finally, we will show that
   isomorphic groups are equal. -}

-- Exercises

-- Exercise 10.1

tr-equiv-eq-ap : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A}
  (p : Id x y) → (map-equiv (equiv-eq (ap B p))) ~ tr B p
tr-equiv-eq-ap refl = htpy-refl

-- Exercise 10.2

subuniverse-is-contr :
  {i : Level} → subuniverse i i
subuniverse-is-contr {i} = pair is-contr is-subtype-is-contr

unit' :
  (i : Level) → UU i
unit' i = pr1 (Raise i unit)

abstract
  is-contr-unit' :
    (i : Level) → is-contr (unit' i)
  is-contr-unit' i =
    is-contr-equiv' unit (pr2 (Raise i unit)) is-contr-unit

abstract
  center-UU-contr :
    (i : Level) → total-subuniverse (subuniverse-is-contr {i})
  center-UU-contr i =
    pair (unit' i) (is-contr-unit' i)
  
  contraction-UU-contr :
    {i : Level} (A : Σ (UU i) is-contr) →
    Id (center-UU-contr i) A
  contraction-UU-contr (pair A is-contr-A) =
    eq-Eq-total-subuniverse subuniverse-is-contr
      ( equiv-is-contr (is-contr-unit' _) is-contr-A)

abstract
  is-contr-UU-contr : (i : Level) → is-contr (Σ (UU i) is-contr)
  is-contr-UU-contr i =
    pair (center-UU-contr i) (contraction-UU-contr)
