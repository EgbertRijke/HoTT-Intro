{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module 12-univalence where

import 11-function-extensionality
open 11-function-extensionality public

-- Section 10.1 Type extensionality

equiv-eq : {i : Level} {A : UU i} {B : UU i} → Id A B → A ≃ B
equiv-eq {A = A} refl = equiv-id A

UNIVALENCE : {i : Level} (A B : UU i) → UU (lsuc i)
UNIVALENCE A B = is-equiv (equiv-eq {A = A} {B = B})

is-contr-total-equiv-UNIVALENCE : {i : Level} (A : UU i) →
  ((B : UU i) → UNIVALENCE A B) → is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv-UNIVALENCE A UA =
  fundamental-theorem-id' A
    ( equiv-id A)
    ( λ B → equiv-eq {B = B})
    ( UA)

UNIVALENCE-is-contr-total-equiv : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X)) → (B : UU i) → UNIVALENCE A B
UNIVALENCE-is-contr-total-equiv A c =
  fundamental-theorem-id A
    ( equiv-id A)
    ( c)
    ( λ B → equiv-eq {B = B})

ev-id : {i j : Level} {A : UU i} (P : (B : UU i) → (A ≃ B) → UU j) →
  ((B : UU i) (e : A ≃ B) → P B e) → P A (equiv-id A)
ev-id {A = A} P f = f A (equiv-id A)

IND-EQUIV : {i j : Level} {A : UU i} → ((B : UU i) (e : A ≃ B) → UU j) → UU _
IND-EQUIV P = sec (ev-id P)

triangle-ev-id : {i j : Level} {A : UU i}
  (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) →
  (ev-pt (Σ (UU i) (λ X → A ≃ X)) (pair A (equiv-id A)) P)
  ~ ((ev-id (λ X e → P (pair X e))) ∘ (ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P}))
triangle-ev-id P f = refl

abstract
  IND-EQUIV-is-contr-total-equiv : {i j : Level} (A : UU i) →
    is-contr (Σ (UU i) (λ X → A ≃ X)) →
    (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) → IND-EQUIV (λ B e → P (pair B e))
  IND-EQUIV-is-contr-total-equiv {i} {j} A c P =
    section-comp
      ( ev-pt (Σ (UU i) (λ X → A ≃ X)) (pair A (equiv-id A)) P)
      ( ev-id (λ X e → P (pair X e)))
      ( ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P})
      ( triangle-ev-id P)
      ( sec-ev-pair (UU i) (λ X → A ≃ X) P)
      ( is-sing-is-contr (Σ (UU i) (λ X → A ≃ X))
        ( pair
          ( pair A (equiv-id A))
          ( λ t → 
            ( inv (contraction c (pair A (equiv-id A)))) ∙
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
      ( pair A (equiv-id A))
      ( λ P → section-comp'
        ( ev-pt (Σ (UU i) (λ X → A ≃ X)) (pair A (equiv-id A)) P)
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

inv-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  Id (inv-equiv (inv-equiv e)) e
inv-inv-equiv (pair f (pair (pair g G) (pair h H))) = eq-htpy-equiv refl-htpy

is-equiv-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → is-equiv (inv-equiv {A = A} {B = B})
is-equiv-inv-equiv =
  is-equiv-has-inverse
    ( inv-equiv)
    ( inv-inv-equiv)
    ( inv-inv-equiv)

equiv-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) ≃ (B ≃ A)
equiv-inv-equiv = pair inv-equiv is-equiv-inv-equiv

is-contr-total-equiv' : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → X ≃ A))
is-contr-total-equiv' A =
  is-contr-equiv
    ( Σ (UU _) (λ X → A ≃ X))
    ( equiv-tot (λ X → equiv-inv-equiv))
    ( is-contr-total-equiv A)

abstract
  Ind-equiv : {i j : Level} (A : UU i) (P : (B : UU i) (e : A ≃ B) → UU j) →
    sec (ev-id P)
  Ind-equiv A P =
    IND-EQUIV-is-contr-total-equiv A
    ( is-contr-total-equiv A)
    ( λ t → P (pr1 t) (pr2 t))

ind-equiv : {i j : Level} (A : UU i) (P : (B : UU i) (e : A ≃ B) → UU j) →
  P A (equiv-id A) → {B : UU i} (e : A ≃ B) → P B e
ind-equiv A P p {B} = pr1 (Ind-equiv A P) p B

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

-- Section 12.2 Univalence implies function extensionality

is-equiv-postcomp-univalence :
  {l1 l2 : Level} {X Y : UU l1} (A : UU l2) (e : X ≃ Y) →
  is-equiv (postcomp A (map-equiv e))
is-equiv-postcomp-univalence {X = X} A =
  ind-equiv X
    ( λ Y e → is-equiv (postcomp A (map-equiv e)))
    ( is-equiv-id (A → X))

weak-funext-univalence :
  {l : Level} {A : UU l} {B : A → UU l} → WEAK-FUNEXT A B
weak-funext-univalence {A = A} {B} is-contr-B =
  is-contr-retract-of
    ( fib (postcomp A (pr1 {B = B})) id)
    ( pair
      ( λ f → pair (λ x → pair x (f x)) refl)
      ( pair
        ( λ h x → tr B (htpy-eq (pr2 h) x) (pr2 (pr1 h x)))
        ( refl-htpy)))
    ( is-contr-map-is-equiv
      ( is-equiv-postcomp-univalence A (equiv-pr1 is-contr-B))
      ( id))

funext-univalence :
  {l : Level} {A : UU l} {B : A → UU l} (f : (x : A) → B x) → FUNEXT f
funext-univalence {A = A} {B} f =
  FUNEXT-WEAK-FUNEXT (λ A B → weak-funext-univalence) A B f

-- Section 12.3 Groups in univalent mathematics

{- We first introduce semi-groups, and then groups. We do this because the
   category of groups is a full subcategory of the category of semi-groups.
   In particular, it is a proposition for a semi-group to be a group. Therefore
   this approach gives us in a straightforward way that equality of groups is 
   equality of semi-groups. This will be useful in showing that group 
   isomorphisms are equivalent to identifications of groups. -}

has-associative-mul :
  {l : Level} (X : UU-Set l) → UU l
has-associative-mul X =
  Σ ( ( type-Set X) →
      ( ( type-Set X) → (type-Set X))) (λ μ →
    ( x y z : type-Set X) → Id (μ (μ x y) z) (μ x (μ y z)))

Semi-Group :
  (l : Level) → UU (lsuc l)
Semi-Group l = Σ (UU-Set l) has-associative-mul

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
  has-associative-mul (set-Semi-Group G)
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

{- The property that a semi-group is a monoid is just that the semi-group 
   possesses a unit that satisfies the left and right unit laws. -}

is-unital :
  {l : Level} → Semi-Group l → UU l
is-unital G =
  Σ ( type-Semi-Group G)
    ( λ e →
      ( (y : type-Semi-Group G) → Id (mul-Semi-Group G e y) y) ×
      ( (x : type-Semi-Group G) → Id (mul-Semi-Group G x e) x))

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
  {l : Level} (G : Group l) → has-associative-mul (set-Group G)
associative-mul-Group G = pr2 (semi-group-Group G)

mul-Group :
  {l : Level} (G : Group l) →
  type-Group G → type-Group G → type-Group G
mul-Group G = pr1 (associative-mul-Group G)

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
            ( ( assoc-G (i' x) x (i x)) ∙                   -- = (i'x)·(x·i'x)
              ( ( ap (μ (i' x)) (right-inv-i x)) ∙          -- = (i'x)·1
                ( right-unit-G (i' x)))))))                 -- = i'x

abstract
  is-prop-is-group :
    {l : Level} (G : Semi-Group l) → is-prop (is-group G)
  is-prop-is-group G =
    is-prop-Σ
      ( is-prop-is-unital G)
      ( λ e → is-prop-is-prop' (is-prop-is-group' G e))

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
  {l : Level} (X : UU-Set l) → has-associative-mul (aut-Set X)
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

{- We introduce group homomorphisms. -}

hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) → UU (l1 ⊔ l2)
hom-Group G H =
  hom-Semi-Group
    ( semi-group-Group G)
    ( semi-group-Group H)

{- Bureaucracy of group homomorphisms. -}

map-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( hom-Group G H) →
  ( type-Group G) → (type-Group H)
map-hom-Group G H f = pr1 f

preserves-mul-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  ( f : hom-Group G H) →
  preserves-mul
    ( semi-group-Group G)
    ( semi-group-Group H)
    ( map-hom-Group G H f)
preserves-mul-hom-Group G H f = pr2 f

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

{- Next, we construct the identity group homomorphism, and we show that
   compositions of group homomorphisms are again group homomorphisms. -}

preserves-mul-id :
  {l : Level} (G : Semi-Group l) → preserves-mul G G id
preserves-mul-id (pair (pair G is-set-G) (pair μ-G assoc-G)) x y = refl

id-Semi-Group :
  {l : Level} (G : Semi-Group l) → hom-Semi-Group G G
id-Semi-Group G =
  pair id (preserves-mul-id G)

id-Group :
  {l : Level} (G : Group l) → hom-Group G G
id-Group G = id-Semi-Group (semi-group-Group G)

composition-Semi-Group :
  {l1 l2 l3 : Level} →
  (G : Semi-Group l1) (H : Semi-Group l2) (K : Semi-Group l3) →
  (hom-Semi-Group H K) → (hom-Semi-Group G H) → (hom-Semi-Group G K)
composition-Semi-Group G H K (pair g μ-g) (pair f μ-f) =
  pair
    ( g ∘ f)
    ( λ x y → (ap g (μ-f x y)) ∙ (μ-g (f x) (f y)))

composition-Group :
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3) →
  (hom-Group H K) → (hom-Group G H) → (hom-Group G K)
composition-Group G H K =
  composition-Semi-Group
    ( semi-group-Group G)
    ( semi-group-Group H)
    ( semi-group-Group K)

{- Next, we prove the that the laws for a category hold for group homomorphisms,
   i.e., we show that composition is associative and satisfies the left and
   right unit laws. Before we show that these laws hold, we will characterize
   the identity type of the types of semi-group homomorphisms and group 
   homomorphisms. -}

associative-Semi-Group :
  { l1 l2 l3 l4 : Level} (G : Semi-Group l1) (H : Semi-Group l2)
  ( K : Semi-Group l3) (L : Semi-Group l4) (h : hom-Semi-Group K L) →
  ( g : hom-Semi-Group H K) (f : hom-Semi-Group G H) →
  Id ( composition-Semi-Group G H L
       ( composition-Semi-Group H K L h g) f)
     ( composition-Semi-Group G K L h
       ( composition-Semi-Group G H K g f))
associative-Semi-Group G H K L (pair h μ-h) (pair g μ-g) (pair f μ-f) =
  eq-htpy-hom-Semi-Group G L refl-htpy

left-unit-law-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2)
  ( f : hom-Semi-Group G H) →
  Id ( composition-Semi-Group G H H (id-Semi-Group H) f) f
left-unit-law-Semi-Group G
  (pair (pair H is-set-H) (pair μ-H assoc-H)) (pair f μ-f) =
  eq-htpy-hom-Semi-Group G
    ( pair (pair H is-set-H) (pair μ-H assoc-H))
    ( refl-htpy)

right-unit-law-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2)
  ( f : hom-Semi-Group G H) →
  Id ( composition-Semi-Group G G H f (id-Semi-Group G)) f
right-unit-law-Semi-Group
  (pair (pair G is-set-G) (pair μ-G assoc-G)) H (pair f μ-f) =
  eq-htpy-hom-Semi-Group
    ( pair (pair G is-set-G) (pair μ-G assoc-G)) H refl-htpy

{- Now we introduce the notion of group isomorphism. Finally, we will show that
   isomorphic groups are equal. -}

is-iso-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
  ( f : hom-Semi-Group G H) → UU (l1 ⊔ l2)
is-iso-Semi-Group G H f =
  Σ ( hom-Semi-Group H G) (λ g →
    ( Id (composition-Semi-Group H G H f g) (id-Semi-Group H)) ×
    ( Id (composition-Semi-Group G H G g f) (id-Semi-Group G)))

iso-Semi-Group :
  { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) → UU (l1 ⊔ l2)
iso-Semi-Group G H =
  Σ (hom-Semi-Group G H) (is-iso-Semi-Group G H)

abstract
  is-prop-is-iso-Semi-Group' :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f : hom-Semi-Group G H) → is-prop' (is-iso-Semi-Group G H f)
  is-prop-is-iso-Semi-Group' G H f
    (pair g (pair issec isretr)) (pair g' (pair issec' isretr')) =
    eq-subtype
      ( λ h →
        is-prop-prod
          ( is-set-hom-Semi-Group H H
            ( composition-Semi-Group H G H f h)
            ( id-Semi-Group H))
          ( is-set-hom-Semi-Group G G
            ( composition-Semi-Group G H G h f)
            ( id-Semi-Group G)))
      ( ( inv (left-unit-law-Semi-Group H G g)) ∙
        ( ( inv (ap (λ h → composition-Semi-Group H G G h g) isretr')) ∙
          ( ( associative-Semi-Group H G H G g' f g) ∙
            ( ( ap (composition-Semi-Group H H G g') issec) ∙
              ( right-unit-law-Semi-Group H G g')))))

abstract
  is-prop-is-iso-Semi-Group :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f : hom-Semi-Group G H) → is-prop (is-iso-Semi-Group G H f)
  is-prop-is-iso-Semi-Group G H f =
    is-prop-is-prop' (is-prop-is-iso-Semi-Group' G H f)

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
    is-iso-Semi-Group G H f
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
  is-equiv-hom-is-iso-Semi-Group :
    { l1 l2 : Level} (G : Semi-Group l1) (H : Semi-Group l2) →
    ( f : hom-Semi-Group G H) (is-iso-f : is-iso-Semi-Group G H f) →
    ( is-equiv (pr1 f))
  is-equiv-hom-is-iso-Semi-Group
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
  ( μ-H : has-associative-mul H) →
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
          ( is-prop-is-iso-Semi-Group G H)
          ( is-iso-is-equiv-hom-Semi-Group G H)
          ( is-equiv-hom-is-iso-Semi-Group G H)) ∘e
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
  Σ (has-associative-mul (pr1 G)) (λ μ → preserves-mul G (pair (pr1 G) μ) id)
center-total-preserves-mul-id (pair (pair G is-set-G) (pair μ-G assoc-G)) =
  pair (pair μ-G assoc-G) (λ x y → refl)

contraction-total-preserves-mul-id :
  { l1 : Level} (G : Semi-Group l1) →
  ( t : Σ ( has-associative-mul (pr1 G))
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
  is-contr (Σ (has-associative-mul (pr1 G)) (λ μ → preserves-mul G (pair (pr1 G) μ) id))
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
    ( id-Semi-Group G)
    ( pair
      ( id-Semi-Group G)
      ( pair
        ( left-unit-law-Semi-Group G G (id-Semi-Group G))
        ( right-unit-law-Semi-Group G G (id-Semi-Group G))))

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

{- Finally we show that isomorphic groups are equal. -}

iso-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) → UU (l1 ⊔ l2)
iso-Group G H =
  iso-Semi-Group
    ( semi-group-Group G)
    ( semi-group-Group H)

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

-- Exercises

-- Exercise 10.1

tr-equiv-eq-ap : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A}
  (p : Id x y) → (map-equiv (equiv-eq (ap B p))) ~ tr B p
tr-equiv-eq-ap refl = refl-htpy

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

is-trunc-UU-trunc :
  (k : 𝕋) (i : Level) → is-trunc (succ-𝕋 k) (Σ (UU i) (is-trunc k))
is-trunc-UU-trunc k i X Y =
  is-trunc-is-equiv k
    ( Id (pr1 X) (pr1 Y))
    ( ap pr1)
    ( is-emb-pr1-is-subtype
      ( is-prop-is-trunc k) X Y)
    ( is-trunc-is-equiv k
      ( (pr1 X) ≃ (pr1 Y))
      ( equiv-eq)
      ( univalence (pr1 X) (pr1 Y))
      ( is-trunc-equiv-is-trunc k (pr2 X) (pr2 Y)))

ev-true-false :
  {l : Level} (A : UU l) → (f : bool → A) → A × A
ev-true-false A f = pair (f true) (f false)

map-universal-property-bool :
  {l : Level} {A : UU l} →
  A × A → (bool → A)
map-universal-property-bool (pair x y) true = x
map-universal-property-bool (pair x y) false = y

issec-map-universal-property-bool :
  {l : Level} {A : UU l} →
  ((ev-true-false A) ∘ map-universal-property-bool) ~ id
issec-map-universal-property-bool (pair x y) =
  eq-pair-triv (pair refl refl)

isretr-map-universal-property-bool' :
  {l : Level} {A : UU l} (f : bool → A) →
  (map-universal-property-bool (ev-true-false A f)) ~ f
isretr-map-universal-property-bool' f true = refl
isretr-map-universal-property-bool' f false = refl

isretr-map-universal-property-bool :
  {l : Level} {A : UU l} →
  (map-universal-property-bool ∘ (ev-true-false A)) ~ id
isretr-map-universal-property-bool f =
  eq-htpy (isretr-map-universal-property-bool' f)

universal-property-bool :
  {l : Level} (A : UU l) →
  is-equiv (λ (f : bool → A) → pair (f true) (f false))
universal-property-bool A =
  is-equiv-has-inverse
    map-universal-property-bool
    issec-map-universal-property-bool
    isretr-map-universal-property-bool

ev-true :
  {l : Level} {A : UU l} → (bool → A) → A
ev-true f = f true

triangle-ev-true :
  {l : Level} (A : UU l) →
  (ev-true) ~ (pr1 ∘ (ev-true-false A))
triangle-ev-true A = refl-htpy

aut-bool-bool :
  bool → (bool ≃ bool)
aut-bool-bool true = equiv-id bool
aut-bool-bool false = equiv-neg-𝟚

bool-aut-bool :
  (bool ≃ bool) → bool
bool-aut-bool e = map-equiv e true

decide-true-false :
  (b : bool) → coprod (Id b true) (Id b false)
decide-true-false true = inl refl
decide-true-false false = inr refl

eq-false :
  (b : bool) → (¬ (Id b true)) → (Id b false)
eq-false true p = ind-empty (p refl)
eq-false false p = refl

eq-true :
  (b : bool) → (¬ (Id b false)) → Id b true
eq-true true p = refl
eq-true false p = ind-empty (p refl)

eq-false-equiv' :
  (e : bool ≃ bool) → Id (map-equiv e true) true →
  is-decidable (Id (map-equiv e false) false) → Id (map-equiv e false) false
eq-false-equiv' e p (inl q) = q
eq-false-equiv' e p (inr x) =
  ind-empty
    ( Eq-𝟚-eq true false
      ( ap pr1
        ( is-prop-is-contr'
          ( is-contr-map-is-equiv (is-equiv-map-equiv e) true)
          ( pair true p)
          ( pair false (eq-true (map-equiv e false) x)))))

eq-false-equiv :
  (e : bool ≃ bool) → Id (map-equiv e true) true → Id (map-equiv e false) false
eq-false-equiv e p =
  eq-false-equiv' e p (has-decidable-equality-𝟚 (map-equiv e false) false)

{-
eq-true-equiv :
  (e : bool ≃ bool) →
  ¬ (Id (map-equiv e true) true) → Id (map-equiv e false) true
eq-true-equiv e f = {!!}

issec-bool-aut-bool' :
  ( e : bool ≃ bool) (d : is-decidable (Id (map-equiv e true) true)) →
  htpy-equiv (aut-bool-bool (bool-aut-bool e)) e
issec-bool-aut-bool' e (inl p) true =
  ( htpy-equiv-eq (ap aut-bool-bool p) true) ∙ (inv p)
issec-bool-aut-bool' e (inl p) false =
  ( htpy-equiv-eq (ap aut-bool-bool p) false) ∙
  ( inv (eq-false-equiv e p))
issec-bool-aut-bool' e (inr f) true =
  ( htpy-equiv-eq
    ( ap aut-bool-bool (eq-false (map-equiv e true) f)) true) ∙
  ( inv (eq-false (map-equiv e true) f))
issec-bool-aut-bool' e (inr f) false =
  ( htpy-equiv-eq (ap aut-bool-bool {!eq-true-equiv e ?!}) {!!}) ∙
  ( inv {!!})

issec-bool-aut-bool :
  (aut-bool-bool ∘ bool-aut-bool) ~ id
issec-bool-aut-bool e =
  eq-htpy-equiv
    ( issec-bool-aut-bool' e
      ( has-decidable-equality-𝟚 (map-equiv e true) true))
-}

-- Exercise

unit-classical-Prop : classical-Prop lzero
unit-classical-Prop =
  pair (pair {!!} {!!}) {!!}

raise-unit-classical-Prop :
  (l : Level) → classical-Prop l
raise-unit-classical-Prop l =
  pair
    ( pair
      ( raise l unit)
      ( is-prop-is-equiv' unit
        ( map-raise l unit)
        ( is-equiv-map-raise l unit)
        ( is-prop-unit)))
    ( inl (map-raise l unit star))

bool-classical-Prop :
  (l : Level) → classical-Prop l → bool
bool-classical-Prop l (pair P (inl x)) = true
bool-classical-Prop l (pair P (inr x)) = false

classical-Prop-bool :
  (l : Level) → bool → classical-Prop l
classical-Prop-bool l true = raise-unit-classical-Prop l
classical-Prop-bool l false = {!!}

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

-- Exercise

{-
hom-mul-Group :
  {l : Level} (G : Group l) →
  hom-Group G Aut
-}

-- Reviewing

LL : {l1 : Level} (l2 : Level) (X : UU l1) → UU ((lsuc l2) ⊔ l1)
LL l2 X = Σ (UU l2) (λ P → (P → X) × (is-prop P))

Eq-LL :
  {l1 : Level} (l2 : Level) (X : UU l1) →
  (x y : LL l2 X) → UU (l2 ⊔ l1)
Eq-LL l2 X (pair P (pair f p)) y =
  Σ (P ≃ (pr1 y)) (λ e → f ~ ((pr1 (pr2 y)) ∘ (map-equiv e)))

reflexive-Eq-LL :
  {l1 : Level} (l2 : Level) (X : UU l1) →
  (x : LL l2 X) → Eq-LL l2 X x x
reflexive-Eq-LL l2 X (pair P (pair f p)) = pair (equiv-id P) refl-htpy

Eq-LL-eq :
  {l1 l2 : Level} {X : UU l1} →
  (x y : LL l2 X) → Id x y → Eq-LL l2 X x y
Eq-LL-eq {l1} {l2} {X} x .x refl = reflexive-Eq-LL l2 X x

is-contr-total-Eq-LL :
  {l1 l2 : Level} {X : UU l1} (x : LL l2 X) →
  is-contr (Σ (LL l2 X) (Eq-LL l2 X x))
is-contr-total-Eq-LL (pair P (pair f p)) =
  is-contr-total-Eq-structure
    ( λ Q gq (e : P ≃ Q) → f ~ ((pr1 gq) ∘ (map-equiv e)))
    ( is-contr-total-equiv P)
    ( pair P (equiv-id P))
    ( is-contr-total-Eq-substructure
      ( is-contr-total-htpy f)
      ( λ h → is-prop-is-prop P)
      ( f)
      ( refl-htpy)
      ( p))

unit-LL : {l1 : Level} (l2 : Level) {X : UU l1} → X → LL l2 X
unit-LL l2 {X} x =
  pair
    ( raise l2 unit)
    ( pair
      ( const (raise l2 unit) X x)
      ( is-prop-is-equiv'
        unit
        ( map-raise l2 unit)
        ( is-equiv-map-raise l2 unit)
        is-prop-unit))

functor-LL :
  {l1 l1' : Level} (l2 : Level) {X : UU l1} {X' : UU l1'} (h : X → X') →
  LL l2 X → LL l2 X'
functor-LL l2 h =
  tot
    ( λ P →
      toto
        ( λ f → is-prop P)
        ( λ f → h ∘ f)
        ( λ f → id))

htpy-id-functor-LL :
  {l1 : Level} (l2 : Level) {X : UU l1} →
  (functor-LL l2 (id {A = X})) ~ id
htpy-id-functor-LL l2 {X} (pair P (pair f p)) = refl

mul-LL :
  {l1 l2 : Level} (X : UU l1) → (LL l2 (LL l2 X)) → LL l2 X
mul-LL X (pair P (pair f p)) =
  pair
    ( Σ P (λ p → pr1 (f p)))
    ( pair
      ( λ p → {!!})
      {!!})

