{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module 20-sequences where

import 19-id-pushout
open 19-id-pushout public

{- We introduce two types of sequences: one with the arrows going up and one
   with the arrows going down. -}

Sequence :
  ( l : Level) → UU (lsuc l)
Sequence l = Σ (ℕ → UU l) (λ A → (n : ℕ) → A n → A (succ-ℕ n))

type-seq :
  { l : Level} (A : Sequence l) → (n : ℕ) → UU l
type-seq A = pr1 A

map-seq :
  { l : Level} (A : Sequence l) →
  ( n : ℕ) → (type-seq A n) → (type-seq A (succ-ℕ n))
map-seq A = pr2 A

Sequence' :
  ( l : Level) → UU (lsuc l)
Sequence' l = Σ (ℕ → UU l) (λ A → (n : ℕ) → A (succ-ℕ n) → A n)

type-seq' :
  { l : Level} (A : Sequence' l) → (n : ℕ) → UU l
type-seq' A = pr1 A

map-seq' :
  { l : Level} (A : Sequence' l) →
  (n : ℕ) → (type-seq' A (succ-ℕ n)) → (type-seq' A n)
map-seq' A = pr2 A

{- We characterize the identity type of Sequence l. -}

naturality-hom-Seq :
  { l1 l2 : Level} (A : Sequence l1) (B : Sequence l2)
  ( h : (n : ℕ) → type-seq A n → type-seq B n) (n : ℕ) → UU (l1 ⊔ l2)
naturality-hom-Seq A B h n =
  ((map-seq B n) ∘ (h n)) ~ ((h (succ-ℕ n)) ∘ (map-seq A n))

equiv-Seq :
  { l1 l2 : Level} (A : Sequence l1) (B : Sequence l2) → UU (l1 ⊔ l2)
equiv-Seq A B =
  Σ ( (n : ℕ) → (type-seq A n) ≃ (type-seq B n))
    ( λ e → (n : ℕ) →
      naturality-hom-Seq A B (λ n → map-equiv (e n)) n)

reflexive-equiv-Seq :
  { l1 : Level} (A : Sequence l1) → equiv-Seq A A
reflexive-equiv-Seq A =
  pair
    ( λ n → equiv-id (type-seq A n))
    ( λ n → htpy-refl)

equiv-eq-Seq :
  { l1 : Level} (A B : Sequence l1) → Id A B → equiv-Seq A B
equiv-eq-Seq A .A refl = reflexive-equiv-Seq A

is-contr-total-equiv-Seq :
  { l1 : Level} (A : Sequence l1) →
  is-contr (Σ (Sequence l1) (equiv-Seq A))
is-contr-total-equiv-Seq A =
  is-contr-total-Eq-structure
    ( λ B g (e : (n : ℕ) → (type-seq A n) ≃ B n) →
      (n : ℕ) → naturality-hom-Seq A (pair B g) (λ n → map-equiv (e n)) n)
    ( is-contr-total-Eq-Π
      ( λ n X → type-seq A n ≃ X)
      ( λ n → is-contr-total-equiv (type-seq A n))
      ( type-seq A))
    ( pair (type-seq A) (λ n → equiv-id (type-seq A n)))
    ( is-contr-total-Eq-Π
      ( λ n h → h ~ (map-seq A n))
      ( λ n → is-contr-total-htpy' (map-seq A n))
      ( map-seq A))

is-equiv-equiv-eq-Seq :
  { l1 : Level} (A B : Sequence l1) → is-equiv (equiv-eq-Seq A B)
is-equiv-equiv-eq-Seq A =
  fundamental-theorem-id A
    ( reflexive-equiv-Seq A)
    ( is-contr-total-equiv-Seq A)
    ( equiv-eq-Seq A)

eq-equiv-Seq :
  { l1 : Level} {A B : Sequence l1} → equiv-Seq A B → Id A B
eq-equiv-Seq {A = A} {B} =
  inv-is-equiv (is-equiv-equiv-eq-Seq A B)

{- We characterize the identity type of Sequence' l. -}

equiv-Seq' :
  { l1 l2 : Level} (A : Sequence' l1) (B : Sequence' l2) → UU (l1 ⊔ l2)
equiv-Seq' A B =
  Σ ( (n : ℕ) → (type-seq' A n) ≃ (type-seq' B n)) (λ e →
    ( n : ℕ) →
      ( (map-seq' B n) ∘ (map-equiv (e (succ-ℕ n)))) ~
      ( (map-equiv (e n)) ∘ (map-seq' A n)))

reflexive-equiv-Seq' :
  { l1 : Level} (A : Sequence' l1) → equiv-Seq' A A
reflexive-equiv-Seq' A =
  pair
    ( λ n → equiv-id (type-seq' A n))
    ( λ n → htpy-refl)

equiv-eq-Seq' :
  { l1 : Level} (A B : Sequence' l1) → Id A B → equiv-Seq' A B
equiv-eq-Seq' A .A refl = reflexive-equiv-Seq' A

is-contr-total-equiv-Seq' :
  { l1 : Level} (A : Sequence' l1) →
  is-contr (Σ (Sequence' l1) (equiv-Seq' A))
is-contr-total-equiv-Seq' A =
  is-contr-total-Eq-structure
    ( λ B g (e : (n : ℕ) → (type-seq' A n) ≃ (B n)) → (n : ℕ) →
      ( (g n) ∘ (map-equiv (e (succ-ℕ n)))) ~
      ( (map-equiv (e n)) ∘ (map-seq' A n)))
    ( is-contr-total-Eq-Π
      ( λ n B → (type-seq' A n) ≃ B)
      ( λ n → is-contr-total-equiv (type-seq' A n))
      ( type-seq' A))
    ( pair (type-seq' A) (λ n → equiv-id (type-seq' A n)))
    ( is-contr-total-Eq-Π
      ( λ n g → g ~ (map-seq' A n))
      ( λ n → is-contr-total-htpy' (map-seq' A n))
      ( map-seq' A))

is-equiv-equiv-eq-Seq' :
  { l1 : Level} (A B : Sequence' l1) → is-equiv (equiv-eq-Seq' A B)
is-equiv-equiv-eq-Seq' A =
  fundamental-theorem-id A
    ( reflexive-equiv-Seq' A)
    ( is-contr-total-equiv-Seq' A)
    ( equiv-eq-Seq' A)

eq-equiv-Seq' :
  { l1 : Level} (A B : Sequence' l1) → equiv-Seq' A B → Id A B
eq-equiv-Seq' A B = inv-is-equiv (is-equiv-equiv-eq-Seq' A B)

{- We introduce cones on a type sequence. -}

cone-sequence :
  { l1 l2 : Level} (A : Sequence' l1) (X : UU l2) → UU (l1 ⊔ l2)
cone-sequence A X =
  Σ ( (n : ℕ) → X → type-seq' A n)
    ( λ p → (n : ℕ) → ((map-seq' A n) ∘ (p (succ-ℕ n))) ~ (p n))

map-cone-sequence :
  { l1 l2 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  ( n : ℕ) → X → type-seq' A n
map-cone-sequence A c = pr1 c

triangle-cone-sequence :
  { l1 l2 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  ( n : ℕ) →
  ( (map-seq' A n) ∘ (map-cone-sequence A c (succ-ℕ n))) ~
  ( map-cone-sequence A c n)
triangle-cone-sequence A c = pr2 c

{- We characterize the identity type of cone-sequence. -}

naturality-htpy-cone-sequence :
  { l1 l2 : Level} (A : Sequence' l1) {X : UU l2} (c c' : cone-sequence A X) →
  ( H : (n : ℕ) → (map-cone-sequence A c n) ~ (map-cone-sequence A c' n)) →
  ( n : ℕ) → UU (l1 ⊔ l2)
naturality-htpy-cone-sequence A c c' H n =
  ( ((map-seq' A n) ·l (H (succ-ℕ n))) ∙h (triangle-cone-sequence A c' n)) ~
  ( (triangle-cone-sequence A c n) ∙h (H n))

htpy-cone-sequence :
  { l1 l2 : Level} (A : Sequence' l1) {X : UU l2} →
  ( c c' : cone-sequence A X) → UU (l1 ⊔ l2)
htpy-cone-sequence A c c' =
  Σ ( (n : ℕ) → (map-cone-sequence A c n) ~ (map-cone-sequence A c' n)) (λ H →
    (n : ℕ) → naturality-htpy-cone-sequence A c c' H n)

reflexive-htpy-cone-sequence :
  { l1 l2 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  htpy-cone-sequence A c c
reflexive-htpy-cone-sequence A c =
  pair
    ( λ n → htpy-refl)
    ( λ n → htpy-inv htpy-right-unit)

htpy-cone-sequence-eq :
  { l1 l2 : Level} (A : Sequence' l1) {X : UU l2} (c c' : cone-sequence A X) →
  Id c c' → htpy-cone-sequence A c c'
htpy-cone-sequence-eq A c .c refl = reflexive-htpy-cone-sequence A c

is-contr-total-htpy-cone-sequence :
  { l1 l2 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  is-contr (Σ (cone-sequence A X) (htpy-cone-sequence A c))
is-contr-total-htpy-cone-sequence A c =
  is-contr-total-Eq-structure
    ( λ p t H → (n : ℕ) → naturality-htpy-cone-sequence A c (pair p t) H n)
    ( is-contr-total-Eq-Π
      ( λ n pn → (map-cone-sequence A c n) ~ pn)
      ( λ n → is-contr-total-htpy (map-cone-sequence A c n))
      ( map-cone-sequence A c))
    ( pair (map-cone-sequence A c) (λ n → htpy-refl))
    ( is-contr-total-Eq-Π
      ( λ n H → H ~ ((triangle-cone-sequence A c n) ∙h htpy-refl))
      ( λ n →
        is-contr-total-htpy' ((triangle-cone-sequence A c n) ∙h htpy-refl))
      ( triangle-cone-sequence A c))

is-equiv-htpy-cone-sequence-eq :
  { l1 l2 : Level} (A : Sequence' l1) {X : UU l2} (c c' : cone-sequence A X) →
  is-equiv (htpy-cone-sequence-eq A c c')
is-equiv-htpy-cone-sequence-eq A c =
  fundamental-theorem-id c
    ( reflexive-htpy-cone-sequence A c)
    ( is-contr-total-htpy-cone-sequence A c)
    ( htpy-cone-sequence-eq A c)

eq-htpy-cone-sequence :
  { l1 l2 : Level} (A : Sequence' l1) {X : UU l2} (c c' : cone-sequence A X) →
  htpy-cone-sequence A c c' → Id c c'
eq-htpy-cone-sequence A {X} c c' =
  inv-is-equiv (is-equiv-htpy-cone-sequence-eq A c c')

equiv-htpy-cone-sequence-eq :
  { l1 l2 : Level} (A : Sequence' l1) {X : UU l2} (c c' : cone-sequence A X) →
  Id c c' ≃ (htpy-cone-sequence A c c')
equiv-htpy-cone-sequence-eq A c c' =
  pair
    ( htpy-cone-sequence-eq A c c')
    ( is-equiv-htpy-cone-sequence-eq A c c')

{- We introduce sequential limits. -}

cone-sequence-map :
  { l1 l2 l3 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  ( Y : UU l3) → (Y → X) → cone-sequence A Y
cone-sequence-map A c Y h =
  pair
    ( λ n → (map-cone-sequence A c n) ∘ h)
    ( λ n → (triangle-cone-sequence A c n) ·r h)

universal-property-sequential-limit :
  ( l : Level) {l1 l2 : Level} (A : Sequence' l1) {X : UU l2}
  ( c : cone-sequence A X) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-sequential-limit l A c =
  (Y : UU l) → is-equiv (cone-sequence-map A c Y)

{- We introduce the canonical sequential limit. -}

canonical-sequential-limit :
  { l1 : Level} (A : Sequence' l1) → UU l1
canonical-sequential-limit A =
  Σ ( (n : ℕ) → type-seq' A n)
    ( λ a → (n : ℕ) → Id (map-seq' A n (a (succ-ℕ n))) (a n))

{- We characterize the identity type of the canonical sequential limit. -}

Eq-canonical-sequential-limit :
  { l1 : Level} (A : Sequence' l1) (x y : canonical-sequential-limit A) → UU l1
Eq-canonical-sequential-limit A x y =
  Σ ( (pr1 x) ~ (pr1 y)) (λ H →
    (n : ℕ) →
    Id ((ap (map-seq' A n) (H (succ-ℕ n))) ∙ (pr2 y n)) ((pr2 x n) ∙ (H n)))

reflexive-Eq-canonical-sequential-limit :
  { l1 : Level} (A : Sequence' l1) (x : canonical-sequential-limit A) →
  Eq-canonical-sequential-limit A x x
reflexive-Eq-canonical-sequential-limit A x =
  pair htpy-refl (htpy-inv htpy-right-unit)

Eq-canonical-sequential-limit-eq :
  { l1 : Level} (A : Sequence' l1) (x y : canonical-sequential-limit A) →
  Id x y → Eq-canonical-sequential-limit A x y
Eq-canonical-sequential-limit-eq A x .x refl =
  reflexive-Eq-canonical-sequential-limit A x

is-contr-total-Eq-canonical-sequential-limit :
  { l1 : Level} (A : Sequence' l1) (x : canonical-sequential-limit A) →
  is-contr
    ( Σ (canonical-sequential-limit A) (Eq-canonical-sequential-limit A x))
is-contr-total-Eq-canonical-sequential-limit A x =
  is-contr-total-Eq-structure
    ( λ y q (H : (n : ℕ) → Id (pr1 x n) (y n)) →
      (n : ℕ) →
        Id ((ap (map-seq' A n) (H (succ-ℕ n))) ∙ (q n)) ((pr2 x n) ∙ (H n)))
    ( is-contr-total-Eq-Π
      ( λ n yn → Id (pr1 x n) yn)
      ( λ n → is-contr-total-path (pr1 x n))
      ( pr1 x))
    ( pair (pr1 x) htpy-refl)
    ( is-contr-total-Eq-Π
      ( λ n q → Id q ((pr2 x n) ∙ refl))
      ( λ n → is-contr-total-path' ((pr2 x n) ∙ refl))
      ( pr2 x))

is-equiv-Eq-canonical-sequential-limit :
  { l1 : Level} (A : Sequence' l1) (x y : canonical-sequential-limit A) →
  is-equiv (Eq-canonical-sequential-limit-eq A x y)
is-equiv-Eq-canonical-sequential-limit A x =
  fundamental-theorem-id x
    ( reflexive-Eq-canonical-sequential-limit A x)
    ( is-contr-total-Eq-canonical-sequential-limit A x)
    ( Eq-canonical-sequential-limit-eq A x)

eq-Eq-canonical-sequential-limit :
  { l1 : Level} (A : Sequence' l1) {x y : canonical-sequential-limit A} →
  Eq-canonical-sequential-limit A x y → Id x y
eq-Eq-canonical-sequential-limit A {x} {y} =
  inv-is-equiv (is-equiv-Eq-canonical-sequential-limit A x y)

{- We equip the canonical sequential limit with the structure of a cone. -}

cone-canonical-sequential-limit :
  { l1 : Level} (A : Sequence' l1) →
  cone-sequence A (canonical-sequential-limit A)
cone-canonical-sequential-limit A =
  pair
    ( λ n a → pr1 a n)
    ( λ n a → pr2 a n)

{- We show that the canonical sequential limit satisfies the universal property
   of sequential limits. -}

inv-canonical-cone-sequence-map :
  { l1 l2 : Level} (A : Sequence' l1) (Y : UU l2) →
  cone-sequence A Y → (Y → canonical-sequential-limit A)
inv-canonical-cone-sequence-map A Y c y =
  pair
    ( λ n → map-cone-sequence A c n y)
    ( λ n → triangle-cone-sequence A c n y)

issec-inv-canonical-cone-sequence-map :
  { l1 l2 : Level} (A : Sequence' l1) (Y : UU l2) →
  ( ( cone-sequence-map A (cone-canonical-sequential-limit A) Y) ∘
    ( inv-canonical-cone-sequence-map A Y)) ~ id
issec-inv-canonical-cone-sequence-map A Y c =
  eq-htpy-cone-sequence A
    ( cone-sequence-map A
      ( cone-canonical-sequential-limit A)
      ( Y)
      ( inv-canonical-cone-sequence-map A Y c))
    ( c)
    ( reflexive-htpy-cone-sequence A c)

isretr-inv-canonical-cone-sequence-map :
  { l1 l2 : Level} (A : Sequence' l1) (Y : UU l2) →
  ( ( inv-canonical-cone-sequence-map A Y) ∘
    ( cone-sequence-map A (cone-canonical-sequential-limit A) Y)) ~ id
isretr-inv-canonical-cone-sequence-map A Y h =
  eq-htpy (λ y →
    eq-Eq-canonical-sequential-limit A
      ( reflexive-Eq-canonical-sequential-limit A (h y)))

universal-property-canonical-sequential-limit :
  ( l : Level) {l1 : Level} (A : Sequence' l1) →
  universal-property-sequential-limit l A (cone-canonical-sequential-limit A)
universal-property-canonical-sequential-limit l A Y =
  is-equiv-has-inverse
    ( inv-canonical-cone-sequence-map A Y)
    ( issec-inv-canonical-cone-sequence-map A Y)
    ( isretr-inv-canonical-cone-sequence-map A Y)

{- Unique mapping property for sequential limits. -}

unique-mapping-property-sequential-limit' :
  { l1 l2 l3 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  ( up-X : (l : Level) → universal-property-sequential-limit l A c)
  { Y : UU l3} (c' : cone-sequence A Y) →
  is-contr (fib (cone-sequence-map A c Y) c')
unique-mapping-property-sequential-limit' {l3 = l3} A c up-X {Y} =
  is-contr-map-is-equiv (up-X l3 Y)

map-universal-property-sequential-limit :
  { l1 l2 l3 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  ( up-X : (l : Level) → universal-property-sequential-limit l A c) →
  { Y : UU l3} (c' : cone-sequence A Y) → Y → X
map-universal-property-sequential-limit A c up-X c' =
  pr1 (center (unique-mapping-property-sequential-limit' A c up-X c'))

path-universal-property-sequential-limit :
  { l1 l2 l3 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  ( up-X : (l : Level) → universal-property-sequential-limit l A c) →
  { Y : UU l3} (c' : cone-sequence A Y) →
  Id ( cone-sequence-map A c Y
       ( map-universal-property-sequential-limit A c up-X c'))
     ( c')
path-universal-property-sequential-limit A c up-X c' =
  pr2 (center (unique-mapping-property-sequential-limit' A c up-X c'))

unique-mapping-property-sequential-limit :
  { l1 l2 l3 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  ( up-X : (l : Level) → universal-property-sequential-limit l A c) →
  { Y : UU l3} (c' : cone-sequence A Y) →
  is-contr
    ( Σ ( Y → X)
        ( λ h → htpy-cone-sequence A (cone-sequence-map A c Y h) c'))
unique-mapping-property-sequential-limit {l3 = l3} A c up-X {Y} c' =
  is-contr-equiv'
    ( fib (cone-sequence-map A c Y) c')
    ( equiv-tot
      ( λ h → equiv-htpy-cone-sequence-eq A (cone-sequence-map A c Y h) c'))
    ( unique-mapping-property-sequential-limit' A c up-X c')

htpy-universal-property-sequential-limit :
  { l1 l2 l3 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  ( up-X : (l : Level) → universal-property-sequential-limit l A c) →
  { Y : UU l3} (c' : cone-sequence A Y) →
  htpy-cone-sequence A
    ( cone-sequence-map A c Y
      ( map-universal-property-sequential-limit A c up-X c'))
    ( c')
htpy-universal-property-sequential-limit A c up-X {Y} c' =
  htpy-cone-sequence-eq A
    ( cone-sequence-map A c Y
      ( map-universal-property-sequential-limit A c up-X c'))
    ( c')
    ( path-universal-property-sequential-limit A c up-X c')

uniqueness-map-sequential-limit' :
  { l1 l2 l3 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  ( up-X : (l : Level) → universal-property-sequential-limit l A c)
  { Y : UU l3} (c' : cone-sequence A Y) →
  ( h : Y → X) (H : Id (cone-sequence-map A c Y h) c')
  ( h' : Y → X) (H' : Id (cone-sequence-map A c Y h') c') →
  h ~ h'
uniqueness-map-sequential-limit' A c up-X c' h H h' H' =
  htpy-eq
    ( ap pr1
      ( is-prop-is-contr'
        ( unique-mapping-property-sequential-limit' A c up-X c')
          ( pair h H)
          ( pair h' H')))

uniqueness-map-sequential-limit :
  { l1 l2 l3 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  ( up-X : (l : Level) → universal-property-sequential-limit l A c) →
  { Y : UU l3} (c' : cone-sequence A Y)
  ( h : Y → X) (H : htpy-cone-sequence A (cone-sequence-map A c Y h) c')
  ( h' : Y → X) (H' : htpy-cone-sequence A (cone-sequence-map A c Y h') c') →
  h ~ h'
uniqueness-map-sequential-limit A c up-X c' h H h' H' =
  htpy-eq
    ( ap pr1
      ( is-prop-is-contr'
        ( unique-mapping-property-sequential-limit A c up-X c')
        ( pair h H)
        ( pair h' H')))
    
{- We show a 3-for-2 property of sequential limits. -}

compose-cone-sequence-map :
  { l1 l2 l3 l4 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X)
  { Y : UU l3} {Z : UU l4} (h : Y → X) (k : Z → Y) →
  Id ( cone-sequence-map A (cone-sequence-map A c Y h) Z k)
     ( cone-sequence-map A c Z (h ∘ k))
compose-cone-sequence-map A c h k = refl

module 3-for-2-sequential-limit
  { l1 l2 l3 : Level} (A : Sequence' l1) {X : UU l2} {Y : UU l3}
  ( c : cone-sequence A X) (c' : cone-sequence A Y) (h : Y → X)
  ( e : htpy-cone-sequence A (cone-sequence-map A c Y h) c')
  where

  triangle-cone-cone-sequence :
    {l4 : Level} (Z : UU  l4) →
      ( cone-sequence-map A c' Z) ~
      ( ( cone-sequence-map A c Z) ∘ (λ (k : Z → Y) → h ∘ k))
  triangle-cone-cone-sequence Z k =
    ap (λ t → cone-sequence-map A t Z k)
      (inv (eq-htpy-cone-sequence A (cone-sequence-map A c Y h) c' e))

  is-equiv-universal-property-sequential-limit :
    ((l : Level) → universal-property-sequential-limit l A c) →
    ((l : Level) → universal-property-sequential-limit l A c') →
    is-equiv h
  is-equiv-universal-property-sequential-limit up-X up-Y =
    is-equiv-is-equiv-postcomp h (λ {l} Z →
      is-equiv-right-factor
        ( cone-sequence-map A c' Z)
        ( cone-sequence-map A c Z)
        ( λ k → h ∘ k)
        ( triangle-cone-cone-sequence Z)
        ( up-X l Z)
        ( up-Y l Z))

  universal-property-sequential-limit-is-equiv' :
    ((l : Level) → universal-property-sequential-limit l A c) →
    is-equiv h →
    ((l : Level) → universal-property-sequential-limit l A c')
  universal-property-sequential-limit-is-equiv' up-X is-equiv-h l Z =
    is-equiv-comp
      ( cone-sequence-map A c' Z)
      ( cone-sequence-map A c Z)
      ( λ k → h ∘ k)
      ( triangle-cone-cone-sequence Z)
      ( is-equiv-postcomp-is-equiv h is-equiv-h Z)
      ( up-X l Z)

  universal-property-sequential-limit-is-equiv :
    ((l : Level) → universal-property-sequential-limit l A c') →
    is-equiv h →
    ((l : Level) → universal-property-sequential-limit l A c)
  universal-property-sequential-limit-is-equiv up-Y is-equiv-h l Z =
    is-equiv-left-factor
      ( cone-sequence-map A c' Z)
      ( cone-sequence-map A c Z)
      ( λ k → h ∘ k)
      ( triangle-cone-cone-sequence Z)
      ( up-Y l Z)
      ( is-equiv-postcomp-is-equiv h is-equiv-h Z)

open 3-for-2-sequential-limit public

{- We prove the uniquely uniqueness of sequential limits. -}

uniquely-uniqueness-sequential-limit :
  { l1 l2 l3 : Level} (A : Sequence' l1) {X : UU l2} {Y : UU l3} →
  ( c : cone-sequence A X) (c' : cone-sequence A Y) →
  ( (l : Level) → universal-property-sequential-limit l A c) →
  ( (l : Level) → universal-property-sequential-limit l A c') →
  is-contr (Σ (Y ≃ X)
    (λ e → htpy-cone-sequence A (cone-sequence-map A c Y (map-equiv e)) c'))
uniquely-uniqueness-sequential-limit A {X} {Y} c c' up-X up-Y =
  is-contr-total-Eq-substructure
    ( unique-mapping-property-sequential-limit A c up-X c')
    ( is-subtype-is-equiv)
    ( map-universal-property-sequential-limit A c up-X c')
    ( htpy-universal-property-sequential-limit A c up-X c')
    ( is-equiv-universal-property-sequential-limit A c c'
      ( map-universal-property-sequential-limit A c up-X c')
      ( htpy-universal-property-sequential-limit A c up-X c')
      ( up-X)
      ( up-Y))

{- We introduce the sequence of function types. -}

mapping-sequence :
  { l1 l2 : Level} (A : Sequence' l1) (X : UU l2) → Sequence' (l1 ⊔ l2)
mapping-sequence A X =
  pair
    ( λ n → X → type-seq' A n)
    ( λ n h → (map-seq' A n) ∘ h)

cone-mapping-sequence :
  { l1 l2 l3 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  ( Y : UU l3) → cone-sequence (mapping-sequence A Y) (Y → X)
cone-mapping-sequence A c Y =
  pair
    ( λ n h → (map-cone-sequence A c n) ∘ h)
    ( λ n h → eq-htpy ((triangle-cone-sequence A c n) ·r h))

universal-property-sequential-limit-cone-mapping-sequence :
  { l1 l2 l3 : Level} (A : Sequence' l1) {X : UU l2} (c : cone-sequence A X) →
  ( up-X : (l : Level) → universal-property-sequential-limit l A c) →
  ( Y : UU l3) (l : Level) →
  universal-property-sequential-limit l
    ( mapping-sequence A Y)
    ( cone-mapping-sequence A c Y)
universal-property-sequential-limit-cone-mapping-sequence A c up-X Y l Z =
  {!!}

{- We introduce cocones on a type sequence. -}

cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) (X : UU l2) → UU (l1 ⊔ l2)
cocone-sequence A X =
  Σ ( (n : ℕ) → type-seq A n → X) (λ i →
    (n : ℕ) → (i n) ~ ((i (succ-ℕ n)) ∘ (map-seq A n)))

map-cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} (c : cocone-sequence A X) →
  ( n : ℕ) → type-seq A n → X
map-cocone-sequence A c = pr1 c

triangle-cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} (c : cocone-sequence A X) →
  ( n : ℕ) →
  ( map-cocone-sequence A c n) ~
  ( (map-cocone-sequence A c (succ-ℕ n)) ∘ (map-seq A n))
triangle-cocone-sequence A c = pr2 c

{- We characterize the identity type of cocone-sequence. -}

naturality-htpy-cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} (c c' : cocone-sequence A X) →
  ( H : (n : ℕ) →
    (map-cocone-sequence A c n) ~ (map-cocone-sequence A c' n)) →
  ( n : ℕ) → UU (l1 ⊔ l2)
naturality-htpy-cocone-sequence A c c' H n =
  ( (H n) ∙h (triangle-cocone-sequence A c' n)) ~
      ( ( triangle-cocone-sequence A c n) ∙h
        ( (H (succ-ℕ n)) ·r (map-seq A n)))

htpy-cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2}
  ( c c' : cocone-sequence A X) → UU (l1 ⊔ l2)
htpy-cocone-sequence A c c' =
  Σ ( (n : ℕ) → (map-cocone-sequence A c n) ~ (map-cocone-sequence A c' n))
    ( λ H → (n : ℕ) → naturality-htpy-cocone-sequence A c c' H n)

reflexive-htpy-cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} →
  ( c : cocone-sequence A X) → htpy-cocone-sequence A c c
reflexive-htpy-cocone-sequence A c =
  pair
    ( λ n → htpy-refl)
    ( λ n → htpy-inv htpy-right-unit)

htpy-cocone-sequence-eq :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} →
  ( c c' : cocone-sequence A X) → Id c c' → htpy-cocone-sequence A c c'
htpy-cocone-sequence-eq A c .c refl =
  reflexive-htpy-cocone-sequence A c

is-contr-total-htpy-cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} (c : cocone-sequence A X) →
  is-contr (Σ (cocone-sequence A X) (htpy-cocone-sequence A c))
is-contr-total-htpy-cocone-sequence A c =
  is-contr-total-Eq-structure
    ( λ j t H →
      (n : ℕ) → naturality-htpy-cocone-sequence A c (pair j t) H n)
    ( is-contr-total-Eq-Π
      ( λ n j → map-cocone-sequence A c n ~ j)
      ( λ n → is-contr-total-htpy (map-cocone-sequence A c n))
      ( map-cocone-sequence A c))
    ( pair
      ( map-cocone-sequence A c)
      ( λ n → htpy-refl))
    ( is-contr-total-Eq-Π
      ( λ n H → H ~ ((triangle-cocone-sequence A c n) ∙h htpy-refl))
      ( λ n → is-contr-total-htpy'
        ( (triangle-cocone-sequence A c n) ∙h htpy-refl))
      ( triangle-cocone-sequence A c))

is-equiv-htpy-cocone-sequence-eq :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} (c c' : cocone-sequence A X) →
  is-equiv (htpy-cocone-sequence-eq A c c')
is-equiv-htpy-cocone-sequence-eq A c =
  fundamental-theorem-id c
    ( reflexive-htpy-cocone-sequence A c)
    ( is-contr-total-htpy-cocone-sequence A c)
    ( htpy-cocone-sequence-eq A c)

{- We introduce the universal property of sequential colimits. -}

cocone-sequence-map :
  { l1 l2 l3 : Level} (A : Sequence l1)
  {X : UU l2} → cocone-sequence A X →
  (Y : UU l3) → (X → Y) → cocone-sequence A Y
cocone-sequence-map A c Y h =
  pair
    ( λ n → h ∘ (map-cocone-sequence A c n))
    ( λ n → h ·l (triangle-cocone-sequence A c n))

universal-property-sequential-colimit :
  ( l : Level) {l1 l2 : Level} (A : Sequence l1) {X : UU l2}
  ( c : cocone-sequence A X) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-sequential-colimit l A c =
  (Y : UU l) → is-equiv (cocone-sequence-map A c Y)
