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

Group-operations :
  {l : Level} (G : hSet l) → UU l
Group-operations (pair G is-set-G) =
  (G → G → G) × (G × (G → G))

Group-laws :
  {l : Level} {G : hSet l} (μ : Group-operations G) → UU l
Group-laws {G = pair G is-set-G} (pair μ (pair e i)) =
  Σ ( (x y z : G) → Id (μ (μ x y) z) (μ x (μ y z))) ( λ assoc-μ →
    Σ (((y : G) → Id (μ e y) y) × ((x : G) → Id (μ x e) x)) (λ unit-laws-μ →
      ((x : G) → Id (μ (i x) x) e) × ((x : G) → Id (μ x (i x)) e)))

is-prop-Group-laws :
  {l : Level} {G : hSet l} (μ : Group-operations G) → is-prop (Group-laws μ)
is-prop-Group-laws {G = pair G is-set-G} (pair μ (pair e i)) =
  is-prop-prod
    ( is-prop-Π (λ x →
        is-prop-Π (λ y →
          is-prop-Π (λ z → is-set-G (μ (μ x y) z) (μ x (μ y z))))))
    ( is-prop-prod
      ( is-prop-prod
        ( is-prop-Π (λ y → is-set-G (μ e y) y))
        ( is-prop-Π (λ x → is-set-G (μ x e) x)))
      ( is-prop-prod
        ( is-prop-Π (λ x → is-set-G (μ (i x) x) e))
        ( is-prop-Π (λ x → is-set-G (μ x (i x)) e))))

Group :
  (l : Level) → UU (lsuc l)
Group l =
  Σ (hSet l) (λ G → Σ (Group-operations G) (λ μ → Group-laws μ))

{- We give two examples of groups. The first is the group ℤ of integers. The
   second is the loop space of a pointed 1-type.  -}

group-ℤ : Group lzero
group-ℤ =
  pair set-ℤ
    ( pair
      ( pair add-ℤ (pair zero-ℤ neg-ℤ))
      ( pair associative-add-ℤ
        ( pair
          ( pair left-unit-law-add-ℤ right-unit-law-add-ℤ)
          ( pair left-inverse-law-add-ℤ right-inverse-law-add-ℤ))))

loop-space :
  {l : Level} {A : UU l} → A → UU l
loop-space a = Id a a

set-loop-space :
  {l : Level} (A : 1-type l) (a : pr1 A) → hSet l
set-loop-space (pair A is-1-type-A) a =
  pair (loop-space a) (is-1-type-A a a)

group-loop-space :
  {l : Level} (A : 1-type l) (a : pr1 A) → Group l
group-loop-space (pair A is-1-type-A) a =
  pair
    ( set-loop-space (pair A is-1-type-A) a)
    ( pair
      ( pair
        ( λ p q → p ∙ q)
        ( pair refl inv))
      ( pair assoc
        ( pair
          ( pair (λ y → left-unit) (λ y → right-unit))
          ( pair left-inv right-inv))))

{- Next we define group homomorphisms. We define first a notion of 'complete'
   group homomorphisms, which is postulated to preserve all the group
   operations. We do this because it is easier to first show that equality on
   the type of all groups is equivalent to complete isomorphism. Then we show
   that any ordinary group homomorphism preserves all the group operations as
   a consequence of just preserving the group multiplication. It will follow
   that equality of groups is equivalent to isomorphism. -}

underlying-type-group :
  {l : Level} → Group l → UU l
underlying-type-group (pair (pair G is-set-G) t) = G

preserves-mul-group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) →
  (underlying-type-group G → underlying-type-group H) → UU (l1 ⊔ l2)
preserves-mul-group 
  ( pair (pair G is-set-G) (pair (pair μ-G (pair e-G i-G)) laws-μ-G))
  ( pair (pair H is-set-H) (pair (pair μ-H (pair e-H i-H)) laws-μ-H))
  f =
  (x y : G) → Id (f (μ-G x y)) (μ-H (f x) (f y))

preserves-unit-group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) →
  (underlying-type-group G → underlying-type-group H) → UU l2
preserves-unit-group
  ( pair (pair G is-set-G) (pair (pair μ-G (pair e-G i-G)) laws-μ-G))
  ( pair (pair H is-set-H) (pair (pair μ-H (pair e-H i-H)) laws-μ-H))
  f =
  Id (f e-G) e-H

preserves-inv-group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) →
  (underlying-type-group G → underlying-type-group H) → UU (l1 ⊔ l2)
preserves-inv-group
  ( pair (pair G is-set-G) (pair (pair μ-G (pair e-G i-G)) laws-μ-G))
  ( pair (pair H is-set-H) (pair (pair μ-H (pair e-H i-H)) laws-μ-H))
  f =
  (x : G) → Id (f (i-G x)) (i-H (f x))

complete-Group-Hom :
  {l1 l2 : Level} → Group l1 → Group l2 → UU (l1 ⊔ l2)
complete-Group-Hom G H =
  Σ ( underlying-type-group G → underlying-type-group H) (λ f →
     ( preserves-mul-group G H f) ×
     ( ( preserves-unit-group G H f) × (preserves-inv-group G H f)))

Group-Hom :
  {l1 l2 : Level} → Group l1 → Group l2 → UU (l1 ⊔ l2)
Group-Hom G H =
  Σ ( underlying-type-group G → underlying-type-group H)
    ( preserves-mul-group G H)

{- Now we show that any (ordinary) group homomorphism preserves the unit and
   inverse operation on the group. In other words, any group homomorphism is
   a complete group homomorphism in the above sense. -}

underlying-function-group-hom :
  {l1 l2 : Level} {G : Group l1} {H : Group l2} (f : Group-Hom G H) →
  underlying-type-group G → underlying-type-group H
underlying-function-group-hom f = (pr1 f)

preserves-mul-Group-Hom :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : Group-Hom G H) →
  preserves-mul-group G H (underlying-function-group-hom f)
preserves-mul-Group-Hom G H f = pr2 f

preserves-unit-Group-Hom :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : Group-Hom G H) →
  preserves-unit-group G H (underlying-function-group-hom f)
preserves-unit-Group-Hom
  ( pair
    ( pair G is-set-G)
    ( pair
      ( pair μ-G (pair e-G i-G))
      ( pair assoc-G
        ( pair
          ( pair left-unit-G right-unit-G)
          ( pair left-inv-G right-inv-G)))))
  ( pair
    ( pair H is-set-H)
    ( pair
      ( pair μ-H (pair e-H i-H))
      ( pair assoc-H
        ( pair
          ( pair left-unit-H right-unit-H)
          ( pair left-inv-H right-inv-H)))))
  ( pair f μ-f) =
  ( inv (left-unit-H (f e-G))) ∙
  ( ( ap (λ x → μ-H x (f e-G)) (inv (left-inv-H (f e-G)))) ∙
    ( ( assoc-H (i-H (f e-G)) (f e-G) (f e-G)) ∙
      ( ( ap (μ-H (i-H (f e-G))) (inv (μ-f e-G e-G))) ∙
        ( ( ap (λ x → μ-H (i-H (f e-G)) (f x)) (left-unit-G e-G)) ∙
          ( left-inv-H (f e-G))))))

preserves-inv-Group-Hom :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : Group-Hom G H) →
  preserves-inv-group G H (underlying-function-group-hom f)
preserves-inv-Group-Hom
  ( pair
      ( pair G is-set-G)
      ( pair
        ( pair μ-G (pair e-G i-G))
        ( pair assoc-G
          ( pair
            ( pair left-unit-G right-unit-G)
            ( pair left-inv-G right-inv-G)))))
  ( pair
      ( pair H is-set-H)
      ( pair
        ( pair μ-H (pair e-H i-H))
        ( pair assoc-H
          ( pair
            ( pair left-unit-H right-unit-H)
            ( pair left-inv-H right-inv-H)))))
  ( pair f μ-f) x =
  ( inv ( right-unit-H (f (i-G x)))) ∙
  ( ( ap (μ-H (f (i-G x))) (inv (right-inv-H (f x)))) ∙
    ( ( inv (assoc-H (f (i-G x)) (f x) (i-H (f x)))) ∙
      ( ( inv (ap (λ y → μ-H y (i-H (f x))) (μ-f (i-G x) x))) ∙
        ( ( ap (λ y → μ-H (f y) (i-H (f x))) (left-inv-G x)) ∙
          ( ( ap
              ( λ y → μ-H y (i-H (f x)))
              ( preserves-unit-Group-Hom
                ( pair (pair G is-set-G)
                  ( pair (pair μ-G (pair e-G i-G))
                    ( pair assoc-G
                      ( pair
                        ( pair left-unit-G right-unit-G)
                        ( pair left-inv-G right-inv-G)))))
                ( pair (pair H is-set-H)
                  ( pair (pair μ-H (pair e-H i-H))
                    ( pair assoc-H
                      ( pair
                        ( pair left-unit-H right-unit-H)
                        ( pair left-inv-H right-inv-H)))))
                ( pair f μ-f))) ∙
            ( left-unit-H (i-H (f x))))))))

complete-Group-Hom-ordinary-Group-Hom :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) →
  Group-Hom G H → complete-Group-Hom G H
complete-Group-Hom-ordinary-Group-Hom G H f =
  pair
    ( underlying-function-group-hom f)
    ( pair
      ( preserves-mul-Group-Hom G H f)
      ( pair
        ( preserves-unit-Group-Hom G H f)
        ( preserves-inv-Group-Hom G H f)))

{- Next, we construct the identity group homomorphism, and we show that
   compositions of group homomorphisms are again group homomorphisms. -}
   
complete-id-group :
  {l : Level} (G : Group l) → complete-Group-Hom G G
complete-id-group (pair (pair G is-set-G) (pair (pair μ (pair e i)) laws-μ)) =
  pair id
    ( pair
      ( λ x y → refl)
      ( pair refl htpy-refl))

{- Next, we prove the that the laws for a category hold for group homomorphisms,
   i.e., we show that composition is associative and satisfies the left and
   right unit laws. -}

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
