{-# OPTIONS --without-K #-}

module Lecture07 where

import Lecture06
open Lecture06 public

-- Section 7.1 Fiberwise equivalences
tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x → C x) → ( Σ A B → Σ A C)
tot f t = dpair (pr1 t) (f (pr1 t) (pr2 t))

-- There is a function from the fibers of the induced map on total spaces, to the fibers of the fiberwise transformation
fib-ftr-fib-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  fib (tot f) t → fib (f (pr1 t)) (pr2 t)
fib-ftr-fib-tot f .(dpair x (f x y)) (dpair (dpair x y) refl) = dpair y refl

-- This function has a converse
fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  fib (f (pr1 t)) (pr2 t) → fib (tot f) t
fib-tot-fib-ftr F (dpair a .(F a y)) (dpair y refl) = dpair (dpair a y) refl

issec-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  ((fib-ftr-fib-tot f t) ∘ (fib-tot-fib-ftr f t)) ~ id
issec-fib-tot-fib-ftr f (dpair x .(f x y)) (dpair y refl) = refl

isretr-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  ((fib-tot-fib-ftr f t) ∘ (fib-ftr-fib-tot f t)) ~ id
isretr-fib-tot-fib-ftr f .(dpair x (f x y)) (dpair (dpair x y) refl) = refl

-- We establish that the fibers of the induced map on total spaces are equivalent to the fibers of the fiberwise transformation.
is-equiv-fib-ftr-fib-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  is-equiv (fib-ftr-fib-tot f t)
is-equiv-fib-ftr-fib-tot f t =
  is-equiv-has-inverse'
    ( fib-tot-fib-ftr f t)
    ( issec-fib-tot-fib-ftr f t)
    ( isretr-fib-tot-fib-ftr f t)

is-equiv-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  is-equiv (fib-tot-fib-ftr f t)
is-equiv-fib-tot-fib-ftr f t =
  is-equiv-has-inverse'
    ( fib-ftr-fib-tot f t)
    ( isretr-fib-tot-fib-ftr f t)
    ( issec-fib-tot-fib-ftr f t)

-- Any fiberwise equivalence induces an equivalence on total spaces
is-fiberwise-equiv :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x → C x) → UU (i ⊔ (j ⊔ k))
is-fiberwise-equiv f = (x : _) → is-equiv (f x)

is-equiv-tot-is-fiberwise-equiv :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  {f : (x : A) → B x → C x} → is-fiberwise-equiv f →
  is-equiv (tot f )
is-equiv-tot-is-fiberwise-equiv {f = f} H =
  is-equiv-is-contr-map
    ( λ t → is-contr-is-equiv _
      ( fib-ftr-fib-tot f t)
      ( is-equiv-fib-ftr-fib-tot f t)
      ( is-contr-map-is-equiv (H _) (pr2 t)))

-- Conversely, any fiberwise transformation that induces an equivalence on total spaces is a fiberwise equivalence.
is-fiberwise-equiv-is-equiv-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → is-equiv (tot f) →
  is-fiberwise-equiv f
is-fiberwise-equiv-is-equiv-tot f H x =
  is-equiv-is-contr-map
    (λ z → is-contr-is-equiv' _
      (fib-ftr-fib-tot f (dpair x z))
      (is-equiv-fib-ftr-fib-tot f (dpair x z))
      (is-contr-map-is-equiv H (dpair x z)))

-- Section 7.2 The fundamental theorem

-- The general form of the fundamental theorem of identity types
id-fundamental-gen :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  is-contr (Σ A B) → (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f
id-fundamental-gen {_} {_} {A} {B} a b C f x =
  is-fiberwise-equiv-is-equiv-tot f
    ( is-equiv-is-contr _ (is-contr-total-path A a) C) x

id-fundamental-gen' :
  {i j : Level} {A : UU i} {B : A → UU j}
  (a : A) (b : B a) (f : (x : A) → Id a x → B x) →
  is-fiberwise-equiv f → is-contr (Σ A B)
id-fundamental-gen' {A = A} {B = B} a b f is-fiberwise-equiv-f =
  is-contr-is-equiv'
    ( Σ A (Id a))
    ( tot f)
    ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-f)
    ( is-contr-total-path A a)

-- The canonical form of the fundamental theorem of identity types
id-fundamental :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  is-contr (Σ A B) → is-fiberwise-equiv (ind-Id a (λ x p → B x) b)
id-fundamental {i} {j} {A} {B} a b H =
  id-fundamental-gen a b H (ind-Id a (λ x p → B x) b)

-- The converse of the fundamental theorem of identity types
id-fundamental' :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  (is-fiberwise-equiv (ind-Id a (λ x p → B x) b)) → is-contr (Σ A B)
id-fundamental' {i} {j} {A} {B} a b H =
  is-contr-is-equiv' _
    ( tot (ind-Id a (λ x p → B x) b))
    ( is-equiv-tot-is-fiberwise-equiv H)
    ( is-contr-total-path A a)

-- As an application we show that equivalences are embeddings.
is-emb :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-emb f = (x y : _) → is-equiv (ap f {x} {y})

is-emb-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → is-equiv f → is-emb f
is-emb-is-equiv {i} {j} {A} {B} f E x =
  id-fundamental-gen x refl
    ( is-contr-is-equiv' _
      ( tot (λ y (p : Id (f y) (f x)) → inv p))
      ( is-equiv-tot-is-fiberwise-equiv (λ y → is-equiv-inv (f y) (f x)))
      ( is-contr-map-is-equiv E (f x)))
    ( λ y p → ap f p)

-- Section 7.3 Fiberwise equivalences over an equivalence

Σ-map-base-map :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  Σ A (λ x → C (f x)) → Σ B C
Σ-map-base-map f C s = dpair (f (pr1 s)) (pr2 s)

coherence-is-half-adjoint-equivalence :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  (G : (f ∘ g) ~ id) (H : (g ∘ f) ~ id) → UU (l1 ⊔ l2)
coherence-is-half-adjoint-equivalence f g G H =
  ( htpy-right-whisk G f) ~ (htpy-left-whisk f H)

is-half-adjoint-equivalence :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-half-adjoint-equivalence {A = A} {B = B} f =
  Σ (B → A)
    ( λ g → Σ ((f ∘ g) ~ id)
      ( λ G → Σ ((g ∘ f) ~ id) (coherence-is-half-adjoint-equivalence f g G)))

is-path-split :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-path-split {A = A} {B = B} f =
  sec f × ((x y : A) → sec (ap f {x = x} {y = y}))

is-path-split-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-path-split f
is-path-split-is-equiv f is-equiv-f =
  pair (pr1 is-equiv-f) (λ x y → pr1 (is-emb-is-equiv f is-equiv-f x y))

is-half-adjoint-equivalence-is-path-split :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-path-split f → is-half-adjoint-equivalence f
is-half-adjoint-equivalence-is-path-split {A = A} {B = B} f
  ( dpair (dpair g issec-g) sec-ap-f) =
  let φ : ((x : A) → fib (ap f) (issec-g (f x))) →
            Σ ((g ∘ f) ~ id)
              ( λ H → (htpy-right-whisk issec-g f) ~ (htpy-left-whisk f H))
      φ =  ( tot (λ H' → htpy-inv)) ∘
             ( λ s → dpair (λ x → pr1 (s x)) (λ x → pr2 (s x)))
  in
  dpair g
    ( dpair issec-g
      ( φ (λ x → dpair
        ( pr1 (sec-ap-f (g (f x)) x) (issec-g (f x)))
        ( pr2 (sec-ap-f (g (f x)) x) (issec-g (f x))))))

is-equiv-is-half-adjoint-equivalence :
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) → is-half-adjoint-equivalence f → is-equiv f
is-equiv-is-half-adjoint-equivalence f (dpair g (dpair G (dpair H K))) =
  is-equiv-has-inverse' g G H

is-equiv-is-path-split :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-path-split f → is-equiv f
is-equiv-is-path-split f =
  ( is-equiv-is-half-adjoint-equivalence f) ∘
  ( is-half-adjoint-equivalence-is-path-split f)

is-half-adjoint-equivalence-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-half-adjoint-equivalence f
is-half-adjoint-equivalence-is-equiv f =
  ( is-half-adjoint-equivalence-is-path-split f) ∘ (is-path-split-is-equiv f)

tr-precompose-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) {x y : A} (p : Id x y) → tr C (ap f p) ~ tr (λ x → C (f x)) p
tr-precompose-fam C f refl = htpy-refl _

is-equiv-Σ-map-is-equiv-base-map :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (f : A → B) →
  is-equiv f → is-equiv (Σ-map-base-map f C)
is-equiv-Σ-map-is-equiv-base-map C f is-equiv-f =
  let is-hae-f = is-half-adjoint-equivalence-is-path-split f
                 ( is-path-split-is-equiv f is-equiv-f)
      g = pr1 (is-hae-f)
      G = pr1 (pr2 is-hae-f)
      H = pr1 (pr2 (pr2 is-hae-f))
      coh = pr2 (pr2 (pr2 is-hae-f))
  in
  is-equiv-has-inverse'
    ( λ t → dpair (g (pr1 t)) (tr C (inv (G (pr1 t))) (pr2 t)))
    ( λ t → eq-pair (dpair
      ( G (pr1 t))
      ( ( tr-concat (inv (G (pr1 t))) (G (pr1 t)) (pr2 t)) ∙
        ( ap (λ α → tr C α (pr2 t)) (left-inv (G (pr1 t)))))))
    ( λ t → eq-pair (dpair
      ( H (pr1 t))
      ( ( inv
          ( tr-precompose-fam C f (H (pr1 t))
             ( tr C (inv (G (f (pr1 t)))) (pr2 t)))) ∙ 
        ( ( tr-concat (inv (G (f (pr1 t)))) (ap f (H (pr1 t))) (pr2 t)) ∙
          ( ap
            ( λ α → tr C α (pr2 t))
            ( inv
              ( inv-con
                ( G (f (pr1 t)))
                ( refl)
                ( ap f (H (pr1 t)))
                ( (right-unit (G (f (pr1 t)))) ∙ (coh (pr1 t))))))))))

toto :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  Σ A C → Σ B D
toto D f g t = dpair (f (pr1 t)) (g (pr1 t) (pr2 t))

triangle-toto :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  (toto D f g) ~ ((Σ-map-base-map f D) ∘ (tot g))
triangle-toto D f g t = refl

is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  is-equiv f → (is-fiberwise-equiv g) →
  is-equiv (toto D f g)
is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map
  D f g is-equiv-f is-fiberwise-equiv-g =
  is-equiv-comp
    ( toto D f g)
    ( Σ-map-base-map f D)
    ( tot g)
    ( triangle-toto D f g)
    ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-g)
    ( is-equiv-Σ-map-is-equiv-base-map D f is-equiv-f)

is-fiberwise-equiv-is-equiv-toto-is-equiv-base-map :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  is-equiv f → is-equiv (toto D f g) → is-fiberwise-equiv g
is-fiberwise-equiv-is-equiv-toto-is-equiv-base-map
  D f g is-equiv-f is-equiv-toto-fg =
  is-fiberwise-equiv-is-equiv-tot g
    ( is-equiv-right-factor
      ( toto D f g)
      ( Σ-map-base-map f D)
      ( tot g)
      ( triangle-toto D f g)
      ( is-equiv-Σ-map-is-equiv-base-map D f is-equiv-f)
      ( is-equiv-toto-fg))

is-fiberwise-equiv-id-to-Eq-structure :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (s : Σ A B) {C : A → UU l3}
  ( D : (t : Σ A B) → C (pr1 t) → UU l4)
  ( h : (t : Σ A B) → Id s t → Σ (C (pr1 t)) (D t))
  ( f : (x : A) → Id (pr1 s) x → C x)
  ( g : (t : Σ A B) (α : Id (pr1 s) (pr1 t)) → Id (tr B α (pr2 s)) (pr2 t) →
       D t (f (pr1 t) α))
  ( H : Id (h s refl) (dpair (f (pr1 s) refl) (g s refl refl))) →
  is-fiberwise-equiv f →
  ( (y : B (pr1 s)) → is-equiv (g (dpair (pr1 s) y) refl)) →
  is-fiberwise-equiv h
is-fiberwise-equiv-id-to-Eq-structure
  {A = A} {B = B} s {C} D h f g H is-equiv-f is-equiv-g t =
  is-equiv-comp
    ( h t)
    ( toto (D t) (f (pr1 t)) (g t))
    ( pair-eq)
    ( ind-Id s
      ( λ t α → Id
        (h t α)
        (((toto (D t) (f (pr1 t)) (g t)) ∘ pair-eq) α))
        ( H)
        ( t))
    ( is-equiv-pair-eq' s t)
    ( is-equiv-toto-is-fiberwise-equiv-is-equiv-base-map
      ( D t)
      ( f (pr1 t))
      ( g t)
      ( is-equiv-f (pr1 t))
      ( ind-Σ
        { C = λ t → (α : Id (pr1 s) (pr1 t)) → is-equiv (g t α)}
        ( λ x y α → (ind-Id (pr1 s)
          ( λ (x' : A) (α : Id (pr1 s) x') →
            (y' : B x') → is-equiv (g (dpair x' y') α))
          ( λ y' → is-equiv-g y')) x α y)
        ( t)))

-- Section 7.4 Disjointness of coproducts

-- Raising universe levels

postulate Raise : {l1 : Level} (l2 : Level) → (A : UU l1) → Σ (UU (l1 ⊔ l2)) (λ X → A ≃ X)

raise :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ l2)
raise l2 A = pr1 (Raise l2 A)

eqv-raise :
  {l1 : Level} (l2 : Level) (A : UU l1) → A ≃ raise l2 A
eqv-raise l2 A = pr2 (Raise l2 A)

map-raise :
  {l1 : Level} (l2 : Level) (A : UU l1) → A → raise l2 A
map-raise l2 A = eqv-map (eqv-raise l2 A)

is-equiv-map-raise :
  {l1 : Level} (l2 : Level) (A : UU l1) →
  is-equiv (map-raise l2 A)
is-equiv-map-raise l2 A = is-equiv-eqv-map (eqv-raise l2 A)

-- Lemmas about coproducts

left-distributive-coprod-Σ-map :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2)
  (C : coprod A B → UU l3) → Σ (coprod A B) C →
  coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
left-distributive-coprod-Σ-map A B C (dpair (inl x) z) = inl (dpair x z)
left-distributive-coprod-Σ-map A B C (dpair (inr y) z) = inr (dpair y z)

inv-left-distributive-coprod-Σ-map :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2)
  (C : coprod A B → UU l3) →
  coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y))) → Σ (coprod A B) C
inv-left-distributive-coprod-Σ-map A B C (inl (dpair x z)) = dpair (inl x) z
inv-left-distributive-coprod-Σ-map A B C (inr (dpair y z)) = dpair (inr y) z

issec-inv-left-distributive-coprod-Σ-map :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  ( (left-distributive-coprod-Σ-map A B C) ∘
    (inv-left-distributive-coprod-Σ-map A B C)) ~ id
issec-inv-left-distributive-coprod-Σ-map A B C (inl (dpair x z)) = refl
issec-inv-left-distributive-coprod-Σ-map A B C (inr (dpair y z)) = refl

isretr-inv-left-distributive-coprod-Σ-map :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  ( (inv-left-distributive-coprod-Σ-map A B C) ∘
    (left-distributive-coprod-Σ-map A B C)) ~ id
isretr-inv-left-distributive-coprod-Σ-map A B C (dpair (inl x) z) = refl
isretr-inv-left-distributive-coprod-Σ-map A B C (dpair (inr y) z) = refl

is-equiv-left-distributive-coprod-Σ-map :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3) →
  is-equiv (left-distributive-coprod-Σ-map A B C)
is-equiv-left-distributive-coprod-Σ-map A B C =
  is-equiv-has-inverse'
    ( inv-left-distributive-coprod-Σ-map A B C)
    ( issec-inv-left-distributive-coprod-Σ-map A B C)
    ( isretr-inv-left-distributive-coprod-Σ-map A B C)

is-equiv-map-to-empty :
  {l : Level} {A : UU l} (f : A → empty) → is-equiv f
is-equiv-map-to-empty f =
  is-equiv-has-inverse'
    ind-empty
    ind-empty
    ( λ x → ind-empty {P = λ t → Id (ind-empty (f x)) x} (f x))

map-Σ-empty-fam :
  {l : Level} (A : UU l) → Σ A (λ x → empty) → empty
map-Σ-empty-fam A (dpair x ()) 

is-equiv-map-Σ-empty-fam :
  {l : Level} (A : UU l) → is-equiv (map-Σ-empty-fam A)
is-equiv-map-Σ-empty-fam A = is-equiv-map-to-empty (map-Σ-empty-fam A)

inv-inl-coprod-empty : {l : Level} (A : UU l) → coprod A empty → A
inv-inl-coprod-empty A (inl x) = x
inv-inl-coprod-empty A (inr ())

issec-inv-inl-coprod-empty :
  {l : Level} (A : UU l) → (inl ∘ (inv-inl-coprod-empty A)) ~ id
issec-inv-inl-coprod-empty A (inl x) = refl
issec-inv-inl-coprod-empty A (inr ())

is-equiv-inl-coprod-empty :
  {l : Level} (A : UU l) → is-equiv (inl {A = A} {B = empty})
is-equiv-inl-coprod-empty A =
  is-equiv-has-inverse'
    ( inv-inl-coprod-empty A)
    ( issec-inv-inl-coprod-empty A)
    ( λ x → refl)

inv-inr-coprod-empty :
  {l : Level} (B : UU l) → coprod empty B → B
inv-inr-coprod-empty B (inl ())
inv-inr-coprod-empty B (inr x) = x

issec-inv-inr-coprod-empty :
  {l : Level} (B : UU l) → (inr ∘ (inv-inr-coprod-empty B)) ~ id
issec-inv-inr-coprod-empty B (inl ())
issec-inv-inr-coprod-empty B (inr x) = refl

is-equiv-inr-coprod-empty :
  {l : Level} (B : UU l) → is-equiv (inr {A = empty} {B = B})
is-equiv-inr-coprod-empty B =
  is-equiv-has-inverse'
    ( inv-inr-coprod-empty B)
    ( issec-inv-inr-coprod-empty B)
    ( λ x → refl)

-- The identity types of coproducts

Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  coprod A B → coprod A B → UU (l1 ⊔ l2)
Eq-coprod {l1} {l2} A B (inl x) (inl y) = raise (l1 ⊔ l2) (Id x y)
Eq-coprod {l1} {l2} A B (inl x) (inr y) = raise (l1 ⊔ l2) empty
Eq-coprod {l1} {l2} A B (inr x) (inl y) = raise (l1 ⊔ l2) empty
Eq-coprod {l1} {l2} A B (inr x) (inr y) = raise (l1 ⊔ l2) (Id x y)

reflexive-Eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (t : coprod A B) → Eq-coprod A B t t
reflexive-Eq-coprod {l1} {l2} A B (inl x) = map-raise (l1 ⊔ l2) (Id x x) refl
reflexive-Eq-coprod {l1} {l2} A B (inr x) = map-raise (l1 ⊔ l2) (Id x x) refl

Eq-coprod-eq :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (s t : coprod A B) → Id s t → Eq-coprod A B s t
Eq-coprod-eq A B s .s refl = reflexive-Eq-coprod A B s

is-contr-total-Eq-coprod-inl :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : A) →
  is-contr (Σ (coprod A B) (Eq-coprod A B (inl x)))
is-contr-total-Eq-coprod-inl A B x =
  is-contr-is-equiv
     ( coprod
       ( Σ A (λ y → Eq-coprod A B (inl x) (inl y)))
       ( Σ B (λ y → Eq-coprod A B (inl x) (inr y))))
     ( left-distributive-coprod-Σ-map A B (Eq-coprod A B (inl x)))
     ( is-equiv-left-distributive-coprod-Σ-map A B (Eq-coprod A B (inl x)))
     ( is-contr-is-equiv'
       ( coprod
         ( Σ A (Id x))
         ( Σ B (λ y → empty)))
       ( functor-coprod
         ( tot (λ y → map-raise _ (Id x y)))
         ( tot (λ y → map-raise _ empty)))
       ( is-equiv-functor-coprod
         ( is-equiv-tot-is-fiberwise-equiv
           ( λ y → is-equiv-map-raise _ (Id x y)))
         ( is-equiv-tot-is-fiberwise-equiv
           ( λ y → is-equiv-map-raise _ empty)))
       ( is-contr-is-equiv
         ( coprod (Σ A (Id x)) empty)
         ( functor-coprod id (map-Σ-empty-fam B))
         ( is-equiv-functor-coprod
           ( is-equiv-id (Σ A (Id x)))
         ( is-equiv-map-Σ-empty-fam B))
         ( is-contr-is-equiv'
           ( Σ A (Id x))
           ( inl)
           ( is-equiv-inl-coprod-empty (Σ A (Id x)))
           ( is-contr-total-path A x))))

is-contr-total-Eq-coprod-inr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : B) →
  is-contr (Σ (coprod A B) (Eq-coprod A B (inr x)))
is-contr-total-Eq-coprod-inr A B x =
  is-contr-is-equiv
    ( coprod
      ( Σ A (λ y → Eq-coprod A B (inr x) (inl y)))
      ( Σ B (λ y → Eq-coprod A B (inr x) (inr y))))
    ( left-distributive-coprod-Σ-map A B (Eq-coprod A B (inr x)))
    ( is-equiv-left-distributive-coprod-Σ-map A B (Eq-coprod A B (inr x)))
    ( is-contr-is-equiv'
      ( coprod (Σ A (λ y → empty)) (Σ B (Id x)))
      ( functor-coprod
        ( tot (λ y → map-raise _ empty))
        ( tot (λ y → map-raise _ (Id x y))))
      ( is-equiv-functor-coprod
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ y → is-equiv-map-raise _ empty))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ y → is-equiv-map-raise _ (Id x y))))
      ( is-contr-is-equiv
        ( coprod empty (Σ B (Id x)))
        ( functor-coprod (map-Σ-empty-fam A) id)
        ( is-equiv-functor-coprod
          ( is-equiv-map-Σ-empty-fam A)
          ( is-equiv-id (Σ B (Id x))))
        ( is-contr-is-equiv'
          ( Σ B (Id x))
          ( inr)
          ( is-equiv-inr-coprod-empty (Σ B (Id x)))
          ( is-contr-total-path B x))))

is-equiv-Eq-coprod-eq-inl :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : A) →
  is-fiberwise-equiv (Eq-coprod-eq A B (inl x))
is-equiv-Eq-coprod-eq-inl A B x =
  id-fundamental-gen
    ( inl x)
    ( reflexive-Eq-coprod A B (inl x))
    ( is-contr-total-Eq-coprod-inl A B x)
    ( Eq-coprod-eq A B (inl x))

is-equiv-Eq-coprod-eq-inr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : B) →
  is-fiberwise-equiv (Eq-coprod-eq A B (inr x))
is-equiv-Eq-coprod-eq-inr A B x =
  id-fundamental-gen
    ( inr x)
    ( reflexive-Eq-coprod A B (inr x))
    ( is-contr-total-Eq-coprod-inr A B x)
    ( Eq-coprod-eq A B (inr x))

is-equiv-Eq-coprod-eq :
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  (s : coprod A B) → is-fiberwise-equiv (Eq-coprod-eq A B s)
is-equiv-Eq-coprod-eq A B (inl x) = is-equiv-Eq-coprod-eq-inl A B x
is-equiv-Eq-coprod-eq A B (inr x) = is-equiv-Eq-coprod-eq-inr A B x

map-compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → Id (inl {B = B} x) (inl {B = B} x') → Id x x'
map-compute-eq-coprod-inl-inl x x' =
  ( inv-is-equiv (is-equiv-map-raise _ (Id x x'))) ∘
    ( Eq-coprod-eq _ _ (inl x) (inl x')) 

is-equiv-map-compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → is-equiv (map-compute-eq-coprod-inl-inl {B = B} x x')
is-equiv-map-compute-eq-coprod-inl-inl x x' =
   is-equiv-comp
     ( map-compute-eq-coprod-inl-inl x x')
     ( inv-is-equiv (is-equiv-map-raise _ (Id x x')))
     ( Eq-coprod-eq _ _ (inl x) (inl x'))
     ( htpy-refl _)
     ( is-equiv-Eq-coprod-eq _ _ (inl x) (inl x'))
     ( is-equiv-inv-is-equiv (is-equiv-map-raise _ (Id x x')))

compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → (Id (inl {B = B} x) (inl x')) ≃ (Id x x')
compute-eq-coprod-inl-inl x x' =
  dpair
    ( map-compute-eq-coprod-inl-inl x x')
    ( is-equiv-map-compute-eq-coprod-inl-inl x x')

map-compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → Id (inl x) (inr y') → empty
map-compute-eq-coprod-inl-inr x y' =
  ( inv-is-equiv (is-equiv-map-raise _ empty)) ∘
    ( Eq-coprod-eq _ _ (inl x) (inr y'))

is-equiv-map-compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → is-equiv (map-compute-eq-coprod-inl-inr x y')
is-equiv-map-compute-eq-coprod-inl-inr x y' =
   is-equiv-comp
     ( map-compute-eq-coprod-inl-inr x y')
     ( inv-is-equiv (is-equiv-map-raise _ empty))
     ( Eq-coprod-eq _ _ (inl x) (inr y'))
     ( htpy-refl _)
     ( is-equiv-Eq-coprod-eq _ _ (inl x) (inr y'))
     ( is-equiv-inv-is-equiv (is-equiv-map-raise _ empty))

compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → (Id (inl x) (inr y')) ≃ empty
compute-eq-coprod-inl-inr x y' =
  dpair
    ( map-compute-eq-coprod-inl-inr x y')
    ( is-equiv-map-compute-eq-coprod-inl-inr x y')

map-compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → (Id (inr {A = A} y) (inl x')) → empty
map-compute-eq-coprod-inr-inl y x' =
   ( inv-is-equiv (is-equiv-map-raise _ empty)) ∘
     ( Eq-coprod-eq _ _ (inr y) (inl x'))

is-equiv-map-compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → is-equiv (map-compute-eq-coprod-inr-inl y x')
is-equiv-map-compute-eq-coprod-inr-inl y x' =
  is-equiv-comp
    ( map-compute-eq-coprod-inr-inl y x')
    ( inv-is-equiv (is-equiv-map-raise _ empty))
    ( Eq-coprod-eq _ _ (inr y) (inl x'))
    ( htpy-refl _)
    ( is-equiv-Eq-coprod-eq _ _ (inr y) (inl x'))
    ( is-equiv-inv-is-equiv (is-equiv-map-raise _ empty))

compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → (Id (inr y) (inl x')) ≃ empty
compute-eq-coprod-inr-inl y x' =
  dpair
    ( map-compute-eq-coprod-inr-inl y x')
    ( is-equiv-map-compute-eq-coprod-inr-inl y x')

map-compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → (Id (inr {A = A} y) (inr y')) → Id y y'
map-compute-eq-coprod-inr-inr y y' =
  ( inv-is-equiv (is-equiv-map-raise _ (Id y y'))) ∘
    ( Eq-coprod-eq _ _ (inr y) (inr y'))

is-equiv-map-compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → is-equiv (map-compute-eq-coprod-inr-inr {A = A} y y')
is-equiv-map-compute-eq-coprod-inr-inr y y' =
  is-equiv-comp
    ( map-compute-eq-coprod-inr-inr y y')
    ( inv-is-equiv (is-equiv-map-raise _ (Id y y')))
    ( Eq-coprod-eq _ _ (inr y) (inr y'))
    ( htpy-refl _)
    ( is-equiv-Eq-coprod-eq _ _ (inr y) (inr y'))
    ( is-equiv-inv-is-equiv (is-equiv-map-raise _ (Id y y')))

compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → (Id (inr {A = A} y) (inr y')) ≃ (Id y y')
compute-eq-coprod-inr-inr y y' =
  dpair
    ( map-compute-eq-coprod-inr-inr y y')
    ( is-equiv-map-compute-eq-coprod-inr-inr y y')

-- Exercises

-- Exercise 7.1

tot-htpy :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k}
  {f g : (x : A) → B x → C x} → (H : (x : A) → f x ~ g x) → tot f ~ tot g
tot-htpy H (dpair x y) = eq-pair (dpair refl (H x y))

tot-id :
  {i j : Level} {A : UU i} (B : A → UU j) →
  (tot (λ x (y : B x) → y)) ~ id
tot-id B (dpair x y) = refl

tot-comp :
  {i j j' j'' : Level}
  {A : UU i} {B : A → UU j} {B' : A → UU j'} {B'' : A → UU j''}
  (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  tot (λ x → (g x) ∘ (f x)) ~ ((tot g) ∘ (tot f))
tot-comp f g (dpair x y) = refl

-- Exercise 7.2
fib' :
  {i j : Level} {A : UU i} {B : UU j} → (A → B) → B → UU (i ⊔ j)
fib' f y = Σ _ (λ x → Id y (f x))

fib'-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  fib f y → fib' f y
fib'-fib f y t = tot (λ x → inv) t

is-equiv-fib'-fib :
  {i j : Level} {A : UU i} {B : UU j}
  (f : A → B) → is-fiberwise-equiv (fib'-fib f)
is-equiv-fib'-fib f y =
  is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-inv (f x) y)

-- Exercise 7.3
is-equiv-top-is-equiv-bottom-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  (is-equiv f) → (is-equiv g) → (is-equiv i) → (is-equiv h)
is-equiv-top-is-equiv-bottom-square f g h i H Ef Eg Ei =
  is-equiv-right-factor (i ∘ f) g h H Eg
    (is-equiv-comp (i ∘ f) i f (htpy-refl _) Ef Ei)

is-equiv-bottom-is-equiv-top-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  (is-equiv f) → (is-equiv g) → (is-equiv h) → (is-equiv i)
is-equiv-bottom-is-equiv-top-square f g h i H Ef Eg Eh =
  is-equiv-left-factor (g ∘ h) i f (htpy-inv H)
    (is-equiv-comp (g ∘ h) g h (htpy-refl _) Eh Eg) Ef

fib-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  (x : X) → (fib f x) → (fib g x)
fib-triangle f g h H .(f a) (dpair a refl) = dpair (h a) (inv (H a))

square-tot-fib-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (h ∘ (Σ-fib-to-domain f)) ~
  ((Σ-fib-to-domain g) ∘ (tot (fib-triangle f g h H)))
square-tot-fib-triangle f g h H (dpair .(f a) (dpair a refl)) = refl

is-fiberwise-equiv-is-equiv-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (E : is-equiv h) → is-fiberwise-equiv (fib-triangle f g h H)
is-fiberwise-equiv-is-equiv-triangle f g h H E =
  is-fiberwise-equiv-is-equiv-tot
    ( fib-triangle f g h H)
    ( is-equiv-top-is-equiv-bottom-square
      ( Σ-fib-to-domain f)
      ( Σ-fib-to-domain g)
      ( tot (fib-triangle f g h H))
      ( h)
      ( square-tot-fib-triangle f g h H)
      ( is-equiv-Σ-fib-to-domain f)
      ( is-equiv-Σ-fib-to-domain g)
      ( E))

is-equiv-triangle-is-fiberwise-equiv :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (E : is-fiberwise-equiv (fib-triangle f g h H)) → is-equiv h
is-equiv-triangle-is-fiberwise-equiv f g h H E =
  is-equiv-bottom-is-equiv-top-square
    ( Σ-fib-to-domain f)
    ( Σ-fib-to-domain g)
    ( tot (fib-triangle f g h H))
    ( h)
    ( square-tot-fib-triangle f g h H)
    ( is-equiv-Σ-fib-to-domain f)
    ( is-equiv-Σ-fib-to-domain g)
    ( is-equiv-tot-is-fiberwise-equiv E)

-- Exercise 7.4
fib-ap-eq-fib-fiberwise :
  {i j : Level} {A : UU i} {B : UU j}
  (f : A → B) {b : B} (s t : fib f b) (p : Id (pr1 s) (pr1 t)) →
  (Id (tr (λ (a : A) → Id (f a) b) p (pr2 s)) (pr2 t)) →
  (Id (ap f p) (concat b (pr2 s) (inv (pr2 t))))
fib-ap-eq-fib-fiberwise f (dpair .x' p) (dpair x' refl) refl =
  inv ∘ (concat p (right-unit p))

is-fiberwise-equiv-fib-ap-eq-fib-fiberwise :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {b : B} (s t : fib f b) →
  is-fiberwise-equiv (fib-ap-eq-fib-fiberwise f s t)
is-fiberwise-equiv-fib-ap-eq-fib-fiberwise
  f (dpair x y) (dpair .x refl) refl =
  is-equiv-comp
    ( fib-ap-eq-fib-fiberwise f (dpair x y) (dpair x refl) refl)
    ( inv)
    ( concat y (right-unit y))
    ( htpy-refl (fib-ap-eq-fib-fiberwise f (dpair x y) (dpair x refl) refl))
    ( is-equiv-concat (right-unit y) refl)
    ( is-equiv-inv (concat (f x) y refl) refl)

fib-ap-eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {b : B}
  (s t : fib f b) → Id s t →
  fib (ap f {x = pr1 s} {y = pr1 t}) (concat _ (pr2 s) (inv (pr2 t)))
fib-ap-eq-fib f s .s refl = dpair refl (inv (right-inv (pr2 s)))

triangle-fib-ap-eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B)
  {b : B} (s t : fib f b) →
  (fib-ap-eq-fib f s t) ~ ((tot (fib-ap-eq-fib-fiberwise f s t)) ∘ (pair-eq' s t))
triangle-fib-ap-eq-fib f (dpair x refl) .(dpair x refl) refl = refl

is-equiv-fib-ap-eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {b : B}
  (s t : fib f b) → is-equiv (fib-ap-eq-fib f s t)
is-equiv-fib-ap-eq-fib f s t =
  is-equiv-comp
    ( fib-ap-eq-fib f s t)
    ( tot (fib-ap-eq-fib-fiberwise f s t))
    ( pair-eq' s t)
    ( triangle-fib-ap-eq-fib f s t)
    ( is-equiv-pair-eq' s t)
    ( is-equiv-tot-is-fiberwise-equiv
      ( is-fiberwise-equiv-fib-ap-eq-fib-fiberwise f s t))

eq-fib-fib-ap :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (x y : A)
  (q : Id (f x) (f y)) →
  Id (dpair x q) (dpair y (refl {x = f y})) → fib (ap f {x = x} {y = y}) q
eq-fib-fib-ap f x y q = (tr (fib (ap f)) (right-unit q)) ∘ (fib-ap-eq-fib f (dpair x q) (dpair y refl))

is-equiv-eq-fib-fib-ap :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (x y : A)
  (q : Id (f x) (f y)) → is-equiv (eq-fib-fib-ap f x y q)
is-equiv-eq-fib-fib-ap f x y q =
  is-equiv-comp
    ( eq-fib-fib-ap f x y q)
    ( tr (fib (ap f)) (right-unit q))
    ( fib-ap-eq-fib f (dpair x q) (dpair y refl))
    ( htpy-refl _)
    ( is-equiv-fib-ap-eq-fib f (dpair x q) (dpair y refl))
    ( is-equiv-tr (fib (ap f)) (right-unit q))

-- Exercise 7.5

-- This exercise was already done in id-fundamental-gen above.

-- Exercise 7.6
id-fundamental-retr :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) →
  (i : (x : A) → B x → Id a x) → (R : (x : A) → retr (i x)) →
  is-fiberwise-equiv i
id-fundamental-retr {_} {_} {A} {B} a i R =
  is-fiberwise-equiv-is-equiv-tot i
    ( is-equiv-is-contr (tot i)
      ( is-contr-retract-of (Σ _ (λ y → Id a y))
        ( dpair (tot i)
          ( dpair (tot λ x → pr1 (R x))
            ( htpy-concat
              ( tot (λ x → pr1 (R x) ∘ i x))
              ( htpy-inv (tot-comp i (λ x → pr1 (R x))))
                ( htpy-concat (tot (λ x → id))
                  ( tot-htpy λ x → pr2 (R x))
                  ( tot-id B)))))
        ( is-contr-total-path _ a))
      ( is-contr-total-path _ a))

is-equiv-sec-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (sec-f : sec f) →
  is-equiv (pr1 sec-f) → is-equiv f
is-equiv-sec-is-equiv {A = A} {B = B} f (dpair g issec-g) is-equiv-sec-f =
  let h : A → B
      h = inv-is-equiv is-equiv-sec-f
  in
  is-equiv-htpy h
    ( htpy-concat
      ( f ∘ (g ∘ h))
      ( htpy-left-whisk f (htpy-inv (issec-inv-is-equiv is-equiv-sec-f)))
      ( htpy-right-whisk issec-g h))
    ( is-equiv-inv-is-equiv is-equiv-sec-f)

id-fundamental-sec :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A)
  (f : (x : A) → Id a x → B x) → ((x : A) → sec (f x)) →
  is-fiberwise-equiv f
id-fundamental-sec {A = A} {B = B} a f sec-f x =
  let i : (x : A) → B x → Id a x
      i = λ x → pr1 (sec-f x)
      retr-i : (x : A) → retr (i x)
      retr-i = λ x → dpair (f x) (pr2 (sec-f x))
      is-fiberwise-equiv-i : is-fiberwise-equiv i
      is-fiberwise-equiv-i = id-fundamental-retr a i retr-i
  in is-equiv-sec-is-equiv (f x) (sec-f x) (is-fiberwise-equiv-i x)

-- Exercise 7.7

is-emb-empty :
  {i : Level} (A : UU i) → is-emb (ind-empty {P = λ x → A})
is-emb-empty A = ind-empty

-- Exercise 7.8

is-equiv-top-is-equiv-left-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
  is-equiv i → is-equiv f → is-equiv g → is-equiv h
is-equiv-top-is-equiv-left-square f g h i H Ei Ef Eg =
  is-equiv-right-factor (i ∘ f) g h H Eg
    ( is-equiv-comp (i ∘ f) i f (htpy-refl _) Ef Ei)

is-emb-htpy :
  {i j : Level} {A : UU i} {B : UU j} (f g : A → B) → (f ~ g) →
  is-emb g → is-emb f
is-emb-htpy f g H is-emb-g x y =
  is-equiv-top-is-equiv-left-square
    ( ap g)
    ( concat' (f y) (H y))
    ( ap f)
    ( concat (g x) (H x))
    ( htpy-nat H)
    ( is-equiv-concat (H x) (g y))
    ( is-emb-g x y)
    ( is-equiv-concat' (f x) (H y))

-- Exercise 7.9

is-emb-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
  is-emb h → is-emb f
is-emb-comp f g h H is-emb-g is-emb-h =
  is-emb-htpy f (g ∘ h) H
    ( λ x y → is-equiv-comp (ap (g ∘ h)) (ap g) (ap h) (ap-comp g h)
      ( is-emb-h x y)
      ( is-emb-g (h x) (h y)))

is-emb-right-factor :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
  is-emb f → is-emb h
is-emb-right-factor f g h H is-emb-g is-emb-f x y =
  is-equiv-right-factor (ap (g ∘ h)) (ap g) (ap h) (ap-comp g h) (is-emb-g (h x) (h y)) (is-emb-htpy (g ∘ h) f (htpy-inv H) is-emb-f x y )

is-emb-triangle-is-equiv :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (e : A → B) (H : f ~ (g ∘ e)) →
  is-equiv e → is-emb g → is-emb f
is-emb-triangle-is-equiv f g e H is-equiv-e is-emb-g =
  is-emb-comp f g e H is-emb-g (is-emb-is-equiv e is-equiv-e)

is-emb-triangle-is-equiv' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (e : A → B) (H : f ~ (g ∘ e)) →
  is-equiv e → is-emb f → is-emb g
is-emb-triangle-is-equiv' f g e H is-equiv-e is-emb-f =
  is-emb-triangle-is-equiv g f
    ( inv-is-equiv is-equiv-e)
    ( triangle-section f g e H
      ( dpair
        ( inv-is-equiv is-equiv-e)
        ( issec-inv-is-equiv is-equiv-e)))
    ( is-equiv-inv-is-equiv is-equiv-e)
    ( is-emb-f)

-- Exercise 7.10
is-emb-sec-ap :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  ((x y : A) → sec (ap f {x = x} {y = y})) → is-emb f
is-emb-sec-ap f sec-ap-f x =
  id-fundamental-sec x (λ y → ap f {y = y}) (sec-ap-f x)

-- Exercise 7.11
is-emb-inl :
  {i j : Level} (A : UU i) (B : UU j) → is-emb (inl {A = A} {B = B})
is-emb-inl A B x =
  id-fundamental-gen x refl
    ( is-contr-is-equiv
      ( Σ A (λ y → Eq-coprod A B (inl x) (inl y)))
      ( tot (λ y → Eq-coprod-eq A B (inl x) (inl y)))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ y → is-equiv-Eq-coprod-eq A B (inl x) (inl y)))
      ( is-contr-is-equiv'
        ( Σ A (Id x))
        ( tot (λ y → map-raise _ (Id x y)))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ y → is-equiv-map-raise _ (Id x y)))
        ( is-contr-total-path A x)))
    ( λ y → ap inl)

is-emb-inr :
  {i j : Level} (A : UU i) (B : UU j) → is-emb (inr {A = A} {B = B})
is-emb-inr A B x =
  id-fundamental-gen x refl
    ( is-contr-is-equiv
      ( Σ B (λ y → Eq-coprod A B (inr x) (inr y)))
      ( tot (λ y → Eq-coprod-eq A B (inr x) (inr y)))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ y → is-equiv-Eq-coprod-eq A B (inr x) (inr y)))
      ( is-contr-is-equiv'
        ( Σ B (Id x))
        ( tot (λ y → map-raise _ (Id x y)))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ y → is-equiv-map-raise _ (Id x y)))
        ( is-contr-total-path B x)))
    ( λ y → ap inr)
