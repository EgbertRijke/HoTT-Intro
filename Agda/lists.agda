{-# OPTIONS --without-K --exact-split #-}

module lists where

import 16-number-theory
open 16-number-theory public

unit-list :
  {l1 : Level} {A : UU l1} → A → list A
unit-list a = cons a nil

{- First we introduce the functoriality of the list operation, because it will
   come in handy when we try to define and prove more advanced things. -}

functor-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  list A → list B
functor-list f nil = nil
functor-list f (cons a x) = cons (f a) (functor-list f x)

identity-law-functor-list :
  {l1 : Level} {A : UU l1} →
  functor-list (id {A = A}) ~ id
identity-law-functor-list nil = refl
identity-law-functor-list (cons a x) =
  ap (cons a) (identity-law-functor-list x)

composition-law-functor-list :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (f : A → B) (g : B → C) →
  functor-list (g ∘ f) ~ (functor-list g ∘ functor-list f)
composition-law-functor-list f g nil = refl
composition-law-functor-list f g (cons a x) =
  ap (cons (g (f a))) (composition-law-functor-list f g x)

{- Concatenation of lists is an associative operation and nil is the unit for
   list concatenation. -}

assoc-concat-list :
  {l1 : Level} {A : UU l1} (x y z : list A) →
  Id (concat-list (concat-list x y) z) (concat-list x (concat-list y z))
assoc-concat-list nil y z = refl
assoc-concat-list (cons a x) y z = ap (cons a) (assoc-concat-list x y z)

left-unit-law-concat-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list nil x) x
left-unit-law-concat-list x = refl

right-unit-law-concat-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list x nil) x
right-unit-law-concat-list nil = refl
right-unit-law-concat-list (cons a x) =
  ap (cons a) (right-unit-law-concat-list x)

{- The length operation or course behaves well with respect to the other list
   operations. -}

length-nil :
  {l1 : Level} {A : UU l1} →
  Id (length-list {A = A} nil) zero-ℕ
length-nil = refl

length-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id (length-list (concat-list x y)) (add-ℕ (length-list x) (length-list y))
length-concat-list nil y = inv (left-unit-law-add-ℕ (length-list y))
length-concat-list (cons a x) y =
  ( ap succ-ℕ (length-concat-list x y)) ∙
  ( inv (left-successor-law-add-ℕ (length-list x) (length-list y)))

{- We now prove the properties of flattening. -}

flatten-unit-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (flatten-list (unit-list x)) x
flatten-unit-list x = right-unit-law-concat-list x

length-flatten-list :
  {l1 : Level} {A : UU l1} (x : list (list A)) →
  Id ( length-list (flatten-list x))
     ( sum-list-ℕ (functor-list length-list x))
length-flatten-list nil = refl
length-flatten-list (cons a x) =
  ( length-concat-list a (flatten-list x)) ∙
  ( ap (add-ℕ (length-list a)) (length-flatten-list x))

flatten-concat-list :
  {l1 : Level} {A : UU l1} (x y : list (list A)) →
  Id ( flatten-list (concat-list x y))
     ( concat-list (flatten-list x) (flatten-list y))
flatten-concat-list nil y = refl
flatten-concat-list (cons a x) y =
  ( ap (concat-list a) (flatten-concat-list x y)) ∙
  ( inv (assoc-concat-list a (flatten-list x) (flatten-list y)))

flatten-flatten-list :
  {l1 : Level} {A : UU l1} (x : list (list (list A))) →
  Id ( flatten-list (flatten-list x))
     ( flatten-list (functor-list flatten-list x))
flatten-flatten-list nil = refl
flatten-flatten-list (cons a x) =
  ( flatten-concat-list a (flatten-list x)) ∙
  ( ap (concat-list (flatten-list a)) (flatten-flatten-list x))

{- Next, we prove the basic properties of list reversal. -}

reverse-unit-list :
  {l1 : Level} {A : UU l1} (a : A) →
  Id (reverse-list (unit-list a)) (unit-list a)
reverse-unit-list a = refl

length-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (length-list (reverse-list x)) (length-list x)
length-reverse-list nil = refl
length-reverse-list (cons a x) =
  ( length-concat-list (reverse-list x) (unit-list a)) ∙
  ( ap succ-ℕ (length-reverse-list x))

reverse-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id ( reverse-list (concat-list x y))
     ( concat-list (reverse-list y) (reverse-list x))
reverse-concat-list nil y =
  inv (right-unit-law-concat-list (reverse-list y))
reverse-concat-list (cons a x) y =
  ( ap (λ t → concat-list t (unit-list a)) (reverse-concat-list x y)) ∙
  ( assoc-concat-list (reverse-list y) (reverse-list x) (unit-list a))

reverse-flatten-list :
  {l1 : Level} {A : UU l1} (x : list (list A)) →
  Id ( reverse-list (flatten-list x))
     ( flatten-list (reverse-list (functor-list reverse-list x)))
reverse-flatten-list nil = refl
reverse-flatten-list (cons a x) =
  ( reverse-concat-list a (flatten-list x)) ∙
  ( ( ap (λ t → concat-list t (reverse-list a)) (reverse-flatten-list x)) ∙
    ( ( ap
        ( concat-list
          ( flatten-list (reverse-list (functor-list reverse-list x))))
          ( inv (flatten-unit-list (reverse-list a)))) ∙
      ( inv
        ( flatten-concat-list
          ( reverse-list (functor-list reverse-list x))
          ( unit-list (reverse-list a))))))

reverse-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (reverse-list (reverse-list x)) x
reverse-reverse-list nil = refl
reverse-reverse-list (cons a x) =
  ( reverse-concat-list (reverse-list x) (unit-list a)) ∙
  ( ap (concat-list (unit-list a)) (reverse-reverse-list x))

--------------------------------------------------------------------------------

{- Next we define the head and tail operations, and we define the operations
   of picking and removing the last element from a list. -}

head-list :
  {l1 : Level} {A : UU l1} → list A → list A
head-list nil = nil
head-list (cons a x) = unit-list a

tail-list :
  {l1 : Level} {A : UU l1} → list A → list A
tail-list nil = nil
tail-list (cons a x) = x

last-element-list :
  {l1 : Level} {A : UU l1} → list A → list A
last-element-list nil = nil
last-element-list (cons a nil) = unit-list a
last-element-list (cons a (cons b x)) = last-element-list (cons b x)

remove-last-element-list :
  {l1 : Level} {A : UU l1} → list A → list A
remove-last-element-list nil = nil
remove-last-element-list (cons a nil) = nil
remove-last-element-list (cons a (cons b x)) =
  cons a (remove-last-element-list (cons b x))

cons' :
  {l1 : Level} {A : UU l1} → list A → A → list A
cons' x a = concat-list x (unit-list a)

{- We prove the basic properties about heads and tails and their duals. -}

eta-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list (head-list x) (tail-list x)) x
eta-list nil = refl
eta-list (cons a x) = refl

eta-list' :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list (remove-last-element-list x) (last-element-list x)) x
eta-list' nil = refl
eta-list' (cons a nil) = refl
eta-list' (cons a (cons b x)) = ap (cons a) (eta-list' (cons b x))

last-element-cons' :
  {l1 : Level} {A : UU l1} (x : list A) (a : A) →
  Id (last-element-list (cons' x a)) (unit-list a)
last-element-cons' nil a = refl
last-element-cons' (cons b nil) a = refl
last-element-cons' (cons b (cons c x)) a =
  last-element-cons' (cons c x) a

head-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id ( head-list (concat-list x y))
     ( head-list (concat-list (head-list x) (head-list y)))
head-concat-list nil nil = refl
head-concat-list nil (cons x y) = refl
head-concat-list (cons a x) y = refl

tail-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id ( tail-list (concat-list x y))
     ( concat-list (tail-list x) (tail-list (concat-list (head-list x) y)))
tail-concat-list nil y = refl
tail-concat-list (cons a x) y = refl

last-element-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id ( last-element-list (concat-list x y))
     ( last-element-list
       ( concat-list (last-element-list x) (last-element-list y)))
last-element-concat-list nil nil = refl
last-element-concat-list nil (cons b nil) = refl
last-element-concat-list nil (cons b (cons c y)) =
  last-element-concat-list nil (cons c y)
last-element-concat-list (cons a nil) nil = refl
last-element-concat-list (cons a nil) (cons b nil) = refl
last-element-concat-list (cons a nil) (cons b (cons c y)) =
  last-element-concat-list (cons a nil) (cons c y)
last-element-concat-list (cons a (cons b x)) y =
  last-element-concat-list (cons b x) y

remove-last-element-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id ( remove-last-element-list (concat-list x y))
     ( concat-list
       ( remove-last-element-list (concat-list x (head-list y)))
       ( remove-last-element-list y))
remove-last-element-concat-list nil nil = refl
remove-last-element-concat-list nil (cons a nil) = refl
remove-last-element-concat-list nil (cons a (cons b y)) = refl
remove-last-element-concat-list (cons a nil) nil = refl
remove-last-element-concat-list (cons a nil) (cons b y) = refl
remove-last-element-concat-list (cons a (cons b x)) y =
  ap (cons a) (remove-last-element-concat-list (cons b x) y)

head-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (head-list (reverse-list x)) (last-element-list x)
head-reverse-list nil = refl
head-reverse-list (cons a nil) = refl
head-reverse-list (cons a (cons b x)) =
  ( ap head-list
    ( assoc-concat-list (reverse-list x) (unit-list b) (unit-list a))) ∙
  ( ( head-concat-list
      ( reverse-list x)
      ( concat-list (unit-list b) (unit-list a))) ∙
    ( ( inv (head-concat-list (reverse-list x) (unit-list b))) ∙
      ( head-reverse-list (cons b x))))

last-element-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (last-element-list (reverse-list x)) (head-list x)
last-element-reverse-list x =
  ( inv (head-reverse-list (reverse-list x))) ∙
  ( ap head-list (reverse-reverse-list x))

tail-concat-list' :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id ( tail-list (concat-list x y))
     ( concat-list
       ( tail-list x)
       ( tail-list (concat-list (last-element-list x) y)))
tail-concat-list' nil y = refl
tail-concat-list' (cons a nil) y = refl
tail-concat-list' (cons a (cons b x)) y =
  ap (cons b) (tail-concat-list' (cons b x) y)

tail-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (tail-list (reverse-list x)) (reverse-list (remove-last-element-list x))
tail-reverse-list nil = refl
tail-reverse-list (cons a nil) = refl
tail-reverse-list (cons a (cons b x)) =
  ( tail-concat-list' (reverse-list (cons b x)) (unit-list a)) ∙
  ( ( ap
      ( λ t → concat-list
        ( tail-list (reverse-list (cons b x)))
        ( tail-list (concat-list t (unit-list a))))
      ( last-element-cons' (reverse-list x) b)) ∙
    ( ap (λ t → concat-list t (unit-list a)) (tail-reverse-list (cons b x))))

remove-last-element-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (remove-last-element-list (reverse-list x)) (reverse-list (tail-list x))
remove-last-element-reverse-list x =
  ( inv (reverse-reverse-list (remove-last-element-list (reverse-list x)))) ∙
  ( ( inv (ap reverse-list (tail-reverse-list (reverse-list x)))) ∙
    ( ap (reverse-list ∘ tail-list) (reverse-reverse-list x)))

--------------------------------------------------------------------------------

map-algebra-list :
  {l1 : Level} (A : UU l1) →
  coprod unit (A × list A) → list A
map-algebra-list A (inl star) = nil
map-algebra-list A (inr (pair a x)) = cons a x

inv-map-algebra-list :
  {l1 : Level} (A : UU l1) →
  list A → coprod unit (A × list A)
inv-map-algebra-list A nil = inl star
inv-map-algebra-list A (cons a x) = inr (pair a x)

issec-inv-map-algebra-list :
  {l1 : Level} (A : UU l1) →
  (map-algebra-list A ∘ inv-map-algebra-list A) ~ id
issec-inv-map-algebra-list A nil = refl
issec-inv-map-algebra-list A (cons a x) = refl

isretr-inv-map-algebra-list :
  {l1 : Level} (A : UU l1) →
  (inv-map-algebra-list A ∘ map-algebra-list A) ~ id
isretr-inv-map-algebra-list A (inl star) = refl
isretr-inv-map-algebra-list A (inr (pair a x)) = refl

is-equiv-map-algebra-list :
  {l1 : Level} (A : UU l1) → is-equiv (map-algebra-list A)
is-equiv-map-algebra-list A =
  is-equiv-has-inverse
    ( inv-map-algebra-list A)
    ( issec-inv-map-algebra-list A)
    ( isretr-inv-map-algebra-list A)

--------------------------------------------------------------------------------

Eq-list :
  {l1 : Level} {A : UU l1} →
  list A → list A → UU l1
Eq-list nil nil = raise _ unit
Eq-list nil (cons x y) = raise _ empty
Eq-list (cons a x) nil = raise _ empty
Eq-list (cons a x) (cons b y) = (Id a b) × (Eq-list x y)

data Eq-list' {l1 : Level} {A : UU l1} : list A → list A → UU l1 where
  refl-nil : Eq-list' nil nil
  eq-cons :
    (x y : list A) (a b : A) →
    Eq-list' x y → Id a b → Eq-list' (cons a x) (cons b y)

refl-Eq-list :
  {l1 : Level} {A : UU l1} (x : list A) → Eq-list x x
refl-Eq-list nil = map-raise star
refl-Eq-list (cons a x) = pair refl (refl-Eq-list x)

contraction-total-Eq-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  (y : Σ (list A) (Eq-list x)) →
  Id (pair x (refl-Eq-list x)) y
contraction-total-Eq-list nil (pair nil (map-raise star)) = refl
contraction-total-Eq-list nil (pair (cons b y) (map-raise ()))
contraction-total-Eq-list (cons a x) (pair nil (map-raise ()))
contraction-total-Eq-list (cons a x) (pair (cons .a y) (pair refl e)) =
  {!!}

is-contr-total-Eq-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  is-contr (Σ (list A) (Eq-list x))
is-contr-total-Eq-list nil =
  pair
    ( pair nil (map-raise star))
    {!!}
is-contr-total-Eq-list (cons x x₁) = {!!}


