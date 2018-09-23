\begin{code}

{-# OPTIONS --without-K #-}

module cplusplus where

import Lecture5
open Lecture5 public

data list {i : Level} (A : UU i) : UU i where
  [] : list A
  _::_ : A → list A → list A

three-zeroes : list ℕ
three-zeroes = zero-ℕ :: (zero-ℕ :: (zero-ℕ :: [])) 

template-union : (T : list U) → U
template-union [] = empty
template-union (A :: T) = coprod A (template-union T)

template : U → (U → U → U) → list U → U
template X Op [] = X
template X Op (A :: []) = A
template X Op (A :: (B :: L)) =  A × (template X Op (B :: L))

template-struct : (T : list U) → U
template-struct T = template unit prod T

ts : U → U → U → U
ts X Y Z = template-struct (X :: (Y :: (Z :: [])))

s : U → U → U → U
s X Y Z = X × (Y × Z)

eq-ts-s : (X Y Z : U) → Id (ts X Y Z) (s X Y Z)
eq-ts-s X Y Z = refl

\end{code}
