\begin{code}

{-# OPTIONS --without-K #-}

module Basics where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

UU : (i : Level) → Set (lsuc i)
UU i = Set i


U = UU lzero
Type = UU (lsuc lzero)

\end{code}
