\begin{code}

{-# OPTIONS --without-K #-}

module Preamble where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

UU : (i : Level) → Set (lsuc i)
UU i = Set i

{-
record Raise {i j : Level} (A : UU i) : UU (i ⊔ j) where
  instance constructor raise
  field
    lower : A

open Raise public
-}


\end{code}
