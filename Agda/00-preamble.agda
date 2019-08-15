{-# OPTIONS --without-K --exact-split #-}

module 00-preamble where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

UU : (i : Level) → Set (lsuc i)
UU i = Set i
