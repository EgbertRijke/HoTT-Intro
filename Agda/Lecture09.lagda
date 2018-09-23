\begin{code}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture09 where

import Lecture08
open Lecture08 public

htpy-id : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) → (f ~ g)
htpy-id refl = htpy-refl _

Funext : {i j : Level} (A : UU i) (B : A → UU j) → UU (i ⊔ j)
Funext A B = (f g : (x : A) → B x) → is-equiv (htpy-id {_} {_} {_} {_} {f} {g})

\end{code}
