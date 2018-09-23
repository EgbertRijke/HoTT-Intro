\begin{code}

{-# OPTIONS --without-K #-}

module Lecture10 where

import Lecture9
open Lecture9 public

ftr-square : {i1 i2 i3 i4 : Level} {A : UU i1} {X : UU i2} {B : UU i3} {Y : UU i4} {f : A → X} {g : B → Y} {i : X → Y} (h : A → B) (H : (i ∘ f) ~ (g ∘ h)) (x : X) → fib f x → fib g (i x)
ftr-square h H _ (dpair a refl) = dpair (h a) (inv (H a))

gap : {i1 i2 i3 i4 : Level} {A : UU i1} {X : UU i2} {B : UU i3} {Y : UU i4} {f : A → X} {g : B → Y} {i : X → Y} (h : A → B) (H : (i ∘ f) ~ (g ∘ h)) → A → Σ X (λ x → Σ B (λ y → Id (i x) (g y)))
gap h H a = dpair _ (dpair (h a) (H a))

fib-square : {i1 i2 i3 i4 : Level} {A : UU i1} {X : UU i2} {B : UU i3} {Y : UU i4} {f : A → X} {g : B → Y} {i : X → Y} (h : A → B) (H : (i ∘ f) ~ (g ∘ h)) (t : Σ X (λ x → Σ B (λ y → Id (i x) (g y)))) → UU _
fib-square h H t = fib (gap h H) t

fib-square-fib-ftr-square : {i1 i2 i3 i4 : Level} {A : UU i1} {X : UU i2} {B : UU i3} {Y : UU i4} {f : A → X} {g : B → Y} {i : X → Y} (h : A → B) (H : (i ∘ f) ~ (g ∘ h)) (t : Σ X (λ x → Σ B (λ y → Id (i x) (g y)))) →
  fib (ftr-square h H (pr1 t)) (dpair (pr1 (pr2 t)) (inv (pr2 (pr2 t)))) → fib-square h H t
fib-square-fib-ftr-square h H t s = {!!}
\end{code}
