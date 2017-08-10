/-------------------------------------------------------------------------------
  LECTURE 5. The fundamental theorem

-------------------------------------------------------------------------------/

prelude
import .equivalences

definition fmap {A : Type} (B C : A → Type) : Type := Π (x : A), B x → C x

definition fmap_natural {A : Type} {B C : A → Type} (f : fmap B C) {x y : A}
  : Π (p : Id x y) (b : B x), 
    Id (f y (transport p b)) (transport p (f x b))
  := Id.rec (λ b, Id.refl _)

definition total {A : Type} {B C : A → Type} (f : Π (x : A), B x → C x)
  : hSigma A B → hSigma A C :=
  hSigma.rec (λ a b, hSigma.pair a (f a b))

definition fib_total_of_fib_fmap {A : Type} {B C : A → Type} 
  (f : fmap B C) (a : A) (c : C a)
  : fiber (f a) c → fiber (total f) (hSigma.pair a c) :=
  hSigma.rec
    ( λ b p, hSigma.pair 
      ( hSigma.pair a b) 
      ( hSigma.eq_of_pair (total f (hSigma.pair a b)) (hSigma.pair a c) (hSigma.pair (Id.refl a) p))
    )

definition fib_fmap_of_fib_total {A : Type} {B C : A → Type} 
  (f : fmap B C) (a : A) (c : C a)
  : fiber (total f) (hSigma.pair a c) → fiber (f a) c :=
  hSigma.rec
    ( hSigma.rec 
      ( λ x b p, hSigma.pair 
        ( transport (hSigma.base_path p) b)
        ( Id.concat (fmap_natural f _ _) (hSigma.fiber_path p) )
      )
    )

definition fib_total_is_retr {A : Type} {B C : A → Type} {f : fmap B C} {a : A}
  {c : C a}
  : homotopy 
     ( λ x, fib_fmap_of_fib_total f a c (fib_total_of_fib_fmap f a c x)) 
     ( λ x, x) :=
  hSigma.rec
    ( λ b, Id.rec (hSigma.eq_of_pair _ _ (hSigma.pair (Id.refl _) (Id.refl _))))

/--
definition fib_total_is_sec {A : Type} {B C : A → Type} {f : fmap B C} {a : A}
  {c : C a}
  : homotopy
      ( λ x, fib_total_of_fib_fmap f a c (fib_fmap_of_fib_total f a c x))
      ( λ x, x) :=
  hSigma.rec
    ( λ b, (retraction_precompose (@hSigma.pair_of_eq A C _ _) (@hSigma.eq_of_pair A C _ _) (@hSigma.pair ) _)
    )
--/
