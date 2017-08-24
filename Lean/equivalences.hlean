/-------------------------------------------------------------------------------
  LECTURE 4. Equivalences

-------------------------------------------------------------------------------/

prelude

import .identity

definition has_retraction {A B : Type} (i : A → B) : Type :=
  hSigma (B → A) (λ r, homotopy (λ x, r (i x)) (λ x, x))

definition has_section {A B : Type} (p : B → A) : Type :=
  hSigma (A → B) (λ s, homotopy (λ x, p (s x)) (λ x, x))

-- Exercise
definition retraction_swap {A B : Type} {i : A → B} {r : B → A} 
  (H : homotopy (λ x, r (i x)) (λ x, x)) (a : A) 
  : Id (H (r (i a))) (htpy.whisker_left (λ x, r (i x)) H a)  :=
  Id.unwhisker_right 
    ( H a) 
    ( square.whisker_right 
      ( ap.idfun (H a)) 
      ( htpy.natural H (H a))
    )

-- Exercise
definition retraction_precompose {A B : Type} {P : A → Type} (i : A → B) 
  (r : B → A) (H : homotopy (λ x, r (i x)) (λ x, x)) (K : Π (b : B), P (r b)) 
  (a : A) : P a :=
  transport (H a) (K (i a))

-- Exercise
definition computation_retraction_precompose {A B : Type} {P : A → Type} 
  (i : A → B) (r : B → A) (H : homotopy (λ x, r (i x)) (λ x, x)) 
  (K : Π (b : B), P (r b)) (b :B)
  : Id (retraction_precompose i r H K (r b)) (K b) :=
  

definition is_equiv {A B : Type} (f : A → B) : Type :=
  hprod (has_retraction f) (has_section f)

namespace is_equiv

definition construct {A B : Type} {f : A → B}
  : Π (f_linv : B → A) (f_islinv : homotopy (λ x, f_linv (f x)) (λ x, x))
      (f_rinv : B → A) (f_isrinv : homotopy (λ y, f (f_rinv y)) (λ y, y)),
    is_equiv f :=
  λ h H g G, hSigma.pair (hSigma.pair h H) (hSigma.pair g G)

definition destruct {A B : Type} {f : A → B} {P : is_equiv f → Type}
  : (Π (h : B → A) (is_retraction : homotopy (λ x, h (f x)) (λ x, x))
       (g : B → A) (is_section : homotopy (λ y, f (g y)) (λ y, y)),
       P (construct h is_retraction g is_section))
  → Π (E : is_equiv f), P E :=
  λ F, hSigma.rec 
    ( hSigma.rec 
      ( λ h is_retraction, hSigma.rec
        ( λ g is_section, F h is_retraction g is_section)
      )
    )

end is_equiv

definition equiv (A B : Type) : Type := hSigma (A → B) (λ f, is_equiv f)

definition invertible {A B : Type} (f : A → B) : Type :=
  hSigma 
    (B → A) 
    (λ g, hprod 
            (homotopy (λ y, f (g y)) (λ y, y)) 
            (homotopy (λ x, g (f x)) (λ x, x))
    )

namespace invertible

definition construct {A B : Type} {f : A → B} (g : B → A) 
  (is_section : homotopy (λ y, f (g y)) (λ y, y)) 
  (is_retraction : homotopy (λ x, g (f x)) (λ x, x)) 
  : invertible f := 
  hSigma.pair g (hprod.pair is_section is_retraction)

definition destruct {A B : Type} {f : A → B} {P : invertible f → Type}
  (D : Π (g : B → A) (is_sec : homotopy (λ y, f (g y)) (λ y, y))
       ( is_retr : homotopy (λ x, g (f x)) (λ x, x)), 
       P (construct g is_sec is_retr))
  : Π (I : invertible f), P I :=
  hSigma.rec (λ g, hSigma.rec (λ h k, D g h k))

end invertible

definition is_equiv_idfun (A : Type) : is_equiv (λ (x : A), x) :=
  is_equiv.construct (λ x, x) (htpy.refl _) (λ x, x) (htpy.refl _)

definition is_equiv_of_invertible {A B : Type} (f : A → B) 
  : invertible f → is_equiv f :=
  invertible.destruct 
    ( λ g is_sec is_retr, is_equiv.construct g is_retr g is_sec) 

definition invertible_of_is_equiv {A B : Type} (f : A → B) 
  : is_equiv f → invertible f :=
  is_equiv.destruct 
    ( λ h is_retr g is_sec,
      ( invertible.construct g is_sec
        ( λ x, Id.concat 
          ( Id.inv (is_retr (g (f x)))) 
          ( Id.concat (ap h (is_sec (f x))) (is_retr x))
        )
      )  
    )

-- Exercise
definition is_equiv_of_htpy {A B : Type} {f g : A → B} 
  : (homotopy f g) → is_equiv g → is_equiv f :=
  λ H, is_equiv.destruct
    ( λ g_linv g_islinv g_rinv g_isrinv, is_equiv.construct 
      ( g_linv) 
      ( htpy.concat (htpy.whisker_left g_linv H) g_islinv)
      (  g_rinv)
      ( htpy.concat (htpy.whisker_right H g_rinv) g_isrinv)
    )

-- Exercise
definition equiv_compose {A B C : Type} {f : A → B} {g : B → C} {h : A → C} 
  {H : homotopy h (λ x, g (f x))}
  : is_equiv f → is_equiv g → is_equiv h :=
  is_equiv.destruct
    ( λ f_linv f_islinv f_rinv f_isrinv, is_equiv.destruct 
      ( λ g_linv g_islinv g_rinv g_isrinv, is_equiv_of_htpy H
        ( is_equiv.construct
          (λ z, f_linv (g_linv z)) 
          ( htpy.concat 
            ( htpy.whisker_right (htpy.whisker_left f_linv g_islinv) f) 
            ( f_islinv)
          )
          (λ z, f_rinv (g_rinv z)) 
          ( htpy.concat 
            ( htpy.whisker_right (htpy.whisker_left g f_isrinv) g_rinv) 
            ( g_isrinv)
          )
        )
      )
    )

definition inv_of_is_equiv {A B : Type} {e : A → B} 
  : is_equiv e → (B → A) :=
  is_equiv.destruct (λ h is_retr g is_sec, g)

definition inv_of_invertible {A B : Type} {f : A → B}
  : invertible f → (B → A) :=
  invertible.destruct (λ g is_sec is_retr, g)

definition invertible_inv_of_invertible {A B : Type} {f : A → B}
  : Π (I : invertible f), invertible (inv_of_invertible I) :=
  invertible.destruct 
    ( λ g is_sec is_retr, invertible.construct f is_retr is_sec)

definition is_equiv_equiv_inv {A B : Type} {e : A → B} 
  : Π (H : is_equiv e), is_equiv (inv_of_is_equiv H) :=
  λ H, is_equiv_of_htpy 
    ( λ y, is_equiv.destruct ( λ h is_retr g is_sec, (Id.refl _)) H) 
    ( is_equiv_of_invertible _ 
      ( invertible_inv_of_invertible (invertible_of_is_equiv e H))
    )

/--
definition equiv_3for2_left {A B C : Type} {f : A → B} {g : B → C} {h : A → C} 
  {H : homotopy h (λ x, g (f x))}
  : is_equiv f → is_equiv h → is_equiv g :=
  is_equiv.destruct 
    ( λ fl is_retr fr is_sec, is_equiv.destruct
      ( λ hl is_retr hr is_sec, is_equiv.construct 
        _
        _
        _
        _
      )
    )
--/

namespace hSigma

definition eta {A : Type} {B : A → Type} 
  : Π (x : hSigma A B), Id x (pair (pr1 x) (pr2 x)) :=
  hSigma.rec (λ a b, Id.refl _)

/--
In the following we construct an equivalence computing the identity type of a Σ-type. 

--/

definition eq_of_pair {A : Type} {B : A → Type} (u v : hSigma A B)
  : hSigma (Id (pr1 u) (pr1 v)) 
          (λ p, Id (transport p (pr2 u)) (pr2 v)) 
  → Id u v :=
  hSigma.rec 
    ( λ y q, hSigma.rec 
      ( λ x p, hSigma.rec 
        ( λ bpath fpath, Id.rec (Id.rec (Id.refl _) bpath) fpath
        )
      ) u
    ) v

definition pair_of_eq {A : Type} {B : A → Type} (x y : hSigma A B)
  : (Id x y)
  → hSigma (Id (pr1 x) (pr1 y))
    (λ u, Id (transport u (pr2 x)) (pr2 y)) :=
  Id.rec (pair (Id.refl _) (Id.refl _))

definition base_path {A : Type} {B : A → Type} {x y : hSigma A B}
  : Id x y → Id (pr1 x) (pr1 y) :=
  λ p, pr1 (pair_of_eq _ _ p)

definition fiber_path {A : Type} {B : A → Type} {x y : hSigma A B}
  : Π (p : Id x y), Id (transport (base_path p) (pr2 x)) (pr2 y)
  :=
  λ p, pr2 (pair_of_eq _ _ p)

definition base_path_eq_of_pair {A : Type} {B : A → Type} {a : A} {b : B a} {a' : A}
  {b' : B a'} (p : Id a a') (q : Id (transport p b) b')
  : Id ( base_path (eq_of_pair (pair a b) (pair a' b') (pair p q))) p
  :=
  Id.rec (Id.rec (Id.refl (Id.refl a)) p) q

definition fiber_path_eq_of_pair {A : Type} {B : A → Type} {a : A} {b : B a} {a' : A}
  {b' : B a'} (p : Id a a') (q : Id (transport p b) b')
  : Id ( transport (base_path_eq_of_pair p q)
         ( fiber_path (eq_of_pair (pair a b) (pair a' b') (pair p q)))
       )
       ( q)
  :=
  Id.rec (Id.rec (Id.refl (Id.refl b)) p) q

definition eq_of_pair_is_retraction {A : Type} {B : A → Type} (u v : hSigma A B)
  : homotopy (λ x, (eq_of_pair u v (pair_of_eq u v x))) (λ x, x) :=
  Id.rec (hSigma.rec (λ p q, (Id.refl _)) u )

definition eq_of_pair_is_section {A : Type} {B : A → Type} 
  : Π (x y : hSigma A B), homotopy (λ t, pair_of_eq x y (eq_of_pair x y t)) (λ t, t) :=
  hSigma.rec
    ( λ a b, hSigma.rec 
      ( λ a' b', hSigma.rec 
        ( λ p q, eq_of_pair (pair_of_eq _ _ (eq_of_pair _ _ (pair p q))) (pair p q) 
          ( hSigma.pair (base_path_eq_of_pair p q) (fiber_path_eq_of_pair p q))
        ) 
      ) 
    )

definition pair_of_eq_invertible {A : Type} {B : A → Type} (x y : hSigma A B)
  : invertible (pair_of_eq x y) :=
  invertible.construct
    ( eq_of_pair x y)
    ( eq_of_pair_is_section x y)
    ( eq_of_pair_is_retraction x y)

definition pair_of_eq_is_equiv {A : Type} {B : A → Type} (x y : hSigma A B)
  : is_equiv (pair_of_eq x y) :=
  is_equiv_of_invertible (pair_of_eq x y) (pair_of_eq_invertible _ _)

end hSigma

definition is_contr (A : Type) : Type := hSigma A (λ a, Π (x : A), Id a x)

namespace is_contr

definition center {A : Type} (H : is_contr A) : A := hSigma.pr1 H

definition contraction {A : Type} (H : is_contr A) : homotopy (λ x, center H) (λ x, x) := 
  λ x, hSigma.pr2 H x

definition construct {A : Type} (a : A) (H : homotopy (λ x, a) (λ x, x))
  : is_contr A :=
  hSigma.pair a H

definition destruct {A : Type} {P : is_contr A → Type}
  (D : Π (a : A) (H : homotopy (λ x, a) (λ x, x)), P (construct a H))
  : Π (c : is_contr A), P c :=
  hSigma.rec D

end is_contr

definition is_contr_unit : is_contr hunit :=
  hSigma.pair hunit.tt (hunit.rec (Id.refl _))

-- Exercise
definition is_contr_of_retr {A B : Type} (i : A → B) (r : B → A) 
  (H : homotopy (λ x, r (i x)) (λ x, x)) 
  : is_contr B → is_contr A :=
  is_contr.destruct 
    ( λ b q, is_contr.construct (r b) (λ x, Id.concat (ap r (q (i x))) (H x)))

-- Exercise
definition is_contr_of_equiv {A B : Type}
  : equiv A B → is_contr B → is_contr A :=
  hSigma.rec (λ e, hSigma.rec (hSigma.rec (λ r H T, is_contr_of_retr e r H)))

-- Exercise
definition is_contr_of_equiv' {A B : Type}
  : equiv A B → is_contr A → is_contr B :=
  hSigma.rec (λ e, hSigma.rec (λ T, hSigma.rec (λ i H, is_contr_of_retr i e H)))

definition fiber {A B : Type} (f : A → B) (b : B) := hSigma A (λ a, Id (f a) b)

definition fiber' {A B : Type} (f : A → B) (b : B) := hSigma A (λ a, Id b (f a))

namespace map

definition is_contr {A B : Type} (f : A → B) : Type := 
  Π (b : B), is_contr (fiber f b)

end map

definition is_equiv_of_is_contr {A B : Type} (f : A → B) 
  : map.is_contr f → is_equiv f :=
  λ H, is_equiv_of_invertible f 
    ( invertible.construct
      (λ b, hSigma.pr1 (is_contr.center (H b)))
      (λ b, hSigma.pr2 (is_contr.center (H b)))
      (λ a, @hSigma.base_path _ _ _ 
              ( hSigma.pair a (Id.refl (f a))) 
              ( is_contr.contraction (H (f a)) _))
    )

definition is_contr_of_invertible {A B : Type} (f : A → B)
  : invertible f → map.is_contr f :=
  invertible.destruct
    ( λ g is_section is_retraction b, is_contr.construct 
      ( hSigma.pair (g b) 
        ( Id.concat 
          ( Id.inv (ap (λ x, f (g x)) (is_section b))) 
          ( Id.concat (ap f (is_retraction (g b))) (is_section b))
        )
      )
      ( hSigma.rec 
        ( λ a, Id.rec   
          ( hSigma.eq_of_pair _ _ --these arguments are explicit and inferred
            ( hSigma.pair 
              ( is_retraction a) 
              ( Id.concat 
                ( tr.fun_rel _ _ _) 
                ( Id.inv_con'
                  ( Id.concat 
                    ( Id.inv_con' 
                      ( Id.inv
                        ( square.whisker_top 
                          ( retraction_swap is_section (f a)) 
                          ( square.whisker_left 
                            ( Id.inv ( ap (ap f) ( retraction_swap is_retraction a)))
                            ( square.whisker_left 
                              ( ap.compose _ _ _) 
                              ( htpy.natural _ _)
                            )
                          )
                        )
                      )
                    ) 
                    ( Id.inv (Id.right_unit _))
                  ) 
                )
              ) 
            )  
          ) 
        )
      )
    )

definition is_contr_of_is_equiv {A B : Type} (f : A → B)
  : is_equiv f → map.is_contr f :=
  λ H, is_contr_of_invertible f (invertible_of_is_equiv f H)

definition is_contr_idfun {A : Type} : map.is_contr (λ (x : A), x) :=
  is_contr_of_is_equiv (λ x, x) (is_equiv_idfun A)

definition is_contr_total_path {A : Type}
  : Π (a : A), is_contr (hSigma A (λ x, Id x a)) :=
  is_contr_idfun

namespace hint
/--
We prove some basic properties of operations on the integers
--/

definition hnat_hnat_of_hint : hint → hprod hnat hnat :=
  destruct
    ( λ n, hSigma.pair hnat.zero (hnat.succ n))
    ( hSigma.pair hnat.zero hnat.zero)
    ( λ n, hSigma.pair (hnat.succ n) hnat.zero)

definition hint_of_canonical_rep (p : hprod hnat hnat)
  : hnat.is_canonical_rep p → hint :=
  coprod.rec 
    ( hSigma.rec (λ m q, (neg m))) 
    ( coprod.rec (λ q, zero) (hSigma.rec (λ m q, (pos m))))

-- contains sorry :(
eval hint_of_canonical_rep
       (hnat.to_canonical_rep
          (hnat_hnat_of_hint neg_one))
       (hnat.is_canonical_rep_of_to_canoncal_rep
          (hnat_hnat_of_hint neg_one))

definition has_retraction_hnat_hnat_of_hint : 
  has_retraction (hnat_hnat_of_hint) :=
  hSigma.pair 
    ( λ p, hint_of_canonical_rep 
      ( hnat.to_canonical_rep p) 
      ( hnat.is_canonical_rep_of_to_canoncal_rep p)
    )
    ( sorry)
/--
definition pred_neg_succ : Π (n : nat), Id (pred (neg n)) (neg (nat.succ n)) :=
  nat.rec (Id.refl _) (λ n p, _)

definition pred_is_retr : homotopy (λ k, pred (succ k)) (λ k, k) :=
  destruct_full
    (Id.refl _)
    (λ n p, Id.concat _ (ap pred p))
    _
    _
    _

definition assoc_add 
  : Π (k l m : int), Id (add k (add l m)) (add (add k l) m) :=
  int.destruct 
    ( nat.rec 
      ( int.destruct 
        ( nat.rec 
          ( int.destruct 
            ( nat.rec (Id.refl _) 
              ( λ m assoc_negk_negl_negm, ap pred assoc_negk_negl_negm)
            ) 
            ( unit.rec (Id.refl _) unit.tt) 
            ( nat.rec (Id.refl _)
              ( λ m assoc_negk_negl_posm, _)
            )
          ) 
          _
        ) 
        _ _
      )
      ( _)
    ) 
    ( _)
    ( _)

--/

end hint
