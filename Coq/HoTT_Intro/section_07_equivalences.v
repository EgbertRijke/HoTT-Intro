Require Export section_06_universes.

(** Section 7.1. Homotopies *)

(** Definition 7.1.1 *)

Definition htpy {A} {B : A -> Type} (f g : forall x, B x) : Type :=
  forall x, f x == g x.

Notation "f '~' g" := (htpy f g) (at level 90).

(** Definition 7.1.2 *)

Definition refl_htpy {A} {B : A -> Type} {f : forall x, B x} : f ~ f :=
  fun x => refl.

Definition concat_htpy {A} {B : A -> Type} {f g h : forall x, B x} :
  f ~ g -> g ~ h -> f ~ h.
Proof.
  intros H K x.
  exact (concat (H x) (K x)).
Defined.

Definition concat_htpy' {A} {B : A -> Type} {f g h : forall x, B x}
           (K : g ~ h) (H : f ~ g) := concat_htpy H K.

Definition inv_htpy {A} {B : A -> Type} {f g : forall x, B x} :
  f ~ g -> g ~ f.
Proof.
  intros H x.
  exact (inv (H x)).
Defined.

Definition assoc_htpy {A} {B : A -> Type} {f g h k : forall x, B x}
           (H : f ~ g) (K : g ~ h) (L : h ~ k) :
  concat_htpy (concat_htpy H K) L ~ concat_htpy H (concat_htpy K L).
Proof.
  intro x.
  exact (assoc (H x) (K x) (L x)).
Defined.

Definition left_unit_htpy {A} {B : A -> Type} {f g : forall x, B x}
           {H : f ~ g} :
  concat_htpy refl_htpy H ~ H.
Proof.
  intro x.
  exact left_unit.
Defined.

Definition right_unit_htpy {A} {B : A -> Type} {f g : forall x, B x}
           {H : f ~ g} :
  concat_htpy H refl_htpy ~ H.
Proof.
  intro x.
  exact right_unit.
Defined.

Definition left_inv_htpy {A} {B : A -> Type} {f g : forall x, B x}
           {H : f ~ g} :
  concat_htpy (inv_htpy H) H ~ refl_htpy.
Proof.
  intro x.
  exact left_inv.
Defined.

Definition right_inv_htpy {A} {B : A -> Type} {f g : forall x, B x}
           {H : f ~ g} :
  concat_htpy H (inv_htpy H) ~ refl_htpy.
Proof.
  intro x.
  exact right_inv.
Defined.

(** Definition 7.1.3 *)

Definition left_whisker_htpy {A B C} (g : B -> C) {f f' : A -> B} (H : f ~ f') :
  comp g f ~ comp g f'.
Proof.
  intro x.
  exact (ap g (H x)).
Defined.

Definition right_whisker_htpy {A B C} {g g' : B ->C} (H : g ~ g') (f : A -> B) :
  comp g f ~ comp g' f.
Proof.
  intro x.
  exact (H (f x)).
Defined.

(** Section 7.2. Bi-invertible maps *)

(** Definition 7.2.1 *)

Definition sec {A B} (f : A -> B) : Type :=
  Sigma (B -> A) (fun g => comp f g ~ idmap).

Definition map_sec {A B} {f : A -> B} (s : sec f) : B -> A := pr1 s.

Definition is_sec_map_sec {A B} {f : A -> B} (s : sec f) :
  comp f (map_sec s) ~ idmap := pr2 s.

Definition retr {A B} (f : A -> B) : Type :=
  Sigma (B -> A) (fun h => comp h f ~ idmap).

Definition map_retr {A B} {f : A -> B} (r : retr f) : B -> A := pr1 r.

Definition is_retr_map_retr {A B} {f : A -> B} (r : retr f) :
  comp (map_retr r) f ~ idmap := pr2 r.

Definition sr_pair (A B : Type) :=
  Sigma (A -> B) retr.

Definition is_equiv {A B} (f : A -> B) : Type :=
  prod (sec f) (retr f).

Definition equiv (A B : Type) : Type := Sigma (A -> B) is_equiv.

Notation "A '<~>' B" := (equiv A B) (at level 70).

Definition map_equiv {A B} (e : A <~> B) : A -> B := pr1 e.

Definition is_equiv_map_equiv {A B} (e : A <~> B) :
  is_equiv (map_equiv e) := pr2 e.

(** Remark 7.2.2 *)

Definition has_inverse {A B} (f : A -> B) : Type :=
  Sigma (B -> A) (fun g => prod (comp f g ~ idmap) (comp g f ~ idmap)).

Definition inv_has_inverse {A B} {f : A -> B} :
  has_inverse f -> B -> A := pr1.

Definition is_sec_inv_has_inverse {A B} {f : A -> B} (H : has_inverse f) :
  comp f (inv_has_inverse H) ~ idmap := pr1 (pr2 H).

Definition is_retr_inv_has_inverse {A B} {f : A -> B} (H : has_inverse f) :
  comp (inv_has_inverse H) f ~ idmap := pr2 (pr2 H).

Definition is_equiv_has_inverse {A B} {f : A -> B} :
  forall (g : B -> A), (comp f g ~ idmap) -> (comp g f ~ idmap) -> is_equiv f.
Proof.
  intros g G H.
  exact (pair (pair g G) (pair g H)).
Defined.

Definition is_equiv_has_inverse' {A B} (f : A -> B) :
  has_inverse f -> is_equiv f.
Proof.
  intro I.
  destruct I as [g [G H]].
  now apply (is_equiv_has_inverse g).
Defined.

(** Lemma 7.2.3 *)

Definition sec_is_equiv {A B} {f : A -> B} (H : is_equiv f) : sec f := pr1 H.

Definition inv_is_equiv {A B} {f : A -> B} (H : is_equiv f) : B -> A :=
  map_sec (sec_is_equiv H).

Definition is_sec_inv_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  comp f (inv_is_equiv H) ~ idmap := is_sec_map_sec (sec_is_equiv H).

Definition retr_is_equiv {A B} {f : A -> B} (H : is_equiv f) : retr f := pr2 H.

Definition map_retr_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  B -> A := map_retr (retr_is_equiv H).

Definition htpy_retr_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  comp (map_retr_is_equiv H) f ~ idmap := is_retr_map_retr (retr_is_equiv H).

Definition htpy_sec_retr {A B} {f : A -> B} (H : is_equiv f) :
  inv_is_equiv H ~ map_retr_is_equiv H.
Proof.
  intro y.
  transitivity (map_retr_is_equiv H (f (inv_is_equiv H y))).
  - exact (inv (htpy_retr_is_equiv H (inv_is_equiv H y))).
  - exact (ap (map_retr_is_equiv H) (is_sec_inv_is_equiv H y)).
Defined.

Definition is_retr_inv_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  comp (inv_is_equiv H) f ~ idmap.
Proof.
  intro x.
  transitivity (map_retr_is_equiv H (f x)).
  - exact (htpy_sec_retr H (f x)).
  - exact (htpy_retr_is_equiv H x).
Defined.

Definition has_inverse_is_equiv {A B} {f : A -> B} :
  is_equiv f -> has_inverse f.
Proof.
  intro H.
  apply (pair (inv_is_equiv H)).
  apply pair.
  - exact (is_sec_inv_is_equiv H).
  - exact (is_retr_inv_is_equiv H).
Defined.

(** Corollary 7.2.4 *)

Definition has_inverse_inv_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  has_inverse (inv_is_equiv H).
Proof.
  apply (pair f).
  apply pair.
  - exact (is_retr_inv_is_equiv H).
  - exact (is_sec_inv_is_equiv H).
Defined.

Definition is_equiv_inv_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  is_equiv (inv_is_equiv H).
Proof.
  apply is_equiv_has_inverse'.
  apply has_inverse_inv_is_equiv.
Defined.

Definition inv_equiv {A B} : (A <~> B) -> (B <~> A).
Proof.
  intro e.
  simple refine (pair _ _).
  - exact (inv_is_equiv (is_equiv_map_equiv e)).
  - apply is_equiv_inv_is_equiv.
Defined.

(** Remark 7.2.5 *)

Definition is_equiv_idmap {A} : is_equiv (@idmap A).
Proof.
  apply (is_equiv_has_inverse idmap); exact refl_htpy.
Defined.

Definition id_equiv {A} : A <~> A := pair idmap is_equiv_idmap.

(** Example 7.2.6 *)

Definition is_equiv_swap_Pi {A B} (C : A -> B -> Type) :
  is_equiv (@swap_Pi A B C).
Proof.
  simple refine (is_equiv_has_inverse _ _ _).
  - exact (@swap_Pi B A (fun y x => C x y)).
  - exact refl_htpy.
  - exact refl_htpy.
Defined.

(** Section 7.3. The identity type of a Sigma-type *)

(** Definition 7.3.1 *)

Definition Eq_Sigma {A : Type} {B : A -> Type} (s t : Sigma A B) : Type :=
  Sigma (pr1 s == pr1 t) (fun p => tr B p (pr2 s) == pr2 t).

(** Lemma 7.3.2 *)

Lemma refl_Eq_Sigma {A B} {s : Sigma A B} : Eq_Sigma s s.
Proof.
  exact (pair refl refl).
Defined.

(** Definition 7.3.3 *)

Definition pair_eq {A B} {s t : Sigma A B} (p : s == t) : Eq_Sigma s t.
Proof.
  destruct p.
  exact refl_Eq_Sigma.
Defined.

(** Theorem 7.3.4 *)

Definition eq_pair {A B} {s t : Sigma A B} (p : Eq_Sigma s t) : s == t.
Proof.
  destruct p as [p q].
  destruct s as [x y]; destruct t as [x' y'].
  cbn in p; cbn in q.
  destruct p; destruct q.
  reflexivity.
Defined.

Definition is_sec_eq_pair {A B} {s t : Sigma A B} :
  comp (@pair_eq A B s t) (@eq_pair A B s t) ~ idmap.
Proof.
  intro p.
  destruct p as [p q].
  destruct s as [x y]; destruct t as [x' y'].
  cbn in p; cbn in q.
  destruct p; destruct q.
  reflexivity.
Defined.

Definition is_retr_eq_pair {A B} {s t : Sigma A B} :
  comp (@eq_pair A B s t) (@pair_eq A B s t) ~ idmap.
Proof.
  intro p; destruct p.
  destruct s. reflexivity.
Defined.

Theorem is_equiv_pair_eq {A B} {s t : Sigma A B} :
  is_equiv (@pair_eq A B s t).
Proof.
  simple refine (is_equiv_has_inverse _ _ _).
  - exact eq_pair.
  - exact is_sec_eq_pair.
  - exact is_retr_eq_pair.
Defined.

Definition pair_eq_equiv {A B} {s t : Sigma A B} :
  (s == t) <~> Eq_Sigma s t := pair pair_eq is_equiv_pair_eq.

Theorem is_equiv_eq_pair {A B} {s t : Sigma A B} :
  is_equiv (@eq_pair A B s t).
Proof.
  simple refine (is_equiv_has_inverse _ _ _).
  - exact pair_eq.
  - exact is_retr_eq_pair.
  - exact is_sec_eq_pair.
Defined.

Definition eq_pair_equiv {A B} {s t : Sigma A B} :
  (Eq_Sigma s t) <~> (s == t) := pair eq_pair is_equiv_eq_pair.

(** Exercises *)

(** Exercise 7.1 *)

Definition inv_inv {A} {x y : A} (p : x == y) : inv (inv p) == p.
Proof.
  now destruct p.
Defined.

Theorem is_equiv_inv {A} {x y} : is_equiv (@inv A x y).
Proof.
  apply (is_equiv_has_inverse inv); exact inv_inv.
Defined.

Definition invmap_equiv {A} {x y : A} : (x == y) <~> (y == x) :=
  pair inv is_equiv_inv.

Theorem is_equiv_concat {A} {x y z : A} (p : x == y) :
  is_equiv (@concat A x y z p).
Proof.
  apply (is_equiv_has_inverse (concat (inv p))); destruct p; exact refl_htpy.
Defined.

Definition concat_equiv {A} {x y z : A} (p : x == y) :
  (y == z) <~> (x == z) :=
  pair (concat p) (is_equiv_concat p).

Theorem is_equiv_concat' {A} {x y z : A} (q : y == z) :
  is_equiv (@concat' A x y z q).
Proof.
  apply (is_equiv_has_inverse (concat' (inv q)));
    destruct q; intro p; now destruct p.
Defined.

Definition concat_equiv' {A} {x y z : A} (q : y == z) :
  (x == y) <~> (x == z) :=
  pair (concat' q) (is_equiv_concat' q).

Theorem is_equiv_tr {A} {B : A -> Type} {x y} (p : x == y) : is_equiv (tr B p).
Proof.
  apply (is_equiv_has_inverse (tr B (inv p))); destruct p; exact refl_htpy.
Defined.

Definition tr_equiv {A} (B : A -> Type) {x y} (p : x == y) :
  B x <~> B y := pair (tr B p) (is_equiv_tr p).

(** Exercise 7.2 *)

Definition inv_inl {X} : coprod X empty -> X.
Proof.
  intro x; now destruct x.
Defined.

Definition is_sec_inv_inl {X} : comp (@inl X empty) (@inv_inl X) ~ idmap.
Proof.
  intro x; now destruct x.
Defined.

Definition is_retr_inv_inl {X} : comp (@inv_inl X) (@inl X empty) ~ idmap.
Proof.
  now intro x.
Defined.

Theorem is_equiv_inl {X} : is_equiv (@inl X empty).
Proof.
  simple refine (is_equiv_has_inverse _ _ _).
  - exact inv_inl.
  - exact is_sec_inv_inl.
  - exact is_retr_inv_inl.
Defined.

Definition right_unit_law_coprod {X} : X <~> coprod X empty :=
  pair inl is_equiv_inl.

Definition inv_inr {X} : coprod empty X -> X.
Proof.
  intro x; now destruct x.
Defined.

Definition is_sec_inv_inr {X} : comp (@inr empty X) (@inv_inr X) ~ idmap.
Proof.
  intro x; now destruct x.
Defined.

Definition is_retr_inv_inr {X} : comp (@inv_inr X) (@inr empty X) ~ idmap.
Proof.
  now intro x.
Defined.

Theorem is_equiv_inr {X} : is_equiv (@inr empty X).
Proof.
  simple refine (is_equiv_has_inverse _ _ _).
  - exact inv_inr.
  - exact is_sec_inv_inr.
  - exact is_retr_inv_inr.
Defined.

Definition left_unit_law_coprod {X} : X <~> coprod empty X :=
  pair inr is_equiv_inr.

Definition inv_pr1_empty {X} : empty -> prod empty X := ex_falso.

Definition is_sec_inv_pr1_empty {X} :
  comp pr1 (@inv_pr1_empty X) ~ idmap := ex_falso.

Definition is_retr_inv_pr1_empty {X} :
  comp (@inv_pr1_empty X) pr1 ~ idmap.
Proof.
  intro x; now destruct x.
Defined.

Theorem is_equiv_pr1_empty {X} : is_equiv (@pr1 empty (fun t => X)).
Proof.
  simple refine (is_equiv_has_inverse _ _ _).
  - exact inv_pr1_empty.
  - exact is_sec_inv_pr1_empty.
  - exact is_retr_inv_pr1_empty.
Defined.

Definition left_zero_law_prod {X} : prod empty X <~> empty :=
  pair pr1 is_equiv_pr1_empty.

Definition inv_pr2_empty {X} : empty -> prod X empty := ex_falso.

Definition is_sec_inv_pr2_empty {X} :
  comp (@pr2 X (const empty)) (@inv_pr2_empty X) ~ idmap := ex_falso.

Definition is_retr_inv_pr2_empty {X} :
  comp (@inv_pr2_empty X) (@pr2 X (const empty)) ~ idmap.
Proof.
  intro x. now destruct x.
Defined.

Theorem is_equiv_pr2_empty {X} : is_equiv (@pr2 X (const empty)).
Proof.
  simple refine (is_equiv_has_inverse _ _ _).
  - exact inv_pr2_empty.
  - exact is_sec_inv_pr2_empty.
  - exact is_retr_inv_pr2_empty.
Defined.

Definition right_zero_law_prod {X} : prod X empty <~> empty :=
  pair pr2 is_equiv_pr2_empty.

(** Exercise 7.3 *)

(** Exercise 7.3.a *)

Definition is_sec_inv_is_equiv_htpy {A B} {f g : A -> B} (H : f ~ g)
           (is_equiv_g : is_equiv g) :
  comp f (inv_is_equiv is_equiv_g) ~ idmap :=
  concat_htpy
    (right_whisker_htpy H (inv_is_equiv is_equiv_g))
    (is_sec_inv_is_equiv is_equiv_g).

Definition is_retr_inv_is_equiv_htpy {A B} {f g : A -> B} (H : f ~ g)
           (is_equiv_g : is_equiv g) :
  comp (inv_is_equiv is_equiv_g) f ~ idmap :=
  concat_htpy
    (left_whisker_htpy (inv_is_equiv is_equiv_g) H)
    (is_retr_inv_is_equiv is_equiv_g).

Theorem is_equiv_htpy {A B} {f g : A -> B} (H : f ~ g) :
  is_equiv g -> is_equiv f.
Proof.
  intro is_equiv_g.
  simple refine (is_equiv_has_inverse _ _ _).
  - exact (inv_is_equiv is_equiv_g).
  - exact (is_sec_inv_is_equiv_htpy H is_equiv_g).
  - exact (is_retr_inv_is_equiv_htpy H is_equiv_g).
Defined.

Definition is_equiv_htpy' {A B} {f g : A -> B} (H : f ~ g) :
  is_equiv f -> is_equiv g := is_equiv_htpy (inv_htpy H).

(** Exercise 7.3.b *)

Definition htpy_equiv {A B} (e e' : A <~> B) : Type :=
  map_equiv e ~ map_equiv e'.

Notation "e '~e' f" := (htpy_equiv e f) (at level 70).

Definition htpy_inv_equiv {A B} {e e' : A <~> B} :
  e ~e e' -> (inv_equiv e) ~e (inv_equiv e').
Proof.
  intros H y.
  transitivity
    (map_equiv (inv_equiv e') (map_equiv e' (map_equiv (inv_equiv e) y))).
  - apply inv. apply (is_retr_inv_is_equiv (is_equiv_map_equiv e')).
  - transitivity
      (map_equiv (inv_equiv e') (map_equiv e (map_equiv (inv_equiv e) y))).
    * apply inv.
      apply (ap (map_equiv (inv_equiv e'))).
      apply H.
    * apply (ap (map_equiv (inv_equiv e'))).
      apply (is_sec_inv_is_equiv (is_equiv_map_equiv e)).
Defined.

(** Exercise 7.4 *)

(** Exercise 7.4.a *)

Definition hom_slice {A B X} (f : A -> X) (g : B -> X) : Type :=
  Sigma (A -> B) (fun h => f ~ comp g h).

Definition map_hom_slice {A B X} {f : A -> X} {g : B -> X} (h : hom_slice f g) :
  A -> B := pr1 h.

Definition triangle_hom_slice {A B X} {f : A -> X} {g : B -> X} (h : hom_slice f g) : f ~ comp g (map_hom_slice h) := pr2 h.

Definition triangle_sec_map_hom_slice {A B X} {f : A -> X} {g : B -> X} (h : hom_slice f g) (s : sec (map_hom_slice h)) :
  g ~ comp f (map_sec s).
Proof.
  apply inv_htpy.
  eapply concat_htpy.
  - exact (right_whisker_htpy (triangle_hom_slice h) (map_sec s)).
  - exact (left_whisker_htpy g (is_sec_map_sec s)).
Defined.

Definition hom_slice_sec_map_hom_slice {A B X} {f : A -> X} {g : B -> X}
           (h : hom_slice f g) (s : sec (map_hom_slice h)) :
  hom_slice g f.
Proof.
  apply (pair (map_sec s)).
  exact (triangle_sec_map_hom_slice h s).
Defined.

Definition section_comp {A B X} {f : A -> X} {g : B -> X} (h : hom_slice f g) :
  sec (map_hom_slice h) -> sec f -> sec g.
Proof.
  intros sh sf.
  apply (pair (comp (map_hom_slice h) (map_sec sf))).
  eapply concat_htpy.
  - apply inv_htpy.
    exact (right_whisker_htpy (triangle_hom_slice h) (map_sec sf)).
  - exact (is_sec_map_sec sf).
Defined.

Definition section_comp' {A B X} {f : A -> X} {g : B -> X} (h : hom_slice f g) :
  sec (map_hom_slice h) -> sec g -> sec f.
Proof.
  intros sh sg.
  apply (pair (comp (map_sec sh) (map_sec sg))).
  eapply concat_htpy.
  - exact (right_whisker_htpy (triangle_hom_slice h) (comp (map_sec sh) (map_sec sg))).
  - apply (concat_htpy' (is_sec_map_sec sg)).
    apply (left_whisker_htpy g).
    exact (right_whisker_htpy (is_sec_map_sec sh) (map_sec sg)).
Defined.

(** Exercise 7.4.b *)

Definition triangle_retr_map_hom_slice {A B X} {f : A -> X} {g : B -> X}
           (h : hom_slice f g) (r : retr g) :
  (map_hom_slice h) ~ comp (map_retr r) f.
Proof.
  apply inv_htpy.
  eapply concat_htpy.
  - exact (left_whisker_htpy (map_retr r) (triangle_hom_slice h)).
  - exact (right_whisker_htpy (is_retr_map_retr r) (map_hom_slice h)).
Defined.

Definition hom_slice_retr_map_hom_slice {A B X} {f : A -> X} {g : B -> X}
           (h : hom_slice f g) (r : retr g) :
  hom_slice (map_hom_slice h) (map_retr r).
Proof.
  simple refine (pair _ _).
  - exact f.
  - exact (triangle_retr_map_hom_slice h r).
Defined.

Definition retraction_comp {A B X} {f : A -> X} {g : B -> X}
           (h : hom_slice f g) :
  retr g -> retr f -> retr (map_hom_slice h).
Proof.
  intros rg rf.
  simple refine (pair _ _).
  - exact (comp (map_retr rf) g).
  - eapply concat_htpy.
    * apply inv_htpy.
      exact (left_whisker_htpy (map_retr rf) (triangle_hom_slice h)).
    * exact (is_retr_map_retr rf).
Defined.

Definition retraction_comp' {A B X} {f : A -> X} {g : B -> X}
           (h : hom_slice f g) :
  retr g -> retr (map_hom_slice h) -> retr f.
Proof.
  intros rg rh.
  apply (pair (comp (map_retr rh) (map_retr rg))).
  eapply concat_htpy.
  - eapply (left_whisker_htpy (comp (map_retr rh) (map_retr rg))).
    exact (triangle_hom_slice h).
  - eapply concat_htpy.
    * eapply (left_whisker_htpy (map_retr rh)).
      exact (right_whisker_htpy (is_retr_map_retr rg) (map_hom_slice h)).
    * exact (is_retr_map_retr rh).
Defined.

(** Exercise 7.4.c *)

Definition is_equiv_comp {A B X} {f : A -> X} {g : B -> X} (h : hom_slice f g) :
  is_equiv (map_hom_slice h) -> is_equiv g -> is_equiv f.
Proof.
  intros is_equiv_h is_equiv_g.
  apply pair.
  - apply (section_comp' h); now apply sec_is_equiv.
  - apply (retraction_comp' h); now apply retr_is_equiv.
Defined.

Definition is_equiv_comp' {A B X} {g : B -> X} {h : A -> B} :
  is_equiv h -> is_equiv g -> is_equiv (comp g h) :=
  is_equiv_comp (pair h (@refl_htpy _ _ (comp g h))).

Definition comp_equiv {A B C} (e : A <~> B) (e' : B <~> C) : A <~> C.
Proof.
  simple refine (pair _ _).
  exact (comp (map_equiv e') (map_equiv e)).
  exact (is_equiv_comp' (is_equiv_map_equiv e) (is_equiv_map_equiv e')).
Defined.

Definition is_equiv_left_factor {A B X} {f : A -> X} {g : B -> X}
           (h : hom_slice f g) :
  is_equiv f -> is_equiv (map_hom_slice h) -> is_equiv g.
Proof.
  intros is_equiv_f is_equiv_h.
  apply pair.
  - apply (section_comp h); now apply sec_is_equiv.
  - apply
      (retraction_comp'
         (hom_slice_sec_map_hom_slice h (sec_is_equiv is_equiv_h))).
    * now apply retr_is_equiv.
    * apply retr_is_equiv.
      apply is_equiv_inv_is_equiv.
Defined.

Definition is_equiv_left_factor' {A B X} {g : B -> X} {h : A -> B} :
  is_equiv (comp g h) -> is_equiv h -> is_equiv g :=
  is_equiv_left_factor (pair h (@refl_htpy _ _ (comp g h))).

Definition is_equiv_right_factor {A B X} {f : A -> X} {g : B -> X}
           (h : hom_slice f g) :
  is_equiv f -> is_equiv g -> is_equiv (map_hom_slice h).
Proof.
  intros is_equiv_f is_equiv_g.
  apply pair.
  - simple refine (@section_comp' A X B _ _ _ _ _).
    shelve.
    * apply hom_slice_retr_map_hom_slice. 
    * now apply sec_is_equiv.
    * apply sec_is_equiv.
      apply (is_equiv_htpy' (htpy_sec_retr is_equiv_g)).
      now apply is_equiv_inv_is_equiv.
  - apply (retraction_comp h (retr_is_equiv is_equiv_g)).
    now apply retr_is_equiv.
Defined.

Definition is_equiv_right_factor' {A B X} {g : B -> X} {h : A -> B} :
  is_equiv (comp g h) -> is_equiv g -> is_equiv h :=
  is_equiv_right_factor (pair h (@refl_htpy _ _ (comp g h))).

(** Exercise 7.5 *)

(** Exercise 7.5.a *)

Definition negb_negb (b : bool) : negb (negb b) == b.
Proof.
  destruct b; reflexivity.
Defined.

Definition is_equiv_negb : is_equiv negb.
Proof.
  apply (is_equiv_has_inverse negb); exact negb_negb.
Defined.

Definition negb_equiv : bool <~> bool := pair negb is_equiv_negb.

(** Exercise 7.5.b *)

Notation "x =/= y" := (neg (x == y)) (at level 80).

Definition neg_eq_true_false : (true =/= false).
Proof.
  intro p.
  now apply (tr (Eq_bool true) p).
Defined.

(** Exercise 7.5.c *)

Definition neg_is_equiv_const_b (b : bool) :
  neg (is_equiv (@const bool bool b)).
Proof.
  intro H.
  apply neg_eq_true_false.
  transitivity (inv_is_equiv H b).
  - apply inv. apply (is_retr_inv_is_equiv H).
  - apply (is_retr_inv_is_equiv H).
Defined.

(** Exercise 7.6 *)

Definition is_sec_pred_Z : comp succ_Z pred_Z ~ idmap.
Proof.
  intros [n | x];
    try induction n as [n p];
    try destruct x as [x | m];
    try destruct x;
    try induction m as [|m q];
    now try auto.
Defined.

Definition is_retr_pred_Z : comp pred_Z succ_Z ~ idmap.
Proof.
  intros [n | x];
    try induction n as [|n p];
    try destruct x as [x | m];
    try destruct x;
    try induction m as [|m q];
    now try auto.
Defined.
    
Theorem is_equiv_succ_Z : is_equiv succ_Z.
Proof.
  simple refine (is_equiv_has_inverse _ _ _).
  - exact pred_Z.
  - exact is_sec_pred_Z.
  - exact is_retr_pred_Z.
Defined.

Definition succ_Z_equiv : Z <~> Z := pair succ_Z is_equiv_succ_Z.

Theorem is_equiv_pred_Z : is_equiv pred_Z.
Proof.
  simple refine (is_equiv_has_inverse _ _ _).
  - exact succ_Z.
  - exact is_retr_pred_Z.
  - exact is_sec_pred_Z.
Defined.

Definition pred_Z_equiv : Z <~> Z := pair pred_Z is_equiv_pred_Z.

(** Exercise 7.7 *)

Definition swap_coprod {A B} : coprod A B -> coprod B A.
Proof.
  intro x; destruct x.
  - now apply inr.
  - now apply inl.
Defined.

Definition swap_swap_coprod {A B} :
  comp (@swap_coprod A B) (@swap_coprod B A) ~ idmap.
Proof.
  intro x. now destruct x.
Defined.

Theorem is_equiv_swap_coprod {A B} : is_equiv (@swap_coprod A B).
Proof.
  apply (is_equiv_has_inverse swap_coprod); now apply swap_swap_coprod.
Defined.

Definition commutative_coprod A B : coprod A B <~> coprod B A :=
  pair swap_coprod is_equiv_swap_coprod.

Definition swap_prod {A B} : prod A B -> prod B A.
Proof.
  intro x; destruct x.
  now apply pair.
Defined.

Definition swap_swap_prod {A B} :
  comp (@swap_prod A B) (@swap_prod B A) ~ idmap.
Proof.
  intro x; destruct x.
  reflexivity.
Defined.

Theorem is_equiv_swap_prod {A B} : is_equiv (@swap_prod A B).
Proof.
  apply (is_equiv_has_inverse swap_prod); now apply swap_swap_prod.
Defined.

Definition commutative_prod A B : prod A B <~> prod B A :=
  pair swap_prod is_equiv_swap_prod.

(** Exercise 7.8 *)

Definition incl_sr_pair {A B} : sr_pair A B -> A -> B := pr1.

Definition retr_incl_sr_pair {A B} (R : sr_pair A B) :
  retr (incl_sr_pair R) := pr2 R.

Definition map_retr_incl_sr_pair {A B} (R : sr_pair A B) :
  B -> A := map_retr (retr_incl_sr_pair R).

Definition is_retr_map_retr_incl_sr_pair {A B} (R : sr_pair A B) :
  comp (map_retr_incl_sr_pair R) (incl_sr_pair R) ~ idmap :=
  is_retr_map_retr (retr_incl_sr_pair R).

Definition path_sr_pair {A B} (x y : A) (R : sr_pair A B) :
    (sr_pair (x == y) (incl_sr_pair R x == incl_sr_pair R y)).
Proof.
  simple refine (pair _ _).
  - exact (ap (incl_sr_pair R)).
  - simple refine (pair _ _).
    * intro q.
      { transitivity (comp (map_retr_incl_sr_pair R) (incl_sr_pair R) x).
        - apply inv. apply is_retr_map_retr_incl_sr_pair.
        - transitivity (map_retr_incl_sr_pair R (incl_sr_pair R y)).
          * exact (ap (map_retr_incl_sr_pair R) q).
          * apply is_retr_map_retr_incl_sr_pair.
      }
    * intro p; destruct p.
      apply left_inv.
Defined.

(** Exercise 7.13 *)

(** Exercise 7.13.a *)

Definition coprod_map {A B A' B'} (f : A -> A') (g : B -> B') :
  coprod A B -> coprod A' B'.
Proof.
  intro x; destruct x as [a|b].
  - exact (inl (f a)).
  - exact (inr (g b)).
Defined.

(** Exercise 7.13.b *)

Definition coprod_htpy {A B A' B'}
           {f f' : A -> A'} (H : f ~ f') {g g' : B -> B'} (K : g ~ g') :
  coprod_map f g ~ coprod_map f' g'.
Proof.
  intro x; destruct x as [a|b].
  - exact (ap inl (H a)).
  - exact (ap inr (K b)).
Defined.

(** Exercise 7.13.c *)

Definition coprod_idmap {A B} :
  coprod_map (@idmap A) (@idmap B) ~ idmap.
Proof.
  intro x; now destruct x as [a|b].
Defined.

(** Exercise 7.13.d *)

Definition coprod_comp {A B A' B' A'' B''}
           (f : A -> A') (f' : A' -> A'') (g : B -> B') (g' : B' -> B'') :
  coprod_map (comp f' f) (comp g' g) ~
             comp (coprod_map f' g') (coprod_map f g).
Proof.
  intro x; now destruct x as [a|b].
Defined.

(** Exercise 7.13.e *)

Definition inv_coprod_map_is_equiv {A B A' B'} {f : A -> A'} {g : B -> B'}
           (Ef : is_equiv f) (Eg : is_equiv g) :
  coprod A' B' -> coprod A B.
Proof.
  intro x; destruct x as [a|b].
  - exact (inl (inv_is_equiv Ef a)).
  - exact (inr (inv_is_equiv Eg b)).
Defined.

Definition is_sec_inv_coprod_map_is_equiv {A B A' B'} {f : A -> A'} {g : B -> B'}
           (Ef : is_equiv f) (Eg : is_equiv g) :
  comp (coprod_map f g) (inv_coprod_map_is_equiv Ef Eg) ~ idmap.
Proof.
  apply @concat_htpy with (coprod_map (@idmap A') (@idmap B')).
  - apply @concat_htpy
      with (coprod_map (comp f (inv_is_equiv Ef)) (comp g (inv_is_equiv Eg))).
    * apply inv_htpy.
      apply coprod_comp.
    * apply coprod_htpy.
      ** exact (is_sec_inv_is_equiv Ef).
      ** exact (is_sec_inv_is_equiv Eg).
  - apply coprod_idmap.
Defined.

Definition is_retr_inv_coprod_map_is_equiv {A B A' B'}
           {f : A -> A'} {g : B -> B'} (Ef : is_equiv f) (Eg : is_equiv g) :
  comp (inv_coprod_map_is_equiv Ef Eg) (coprod_map f g) ~ idmap.
Proof.
  apply @concat_htpy with (coprod_map (@idmap A) (@idmap B)).
  - apply @concat_htpy
      with (coprod_map (comp (inv_is_equiv Ef) f) (comp (inv_is_equiv Eg) g)).
    * apply inv_htpy.
      apply coprod_comp.
    * apply coprod_htpy.
      ** exact (is_retr_inv_is_equiv Ef).
      ** exact (is_retr_inv_is_equiv Eg).
  - apply coprod_idmap.
Defined.

Theorem is_equiv_coprod_map_is_equiv {A B A' B'}
        {f : A -> A'} {g : B -> B'} (Ef : is_equiv f) (Eg : is_equiv g) :
  is_equiv (coprod_map f g).
Proof.
  apply is_equiv_has_inverse with (inv_coprod_map_is_equiv Ef Eg).
  - exact (is_sec_inv_coprod_map_is_equiv Ef Eg).
  - exact (is_retr_inv_coprod_map_is_equiv Ef Eg).
Defined.

Definition coprod_equiv {A B A' B'} (f : A <~> A') (g : B <~> B') :
  coprod A B <~> coprod A' B' :=
  pair (coprod_map (map_equiv f) (map_equiv g)) (is_equiv_coprod_map_is_equiv (is_equiv_map_equiv f) (is_equiv_map_equiv g)).
