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
           (H : f ~ g) :
  concat_htpy refl_htpy H ~ H.
Proof.
  intro x.
  exact (left_unit (H x)).
Defined.

Definition right_unit_htpy {A} {B : A -> Type} {f g : forall x, B x}
           (H : f ~ g) :
  concat_htpy H refl_htpy ~ H.
Proof.
  intro x.
  exact (right_unit (H x)).
Defined.

Definition left_inv_htpy {A} {B : A -> Type} {f g : forall x, B x}
           (H : f ~ g) :
  concat_htpy (inv_htpy H) H ~ refl_htpy.
Proof.
  intro x.
  exact (left_inv (H x)).
Defined.

Definition right_inv_htpy {A} {B : A -> Type} {f g : forall x, B x}
           (H : f ~ g) :
  concat_htpy H (inv_htpy H) ~ refl_htpy.
Proof.
  intro x.
  exact (right_inv (H x)).
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

Definition htpy_sec {A B} {f : A -> B} (s : sec f) :
  comp f (map_sec s) ~ idmap := pr2 s.

Definition retr {A B} (f : A -> B) : Type :=
  Sigma (B -> A) (fun h => comp h f ~ idmap).

Definition map_retr {A B} {f : A -> B} (r : retr f) : B -> A := pr1 r.

Definition htpy_retr {A B} {f : A -> B} (r : retr f) :
  comp (map_retr r) f ~ idmap := pr2 r.

Definition is_equiv {A B} (f : A -> B) : Type :=
  prod (sec f) (retr f).

Definition equiv (A B : Type) : Type := Sigma (A -> B) is_equiv.

Notation "A '<~>' B" := (equiv A B) (at level 70).

Definition map_equiv {A B} (e : A <~> B) : A -> B := pr1 e.

Definition is_equiv_equiv_map_equiv {A B} (e : A <~> B) :
  is_equiv (map_equiv e) := pr2 e.

(** Remark 7.2.2 *)

Definition has_inverse {A B} (f : A -> B) : Type :=
  Sigma (B -> A) (fun g => prod (comp f g ~ idmap) (comp g f ~ idmap)).

Definition is_equiv_has_inverse {A B} {f : A -> B} (g : B -> A) (G : comp f g ~ idmap) (H : comp g f ~ idmap) : is_equiv f.
Proof.
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
  comp f (inv_is_equiv H) ~ idmap := htpy_sec (sec_is_equiv H).

Definition retr_is_equiv {A B} {f : A -> B} (H : is_equiv f) : retr f := pr2 H.

Definition map_retr_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  B -> A := map_retr (retr_is_equiv H).

Definition htpy_retr_is_equiv {A B} {f : A -> B} (H : is_equiv f) :
  comp (map_retr_is_equiv H) f ~ idmap := htpy_retr (retr_is_equiv H).

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

(** Remark 7.2.5 *)

Definition is_equiv_idmap {A} : is_equiv (@idmap A).
Proof.
  apply (is_equiv_has_inverse idmap); exact refl_htpy.
Defined.

(** Example 7.2.6 *)

Definition is_equiv_swap_Pi {A B} (C : A -> B -> Type) :
  is_equiv (@swap_Pi A B C).
Proof.
  apply (is_equiv_has_inverse (@swap_Pi B A (fun y x => C x y)));
    exact refl_htpy.
Defined.

(** Section 7.3. The identity type of a Sigma-type *)
