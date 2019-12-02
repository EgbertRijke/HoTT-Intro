Require Export section_07_equivalences.

(** Section 8.1 Contractible types *)

(** Definition 8.1.1 *)

Definition is_contr (A : Type) : Type :=
  Sigma A (fun a => forall x, a == x).

Definition center {A : Type} : is_contr A -> A := pr1.

Definition contraction' {A : Type} (c : is_contr A) (x y : A) : x == y :=
  concat (inv (pr2 c x)) (pr2 c y).

Definition contraction {A : Type} (c : is_contr A) :
  forall x, (center c) == x :=
  contraction' c (center c).

Definition coh_contraction {A : Type} (c : is_contr A) :
  contraction c (center c) == refl := left_inv.

(** Remark 8.1.3 *)

Definition contraction_unit : forall x, star == x.
Proof.
  intro x. now destruct x.
Defined.

Theorem is_contr_unit : is_contr unit.
Proof.
  exact (pair star contraction_unit).
Defined.

(** Definition 8.1.4 *)

Definition ev_pt {A} {B : A -> Type} (a : A) :
  (forall x, B x) -> B a :=
  fun h => h a.

Definition Ind_sing {A} (a : A) : Type :=
  forall (B : A -> Type), sec (@ev_pt A B a).

(** Remark 8.1.5 *)

Definition ind_sing_unit (B : unit -> Type) (b : B star) (x : unit) : B x.
Proof.
  now destruct x.
Defined.

Definition comp_sing_unit (B : unit -> Type) (b : B star) :
  ev_pt star (ind_sing_unit B b) == b.
Proof.
  reflexivity.
Defined.

Definition Ind_sing_unit : Ind_sing star.
Proof.
  intro B.
  apply (pair (ind_sing_unit B)).
  exact (comp_sing_unit B).
Defined.

(** Theorem 8.1.6 *)

Definition ind_sing_is_contr {A} {a : A} (c : is_contr A) {B : A -> Type}
           (b : B a) : forall x, B x :=
  fun x => tr B (contraction' c a x) b.

Definition comp_sing_is_contr {A} {a : A} (c : is_contr A) {B : A -> Type}
           (b : B a) :
  ev_pt a (ind_sing_is_contr c b) == b :=
  ap (fun p => tr B p b) left_inv.

Theorem Ind_sing_is_contr {A} (c : is_contr A) (a : A) : Ind_sing a.
Proof.
  intro B.
  exact (pair (ind_sing_is_contr c) (comp_sing_is_contr c)).
Defined.

Theorem is_contr_Ind_sing {A} (a : A) (H : Ind_sing a) : is_contr A.
Proof.
  apply (pair a).
  now apply (map_sec (H (fun x => a == x))).
Defined.

(** Theorem 8.1.7 *)

Definition total_path {A} (a : A) : Type :=
  Sigma A (fun x => a == x).

Definition pt_total_path {A} (a : A) : total_path a :=
  pair a refl.

Definition ev_refl {A} (a : A) {B : forall x, a == x -> Type} :
  (forall x p, B x p) -> B a refl :=
  fun h => h a refl.

Definition ind_sing_total_path {A} (a : A) {B : total_path a -> Type}
           (b : B (pt_total_path a)) :
  forall x, B x.
Proof.
  intro x.
  destruct x as [x p].
  now destruct p.
Defined.

Definition comp_sing_total_path {A} (a : A) {B : total_path a -> Type}
           (b : B (pt_total_path a)) :
  ev_pt (pt_total_path a) (ind_sing_total_path a b) == b := refl.

Definition Ind_sing_total_path {A} (a : A) :
  @Ind_sing (Sigma A (fun x => a == x)) (pair a refl).
Proof.
  intro B.
  apply (pair (ind_sing_total_path a)).
  exact (comp_sing_total_path a).
Defined.

Theorem is_contr_total_path {A} (a : A) : is_contr (total_path a).
Proof.
  apply (is_contr_Ind_sing (pt_total_path a)).
  exact (Ind_sing_total_path a).
Defined.

(** Section 8.2 Contractible maps *)

(** Definition 8.2.1 *)

Definition fib {A B} (f : A -> B) (b : B) : Type :=
  Sigma A (fun x => f x == b).

(** Definition 8.2.2 *)

Definition Eq_fib {A B} (f : A -> B) {b : B} (s t : fib f b) : Type :=
  Sigma (pr1 s == pr1 t) (fun p => pr2 s == concat (ap f p) (pr2 t)).

Definition refl_Eq_fib {A B} (f : A -> B) {b : B} (s : fib f b) :
  Eq_fib f s s := pair refl refl.

(** Lemma 8.2.3 *)

Definition Eq_fib_eq {A B} (f : A -> B) {b : B} {s t : fib f b} :
  s == t -> Eq_fib f s t.
Proof.
  intro p; destruct p.
  apply refl_Eq_fib.
Defined.

Definition eq_Eq_fib {A B} (f : A -> B) {b : B} {s t : fib f b} :
  Eq_fib f s t -> s == t.
Proof.
  induction s as [x p]; induction t as [y q].
  intro e; destruct e as [u v].
  cbn in u; induction u.
  cbn in v; now induction v.
Defined.

Definition is_sec_eq_Eq_fib {A B} (f : A -> B) {b : B} {s t : fib f b} :
  comp (@Eq_fib_eq _ _ f b s t) (eq_Eq_fib f) ~ idmap.
Proof.
  induction s as [x p]; induction t as [y q].
  intro e; destruct e as [u v].
  cbn in u; induction u.
  cbn in v; now induction v.
Defined.

Definition is_retr_eq_Eq_fib {A B} (f : A -> B) {b : B} {s t : fib f b} :
  comp (eq_Eq_fib f) (@Eq_fib_eq _ _ f b s t) ~ idmap.
Proof.
  intro p; destruct p; now destruct s.
Defined.

Theorem is_equiv_Eq_fib_eq {A B} (f : A -> B) {b : B} {s t : fib f b} :
  is_equiv (@Eq_fib_eq _ _ f b s t).
Proof.
  apply (is_equiv_has_inverse (eq_Eq_fib f)).
  - exact (is_sec_eq_Eq_fib f).
  - exact (is_retr_eq_Eq_fib f).
Defined.

Theorem is_equiv_eq_Eq_fib {A B} (f : A -> B) {b : B} {s t : fib f b} :
  is_equiv (@eq_Eq_fib _ _ f b s t).
Proof.
  apply (is_equiv_has_inverse (Eq_fib_eq f)).
  - exact (is_retr_eq_Eq_fib f).
  - exact (is_sec_eq_Eq_fib f).
Defined.

(** Definition 8.2.4 *)

Definition is_contr_map {A B} (f : A -> B) : Type :=
  forall b, is_contr (fib f b).

(** Theorem 8.2.5 *)

Definition inv_is_contr_map {A B} {f : A -> B} (c : is_contr_map f) :
  B -> A.
Proof.
  intro b.
  exact (pr1 (center (c b))).
Defined.

Definition is_sec_inv_is_contr_map {A B} {f : A -> B} (c : is_contr_map f) :
  comp f (inv_is_contr_map c) ~ idmap.
Proof.
  intro b.
  exact (pr2 (center (c b))).
Defined.

(** Sometimes Coq pretends it cannot apply a tactic, while it should certainly
    accept my steps. This is one of those cases, where it is easier to just
    write out the proof term than to convince Coq of some sequence of tactics. *)

Definition is_retr_inv_is_contr_map {A B} {f : A -> B} (c : is_contr_map f) :
  comp (inv_is_contr_map c) f ~ idmap.
Proof.
  intro a.
  set (g := inv_is_contr_map c).
  assert (p : f (g (f a)) == f a) by apply is_sec_inv_is_contr_map.
  assert (q : pair (g (f a)) p == pair a refl) by apply (contraction' (c (f a))).
  exact (ap pr1 q).
Defined.

Theorem is_equiv_is_contr_map {A B} {f : A -> B} :
  is_contr_map f -> is_equiv f.
Proof.
  intro is_contr_f.
  apply (is_equiv_has_inverse (inv_is_contr_map is_contr_f)).
  - apply is_sec_inv_is_contr_map.
  - apply is_retr_inv_is_contr_map.
Defined.

(** Section 8.3 Equivalences are contractible maps *)

(** Definition 8.3.1 *)

Definition is_coh_invertible {A B} (f : A -> B) : Type :=
  Sigma
    (B -> A)
    (fun g => Sigma
                (comp f g ~ idmap)
                (fun G => Sigma
                            (comp g f ~ idmap)
                            (fun H =>
                               right_whisker_htpy G f ~
                                                  left_whisker_htpy f H))).

Definition inv_is_coh_invertible {A B} {f : A -> B} :
  is_coh_invertible f -> B -> A := pr1.

Definition is_sec_inv_is_coh_invertible {A B} {f : A -> B}
           (I : is_coh_invertible f) :
  comp f (inv_is_coh_invertible I) ~ idmap := pr1 (pr2 I).

Definition is_retr_inv_is_coh_invertible {A B} {f : A -> B}
           (I : is_coh_invertible f) :
  comp (inv_is_coh_invertible I) f ~ idmap := pr1 (pr2 (pr2 I)).

Definition coh_inv_is_coh_invertible {A B} {f : A -> B}
           (I : is_coh_invertible f) :
  right_whisker_htpy (is_sec_inv_is_coh_invertible I) f ~
                     left_whisker_htpy f (is_retr_inv_is_coh_invertible I) :=
  pr2 (pr2 (pr2 I)).

(** Lemma 8.3.2 *)

Definition center_fib_is_coh_invertible {A B} {f : A -> B}
           (I : is_coh_invertible f) (b : B) : fib f b :=
  pair (inv_is_coh_invertible I b) (is_sec_inv_is_coh_invertible I b).

Definition contraction_fib_is_coh_invertible {A B} {f : A -> B}
           (I : is_coh_invertible f) (b : B) (x : fib f b) :
  center_fib_is_coh_invertible I b == x.
Proof.
  apply (eq_Eq_fib f).
  destruct x as [x p]; destruct p.
  apply (pair (is_retr_inv_is_coh_invertible I x)).
  transitivity (ap f (is_retr_inv_is_coh_invertible I x)).
  - apply (coh_inv_is_coh_invertible I).
  - apply inv; apply right_unit.
Defined.

Theorem is_contr_map_is_coh_invertible {A B} {f : A -> B} :
  is_coh_invertible f -> is_contr_map f.
Proof.
  intros I b.
  apply (pair (center_fib_is_coh_invertible I b)).
  exact (contraction_fib_is_coh_invertible I b).
Defined.
  
(** Definition 8.3.3 *)

Definition nat_htpy {A B} {f g : A -> B} (H : f ~ g) {x y : A} (p : x == y) :
  concat (ap f p) (H y) == concat (H x) (ap g p).
Proof.
  destruct p.
  apply inv; apply right_unit.
Defined.

(** Definition 8.3.4 *)

Definition left_unwhisk {A} {x y z : A} (p : x == y) {q r : y == z} :
  concat p q == concat p r -> q == r.
Proof.
  now destruct p.
Defined.

Definition right_unwhisk {A} {x y z : A} {p q : x == y} (r : y == z) :
  concat p r == concat q r -> p == q.
Proof.
  destruct r.
  intro s.
  exact (concat (inv right_unit) (concat s right_unit)).
Defined.

Definition reduce_htpy {A} {f : A -> A} {H : f ~ idmap} {x : A} :
  ap f (H x) == H (f x).
Proof.
  apply (right_unwhisk (H x)).
  transitivity (concat (H (f x)) (ap idmap (H x))).
  apply nat_htpy.
  apply (ap (concat (H (f x)))).
  apply inv. apply ap_id.
Defined.

(** Lemma 8.3.5 *)

Definition mod_is_sec_inv_has_inverse {A B} {f : A -> B} (I : has_inverse f) :
  comp f (inv_has_inverse I) ~ idmap.
Proof.
  intro y.
  transitivity (f (inv_has_inverse I (f (inv_has_inverse I y)))).
  - apply inv.
    exact (is_sec_inv_has_inverse I (f (inv_has_inverse I y))).
  - transitivity (f (inv_has_inverse I y)).
    * exact (ap f (is_retr_inv_has_inverse I (inv_has_inverse I y))).
    * exact (is_sec_inv_has_inverse I y).
Defined.

Definition coh_inv_has_inverse {A B} {f : A -> B} (I : has_inverse f) :
  right_whisker_htpy (mod_is_sec_inv_has_inverse I) f ~
                     left_whisker_htpy f (is_retr_inv_has_inverse I).
Proof.
  intro x.
  apply inv; apply inv_con; apply inv.
  transitivity (concat (ap (comp f (comp (inv_has_inverse I) f)) (is_retr_inv_has_inverse I x)) (is_sec_inv_has_inverse I (f x))).
  - apply (ap (concat' (is_sec_inv_has_inverse I (f x)))).
    transitivity (ap f (ap (comp (inv_has_inverse I) f) (is_retr_inv_has_inverse I x))).
    * apply (ap (ap f)).
      apply inv. exact reduce_htpy.
    * apply ap_comp.
  - apply (nat_htpy (right_whisker_htpy (is_sec_inv_has_inverse I) f)).
Defined.

Lemma is_coh_invertible_has_inverse {A B} {f : A -> B} :
  has_inverse f -> is_coh_invertible f.
Proof.
  intro I.
  apply (pair (inv_has_inverse I)).
  apply (pair (mod_is_sec_inv_has_inverse I)).
  apply (pair (is_retr_inv_has_inverse I)).
  exact (coh_inv_has_inverse I).
Defined.

(** Theorem 8.3.6 *)

Lemma is_contr_map_has_inverse {A B} {f : A -> B} :
  has_inverse f -> is_contr_map f.
Proof.
  intro I.
  apply is_contr_map_is_coh_invertible.
  now apply is_coh_invertible_has_inverse.
Defined.

Theorem is_contr_map_is_equiv {A B} {f : A -> B} : is_equiv f -> is_contr_map f.
Proof.
  intro is_equiv_f.
  apply is_contr_map_has_inverse.
  now apply has_inverse_is_equiv.
Defined.

(** Corollary 8.3.7 *)

Definition total_path' {A} (a : A) : Type :=
  Sigma A (fun x => x == a).

Lemma is_contr_map_idmap {A} : is_contr_map (@idmap A).
Proof.
  apply is_contr_map_is_equiv.
  exact is_equiv_idmap.
Defined.

Definition is_contr_total_path' {A} (a : A) : is_contr (total_path' a) :=
  is_contr_map_idmap a.

(** Exercises *)

(** Exercise 8.1 *)

Definition is_prop_is_contr {A} (c : is_contr A) {x y : A} : is_contr (x == y).
Proof.
  apply (pair (contraction' c x y)).
  intro p; destruct p.
  apply left_inv.
Defined.

(** Exercise 8.2 *)

Definition is_contr_retract {A B} (R : sr_pair A B) :
  is_contr B -> is_contr A.
Proof.
  destruct R as [i [r H]].
  intro is_contr_B; destruct is_contr_B as [b c].
  apply (pair (r b)).
  intro x.
  transitivity (r (i x)).
  - now apply (ap r).
  - now apply H.
Defined.

(** Exercise 8.3 *)

(** Exercise 8.3.a *)

Definition sr_pair_is_equiv {A B} {f : A -> B} :
  is_equiv f -> sr_pair A B.
Proof.
  intro H.
  exact (pair f (retr_is_equiv H)).
Defined.

Definition is_contr_is_equiv_const_star {A} :
  is_equiv (@const A unit star) -> is_contr A.
Proof.
  intro H.
  apply (is_contr_retract (sr_pair_is_equiv H)).
  exact is_contr_unit.
Defined.

Definition is_equiv_const_star_is_contr {A} :
  is_contr A -> is_equiv (@const A unit star).
Proof.
  intro c.
  apply (is_equiv_has_inverse (const (center c))).
  exact (contraction is_contr_unit).
  exact (contraction c).
Defined.

(** Exercise 8.3.b *)

Definition is_contr_is_equiv {A B} {f : A -> B} :
  is_equiv f -> is_contr B -> is_contr A.
Proof.
  intro H.
  apply is_contr_retract.
  apply (sr_pair_is_equiv H).
Defined.

Definition is_contr_equiv {A B} (e : A <~> B) :
  is_contr B -> is_contr A :=
  is_contr_is_equiv (is_equiv_map_equiv e).

Definition is_contr_is_equiv' {A B} {f : A -> B} :
  is_equiv f -> is_contr A -> is_contr B.
Proof.
  intro H.
  exact (is_contr_is_equiv (is_equiv_inv_is_equiv H)).
Defined.

Definition is_contr_equiv' {A B} (e : A <~> B) :
  is_contr A -> is_contr B :=
  is_contr_is_equiv' (is_equiv_map_equiv e).

Definition is_equiv_is_contr {A B} (f : A -> B) :
  is_contr A -> is_contr B -> is_equiv f.
Proof.
  intros CA CB.
  apply (@is_equiv_right_factor A B unit
                                (@const A unit star)
                                (@const B unit star)
                                (pair f (@refl_htpy _ _ (@const A unit star)))).
  - now apply is_equiv_const_star_is_contr.
  - now apply is_equiv_const_star_is_contr.
Defined.
