Require Export section_07_equivalences.

(** Section 8.1 Contractible types *)

(** Definition 8.1.1 *)

Definition is_contr (A : Type) : Type :=
  Sigma A (fun a => forall x, a == x).

Definition center {A : Type} : is_contr A -> A := pr1.

Definition contraction {A : Type} (c : is_contr A) :
  forall x, (center c) == x :=
  fun x => concat (inv (pr2 c (center c))) (pr2 c x).

Definition coh_contraction {A : Type} (c : is_contr A) :
  contraction c (center c) == refl :=
  left_inv (pr2 c (center c)).

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

Definition ind_sing_is_contr {A} (c : is_contr A) {B : A -> Type}
           (b : B (center c)) : forall x, B x :=
  fun x => tr B (contraction c x) b.

Definition comp_sing_is_contr {A} (c : is_contr A) {B : A -> Type}
           (b : B (center c)) :
  ev_pt (center c) (ind_sing_is_contr c b) == b :=
  ap (fun p => tr B p b) (coh_contraction c).

Theorem Ind_sing_is_contr {A} (c : is_contr A) : Ind_sing (center c).
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
