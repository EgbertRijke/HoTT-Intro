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
  comp (inv_is_contr_map c) f ~ idmap :=
  fun a =>
    ap pr1
       (contraction' (c (f a))
                     (pair (inv_is_contr_map c (f a))
                           (is_sec_inv_is_contr_map c (f a)))
                     (pair a refl)).

Theorem is_equiv_is_contr_map {A B} {f : A -> B} :
  is_contr_map f -> is_equiv f.
Proof.
  intro is_contr_f.
  apply (is_equiv_has_inverse (inv_is_contr_map is_contr_f)).
  - apply is_sec_inv_is_contr_map.
  - apply is_retr_inv_is_contr_map.
Defined.
    
