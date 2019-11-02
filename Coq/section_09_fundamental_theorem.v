Require Export section_08_contractible.

(** Section 9.1 Families of equivalences *)

(** Definition 9.1.1 *)

Definition tot {A} {B C : A -> Type} (f : forall x, B x -> C x) :
  Sigma A B -> Sigma A C :=
  fun t => pair (pr1 t) (f (pr1 t) (pr2 t)).

(** Lemma 9.1.2 *)

Definition fib_tot_fib_fmap {A} {B C : A -> Type} (f : forall x, B x -> C x)
           (t : Sigma A C) :
  fib (f (pr1 t)) (pr2 t) -> fib (tot f) t.
Proof.
  destruct t as [x z]; cbn.
  intro y; destruct y as [y p]; destruct p.
  exact (pair (pair x y) refl).
Defined.

Definition fib_fmap_fib_tot {A} {B C : A -> Type} (f : forall x, B x -> C x)
           (t : Sigma A C) :
  fib (tot f) t -> fib (f (pr1 t)) (pr2 t).
Proof.
  intro s; destruct s as [s p]; destruct p; destruct s as [x y].
  exact (pair y refl).
Defined.

Definition is_sec_fib_fmap_fib_tot {A} {B C : A -> Type}
           (f : forall x, B x -> C x) (t : Sigma A C) :
  comp (fib_tot_fib_fmap f t) (fib_fmap_fib_tot f t) ~ idmap.
Proof.
  intro s; destruct s as [s p]; destruct p; now destruct s as [x y].
Defined.

Definition is_retr_fib_fmap_fib_tot {A} {B C : A -> Type}
           (f : forall x, B x -> C x) (t : Sigma A C) :
  comp (fib_fmap_fib_tot f t) (fib_tot_fib_fmap f t) ~ idmap.
Proof.
  destruct t as [x z]; cbn.
  intro y; destruct y as [y p]; destruct p.
  reflexivity.
Defined.

Lemma is_equiv_fib_tot_fib_fmap {A} {B C : A -> Type}
      (f : forall x, B x -> C x) (t : Sigma A C) :
  is_equiv (fib_tot_fib_fmap f t).
Proof.
  apply (is_equiv_has_inverse (fib_fmap_fib_tot f t)).
  - exact (is_sec_fib_fmap_fib_tot f t).
  - exact (is_retr_fib_fmap_fib_tot f t).
Defined.

Definition fib_tot_fib_fmap_equiv {A} {B C : A -> Type}
           (f : forall x, B x -> C x) (t : Sigma A C) :
  (fib (f (pr1 t)) (pr2 t)) <~> (fib (tot f) t) :=
  pair (fib_tot_fib_fmap f t) (is_equiv_fib_tot_fib_fmap f t).

Lemma is_equiv_fib_fmap_fib_tot {A} {B C : A -> Type}
      (f : forall x, B x -> C x) (t : Sigma A C) :
  is_equiv (fib_fmap_fib_tot f t).
Proof.
  apply (is_equiv_has_inverse (fib_tot_fib_fmap f t)).
  - exact (is_retr_fib_fmap_fib_tot f t).
  - exact (is_sec_fib_fmap_fib_tot f t).
Defined.

Definition fib_fmap_fib_tot_equiv {A} {B C : A -> Type}
           (f : forall x, B x -> C x) (t : Sigma A C) :
  (fib (tot f) t) <~> (fib (f (pr1 t)) (pr2 t)) :=
  pair (fib_fmap_fib_tot f t) (is_equiv_fib_fmap_fib_tot f t).

(** Theorem 9.1.3 *)

Theorem is_equiv_is_equiv_tot {A} {B C : A -> Type} (f : forall x, B x -> C x) :
  is_equiv (tot f) -> forall x, is_equiv (f x).
Proof.
  intros H x.
  apply is_equiv_is_contr_map.
  intro z.
  apply (is_contr_equiv (fib_tot_fib_fmap_equiv f (pair x z))).
  now apply is_contr_map_is_equiv.
Defined.

Theorem is_equiv_tot_is_equiv {A} {B C : A -> Type} (f : forall x, B x -> C x) :
  (forall x, is_equiv (f x)) -> is_equiv (tot f).
Proof.
  intro H.
  apply is_equiv_is_contr_map.
  intro t; destruct t as [x z].
  apply (is_contr_equiv (fib_fmap_fib_tot_equiv f (pair x z))); cbn.
  now apply is_contr_map_is_equiv.
Defined.

(** Lemma 9.1.4 *)

Definition btot {A B} (f : A -> B) (C : B -> Type) :
  Sigma A (fun x => C (f x)) -> Sigma B C :=
  fun t => pair (f (pr1 t)) (pr2 t).

Definition fib_map_fib_btot {A B} (f : A -> B) (C : B -> Type) (t : Sigma B C) :
  fib (btot f C) t -> fib f (pr1 t).
Proof.
  intro s; destruct s as [s p]; destruct p; destruct s as [x z]; cbn.
  exact (pair x refl).
Defined.

Definition fib_btot_fib_map {A B} (f : A -> B) (C : B -> Type) (t : Sigma B C) :
  fib f (pr1 t) -> fib (btot f C) t.
Proof.
  destruct t as [y z]; cbn.
  intro s; destruct s as [x p]; destruct p.
  now apply (pair (pair x z)).
Defined.

Definition is_sec_fib_btot_fib_map
           {A B} (f : A -> B) (C : B -> Type) (t : Sigma B C) :
  comp (fib_map_fib_btot f C t) (fib_btot_fib_map f C t) ~ idmap.
Proof.
  destruct t as [y z]; cbn.
  intro s; destruct s as [x p]; destruct p.
  reflexivity.
Defined.

Definition is_retr_fib_btot_fib_map
           {A B} (f : A -> B) (C : B -> Type) (t : Sigma B C) :
  comp (fib_btot_fib_map f C t) (fib_map_fib_btot f C t) ~ idmap.
Proof.
  intro s; destruct s as [s p]; destruct p; destruct s as [x z]; cbn.
  reflexivity.
Defined.
