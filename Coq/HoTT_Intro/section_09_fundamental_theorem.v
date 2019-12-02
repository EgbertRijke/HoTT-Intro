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

Theorem is_equiv_tot_is_equiv {A} {B C : A -> Type} {f : forall x, B x -> C x} :
  (forall x, is_equiv (f x)) -> is_equiv (tot f).
Proof.
  intro H.
  apply is_equiv_is_contr_map.
  intro t; destruct t as [x z].
  apply (is_contr_equiv (fib_fmap_fib_tot_equiv f (pair x z))); cbn.
  now apply is_contr_map_is_equiv.
Defined.

Definition tot_equiv {A} {B C : A -> Type} :
  (forall x, (B x <~> C x)) -> ((Sigma A B) <~> (Sigma A C)) :=
  fun e =>
    pair
      (tot (fun x => map_equiv (e x)))
      (is_equiv_tot_is_equiv (fun x => is_equiv_map_equiv (e x))).

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

Lemma is_equiv_fib_map_fib_btot
      {A B} (f : A -> B) (C : B -> Type) (t : Sigma B C) :
  is_equiv (fib_map_fib_btot f C t).
Proof.
  apply (is_equiv_has_inverse (fib_btot_fib_map f C t)).
  - exact (is_sec_fib_btot_fib_map f C t).
  - exact (is_retr_fib_btot_fib_map f C t).
Defined.

Definition fib_map_fib_btot_equiv
           {A B} (f : A -> B) (C : B -> Type) (t : Sigma B C) :
  fib (btot f C) t <~> fib f (pr1 t) :=
  pair (fib_map_fib_btot f C t) (is_equiv_fib_map_fib_btot f C t).

Lemma is_equiv_fib_btot_fib_map
      {A B} (f : A -> B) (C : B -> Type) (t : Sigma B C) :
  is_equiv (fib_btot_fib_map f C t).
Proof.
  apply (is_equiv_has_inverse (fib_map_fib_btot f C t)).
  - exact (is_retr_fib_btot_fib_map f C t).
  - exact (is_sec_fib_btot_fib_map f C t).
Defined.

Definition fib_btot_fib_map_equiv
           {A B} (f : A -> B) (C : B -> Type) (t : Sigma B C) :
  fib f (pr1 t) <~> fib (btot f C) t :=
  pair (fib_btot_fib_map f C t) (is_equiv_fib_btot_fib_map f C t).

Lemma is_equiv_btot_is_equiv {A B} {f : A -> B} (C : B -> Type) :
  is_equiv f -> is_equiv (btot f C).
Proof.
  intro H.
  apply is_equiv_is_contr_map.
  intro t; destruct t as [x z].
  apply (is_contr_equiv (fib_map_fib_btot_equiv f C (pair x z))); cbn.
  now apply is_contr_map_is_equiv.
Defined.

Definition btot_equiv {A B} (e : A <~> B) (C : B -> Type) :
  Sigma A (comp C (map_equiv e)) <~> Sigma B C :=
  pair (btot (map_equiv e) C) (is_equiv_btot_is_equiv C (is_equiv_map_equiv e)).

(** Definition 9.1.5 *)

Definition toto {A B} (f : A -> B) {C : A -> Type} (D : B -> Type) :
  (forall x, C x -> D (f x)) -> Sigma A C -> Sigma B D :=
  fun g t => pair (f (pr1 t)) (g (pr1 t) (pr2 t)).

(** Theorem 9.1.6 *)

Definition triangle_toto {A B} (f : A -> B)
           {C : A -> Type} (D : B -> Type) (g : forall x, C x -> D (f x)) :
  toto f D g ~ comp (btot f D) (tot g).
Proof.
  exact refl_htpy.
Defined.

(** Tactics were again too annoying, but the proof term is easy to write down. 
 *)

Definition is_equiv_toto_is_equiv {A B} {f : A -> B}
        {C : A -> Type} (D : B -> Type) {g : forall x, C x -> D (f x)} :
  is_equiv f -> (forall x, is_equiv (g x)) -> is_equiv (toto f D g) :=
  fun Ef Eg =>
    @is_equiv_comp _ _ _
                   (toto f D g)
                   (btot f D)
                   (pair (tot g) (triangle_toto f D g))
                   (is_equiv_tot_is_equiv Eg)
                   (is_equiv_btot_is_equiv D Ef).

Definition equiv_toto {A B} (e : A <~> B) {C : A -> Type} (D : B -> Type)
           (g : forall x, (C x <~> D (map_equiv e x))) :
  Sigma A C <~> Sigma B D :=
  pair (toto (map_equiv e) D (fun x => map_equiv (g x)))
       (is_equiv_toto_is_equiv D (is_equiv_map_equiv e)
                                 (fun x => is_equiv_map_equiv (g x))).

Definition is_equiv_is_equiv_toto {A B} {f : A -> B}
        {C : A -> Type} (D : B -> Type) {g : forall x, C x -> D (f x)} :
  is_equiv f -> is_equiv (toto f D g) -> (forall x, is_equiv (g x)) :=
  fun Ef Efg =>
    is_equiv_is_equiv_tot g
      (@is_equiv_right_factor _ _ _
                              (toto f D g)
                              (btot f D)
                              (pair (tot g) (triangle_toto f D g))
                              Efg
                              (is_equiv_btot_is_equiv D Ef)).

(** Section 9.2 The fundamental theorem *)

(** Definition 9.2.1 *)

(** We define a generalized ev_refl *)
Definition ev_refl_gen {A} (a : A) {B : A -> Type} (b : B a)
           (C : forall x, B x -> Type) : (forall x y, C x y) -> C a b :=
  fun h => h a b.

(* We also say that a family B over A with b : B a is an identity system if
   it satisfies the following path induction principle. *)

Definition Ind_path {A} {a : A} (B : A -> Type) (b : B a) : Type :=
  forall (C : forall x, B x -> Type), sec (ev_refl_gen a b C).

Definition Identity_System {A} (a : A) : Type :=
  Sigma (A -> Type) (fun B => Sigma (B a) (fun b => Ind_path B b)).

(** Theorem 9.2.3 The fundamental theorem of identity types *)

Theorem fundamental_thm_id {A} {a : A} {B : A -> Type} (b : B a)
        (f : forall x, a == x -> B x) :
  is_contr (Sigma A B) -> forall x, is_equiv (f x).
Proof.
  intro c.
  apply is_equiv_is_equiv_tot.
  apply is_equiv_is_contr.
  - apply is_contr_total_path.
  - assumption.
Defined.

Theorem fundamental_thm_id' {A} {a : A} (B : A -> Type) (b : B a) :
  is_contr (Sigma A B) -> forall x, is_equiv (fun (p : a == x) => tr B p b).
Proof.
  now apply fundamental_thm_id.
Defined.

Theorem conv_fundamental_thm_id {A} {a : A} {B : A -> Type} (b : B a)
        (f : forall x, a == x -> B x) :
  (forall x, is_equiv (f x)) -> is_contr (Sigma A B).
Proof.
  intro H.
  apply (is_contr_is_equiv' (is_equiv_tot_is_equiv H)).
  apply is_contr_total_path.
Defined.

Definition fam_Sigma {A} {B : A -> Type} (C : forall x, B x -> Type) :
  Sigma A B -> Type :=
  fun t =>
    match t with
    | pair x y => C x y
    end.

Definition ev_pair {A} {B : A -> Type} (C : Sigma A B -> Type) :
  (forall (t : Sigma A B), C t) -> (forall x y, C (pair x y)) :=
  fun h x y => h (pair x y).

Definition inv_ev_pair {A} {B : A -> Type} (C : Sigma A B -> Type) :
  (forall x y, C (pair x y)) -> (forall (t : Sigma A B), C t).
Proof.
  intros h t; destruct t as [x y].
  exact (h x y).
Defined.

Definition is_sec_inv_ev_pair {A} {B : A -> Type} (C : Sigma A B -> Type) :
  comp (ev_pair C) (inv_ev_pair C) ~ idmap := refl_htpy.

Definition sec_ev_pair {A} {B : A -> Type} (C : Sigma A B -> Type) :
  sec (ev_pair C) :=
  pair (inv_ev_pair C) (is_sec_inv_ev_pair C).

Definition triangle_path_ind
           {A} {a : A} {B : A -> Type} (b : B a) (C : Sigma A B -> Type) :
  @ev_pt (Sigma A B) C (pair a b) ~
         comp (ev_refl_gen a b (fun x y => C (pair x y))) (ev_pair C) :=
  refl_htpy.

Definition hom_slice_path_ind
           {A} {a : A} {B : A -> Type} (b : B a) (C : Sigma A B -> Type) :
  hom_slice (ev_pt (pair a b)) (ev_refl_gen a b (fun x y => C (pair x y))) :=
  pair (ev_pair C) (triangle_path_ind b C).

Theorem Ind_path_is_contr_total
        {A} {a : A} {B : A -> Type} (b : B a) (C : forall x, B x -> Type) :
  is_contr (Sigma A B) -> sec (ev_refl_gen a b C).
Proof.
  intro c.
  apply section_comp with (hom_slice_path_ind b (fam_Sigma C)).
  - exact (sec_ev_pair (fam_Sigma C)).
  - exact (Ind_sing_is_contr c (pair a b) (fam_Sigma C)).
Defined.

Definition ind_path_is_contr_total
           {A} {a : A} {B : A -> Type} (b : B a) (C : forall x, B x -> Type) :
  is_contr (Sigma A B) -> C a b -> forall x y, C x y :=
  fun is_contr_AB => pr1 (Ind_path_is_contr_total b C is_contr_AB).

Definition comp_path_is_contr_total
           {A} {a : A} {B : A -> Type} (b : B a) (C : forall x, B x -> Type)
           (is_contr_AB : is_contr (Sigma A B)) (c : C a b) :
  ind_path_is_contr_total b C is_contr_AB c a b == c :=
  pr2 (Ind_path_is_contr_total b C is_contr_AB) c.

Theorem is_contr_total_Ind_path
        {A} {a : A} {B : A -> Type} (b : B a) :
  Ind_path B b -> is_contr (Sigma A B).
Proof.
  intro P.
  apply (is_contr_Ind_sing (pair a b)).
  intro C.
  apply section_comp' with (hom_slice_path_ind b C).
  exact (sec_ev_pair C).
  exact (P (fun x y => C (pair x y))).
Defined.

(** Section 9.3 Embeddings *)

(** Definition 9.3.1 *)

Definition is_emb {A B} (f : A -> B) : Type :=
  forall x y, is_equiv (@ap A B f x y).

(** Theorem 9.3.2 *)

Definition fib' {A B} (f : A -> B) (b : B) : Type :=
  Sigma A (fun x => b == f x).

Definition fib_fib_equiv {A B} (f : A -> B) (b : B) :
  fib' f b <~> fib f b :=
  tot_equiv (fun x => @invmap_equiv B b (f x)).

Theorem is_emb_is_equiv {A B} (f : A -> B) :
  is_equiv f -> is_emb f.
Proof.
  intros H x.
  apply fundamental_thm_id.
  - reflexivity.
  - apply (is_contr_equiv (fib_fib_equiv f (f x))).
    now apply is_contr_map_is_equiv.
Defined.

(** Section 9.4 Disjointness of coproducts *)

(** Theorem 9.4.1 *)

(** This theorem is stated at the beginning of the section, and proven at the
    end. *)

(** Definition 9.4.2 *)

Definition Eq_coprod {A B} (x y : coprod A B) : Type.
Proof.
  destruct x as [a|b].
  - destruct y as [a'|b'].
    * exact (a == a').
    * exact empty.
  - destruct y as [a'|b'].
    * exact empty.
    * exact (b == b').
Defined.

(** Lemma 9.4.3 *)

Lemma refl_Eq_coprod {A B} (x : coprod A B) : Eq_coprod x x.
Proof.
  now destruct x.
Defined.

Definition Eq_coprod_eq {A B} {x y : coprod A B} (p : x == y) : Eq_coprod x y.
Proof.
  destruct p. apply refl_Eq_coprod.
Defined.

(** Lemma 9.4.4 *)

(** We show that Sigma distributes over coproducts *)

Definition map_distr_Sigma_coprod {A B} (P : coprod A B -> Type) :
  Sigma (coprod A B) P ->
  coprod (Sigma A (comp P inl)) (Sigma B (comp P inr)).
Proof.
  intro t; destruct t as [[a | b] y].
  - exact (inl (pair a y)).
  - exact (inr (pair b y)).
Defined.

Definition inv_map_distr_Sigma_coprod {A B} (P : coprod A B -> Type) :
  coprod (Sigma A (comp P inl)) (Sigma B (comp P inr)) ->
  Sigma (coprod A B) P.
Proof.
  intro x; destruct x as [[a p]|[b p]].
  - exact (pair (inl a) p).
  - exact (pair (inr b) p).
Defined.

Definition is_sec_inv_map_distr_Sigma_coprod {A B} (P : coprod A B -> Type) :
  comp (map_distr_Sigma_coprod P) (inv_map_distr_Sigma_coprod P) ~ idmap.
Proof.
    intro x; now destruct x as [[a p]|[b p]].
Defined.

Definition is_retr_inv_map_distr_Sigma_coprod {A B} (P : coprod A B -> Type) :
  comp (inv_map_distr_Sigma_coprod P) (map_distr_Sigma_coprod P) ~ idmap.
Proof.
  intro t; now destruct t as [[a | b] y].
Defined.

Lemma is_equiv_map_distr_Sigma_coprod {A B} (P : coprod A B -> Type) :
  is_equiv (map_distr_Sigma_coprod P).
Proof.
  simple refine (is_equiv_has_inverse _ _ _).
  - exact (inv_map_distr_Sigma_coprod P).
  - exact (is_sec_inv_map_distr_Sigma_coprod P).
  - exact (is_retr_inv_map_distr_Sigma_coprod P).
Defined.
  
Definition distr_Sigma_coprod {A B} (P : coprod A B -> Type) :
  Sigma (coprod A B) P
        <~>
        coprod (Sigma A (comp P inl)) (Sigma B (comp P inr)) :=
  pair (map_distr_Sigma_coprod P) (is_equiv_map_distr_Sigma_coprod P).

Lemma is_contr_total_Eq_coprod_inl {A B} (x : A) :
  is_contr (Sigma (coprod A B) (Eq_coprod (inl x))).
Proof.
  apply (is_contr_equiv (distr_Sigma_coprod (Eq_coprod (inl x)))).
  simple refine (is_contr_equiv _ _).
  - exact (coprod (total_path x) empty).
  - refine (coprod_equiv _ _).
    * exact id_equiv.
    * exact right_zero_law_prod.
  - simple refine (is_contr_equiv' _ _).
    * exact (total_path x).
    * exact right_unit_law_coprod.
    * apply is_contr_total_path.
Defined.

Lemma is_contr_total_Eq_coprod_inr {A B} (y : B) :
  is_contr (Sigma (coprod A B) (Eq_coprod (inr y))).
Proof.
  apply (is_contr_equiv (distr_Sigma_coprod (Eq_coprod (inr y)))).
  simple refine (is_contr_equiv _ _).
  - exact (coprod empty (total_path y)).
  - refine (coprod_equiv _ _).
    * exact right_zero_law_prod.
    * exact id_equiv.
  - simple refine (is_contr_equiv' _ _).
    * exact (total_path y).
    * exact left_unit_law_coprod.
    * apply is_contr_total_path.
Defined.

Theorem is_contr_total_Eq_coprod {A B} (x : coprod A B) :
  is_contr (Sigma (coprod A B) (Eq_coprod x)).
Proof.
  destruct x as [x|y].
  - apply is_contr_total_Eq_coprod_inl.
  - apply is_contr_total_Eq_coprod_inr.
Defined.

Theorem is_equiv_Eq_coprod_eq {A B} {x y : coprod A B} :
  is_equiv (@Eq_coprod_eq A B x y).
Proof.
  apply fundamental_thm_id.
  - apply refl_Eq_coprod.
  - apply is_contr_total_Eq_coprod.
Defined.
