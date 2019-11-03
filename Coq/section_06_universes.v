Require Export section_05_identity.

(** Section 6.3. Pointed types *)

Definition pType : Type := Sigma Type (fun X => X).

Definition type_pType (A : pType) : Type := pr1 A.

Definition pt_pType (A : pType) : type_pType A := pr2 A.

Definition pMap (A B : pType) : Type :=
  Sigma (type_pType A -> type_pType B)
        (fun f => f (pt_pType A) == pt_pType B).

Definition map_pMap {A B : pType} (f : pMap A B) :
  type_pType A -> type_pType B :=
  pr1 f.

Definition path_pMap {A B : pType} (f : pMap A B) :
  map_pMap f (pt_pType A) == pt_pType B :=
  pr2 f.

Definition idpmap (A : pType) : pMap A A :=
  pair idmap refl.

Definition pcomp {A B C : pType} (g : pMap B C) (f : pMap A B) :
  pMap A C.
Proof.
  apply (pair (comp (map_pMap g) (map_pMap f))).
  transitivity (map_pMap g (pt_pType B)).
  - exact (ap (map_pMap g) (path_pMap f)).
  - exact (path_pMap g).
Defined.

(** The definition of loopspace is not possible until the identity types are
    not forced to land in Prop. I don't know how to do this. *)

(*
Definition loopspace (A : pType) : pType.
Proof.
  apply (pair (pt_pType A == pt_pType A)).*)

(** Section 6.4. Families and relations on the natural numbers *)

(** Definition 6.4.1 *)

Definition Fin (n : N) : Type.
Proof.
  induction n as [|n F].
  - exact empty.
  - exact (coprod F unit).
Defined.

(** Definition 6.4.2 *)

Definition Eq_N : N -> N -> Type.
Proof.
  intro m; induction m as [|m E].
  - intro n; destruct n.
    * exact unit.
    * exact empty.
  - intro n; destruct n.
    * exact empty.
    * exact (E n).
Defined.

(*
  match m with
  | zero_N =>
    match n with
    | zero_N => unit
    | succ_N n => empty
    end
  | succ_N m =>
    match n with
    | zero_N => empty
    | succ_N n => Eq_N m n
    end
  end.
*)

Definition reflexive_Eq_N (n : N) : Eq_N n n.
Proof.
  induction n as [|n p].
  - exact star.
  - exact p.
Defined.

Definition is_identity_system_Eq_N' (m : N) : 
  forall (n : N) (p : Eq_N m n) (P : forall (x y : N), Eq_N x y -> Type),
    (forall n, P n n (reflexive_Eq_N n)) -> P m n p.
Proof.
  induction m as [|m H]; intros n p P r; destruct n; try now destruct p.
  - destruct p. exact (r zero_N).
  - eapply (H n p).
    intro x. exact (r (succ_N x)).
Defined.

Definition is_identity_system_Eq_N
           {P : forall x y, Eq_N x y -> Type}
           (r : forall x, P x x (reflexive_Eq_N x))
           {m n : N} (p : Eq_N m n) : P m n p :=
  is_identity_system_Eq_N' m n p P r.
  
Definition is_least_reflexive_Eq_N {R : N -> N -> Type} (r : forall n, R n n) :
  forall (m n : N), Eq_N m n -> R m n :=
  @is_identity_system_Eq_N (fun x y (p : Eq_N x y) => R x y) r.

(** Exercises *)

(** Exercise 6.1 *)

Definition symmetric_Eq_N (m : N) : forall n, Eq_N m n -> Eq_N n m.
Proof.
  induction m as [|m H].
  - intro n. destruct n.
    * exact idmap.
    * exact ex_falso.
  - intro n. destruct n.
    * exact ex_falso.
    * exact (H n).
Defined.

Definition transitive_Eq_N (m : N) :
  forall n k, Eq_N m n -> Eq_N n k -> Eq_N m k.
Proof.
  induction m as [|m H]; intros n k p q;
    destruct n; destruct k; try destruct p; try destruct q.
  - exact star.
  - now apply (H n k).
Defined.

(** Exercise 6.2 *)

(** This exercise is solved in Lemma 6.4.3 *)

(** Exercise 6.3 *)

Definition preserves_Eq_N (f : N -> N) :
  forall {m n}, Eq_N m n -> Eq_N (f m) (f n) :=
  @is_least_reflexive_Eq_N
    (fun x y => Eq_N (f x) (f y))
    (fun x => reflexive_Eq_N (f x)).

(** Exercise 6.4 *)

(** Exercise 6.4.a *)

Definition leq_N : N -> N -> Type.
Proof.
  intro m; induction m as [|m L]; intro n; destruct n.
  - exact unit.
  - exact unit.
  - exact empty.
  - exact (L n).
Defined.

Definition le_N : N -> N -> Type.
Proof.
  intro m; induction m as [|m L].
  - intro n; destruct n.
    * exact empty.
    * exact unit.
  - intro n; destruct n.
    * exact empty.
    * exact (L n).
Defined.

(** Exercise 6.4.b *)

Definition reflexive_leq_N (n : N) : leq_N n n.
Proof. now induction n. Defined.

Definition transitive_leq_N :
  forall m n k, leq_N m n -> leq_N n k -> leq_N m k.
Proof.
  intro m; induction m as [|m t];
    intros n k p q; destruct n; destruct k; try now cbn.
  now apply (t n k).
Defined.

Definition anti_symmetric_leq_N :
  forall m n, leq_N m n -> leq_N n m -> m == n.
Proof.
  intro m. induction m as [|m H]; intros n p q; destruct n; try now auto.
  exact (ap succ_N (H n p q)).
Defined.

(** Exercise 6.4.c *)

Definition transitive_le_N :
  forall m n k, le_N m n -> le_N n k -> le_N m k.
Proof.
  intro m; induction m as [|m t];
    intros n k p q; destruct n; destruct k; try now cbn.
  now apply (t n k).
Defined.

Definition anti_reflexive_le_N (n : N) : neg (le_N n n).
Proof. now induction n. Defined.

Definition succ_le_N (n : N) : le_N n (succ_N n).
Proof.
  induction n as [|n l].
  - exact star.
  - exact l.
Defined.

(** Exercise 6.4.d *)

Definition leq_min_N_leq_leq_N :
  forall k m n, leq_N k m -> leq_N k n -> leq_N k (min_N m n).
Proof.
  intro k. induction k as [|k H];
             intros m n p q; destruct m; destruct n; try auto.
  exact (H m n p q).
Defined.

Definition leq_left_leq_min_N :
  forall k m n, leq_N k (min_N m n) -> leq_N k m.
Proof.
  intro k; induction k as [|k H];
    intros m n p; destruct m; destruct n; try auto; try destruct p.
  now apply (H m n).
Defined.

Definition leq_right_leq_min_N :
  forall k m n, leq_N k (min_N m n) -> leq_N k n.
Proof.
  intro k; induction k as [|k H];
    intros m n p; destruct m; destruct n; try auto; try destruct p.
  now apply (H m n).
Defined.

Definition leq_max_N_leq_leq_N :
  forall k m n, leq_N m k -> leq_N n k -> leq_N (max_N m n) k.
Proof.
  intro k; induction k as [|k H];
    intros m n p q; destruct m; destruct n; try auto.
  now apply (H m n).
Defined.

Definition leq_left_leq_max_N :
  forall k m n, leq_N (max_N m n) k -> leq_N m k.
Proof.
  intro k; induction k as [|k H];
    intros m n p; destruct m; destruct n; try auto; try destruct p.
  exact star.
  now apply (H m n).
Defined.

Definition leq_right_leq_max_N :
  forall k m n, leq_N (max_N m n) k -> leq_N n k.
Proof.
  intro k; induction k as [|k H];
    intros m n p; destruct m; destruct n; try auto; try destruct p.
  exact star.
  now apply (H m n).
Defined.

(** Exercise 6.5 *)

(** Exercise 6.5.a *)

Definition Eq_bool (b b' : bool) : Type.
Proof.
  destruct b; destruct b'.
  - exact unit.
  - exact empty.
  - exact empty.
  - exact unit.
Defined.

(** Exercise 6.5.b *)

Definition reflexive_Eq_bool (b : bool) : Eq_bool b b.
Proof.
  destruct b; exact star.
Defined.

(** Exercise 6.5.c *)

Definition is_identity_system_Eq_bool :
  forall (P : forall b b', Eq_bool b b' -> Type)
         (r : forall b, P b b (reflexive_Eq_bool b))
         {b b' : bool} (p : Eq_bool b b'), P b b' p.
Proof.
  intros P r b b' p; destruct b; destruct b'; destruct p; now apply r.
Defined.

Definition is_least_reflexive_Eq_bool :
  forall (R : bool -> bool -> Type)
         (r : forall b, R b b)
         {b b' : bool}, Eq_bool b b' -> R b b'.
Proof.
  intro R.
  apply (is_identity_system_Eq_bool (fun b b' p => R b b')).
Defined.

(** Exercise 6.6 *)

(** Exercise 6.6.a *)

Definition leq_Z : Z -> Z -> Type.
Proof.
  intro k.
  destruct k as [n | x].
  - induction n as [|n L].
    * { intro l; destruct l as [m | y].
        - destruct m.
          * exact unit.
          * exact empty.
        - exact unit.
      }
    * { intro l; destruct l as [m | y].
        - destruct m.
          * exact unit.
          * exact (L (inl m)).
        - exact unit.
      }
  - destruct x as [x | n].
    * { intro l; destruct l as [m | y].
        - exact empty.
        - exact unit.
      }
    * { induction n as [|n L].
        - intro l; destruct l as [m | y].
          * exact empty.
          * destruct y as [y | m].
            ** exact empty.
            ** exact unit.
        - intro l; destruct l as [m | y].
          * exact empty.
          * destruct y as [y | m].
            ** exact empty.
            ** destruct m.
               *** exact empty.
               *** exact (L (inr (inr m))).
      }
Defined.

Definition le_Z : Z -> Z -> Type.
Proof.
  intro k.
  destruct k as [n | x].
  - induction n as [|n L].
    * { intro l; destruct l as [m | y].
        - destruct m.
          * exact empty.
          * exact empty.
        - exact unit.
      }
    * { intro l; destruct l as [m | y].
        - destruct m.
          * exact unit.
          * exact (L (inl m)).
        - exact unit.
      }
  - destruct x as [x | n].
    * { intro l; destruct l as [m | y].
        - exact empty.
        - destruct y as [y | m].
          * exact empty.
          * exact unit.
      }
    * { induction n as [|n L].
        - intro l; destruct l as [m | y].
          * exact empty.
          * destruct y as [y | m].
            ** exact empty.
            ** destruct m.
               *** exact empty.
               *** exact unit.
        - intro l; destruct l as [m | y].
          * exact empty.
          * destruct y as [y | m].
            ** exact empty.
            ** destruct m.
               *** exact empty.
               *** exact (L (inr (inr m))).
      }
Defined.

Definition reflexive_leq_Z (k : Z) : leq_Z k k.
Proof.
  destruct k as [n | x];
    try induction n as [|n r];
    try destruct x as [x | n];
    try induction n as [|n t];
    try now auto.
Defined.

Definition transitive_leq_Z :
  forall k l m, leq_Z k l -> leq_Z l m -> leq_Z k m.
Proof.
  intro k;
    destruct k as [n | x];
    try induction n as [|n t];
    try destruct x as [x | n];
    try induction n as [|n t];
    intros l m p q;
    destruct l as [n' | x'];
    try destruct x' as [x' | n'];
    try destruct n';
    destruct m as [n'' | x''];
    try destruct x'' as [x'' | n''];
    try destruct n'';
    try now auto.
  - now apply (t (inl n') (inl n'')).
  - now apply (t (inr (inr n')) (inr (inr n''))).
Defined.

Definition anti_symmetric_leq_Z :
  forall k l, leq_Z k l -> leq_Z l k -> k == l.
Proof.
  intro k;
    destruct k as [n | x];
    try induction n as [|n a];
    try destruct x as [x2 | n2];
    try destruct x2;
    try induction n2 as [|n2 a];
    intro l;
    try destruct l as [m | y];
    try destruct m;
    try destruct y as [y2 | m2];
    try destruct y2;
    try destruct m2;
    try now auto.
  - intros p q. exact (ap pred_Z (a (inl m) p q)).
  - intros p q. exact (ap succ_Z (a (inr (inr m2)) p q)).
Defined.

Definition anti_reflexive_le_Z (k : Z) : neg (le_Z k k).
Proof.
  destruct k as [n | x];
    try induction n as [|n a];
    try destruct x as [x | n2];
    try induction n2 as [|n2 a];
    try now auto.
Defined.

Definition transitive_le_Z :
  forall k l m, le_Z k l -> le_Z l m -> le_Z k m.
Proof.
  intro k;
    destruct k as [n | x];
    try induction n as [|n t];
    try destruct x as [x | n];
    try induction n as [|n t];
    intros l m p q;
    destruct l as [n' | x'];
    try destruct x' as [x' | n'];
    try destruct n';
    destruct m as [n'' | x''];
    try destruct x'' as [x'' | n''];
    try destruct n'';
    try now auto.
  - now apply (t (inl n') (inl n'')).
  - now apply (t (inr (inr n')) (inr (inr n''))).
Defined.

(** Exercise 6.7 *)

(** Exercise 6.7.a *)

Definition zero_leq_N n : leq_N zero_N n.
Proof.
  induction n as [|n H]; try now auto.
Defined.

Definition fam_strong_ind_N (P : N -> Type) (n : N) : Type :=
  forall x, leq_N x n -> P x.
                                                     
Definition zero_strong_ind_N :
  forall (P : N -> Type), P zero_N -> fam_strong_ind_N P zero_N.
Proof.
  intros P p0 x H.
  induction x; try now auto.
Defined.

Definition succ_strong_ind_N (P : N -> Type) :
  ( forall k, (fam_strong_ind_N P k) -> P (succ_N k)) ->
  forall k, (fam_strong_ind_N P k) -> (fam_strong_ind_N P (succ_N k)).
Proof.
  intros pS k f m t.
  induction m.
  - exact (f zero_N (zero_leq_N k)).
  - apply pS.
    intros m' t'.
    exact (f m' (transitive_leq_N m' m k t' t)).
Defined.

Definition conclusion_strong_ind_N (P : N -> Type) :
  ( forall n, fam_strong_ind_N P n) -> forall n, P n.
Proof.
  intros f n.
  exact (f n n (reflexive_leq_N n)).
Defined.

Definition induction_strong_ind_N :
  forall (P : N -> Type) (p0 : fam_strong_ind_N P zero_N)
         (pS : forall k,
             (fam_strong_ind_N P k) -> (fam_strong_ind_N P (succ_N k))),
    forall n, fam_strong_ind_N P n.
Proof.
  intros P p0 pS n.
  induction n; now auto.
Defined.

Definition strong_ind_N :
  forall (P : N -> Type),
    P zero_N -> (forall x, (forall y, leq_N y x -> P y) -> P (succ_N x)) ->
    forall n, P n.
Proof.
  intros P p0 pS.
  apply conclusion_strong_ind_N.
  apply induction_strong_ind_N.
  - now apply zero_strong_ind_N.
  - now apply succ_strong_ind_N.
Defined.

(** Exercise 6.7.b *)

Definition fam_ordinal_ind_N (P : N -> Type) (n : N) :=
  forall k, (le_N k n) -> P k.

Definition neg_le_zero_N (n : N) : neg (le_N n zero_N).
Proof.
  induction n; now auto.
Defined.

Definition strong_transitive_le_N (m : N) :
  forall n k, le_N m n -> le_N n (succ_N k) -> le_N m k.
Proof.
  induction m as [|m H]; intros n k p q; destruct n; destruct k;
    try now auto.
  - apply ex_falso_map. now apply (neg_le_zero_N n).
  - apply ex_falso_map. now apply (neg_le_zero_N n).
  - now apply (H n k).
Defined.

Definition zero_ordinal_ind_N (P : N -> Type) :
  fam_ordinal_ind_N P zero_N.
Proof.
  intros k p.
  induction k; now auto.
Defined.

Definition succ_ordinal_ind_N
           (P : N -> Type) (pS : forall k, fam_ordinal_ind_N P k -> P k) :
  (forall k, fam_ordinal_ind_N P k -> fam_ordinal_ind_N P (succ_N k)).
Proof.
  intros k H l p.
  apply (pS l).
  intros k' p'.
  apply (H k').
  now apply (strong_transitive_le_N k' l k).
Defined.

Definition inductive_step_ordinal_ind_N (P : N -> Type)
           (p0 : fam_ordinal_ind_N P zero_N)
           (pS : forall k,
               fam_ordinal_ind_N P k -> fam_ordinal_ind_N P (succ_N k)) :
  forall k, fam_ordinal_ind_N P k.
Proof.
  intro k. induction k; now auto.
Defined.

Definition conclusive_step_ordinal_ind_N (P : N -> Type) :
  (forall k, fam_ordinal_ind_N P k) -> (forall k, P k).
Proof.
  intros H k. apply (H (succ_N k)). apply succ_le_N.
Defined.

Definition ordinal_ind_N (P : N -> Type) (H : forall k, fam_ordinal_ind_N P k -> P k) : forall k, P k.
Proof.
  apply conclusive_step_ordinal_ind_N.
  apply inductive_step_ordinal_ind_N.
  - now apply zero_ordinal_ind_N.
  - now apply succ_ordinal_ind_N.
Defined.
