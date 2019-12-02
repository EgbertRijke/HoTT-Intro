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

Definition Fin (n : ℕ) : Type.
Proof.
  induction n as [|n F].
  - exact empty.
  - exact (coprod F unit).
Defined.

(** Definition 6.4.2 *)

Definition shift_fam_ℕ : (ℕ -> Type) -> (ℕ -> Type).
Proof.
  intros P n.
  destruct n.
  - exact empty.
  - exact (P n).
Defined.

Definition Eq_ℕ : ℕ -> ℕ -> Type.
Proof.
  intro m; induction m as [|m E].
  - intro n; destruct n.
    * exact unit.
    * exact empty.
  - exact (shift_fam_ℕ E).
Defined.

Definition reflexive_Eq_ℕ (n : ℕ) : Eq_ℕ n n.
Proof.
  induction n as [|n p].
  - exact star.
  - exact p.
Defined.

Definition is_identity_system_Eq_ℕ' (m : ℕ) : 
  forall (n : ℕ) (p : Eq_ℕ m n) (P : forall (x y : ℕ), Eq_ℕ x y -> Type),
    (forall n, P n n (reflexive_Eq_ℕ n)) -> P m n p.
Proof.
  induction m as [|m H]; intros n p P r; destruct n; try now destruct p.
  - destruct p. exact (r zero_ℕ).
  - eapply (H n p).
    intro x. exact (r (succ_ℕ x)).
Defined.

Definition is_identity_system_Eq_ℕ
           {P : forall x y, Eq_ℕ x y -> Type}
           (r : forall x, P x x (reflexive_Eq_ℕ x))
           {m n : ℕ} (p : Eq_ℕ m n) : P m n p :=
  is_identity_system_Eq_ℕ' m n p P r.
  
Definition is_least_reflexive_Eq_ℕ {R : ℕ -> ℕ -> Type} (r : forall n, R n n) :
  forall (m n : ℕ), Eq_ℕ m n -> R m n :=
  @is_identity_system_Eq_ℕ (fun x y (p : Eq_ℕ x y) => R x y) r.

(** Exercises *)

(** Exercise 6.1 *)

Definition symmetric_Eq_ℕ (m : ℕ) : forall n, Eq_ℕ m n -> Eq_ℕ n m.
Proof.
  induction m as [|m H].
  - intro n. destruct n.
    * exact idmap.
    * exact ex_falso.
  - intro n. destruct n.
    * exact ex_falso.
    * exact (H n).
Defined.

Definition transitive_Eq_ℕ (m : ℕ) :
  forall n k, Eq_ℕ m n -> Eq_ℕ n k -> Eq_ℕ m k.
Proof.
  induction m as [|m H]; intros n k p q;
    destruct n; destruct k; try destruct p; try destruct q.
  - exact star.
  - now apply (H n k).
Defined.

(** Exercise 6.2 *)

(** This exercise is solved in Lemma 6.4.3 *)

(** Exercise 6.3 *)

Definition preserves_Eq_ℕ (f : ℕ -> ℕ) :
  forall {m n}, Eq_ℕ m n -> Eq_ℕ (f m) (f n) :=
  @is_least_reflexive_Eq_ℕ
    (fun x y => Eq_ℕ (f x) (f y))
    (fun x => reflexive_Eq_ℕ (f x)).

(** Exercise 6.4 *)

(** Exercise 6.4.a *)

Definition leq_ℕ : ℕ -> ℕ -> Type.
Proof.
  intro m; induction m as [|m L].
  - exact (const unit).
  - exact (shift_fam_ℕ L).
Defined.

Definition le_ℕ : ℕ -> ℕ -> Type.
Proof.
  intro m.
  exact (shift_fam_ℕ (leq_ℕ m)).
Defined.

(** Exercise 6.4.b *)

Definition reflexive_leq_ℕ {n : ℕ} : leq_ℕ n n.
Proof. now induction n. Defined.

Definition transitive_leq_ℕ :
  forall {m n k}, leq_ℕ m n -> leq_ℕ n k -> leq_ℕ m k.
Proof.
  intro m; induction m as [|m t];
    intros n k p q; destruct n; destruct k; try now cbn.
  now apply (t n k).
Defined.

Definition anti_symmetric_leq_ℕ :
  forall {m n}, leq_ℕ m n -> leq_ℕ n m -> m == n.
Proof.
  intro m. induction m as [|m H]; intros n p q; destruct n; try now auto.
  exact (ap succ_ℕ (H n p q)).
Defined.

(** Exercise 6.4.c *)

Definition transitive_le_ℕ :
  forall {m n k}, le_ℕ m n -> le_ℕ n k -> le_ℕ m k.
Proof.
  intro m; induction m as [|m t];
    intros n k p q; destruct n; destruct k; try now cbn.
  now apply (t n k).
Defined.

Definition irreflexive_le_ℕ {n : ℕ} : neg (le_ℕ n n).
Proof. now induction n. Defined.

Definition succ_le_ℕ {n : ℕ} : le_ℕ n (succ_ℕ n).
Proof.
  induction n as [|n l].
  - exact star.
  - exact l.
Defined.

(** Exercise 6.4.other *)

Definition zero_leq_ℕ {n} : leq_ℕ zero_ℕ n.
Proof.
  induction n as [|n H]; try now auto.
Defined.

Definition zero_le_ℕ {n} : le_ℕ zero_ℕ (succ_ℕ n).
Proof.
  induction n as [|n H].
  - exact star.
  - refine (transitive_le_ℕ _ _).
    * exact H.
    * apply succ_le_ℕ.
Defined.

Definition leq_le_ℕ {m} : forall {n}, le_ℕ m n -> leq_ℕ (succ_ℕ m) n.
Proof.
  induction m as [|m H].
  - intro n; destruct n.
    * apply ex_falso.
    * intros []. exact (@zero_leq_ℕ n).
  - intro n; induction n as [|n K].
    * apply ex_falso.
    * intro l. now apply H.
Defined.

Definition neq_le_ℕ {m} : forall {n}, le_ℕ m n -> neg (m == n).
Proof.
  induction m as [|m H].
  - intros n p; destruct n; now destruct p.
  - intros n p; destruct n.
    * destruct p.
    * intro q.
      rewrite q in p.
      apply (irreflexive_le_ℕ p).
Defined.
    
Definition linear_order_ℕ : forall {a b : ℕ}, coprod (leq_ℕ b a) (le_ℕ a b).
Proof.
  intro b; induction b as [|b H]; intro a.
  - destruct a.
    * now apply inl.
    * apply inr. apply zero_le_ℕ.
  - induction a as [|a K].
    * apply inl. apply zero_leq_ℕ.
    * generalize (H a); intro t; destruct t as [l|l].
      ** now apply inl.
      ** now apply inr.
Defined.

Definition subtract_ℕ : ℕ -> ℕ -> ℕ.
Proof.
  intro a; induction a as [|a s].
  - exact (const zero_ℕ).
  - intro b; destruct b.
    * exact (succ_ℕ a).
    * exact (s b).
Defined.

Lemma leq_succ_ℕ {n} : leq_ℕ n (succ_ℕ n).
Proof.
  now induction n.
Defined.

Lemma left_preserves_leq_add_ℕ {n : ℕ} :
  forall {x y}, leq_ℕ x y -> leq_ℕ (x + n) (y + n).
Proof.
  induction n as [|n H].
  - auto.
  - intros x y p. exact (H x y p).
Defined.

Lemma right_preserves_leq_add_ℕ {n : ℕ} :
  forall {x y}, leq_ℕ x y -> leq_ℕ (n + x) (n + y).
Proof.
  intros x y p.
  rewrite (commutative_add_ℕ n x).
  rewrite (commutative_add_ℕ n y).
  now apply left_preserves_leq_add_ℕ.
Defined.

Lemma preserves_leq_add_ℕ {a b a' b'} :
  leq_ℕ a a' -> leq_ℕ b b' -> leq_ℕ (a + b) (a' + b').
Proof.
  intros p q.
  eapply transitive_leq_ℕ.
  - exact (left_preserves_leq_add_ℕ p).
  - exact (right_preserves_leq_add_ℕ q).
Defined.
  
(** Exercise 6.4.d *)

Definition leq_min_ℕ_leq_leq_ℕ :
  forall k m n, leq_ℕ k m -> leq_ℕ k n -> leq_ℕ k (min_ℕ m n).
Proof.
  intro k. induction k as [|k H];
             intros m n p q; destruct m; destruct n; try auto.
  exact (H m n p q).
Defined.

Definition leq_left_leq_min_ℕ :
  forall k m n, leq_ℕ k (min_ℕ m n) -> leq_ℕ k m.
Proof.
  intro k; induction k as [|k H];
    intros m n p; destruct m; destruct n; try auto; try destruct p.
  now apply (H m n).
Defined.

Definition leq_right_leq_min_ℕ :
  forall k m n, leq_ℕ k (min_ℕ m n) -> leq_ℕ k n.
Proof.
  intro k; induction k as [|k H];
    intros m n p; destruct m; destruct n; try auto; try destruct p.
  now apply (H m n).
Defined.

Definition leq_max_ℕ_leq_leq_ℕ :
  forall k m n, leq_ℕ m k -> leq_ℕ n k -> leq_ℕ (max_ℕ m n) k.
Proof.
  intro k; induction k as [|k H];
    intros m n p q; destruct m; destruct n; try auto.
  now apply (H m n).
Defined.

Definition leq_left_leq_max_ℕ :
  forall k m n, leq_ℕ (max_ℕ m n) k -> leq_ℕ m k.
Proof.
  intro k; induction k as [|k H];
    intros m n p; destruct m; destruct n; try auto; try destruct p.
  exact star.
  now apply (H m n).
Defined.

Definition leq_right_leq_max_ℕ :
  forall k m n, leq_ℕ (max_ℕ m n) k -> leq_ℕ n k.
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

Definition irreflexive_le_Z (k : Z) : neg (le_Z k k).
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

Definition zero_strong_ind_ℕ
           (P : ℕ -> Type)
           (p0 : P zero_ℕ)
           (pS : forall n, (forall x, leq_ℕ x n -> P x) -> P (succ_ℕ n)) :
  forall x, leq_ℕ x zero_ℕ -> P x.
Proof.
  intros x p.
  destruct x.
  - exact p0.
  - destruct p.
Defined.

Print zero_strong_ind_ℕ.

Definition succ_strong_ind_ℕ
           (P : ℕ -> Type)
           (p0 : P zero_ℕ)
           (pS : forall n, (forall x, leq_ℕ x n -> P x) -> P (succ_ℕ n)) :
  forall m,
    (forall y, leq_ℕ y m -> P (succ_ℕ y)) ->
    (forall y, leq_ℕ y (succ_ℕ m) -> P y).  
Proof.
  intros m H y l.
  destruct y.
  - exact p0.
  - apply (H y l).
Defined.

Definition strong_ind_ℕ' n :
  forall
    (P : ℕ -> Type)
    (p0 : P zero_ℕ)
    (pS : forall n, (forall x, leq_ℕ x n -> P x) -> P (succ_ℕ n)), P n.
Proof.
  induction n as [|n H].
  - intros P p0 pS. exact p0.
  - intros P p0 pS.
    apply (H (comp P succ_ℕ)).
    * apply (pS zero_ℕ).
      now apply zero_strong_ind_ℕ.
    * intros m h.
      apply (pS (succ_ℕ m)).
      now apply succ_strong_ind_ℕ.
Defined.

Print strong_ind_ℕ'.

Definition strong_ind_ℕ
           (P : ℕ -> Type)
           (p0 : P zero_ℕ)
           (pS : forall n, (forall x, leq_ℕ x n -> P x) -> P (succ_ℕ n)) :
  forall n, P n :=
  fun n => strong_ind_ℕ' n P p0 pS.
  
Section Strong_induction.

  Variables (P : ℕ -> Type)
            (p0 : P zero_ℕ)
            (pS : forall n, (forall x, leq_ℕ x n -> P x) -> P (succ_ℕ n)).

  Definition zero_comp_strong_ind_ℕ : strong_ind_ℕ P p0 pS zero_ℕ == p0 :=
    refl.

  Goal forall n, (strong_ind_ℕ P p0 pS (succ_ℕ n)) == (strong_ind_ℕ P p0 pS (succ_ℕ n)).
    intro n.
    unfold strong_ind_ℕ.
    unfold strong_ind_ℕ' at 1.

  Definition succ_comp_strong_ind_ℕ (n : ℕ) :
    strong_ind_ℕ P p0 pS (succ_ℕ n) ==
    pS n (fun y t => (strong_ind_ℕ P p0 pS y)) :=
    refl.

Definition fam_strong_ind_ℕ (n : ℕ) : Type :=
  forall x, leq_ℕ x n -> P x.
                                                     
Definition zero_strong_ind_ℕ : fam_strong_ind_ℕ zero_ℕ.
Proof.
  intros x l.
  induction x.
  - exact p0.
  - now destruct l.
Defined.
(*   pS zero_ℕ (fun (y : ℕ) (_ : leq_ℕ y zero_ℕ) => strong_ind_ℕ y)*)

Definition succ_strong_ind_ℕ :
  forall k, (fam_strong_ind_ℕ k) -> (fam_strong_ind_ℕ (succ_ℕ k)).
Proof.
  intro n; induction n as [|n H].
  - intros f x p.
    induction x as [|x K].
    * exact (f zero_ℕ p).
    * destruct x as [|x K'].
      ** exact (pS zero_ℕ f).
      ** destruct p.
  - intros f x p.
    induction x as [|x K].
    * apply (f zero_ℕ). apply zero_leq_ℕ.
    * apply (pS x).
      intros y q. apply (f y). apply (transitive_leq_ℕ q p).
Defined.

Definition induction_strong_ind_ℕ :
  (fam_strong_ind_ℕ zero_ℕ) ->
  (forall k, (fam_strong_ind_ℕ k) -> (fam_strong_ind_ℕ (succ_ℕ k))) ->
  forall n, fam_strong_ind_ℕ n.
Proof.
  intros q0 qS n.
  induction n as [|n H].
  - exact q0.
  - exact (qS n H).
Defined.

Definition conclusion_strong_ind_ℕ :
  (forall n, fam_strong_ind_ℕ n) -> forall n, P n.
Proof.
  intros f n.
  exact (f n n reflexive_leq_ℕ).
Defined.

Definition strong_ind_ℕ : forall n, P n.
Proof.
  apply conclusion_strong_ind_ℕ.
  apply induction_strong_ind_ℕ.
  - now apply zero_strong_ind_ℕ.
  - now apply succ_strong_ind_ℕ.
Defined.



Definition succ_comp_strong_ind_ℕ :
  forall (n : ℕ),
    strong_ind_ℕ (succ_ℕ n) == pS n (fun y t => (strong_ind_ℕ y)).
Proof.
  induction n.
  - cbn.

End Strong_induction.

(** Exercise 6.7.b *)

Definition fam_ordinal_ind_ℕ (P : ℕ -> Type) (n : ℕ) :=
  forall k, (le_ℕ k n) -> P k.

Definition neg_le_zero_ℕ (n : ℕ) : neg (le_ℕ n zero_ℕ).
Proof.
  induction n; now auto.
Defined.

Definition strong_transitive_le_ℕ (m : ℕ) :
  forall n k, le_ℕ m n -> le_ℕ n (succ_ℕ k) -> le_ℕ m k.
Proof.
  induction m as [|m H]; intros n k p q; destruct n; destruct k;
    try now auto.
  now apply (H n k).
Defined.

Definition zero_ordinal_ind_ℕ (P : ℕ -> Type) :
  fam_ordinal_ind_ℕ P zero_ℕ.
Proof.
  intros k p.
  induction k; now auto.
Defined.

Definition succ_ordinal_ind_ℕ
           (P : ℕ -> Type) (pS : forall k, fam_ordinal_ind_ℕ P k -> P k) :
  (forall k, fam_ordinal_ind_ℕ P k -> fam_ordinal_ind_ℕ P (succ_ℕ k)).
Proof.
  intros k H l p.
  apply (pS l).
  intros k' p'.
  apply (H k').
  now apply (strong_transitive_le_ℕ k' l k).
Defined.

Definition inductive_step_ordinal_ind_ℕ (P : ℕ -> Type)
           (p0 : fam_ordinal_ind_ℕ P zero_ℕ)
           (pS : forall k,
               fam_ordinal_ind_ℕ P k -> fam_ordinal_ind_ℕ P (succ_ℕ k)) :
  forall k, fam_ordinal_ind_ℕ P k.
Proof.
  intro k. induction k; now auto.
Defined.

Definition conclusive_step_ordinal_ind_ℕ (P : ℕ -> Type) :
  (forall k, fam_ordinal_ind_ℕ P k) -> (forall k, P k).
Proof.
  intros H k. apply (H (succ_ℕ k)). apply succ_le_ℕ.
Defined.

Definition ordinal_ind_ℕ (P : ℕ -> Type) (H : forall k, fam_ordinal_ind_ℕ P k -> P k) : forall k, P k.
Proof.
  apply conclusive_step_ordinal_ind_ℕ.
  apply inductive_step_ordinal_ind_ℕ.
  - now apply zero_ordinal_ind_ℕ.
  - now apply succ_ordinal_ind_ℕ.
Defined.
