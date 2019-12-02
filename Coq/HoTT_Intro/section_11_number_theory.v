Require Export section_10_truncation_levels.

(** Section 11.5 The Euclidean algorithm *)

Lemma leq_ℕ_subtract_ℕ :
  forall {a b}, leq_ℕ (subtract_ℕ a b) a.
Proof.
  intro a; induction a as [|a H]; intro b.
  - apply reflexive_leq_ℕ.
  - destruct b.
    * apply reflexive_leq_ℕ.
    * refine (transitive_leq_ℕ _ _ _ _ _).
      ** exact (H b).
      ** apply leq_succ_ℕ.
Defined.

Definition gcd_euclid : ℕ -> ℕ -> ℕ.
Proof.
  simple refine (strong_ind_ℕ _ _ _).
  - exact idmap.
  - intros a F.
    simple refine (strong_ind_ℕ _ _ _).
    * exact (succ_ℕ a).
    * intros b G.
      generalize (@linear_order_ℕ a b); intro t; destruct t as [l|l].
      ** apply (F (subtract_ℕ a b)).
         apply leq_ℕ_subtract_ℕ.
         exact (succ_ℕ b).
      ** apply (G (subtract_ℕ b a)).
         apply leq_ℕ_subtract_ℕ.
Defined.

Definition divides_ℕ (d n : ℕ) : Type :=
  Sigma ℕ (fun k => mul_ℕ k d == n).

Definition reflexive_divides_ℕ {d : ℕ} : divides_ℕ d d.
Proof.
  apply (pair one_ℕ).
  apply left_unit_law_mul_ℕ.
Defined.

Definition transitive_divides_ℕ {d n m : ℕ} :
  divides_ℕ d n -> divides_ℕ n m -> divides_ℕ d m.
Proof.
  intros [k p] [l q].
  apply (pair (mul_ℕ l k)).
  transitivity (l * (k * d)).
  - apply associative_mul_ℕ.
  - transitivity (l * n).
    * apply (ap (mul_ℕ l) p).
    * exact q.
Defined.

Definition divides_zero_ℕ {d} : divides_ℕ d zero_ℕ.
Proof.
  apply (pair zero_ℕ).
  apply left_zero_law_mul_ℕ.
Defined.

Definition divides_add_ℕ {d m n} :
  divides_ℕ d m -> divides_ℕ d n -> divides_ℕ d (m + n).
Proof.
  intros [k p] [l q].
  apply (pair (k + l)).
  transitivity ((k * d) + (l * d)).
  - apply right_distributive_mul_add_ℕ.
  - rewrite p; now rewrite q.
Defined.

Definition left_zero_law_subtract_ℕ {n} : subtract_ℕ zero_ℕ n == zero_ℕ.
Proof. reflexivity. Defined.

Definition right_unit_law_subtract_ℕ {n} : subtract_ℕ n zero_ℕ == n.
Proof.
  now induction n as [|n H].
Defined.

Definition cancellation_law_succ_subtract_ℕ :
  forall {m n}, subtract_ℕ m n == subtract_ℕ (succ_ℕ m) (succ_ℕ n).
Proof. intros m n. reflexivity. Defined.

Definition right_cancellation_law_add_subtract_ℕ :
  forall {m n k}, subtract_ℕ m n == subtract_ℕ (m + k) (n + k).
Proof.
  intros m n k; induction k as [|k H].
  - reflexivity.
  - assumption.
Defined.

Definition left_cancellation_law_add_subtract_ℕ :
  forall {m n k}, subtract_ℕ m n == subtract_ℕ (k + m) (k + n).
Proof.
  intros m n k.
  rewrite (commutative_add_ℕ k m); rewrite (commutative_add_ℕ k n).
  apply right_cancellation_law_add_subtract_ℕ.
Defined.

Definition right_distributive_mul_subtract_ℕ :
  forall {m n k}, (subtract_ℕ m n) * k == subtract_ℕ (m * k) (n * k).
Proof.
  intro m; induction m as [|m H]; intro n; induction n as [|n K]; intro k.
  - now repeat rewrite left_zero_law_mul_ℕ.
  - now repeat rewrite left_zero_law_mul_ℕ.
  - rewrite left_zero_law_mul_ℕ.
    now repeat rewrite right_unit_law_subtract_ℕ.
  - transitivity (subtract_ℕ (m * k) (n * k)).
    * exact (H n k).
    * repeat rewrite left_successor_law_mul_ℕ.
      apply right_cancellation_law_add_subtract_ℕ.
Defined.

Definition left_distributive_mul_subtract_ℕ :
  forall {m n k}, k * (subtract_ℕ m n) == (subtract_ℕ (k * m) (k * n)).
Proof.
  intros m n k.
  rewrite (commutative_mul_ℕ k (subtract_ℕ m n)).
  rewrite (commutative_mul_ℕ k m).
  rewrite (commutative_mul_ℕ k n).
  apply right_distributive_mul_subtract_ℕ.
Defined.

Definition divides_subtract_ℕ {d m n} :
  divides_ℕ d m -> divides_ℕ d n -> divides_ℕ d (subtract_ℕ m n).
Proof.
  intros [k p] [l q].
  apply (pair (subtract_ℕ k l)).
  transitivity (subtract_ℕ (k * d) (l * d)).
  - apply right_distributive_mul_subtract_ℕ.
  - rewrite p; rewrite q; reflexivity.
Defined.

Definition compute_leq_gcd_euclid :
  forall {a b}, leq_ℕ b a -> gcd_euclid a b == gcd_euclid (subtract_ℕ a b) b.
Proof.
  simple refine (strong_ind_ℕ _ _ _).
  - intros b l.
    reflexivity.
  - intros a F.
    { simple refine (strong_ind_ℕ _ _ _).
      - intros []. reflexivity.
      - intros b G H.
        apply (F (subtract_ℕ a b)).
        
Definition divides_gcd_euclid {d} :
  forall a b, divides_ℕ d a -> divides_ℕ d b -> divides_ℕ d (gcd_euclid a b).
Proof.
  simple refine (strong_ind_ℕ _ _ _).
  - intros b p q; exact q.
  - intros a F.
    * { simple refine (strong_ind_ℕ _ _ _).
        - intros p q; exact p.
        - intros b G p q.
          generalize (@linear_order_ℕ a b); intro t; destruct t as [l|l].
          simple refine (F (subtract_ℕ (succ_ℕ a) (succ_ℕ b)) _ _ _ _).
      }

