Require Export section_10_truncation_levels.

(** Section 11.5 The Euclidean algorithm *)

Definition zero_le_N {n} : le_N zero_N (succ_N n).
Proof.
  induction n.
  - exact star.
  - refine (transitive_le_N _ _ _ _ _).
    * exact IHn.
    * apply succ_le_N.
Defined.

Definition leq_le_N {m} : forall {n}, le_N m n -> leq_N (succ_N m) n.
Proof.
  induction m as [|m H].
  - intro n; destruct n.
    * apply ex_falso.
    * intro l. apply zero_leq_N.
  - intro n; induction n as [|n K].
    * apply ex_falso.
    * intro l. now apply H.
Defined.

Definition linear_order_N : forall {a b : N}, coprod (leq_N b a) (le_N a b).
Proof.
  intro b; induction b as [|b H]; intro a.
  - destruct a.
    * now apply inl.
    * apply inr. apply zero_le_N.
  - induction a as [|a K].
    * apply inl. apply zero_leq_N.
    * generalize (H a); intro t; destruct t as [l|l].
      ** now apply inl.
      ** now apply inr.
Defined.

Definition truncated_subtract : N -> N -> N.
Proof.
  intro a; induction a as [|a s].
  - exact (const zero_N).
  - intro b; destruct b.
    * exact (succ_N a).
    * exact (s b).
Defined.

Lemma leq_succ_N {n} : leq_N n (succ_N n).
Proof.
  now induction n.
Defined.

Lemma leq_N_truncated_subtract :
  forall {a b}, leq_N (truncated_subtract a b) a.
Proof.
  intro a; induction a as [|a H]; intro b.
  - apply reflexive_leq_N.
  - destruct b.
    * apply reflexive_leq_N.
    * refine (transitive_leq_N _ _ _ _ _).
      ** exact (H b).
      ** apply leq_succ_N.
Defined.

Definition gcd_euclid : N -> N -> N.
Proof.
  simple refine (strong_ind_N _ _ _).
  - exact idmap.
  - intros a F.
    simple refine (strong_ind_N _ _ _).
    * exact (succ_N a).
    * intros b G; cbn.
      generalize (@linear_order_N a b); intro t; destruct t as [l|l].
      ** apply (F (truncated_subtract a b)).
         apply leq_N_truncated_subtract.
         exact (succ_N b).
      ** apply (G (truncated_subtract b a)).
         apply leq_N_truncated_subtract.
Defined.
