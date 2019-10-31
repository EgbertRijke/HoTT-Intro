Require Export section_04_inductive.

Inductive Id {A} (a : A) : A -> Type :=
| refl' : Id a a.

Definition refl {A} {a : A} : Id a a := refl' a.
  
Notation "x '==' y" := (Id x y) (at level 80).

Lemma inv {A} {x y : A} (p : x == y) : y == x.
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma concat {A} {x y z : A} (p : x == y) (q : y == z) : x == z.
Proof.
  destruct p.
  exact q.
Defined.

(* A little short-hand tactic. *)
Ltac transitivity x := apply (@concat _ _ x).

Lemma left_unit {A} {x y : A} (p : x == y) :
  concat refl p == p.
Proof. reflexivity. Defined.

Lemma right_unit {A} {x y : A} (p : x == y) :
  concat p refl == p.
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma assoc {A} {x y z w : A} (p : x == y) (q : y == z) (r : z == w) :
  concat (concat p q) r == concat p (concat q r).
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma left_inv {A} {x y : A} (p : x == y) :
  concat (inv p) p == refl.
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma right_inv {A} {x y : A} (p : x == y) :
  concat p (inv p) == refl.
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma ap {A B} (f : A -> B) {x y : A} (p : x == y) : (f x) == (f y).
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma ap_idmap {A : Type} {x y} (p : x == y) : p == ap (fun (x : A) => x) p.
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma tr {A} (B : A -> Type) {x y : A} (p : x == y) : B x -> B y.
Proof.
  destruct p.
  exact (fun x => x). (* Why can I not use the id here? *)
Defined.

Definition apd {A} {B : A -> Type} (f : forall x, B x) {x y} (p : x == y) :
  Id (tr B p (f x)) (f y).
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma left_unit_law_add_N (n : N) : zero_N + n == n.
Proof.
  induction n.
  - reflexivity.
  - cbn. now apply ap.
Defined.

Lemma right_unit_law_add_N (n : N) : n + zero_N == n.
Proof.
  reflexivity.
Defined.

Lemma left_successor_law_add_N (m n : N) :
  (succ_N m) + n == succ_N (m + n).
Proof.
  induction n.
  - reflexivity.
  - cbn. now apply ap.
Defined.

Lemma right_successor_law_add_N (m n : N) :
  m + (succ_N n) == succ_N (m + n).
Proof.
  reflexivity.
Defined.

Theorem associative_add_N (m n k : N) :
  (m + n) + k == m + (n + k).
Proof.
  induction k.
  - reflexivity.
  - cbn. now apply ap.
Defined.

Theorem commutative_add_N (m n : N) :
  m + n == n + m.
Proof.
  induction n.
  - apply inv, left_unit_law_add_N.
  - transitivity (succ_N (n + m)).
    * now apply (ap succ_N).
    * apply inv, left_successor_law_add_N.
Defined.

Definition left_zero_law_mul_N (n : N) :
  zero_N * n == zero_N.
Proof.
  induction n.
  - reflexivity.
  - transitivity (zero_N * n).
    * apply left_unit_law_add_N.
    * assumption.
Defined.

Definition right_zero_law_mul_N (n : N) :
  n * zero_N == zero_N.
Proof. reflexivity. Defined.

Definition left_successor_law_mul_N (m n : N) :
  (succ_N m) * n == (m * n) + n.
Proof.
  induction n.
  - reflexivity.
  - transitivity (succ_N m + (m * n + n)).
    * now apply (ap (add_N (succ_N m))).
    * { transitivity (succ_N (m + (m * n + n))).
        - apply left_successor_law_add_N.
        - apply (ap succ_N), inv, associative_add_N.
      }
Defined.

Definition right_successor_law_mul_N (m n : N) :
  m * (succ_N n) == m + (m * n).
Proof. reflexivity. Defined.

Definition left_distributive_mul_add_N (m n k : N) :
  m * (n + k) == (m * n) + (m * k).
Proof.
  induction k.
  - reflexivity.
  - transitivity (m + (m * n + m * k)).
    * now apply (ap (add_N m)).
    * { transitivity (m + m * n + m * k).
        - apply inv, associative_add_N.
        - transitivity ((m * n + m) + (m * k)).
          * apply (ap (add_N' (m * k))), commutative_add_N.
          * apply associative_add_N.
      }
Defined.
    
Definition associative_mul_N (m n k : N) :
  (m * n) * k == m * (n * k).
Proof.
  induction k.
  - reflexivity.
  - transitivity (m * n + m * (n * k)).
    * now apply (ap (add_N (m * n))).
    * apply inv, left_distributive_mul_add_N.
Defined.

Definition commutative_mul_N (m n : N) :
  m * n == n * m.
Proof.
  induction n.
  - apply inv, left_zero_law_mul_N.
  - transitivity (m * n + m).
    * apply commutative_add_N.
    * transitivity ((n * m) + m).
      ** now apply (ap (add_N' m)).
      ** apply inv, left_successor_law_mul_N.
Defined.

