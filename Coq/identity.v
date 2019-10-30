Require Export pi nat inductive.

Inductive Id {A} (a : A) : A -> Type :=
| refl : Id a a.

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
  concat (refl x) p == p.
Proof. reflexivity. Defined.

Lemma right_unit {A} {x y : A} (p : x == y) :
  concat p (refl y) == p.
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
  concat (inv p) p == refl y.
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma right_inv {A} {x y : A} (p : x == y) :
  concat p (inv p) == refl x.
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

Lemma left_unit_law_add_NN (n : NN) : zero + n == n.
Proof.
  induction n.
  - apply refl.
  - cbn. now apply ap.
Defined.

Lemma right_unit_law_add_NN (n : NN) : n + zero == n.
Proof.
  reflexivity.
Defined.

Lemma left_successor_law_add_NN (m n : NN) :
  (succ m) + n == succ (m + n).
Proof.
  induction n.
  - reflexivity.
  - cbn. now apply ap.
Defined.

Lemma right_successor_law_add_NN (m n : NN) :
  m + (succ n) == succ (m + n).
Proof.
  reflexivity.
Defined.

Theorem associative_add_NN (m n k : NN) :
  (m + n) + k == m + (n + k).
Proof.
  induction k.
  - reflexivity.
  - cbn. now apply ap.
Defined.

Theorem commutative_add_NN (m n : NN) :
  m + n == n + m.
Proof.
  induction n.
  - apply inv.
    apply left_unit_law_add_NN.
  - transitivity (succ (n + m)).
    * now apply (ap succ).
    * apply inv, left_successor_law_add_NN.
Defined.

Definition left_zero_law_mul_NN (n : NN) :
  zero * n == zero.
Proof.
  induction n.
  - reflexivity.
  - transitivity (zero * n).
    * apply left_unit_law_add_NN.
    * assumption.
Defined.

Definition right_zero_law_mul_NN (n : NN) :
  n * zero == zero.
Proof. reflexivity. Defined.

Definition left_successor_law_mul_NN (m n : NN) :
  (succ m) * n == (m * n) + n.
Proof.
  induction n.
  - reflexivity.
  - transitivity (succ m + (m * n + n)).
    * now apply (ap (add_NN (succ m))).
    * { transitivity (succ (m + (m * n + n))).
        - apply left_successor_law_add_NN.
        - apply (ap succ), inv, associative_add_NN.
      }
Defined.

Definition right_successor_law_mul_NN (m n : NN) :
  m * (succ n) == m + (m * n).
Proof. reflexivity. Defined.

Definition left_distributive_mul_add_NN (m n k : NN) :
  m * (n + k) == (m * n) + (m * k).
Proof.
  induction k.
  - reflexivity.
  - transitivity (m + (m * n + m * k)).
    * now apply (ap (add_NN m)).
    * { transitivity (m + m * n + m * k).
        - apply inv, associative_add_NN.
        - transitivity ((m * n + m) + (m * k)).
          * apply (ap (fun x => x + (m * k))).
            apply commutative_add_NN.
          * apply associative_add_NN.
      }
Defined.
    
Definition associative_mul_NN (m n k : NN) :
  (m * n) * k == m * (n * k).
Proof.
  induction k.
  - reflexivity.
  - transitivity (m * n + m * (n * k)).
    * now apply (ap (add_NN (m * n))).
    * apply inv, left_distributive_mul_add_NN.
Defined.

Definition commutative_mul_NN (m n : NN) :
  m * n == n * m.
Proof.
  induction n.
  - apply inv. apply left_zero_law_mul_NN.
  - cbn. transitivity (m * n + m).
    * apply commutative_add_NN.
    * cbn. transitivity ((n * m) + m).
      ** now apply (ap (add_NN' m)).
      ** apply inv, left_successor_law_mul_NN.
Defined.

