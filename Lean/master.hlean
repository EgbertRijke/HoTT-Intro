prelude

/-------------------------------------------------------------------------------
  LECTURE 2. Inductive types

-------------------------------------------------------------------------------/

inductive nat.{u} : Type.{u} :=
  | zero : nat
  | succ : nat → nat

print nat.rec
print nat.rec_on

notation `ℕ` := nat

namespace nat

definition add : nat → nat → nat :=
  nat.rec (λ m, m) (λ m (add_m : nat → nat) k, succ (add_m k))

definition mul : nat → nat → nat :=
  nat.rec (λ m, nat.zero) (λ m (mul_m : nat → nat) k, add m (mul_m k))

end nat

inductive unit.{u} : Type.{u} :=
  | tt : unit

notation `𝟙` := unit

namespace unit

definition terminating (A : Type) : A → unit :=
  λ a, unit.tt

end unit

inductive empty.{u} : Type.{u} 

print empty.rec
print empty.rec_on

notation `∅` := empty
notation `𝟘` := empty

definition not (A : Type) := A → ∅

namespace empty

definition initiating (A : Type) : ∅ → A :=
  @empty.rec (λ x, A)

end empty

inductive bool.{u} : Type.{u} :=
  | false : bool
  | true : bool

notation `ℤ₂` := bool
notation `𝟚` := bool

namespace bool

definition taut : bool → Type :=
  bool.rec empty unit

definition or : bool → bool → bool :=
  bool.rec (bool.rec false true) (λ s, true)

definition and : bool → bool → bool :=
  bool.rec (λ b, false) (bool.rec false true)

definition implies : bool → bool → bool :=
  bool.rec (λ b, true) (bool.rec false true)

definition neg : bool → bool :=
  bool.rec true false

definition mul : bool → bool → bool :=
  bool.rec (bool.rec false false) (bool.rec false true)

definition mul_unit : bool := true

definition add : bool → bool → bool :=
  bool.rec (λ b, b) (λ b, neg b)

definition add_unit : bool := false

definition add_inv : bool → bool :=
  λ b, b

end bool

inductive coprod.{u v} (A : Type.{u}) (B : Type.{v}) : Type.{max u v} :=
  | inl : A → coprod A B
  | inr : B → coprod A B

print coprod.inl

definition int : Type :=
  coprod nat (coprod unit nat)

notation `ℤ` := int

namespace int

definition neg : nat → int :=
  @coprod.inl nat (coprod unit nat)

definition zero : int :=
  @coprod.inr nat (coprod unit nat) (@coprod.inl unit nat unit.tt)

definition one : int :=
  @coprod.inr nat (coprod unit nat) (@coprod.inr unit nat nat.zero)

definition neg_one : int :=
  @coprod.inl nat (coprod unit nat) nat.zero

definition pos : nat → int :=
  λ n, @coprod.inr nat (coprod unit nat) (@coprod.inr unit nat n)

definition destruct {P : int → Type} (pneg : Π (n : nat), P (neg n)) 
  (pzero : P zero) (ppos : Π (n : nat), P (pos n))
  : Π (k : int), P k :=
  coprod.rec (λ n, pneg n) (λ l, coprod.rec (λ t, unit.rec pzero t) (λ n, ppos n) l)

definition destruct_full {P : int → Type} 
  (pneg_one : P (neg_one))
  (pneg_succ : Π (n : nat), P (neg n) → P (neg (nat.succ n)))
  (pzero : P zero)
  (ppos_one : P (one))
  (ppos_succ : Π (n : nat), P (pos n) → P (pos (nat.succ n)))
  : Π (k : int), P k :=
  destruct (nat.rec pneg_one pneg_succ) pzero (nat.rec ppos_one ppos_succ)

definition succ : int → int :=
  destruct
    ( nat.rec zero (λ m k, neg m))
    one 
    ( λ n, pos (nat.succ n))

definition pred : int → int :=
  destruct_full
    ( neg (nat.succ nat.zero))
    ( λ n k, neg (nat.succ n))
    neg_one
    zero 
    ( λ m k, pos m)

definition minus : int → int :=
  destruct (λ n, pos n) zero (λ n, neg n)

definition add : int → int → int :=
  destruct_full
    pred
    ( λ m (add_neg_m : int → int) (l : int), pred (add_neg_m l))
    (λ l, l)
    succ
    ( λ m (add_pos_m : int → int) (l : int), succ (add_pos_m l))

-- The additive inverse
definition add_inv : int → int := minus

-- The additive unit
definition add_unit : int := zero

definition mul : int → int → int :=
  destruct_full
    minus
    ( λ m (mul_neg_m : int → int) (l : int), add (neg m) (mul_neg_m l))
    ( λ l, zero)
    ( λ l, l)
    ( λ m (mul_pos_m : int → int) (l : int), add (pos m) (mul_pos_m l))

definition mul_unit : int := one

end int

inductive Sigma.{u v} (A : Type.{u}) (B : A → Type.{v}) : Type.{max u v} :=
  pair : Π (x : A), B x → Sigma A B

definition prod (A : Type) (B : Type) : Type :=
  Sigma A (λ x, B)

namespace prod
  
  definition pair {A : Type} {B : Type} : A → B → prod A B :=
    λ a b, Sigma.pair a b

end prod

namespace Sigma

definition pr1 {A : Type} {B : A → Type} (x : Sigma A B) : A :=
  Sigma.rec (λ a b, a) x

definition pr2 {A : Type} {B : A → Type} (x : Sigma A B) : B (pr1 x) :=
  Sigma.rec (λ a b, b) x

end Sigma

/-------------------------------------------------------------------------------
  LECTURE 3. Identity types

-------------------------------------------------------------------------------/

/--
From the perspective of types as proof-relevant propositions, how should we 
think of \emph{equality} in type theory? Given a type $A$, and two terms 
$x,y:A$, the equality $\id{x}{y}$ should again be a type. Indeed, we want to 
\emph{use} type theory to prove equalities. \emph{Dependent} type theory 
provides us with a convenient setting for this: the equality type $\id{x}{y}$ 
is dependent on $x,y:A$. 

Then, if $\id{x}{y}$ is to be a type, how should we think of the terms of 
$\id{x}{y}$. A term $p:\id{x}{y}$ witnesses that $x$ and $y$ are equal terms of 
type $A$. In other words $p:\id{x}{y}$ is an \emph{identification} of $x$ and 
$y$. In a proof-relevant world, there might be many terms of type $\id{x}{y}$. 
I.e.~there might be many identifications of $x$ and $y$. And, since $\id{x}{y}$ 
is itself a type, we can form the type $\id{p}{q}$ for any two identifications 
$p,q:\id{x}{y}$. That is, since $\id{x}{y}$ is a type, we may also use the type 
theory to prove things \emph{about} identifications (for instance, that two 
given such identifications can themselves be identified), and we may use the 
type theory to perform constructions with them. As we will see shortly, we can 
give every type a groupoid-like structure.

Clearly, the equality type should not just be any type dependent on $x,y:A$. 
Then how do we form the equality type, and what ways are there to use 
identifications in constructions in type theory? The answer to both these 
questions is that we will form the identity type as an \emph{inductive} type, 
generated by just a reflexivity term providing an identification of $x$ to 
itself. The induction principle then provides us with a way of performing 
constructions with identifications, such as concatenating them, inverting them, 
and so on. Thus, the identity type is equipped with a reflexivity term, and 
further possesses the structure that are generated by its induction principle 
and by the type theory. This inductive construction of the identity type is 
elegant, beautifully simple, but far from trivial!

The situation where two terms can be identified in possibly more than one way 
is analogous to the situation in \emph{homotopy theory}, where two points of a 
space can be connected by possibly more than one \emph{path}. Indeed, for any 
two points $x,y$ in a space, there is a \emph{space of paths} from $x$ to $y$. 
Moreover, between any two paths from $x$ to $y$ there is a space of 
\emph{homotopies} between them, and so on. This analogy has been made precise 
by the construction of \emph{homotopical models} of type theory, and it has led 
to the fruitful research area of \emph{synthetic homotopy theory}, the subfield 
of \emph{homotopy type theory} that is the topic of this course.
--/

inductive Id.{l} {A : Type.{l}} (x : A) : A → Type.{l} :=
  refl : Id x x

print Id.refl
print Id.rec
print Id.rec_on

namespace Id

/--
In the following few definitions we establish that any type possesses a 
groupoid-like structure. More precisely, we construct inverses and 
concatenations of paths, and show that the associativity, inverse, and unit 
laws are satisfied.
--/

definition inv {A : Type} {x y : A} (p : Id x y) : Id y x :=
  Id.rec (refl x) p

definition concat {A : Type} {x y : A} (p : Id x y) {z : A} (q : Id y z) 
  : (Id x z) :=
  Id.rec p q

definition assoc {A : Type} {x1 x2 : A} (p : Id x1 x2) {x3 : A} (q : Id x2 x3) 
  {x4 : A} (r : Id x3 x4) 
  : Id (concat (concat p q) r) (concat p (concat q r)) :=
  Id.rec (Id.rec (Id.rec (refl _) p) q) r

definition left_inv {A : Type} {x y : A} (p : Id x y) 
  : Id (concat (inv p) p) (Id.refl y) :=
  Id.rec (refl (refl x)) p 

definition right_inv {A : Type} {x y : A} (p : Id x y) 
  : Id (concat p (inv p)) (Id.refl x) :=
  Id.rec (refl (refl x)) p

definition left_unit {A : Type} {x y : A} (p : Id x y) 
  : Id (concat (refl x) p) p :=
  Id.rec (refl (refl x)) p

definition right_unit {A : Type} {x y : A} (p : Id x y) 
  : Id (concat p (Id.refl y)) p :=
  Id.rec (refl (refl x)) p

/--
Apart from the groupoid operations and laws, the whiskering and unwhiskering
operations are also basic operations of importance. We will need the whiskering
operations, for instance, to establish that the action on paths of a function
respects the groupoid-like structure of types that we established above. The
unwhiskering operations are inverse to the whiskering operations.
--/

definition whisker_left {A : Type} {x y : A} (p : Id x y) {z : A} 
  {q r : Id y z} (u : Id q r) 
  : Id (concat p q) (concat p r) :=
  Id.rec (refl (concat p q)) u

definition whisker_right {A : Type} {x y : A} {p q : Id x y} (u : Id p q) 
  {z : A} (r : Id y z) 
  : Id (concat p r) (concat q r) :=
  Id.rec u r

definition unwhisker_left {A : Type} {x y : A} (p : Id x y) 
  : forall {z : A} {q r : Id y z} (u : Id (concat p q) (concat p r)), Id q r 
  :=
  Id.rec (λ z q r u, concat (inv (left_unit q)) (concat u (left_unit r))) p

definition unwhisker_right {A : Type} {x y : A} {p q : Id x y} {z : A} 
  (r : Id y z) 
  : forall (u : Id (concat p r) (concat q r)), Id p q :=
  Id.rec (λ u, concat (inv (right_unit p)) (concat u (right_unit q))) r

definition inv_con {A : Type} {x y z : A} (p : Id x y) 
  : Π (q : Id y z) (r : Id x z), Id (Id.concat p q) r 
  → Id q (Id.concat (Id.inv p) r) :=
  Id.rec (Id.rec (λ r, Id.rec (Id.refl _))) p

definition con_inv {A : Type} {x y z : A} (p : Id x y) (q : Id y z) 
  (r : Id x z)
  : Id (Id.concat p q) r → Id p (Id.concat r (Id.inv q)) :=
  Id.rec (Id.rec (Id.refl _) q)

definition inv_con' {A : Type} {x y z : A} {p : Id x y} 
  {q : Id y z} {r : Id x z}
  (s : Id r (concat p q)) : Id (concat (inv p) r) q :=
  inv (inv_con p q r (inv s))

definition con_inv' {A : Type} {x y z : A} {p : Id x y} {q : Id y z}
  {r : Id x z} (s : Id r (concat p q)) 
  : Id (concat r (inv q)) p
  :=
  inv (con_inv p q r (inv s))

end Id

/--
Action on paths
--/

definition ap {A B : Type} (f : A → B) {x y : A} (p : Id x y) 
  : Id (f x) (f y) :=
  Id.rec (Id.refl (f x)) p

namespace ap

/-- 
Before we show that ap f preserves the groupoid structure, we show that ap (idfun A) is (pointwise equal to) the identity funcion on Id x y.
--/

definition idfun {A : Type} {x y : A} (p : Id x y) : Id (ap (λ a, a) p) p :=
  Id.rec (Id.refl _) p

definition compose {A B C : Type} (f : A → B) (g : B → C) {x y : A} 
  (p : Id x y)
  : Id (ap (λ x, g (f (x))) p) (ap g (ap f p))
  :=
  Id.rec (Id.refl _) p

definition concat {A B : Type} (f : A → B) {x y : A} (p : Id x y) {z : A} 
  (q : Id y z) 
  : Id (ap f (Id.concat p q)) (Id.concat (ap f p) (ap f q)) :=
  Id.rec (Id.rec (Id.refl (Id.refl (f x))) p) q

definition inv {A B : Type} (f : A → B) {x y : A} (p : Id x y) 
  : Id (ap f (Id.inv p)) (Id.inv (ap f p)) :=
  Id.rec (Id.refl (Id.refl (f x))) p 

/--
The following construction shows that [ap f] respects associativity, in the 
sense that the diagram

  ap f ((p⬝q)⬝r) === (ap f (p⬝q))⬝(ap f r) === ((ap f p)⬝(ap f q))⬝(ap f r)
     ||                                                           ||
     || ap f (assoc p q r)       assoc (ap f p) (ap f q) (ap f r) ||
     ||                                                           ||
  ap f (p⬝(q⬝r)) === (ap f p)⬝(ap f (q⬝r)) === (ap f p)⬝((ap f q)⬝(ap f r))

commutes. Unsurprisingly, the structure of the proof is exactly the same as 
that for the proof of associativity of path concatenation.
--/

definition assoc {A B : Type} (f : A → B) {x1 x2 : A} (p : Id x1 x2) {x3 : A} 
  (q : Id x2 x3) {x4 : A} (r : Id x3 x4) 
  : Id ( Id.concat 
         ( Id.concat 
           ( concat f (Id.concat p q) r) 
           ( Id.whisker_right (concat f p q) (ap f r))
         ) 
         ( Id.assoc (ap f p) (ap f q) (ap f r))
       ) 
       ( Id.concat
         ( ap (@ap _ _ f x1 x4) (Id.assoc p q r))
         ( Id.concat 
           ( concat f p (Id.concat q r)) 
           ( Id.whisker_left (ap f p) (concat f q r))
         )
       ) :=
  Id.rec (Id.rec (Id.rec (Id.refl _) p) q) r

/--
  ap f (p⁻¹ ⬝ p) ======================== ap f (refl y) 
    ||                                           ||
    || ap.concat f p⁻¹ p    Id.left_inv (ap f p) ||
    ||                                           || 
  (ap f p⁻¹) ⬝ (ap f p) ========= (ap f p)⁻¹ ⬝ (ap f p)
--/

definition left_inv {A B : Type} (f : A → B) {x y : A} (p : Id x y)
  : Id ( ap (@ap _ _ f y y) (Id.left_inv p))
     ( Id.concat
       ( Id.concat
         ( concat f (Id.inv p) p)
         ( Id.whisker_right (inv f p) (ap f p)) 
       )
       ( Id.left_inv (ap f p))
     ) :=
  Id.rec (Id.refl _) p

definition right_inv {A B : Type} (f : A → B) {x y : A} (p : Id x y)
  : Id ( ap (@ap _ _ f x x) (Id.right_inv p))
     ( Id.concat
       ( Id.concat
         ( concat f p (Id.inv p))
         ( Id.whisker_left (ap f p) (inv f p))
       )
       ( Id.right_inv (ap f p))
     ) :=
  Id.rec (Id.refl _) p

definition left_unit {A B : Type} (f : A → B) {x y : A} (p : Id x y)
  : Id ( ap (@ap _ _ f x y) (Id.left_unit p))
     ( Id.concat
       ( concat f (Id.refl x) p)
       ( Id.left_unit (ap f p))
     ) :=
  Id.rec (Id.refl _) p

definition right_unit {A B : Type} (f : A → B) {x y : A} (p : Id x y)
  : Id ( ap (@ap _ _ f x y) (Id.right_unit p))
     ( Id.concat
       ( concat f p (Id.refl y))
       ( Id.right_unit (ap f p))
     ) :=
  Id.rec (Id.refl _) p

/--
In the following construction we show that ap f respects whiskering. In the 
case of left whiskering this amounts to showing that the following diagram
commutes.

                         ap (ap f) (wh_l p u)
  ap f (p ⬝ q) ======================================= ap f (p ⬝ r)
    ||                                                     ||
    || ap.concat f p q                     ap.concat f p r ||
    ||                                                     ||
  (ap f p) ⬝ (ap f q) ============================ (ap f p) ⬝ (ap f r)
                      wh_l (ap f p) (ap (ap f) u)
--/

definition whisker_left {A B : Type} (f : A → B) {x y : A} (p : Id x y) {z : A}
  {q r : Id y z} (u : Id q r)
  : Id ( Id.concat 
         ( ap (@ap _ _ f x z) (Id.whisker_left p u))
         ( concat f p r)
       )
       ( Id.concat
         ( concat f p q)
         ( Id.whisker_left (ap f p) (ap (@ap _ _ f y z) u))
       )
  :=
  Id.rec (Id.rec (Id.rec (Id.refl _) p) q) u

definition whisker_right {A B : Type} (f : A → B) {x y : A} {p q : Id x y} 
  (u : Id p q) {z : A} (r : Id y z)
  : Id ( Id.concat
         ( ap (@ap _ _ f x z) (Id.whisker_right u r))
         ( concat f q r)
       )
       ( Id.concat
         ( concat f p r)
         ( Id.whisker_right (ap (@ap _ _ f x y) u) (ap f r))
       ) 
  :=
  Id.rec (Id.rec (Id.rec (Id.refl _) p) u) r

end ap

/--
Homotopies are pointwise identifications of functions. That is, we say that two 
functions are \emph{homotopic} if we can construct a pointwise identification 
between them. Just like identifications, there is a reflexivity homotopy, and 
homotopies can be inverted, concatenated, and satisfy the groupoid laws that we 
established earlier for the identity type. However, these laws are only
satisfied up to homotopy.
--/

definition homotopy {A : Type} {B : A → Type} (f g : forall x, B x) 
  : Type :=
  forall x, Id (f x) (g x)

namespace htpy

definition refl {A : Type} {B : A → Type} (f : forall x, B x) 
  : homotopy f f :=
  λ x, Id.refl (f x)

definition inv {A : Type} {B : A → Type} {f g : forall x, B x} 
  (H : homotopy f g) 
  : homotopy g f :=
  λ x, Id.inv (H x)

definition concat {A : Type} {B : A → Type} {f g h : forall x, B x} 
  (H : homotopy f g) (K : homotopy g h) 
  : homotopy f h :=
  λ x, Id.concat (H x) (K x)

definition assoc {A : Type} {B : A → Type} {f1 f2 f3 f4 : forall x, B x} 
  (H : homotopy f1 f2) (K : homotopy f2 f3) (L : homotopy f3 f4) 
  : homotopy (concat (concat H K) L) (concat H (concat K L)) :=
  λ x, Id.assoc (H x) (K x) (L x)

definition left_inv {A : Type} {B : A → Type} {f g : forall x, B x} 
  (H : homotopy f g) 
  : homotopy (concat (inv H) H) (refl g) :=
  λ x, Id.left_inv (H x)

definition right_inv {A : Type} {B : A → Type} {f g : forall x, B x} 
  (H : homotopy f g) 
  : homotopy (concat H (inv H)) (refl f) :=
  λ x, Id.right_inv (H x)

definition left_unit {A : Type} {B : A → Type} {f g : forall x, B x} 
  (H : homotopy f g) 
  : homotopy (concat (refl f) H) H :=
  λ x, Id.left_unit (H x)

definition right_unit {A : Type} {B : A → Type} {f g : forall x, B x} 
  (H : homotopy f g) 
  : homotopy (concat H (refl g)) H :=
  λ x, Id.right_unit (H x)

definition whisker_left {A B C : Type} {f g : A → B} (h : B → C) 
  (H : homotopy f g)  
  : homotopy (λ x, h (f (x))) (λ x, h (g (x))) :=
  λ x, ap h (H x)

definition whisker_right {A B C : Type} {g h : B → C} (H : homotopy g h) 
  (f : A → B)
  : homotopy (λ x, g (f (x))) (λ x, h (f (x))) :=
  λ x, H (f x)

/--
The naturality of homotopies is the construction that for each homotopy 
H : f ~ g and each p : x = y, the square

             H x
        f x ===== g x 
         ||       ||
  ap f p ||       || ap g p
         ||       ||
        f y ===== g y
             H y

commutes.
--/

definition natural {A B : Type} {f g : A → B} (H : homotopy f g) {x y : A} 
  (p : Id x y) 
  : Id (Id.concat (H x) (ap g p)) (Id.concat (ap f p) (H y)) :=
  Id.rec (Id.concat (Id.right_unit (H x)) (Id.inv (Id.left_unit (H x)))) p

end htpy

/--
Next, we show that type families behave analogous to fibrations in homotopy 
theory. That is, we construct the transport function, that lets us transport a 
term from one fiber to another over an identification in the base type. 
Moreover, we construct a \emph{path lifting} operation, that lifts an 
identification in the base type to an identification in the dependent pair 
type, starting at any given point in the fiber.
--/

definition transport {A : Type} {B : A → Type} {x y : A} (p : Id x y) 
  : B x → B y :=
  Id.rec (λ b, b) p

namespace tr

definition refl {A : Type} {B : A → Type} (x : A) : B x → B x :=
  λ b, b

definition concat_compute {A : Type} {B : A → Type} {x y : A} (p : Id x y) {z : A} 
  (q : Id y z) 
  : B x → B z :=
  λ b, transport q (transport p b)

definition concat {A : Type} {B : A → Type} {x y : A} (p : Id x y) 
  {z : A} (q : Id y z)
  : homotopy (concat_compute p q) (transport (Id.concat p q)) :=
  Id.rec (Id.rec (λ (b : B x), Id.refl _) p) q

definition inv_compute {A : Type} {B : A → Type} {x y : A} (p : Id x y)  
  : B y → B x :=
  Id.rec (λ b, b) p

definition inv {A : Type} {B : A → Type} {x y : A} (p : Id x y) 
  : homotopy (inv_compute p) (transport (Id.inv p)) :=
  Id.rec (λ (b : B x), Id.refl b) p

definition assoc {A : Type} {B : A → Type} {x1 x2 : A} (p : Id x1 x2) 
  {x3 : A} (q : Id x2 x3) {x4 : A} (r : Id x3 x4) 
  : homotopy (concat_compute (Id.concat p q) r) 
             (concat_compute p (Id.concat q r)) :=
  Id.rec (Id.rec (Id.rec (λ (b : B x1), Id.refl _) p) q) r

definition fun_rel {A B : Type} (f : A → B) {x y : A} (p : Id x y) {b : B}
  (q : Id (f x) b) : Id (transport p q) (Id.concat (Id.inv (ap f p)) q) :=
  Id.rec (Id.rec (Id.refl _) p) q

definition fun_rel' {A B : Type} (f : A → B) {x y : A} (p : Id x y) {b : B}
  (q : Id b (f x)) : Id (transport p q) (Id.concat q (ap f p)) :=
  Id.rec (Id.rec (Id.refl _) p) q
  

end tr

definition apd {A : Type} {B : A → Type} (f : forall x, B x) {x y : A} 
  (p : Id x y) 
  : Id (transport p (f x)) (f y) :=
  Id.rec (Id.refl (f x)) p

namespace square
/--
When we make constructions of higher identities, we soon run into commuting 
squares. A square

       ptop  
  x00 ====== x01
   ||         ||
   || pleft   || pright
   ||         ||
  x10 ====== x11
       pbot

is said to commute, if we can construct an identification of type

  Id (Id.concat ptop pright) (Id.concat pleft pbot).

Some basic manipulations on commuting squares include the whiskering 
operations.
--/

definition whisker_top {A : Type} {x00 x01 x10 x11 : A}
  {ptop ptop' : Id x00 x01} (q : Id ptop ptop')
  : Π {pright : Id x01 x11} {pleft : Id x00 x10} {pbot : Id x10 x11}
  (sq : Id (Id.concat ptop pright) (Id.concat pleft pbot)),
  Id (Id.concat ptop' pright) (Id.concat pleft pbot)
  :=
  Id.rec (λ pright pleft pbot sq, sq) q

definition whisker_right {A : Type} {x00 x01 x10 x11 : A} 
  {ptop : Id x00 x01} 
  {pright pright' : Id x01 x11} (q : Id pright pright') 
  
  : forall {pleft : Id x00 x10} {pbot : Id x10 x11}, 
  Id (Id.concat ptop pright) (Id.concat pleft pbot) 
  → Id (Id.concat ptop pright') (Id.concat pleft pbot)
  :=
  Id.rec (λ pw ps sq, sq) q

definition whisker_left {A : Type} {x00 x01 x10 x11 : A}
  {ptop : Id x00 x01}
  {pright : Id x01 x11}
  {pleft pleft' : Id x00 x10} (q : Id pleft pleft')
  : Π {pbot : Id x10 x11}, 
    Id (Id.concat ptop pright) (Id.concat pleft pbot)
    → Id (Id.concat ptop pright) (Id.concat pleft' pbot) :=
  Id.rec (λ pbot sq, sq) q

definition whisker_bot {A : Type} {x00 x01 x10 x11 : A}
  {ptop : Id x00 x01}
  {pright : Id x01 x11}
  {pleft : Id x00 x10}
  {pbot pbot' : Id x10 x11} (q : Id pbot pbot')
  : Id (Id.concat ptop pright) (Id.concat pleft pbot)
    → Id (Id.concat ptop pright) (Id.concat pleft pbot') :=
  Id.rec (λ sq, sq) q

end square

namespace int
/--
We prove some basic properties of operations on the integers
--/

/--
definition pred_neg_succ : Π (n : nat), Id (pred (neg n)) (neg (nat.succ n)) :=
  nat.rec (Id.refl _) (λ n p, _)

definition pred_is_retr : homotopy (λ k, pred (succ k)) (λ k, k) :=
  destruct_full
    (Id.refl _)
    (λ n p, Id.concat _ (ap pred p))
    _
    _
    _

definition assoc_add 
  : Π (k l m : int), Id (add k (add l m)) (add (add k l) m) :=
  int.destruct 
    ( nat.rec 
      ( int.destruct 
        ( nat.rec 
          ( int.destruct 
            ( nat.rec (Id.refl _) 
              ( λ m assoc_negk_negl_negm, ap pred assoc_negk_negl_negm)
            ) 
            ( unit.rec (Id.refl _) unit.tt) 
            ( nat.rec (Id.refl _)
              ( λ m assoc_negk_negl_posm, _)
            )
          ) 
          _
        ) 
        _ _
      )
      ( _)
    ) 
    ( _)
    ( _)

--/

end int

-- Exercise
definition retraction_swap {A B : Type} {i : A → B} {r : B → A} 
  (H : homotopy (λ x, r (i x)) (λ x, x)) (a : A) 
  : Id (H (r (i a))) (htpy.whisker_left (λ x, r (i x)) H a)  :=
  Id.unwhisker_right 
    ( H a) 
    ( square.whisker_right 
      ( ap.idfun (H a)) 
      ( htpy.natural H (H a))
    )

definition retraction_precompose {A B : Type} {P : A → Type} {i : A → B} 
  {r : B → A} (H : homotopy (λ x, r (i x)) (λ x, x)) (K : Π (b : B), P (r b)) 
  (a : A) : P a :=
  transport (H a) (K (i a))

/-------------------------------------------------------------------------------
  LECTURE 4. Equivalences

-------------------------------------------------------------------------------/

definition has_retraction {A B : Type} (i : A → B) : Type :=
  Sigma (B → A) (λ r, homotopy (λ x, r (i x)) (λ x, x))

definition has_section {A B : Type} (p : B → A) : Type :=
  Sigma (A → B) (λ s, homotopy (λ x, p (s x)) (λ x, x))

definition is_equiv {A B : Type} (f : A → B) : Type :=
  prod (has_retraction f) (has_section f)

namespace is_equiv

definition construct {A B : Type} {f : A → B}
  : Π (f_linv : B → A) (f_islinv : homotopy (λ x, f_linv (f x)) (λ x, x))
      (f_rinv : B → A) (f_isrinv : homotopy (λ y, f (f_rinv y)) (λ y, y)),
    is_equiv f :=
  λ h H g G, Sigma.pair (Sigma.pair h H) (Sigma.pair g G)

definition destruct {A B : Type} {f : A → B} {P : is_equiv f → Type}
  : (Π (h : B → A) (is_retraction : homotopy (λ x, h (f x)) (λ x, x))
       (g : B → A) (is_section : homotopy (λ y, f (g y)) (λ y, y)),
       P (construct h is_retraction g is_section))
  → Π (E : is_equiv f), P E :=
  λ F, Sigma.rec 
    ( Sigma.rec 
      ( λ h is_retraction, Sigma.rec
        ( λ g is_section, F h is_retraction g is_section)
      )
    )

end is_equiv

definition equiv (A B : Type) : Type := Sigma (A → B) (λ f, is_equiv f)

definition invertible {A B : Type} (f : A → B) : Type :=
  Sigma 
    (B → A) 
    (λ g, prod 
            (homotopy (λ y, f (g y)) (λ y, y)) 
            (homotopy (λ x, g (f x)) (λ x, x))
    )

namespace invertible

definition construct {A B : Type} {f : A → B} (g : B → A) 
  (is_section : homotopy (λ y, f (g y)) (λ y, y)) 
  (is_retraction : homotopy (λ x, g (f x)) (λ x, x)) 
  : invertible f := 
  Sigma.pair g (prod.pair is_section is_retraction)

definition destruct {A B : Type} {f : A → B} {P : invertible f → Type}
  (D : Π (g : B → A) (is_sec : homotopy (λ y, f (g y)) (λ y, y))
       ( is_retr : homotopy (λ x, g (f x)) (λ x, x)), 
       P (construct g is_sec is_retr))
  : Π (I : invertible f), P I :=
  Sigma.rec (λ g, Sigma.rec (λ h k, D g h k))

end invertible

definition is_equiv_idfun (A : Type) : is_equiv (λ (x : A), x) :=
  is_equiv.construct (λ x, x) (htpy.refl _) (λ x, x) (htpy.refl _)

definition is_equiv_of_invertible {A B : Type} (f : A → B) 
  : invertible f → is_equiv f :=
  invertible.destruct 
    ( λ g is_sec is_retr, is_equiv.construct g is_retr g is_sec) 

definition invertible_of_is_equiv {A B : Type} (f : A → B) 
  : is_equiv f → invertible f :=
  is_equiv.destruct 
    ( λ h is_retr g is_sec,
      ( invertible.construct g is_sec
        ( λ x, Id.concat 
          ( Id.inv (is_retr (g (f x)))) 
          ( Id.concat (ap h (is_sec (f x))) (is_retr x))
        )
      )  
    )

-- Exercise
definition is_equiv_of_htpy {A B : Type} {f g : A → B} 
  : (homotopy f g) → is_equiv g → is_equiv f :=
  λ H, is_equiv.destruct
    ( λ g_linv g_islinv g_rinv g_isrinv, is_equiv.construct 
      ( g_linv) 
      ( htpy.concat (htpy.whisker_left g_linv H) g_islinv)
      (  g_rinv)
      ( htpy.concat (htpy.whisker_right H g_rinv) g_isrinv)
    )

-- Exercise
definition equiv_compose {A B C : Type} {f : A → B} {g : B → C} {h : A → C} 
  {H : homotopy h (λ x, g (f x))}
  : is_equiv f → is_equiv g → is_equiv h :=
  is_equiv.destruct
    ( λ f_linv f_islinv f_rinv f_isrinv, is_equiv.destruct 
      ( λ g_linv g_islinv g_rinv g_isrinv, is_equiv_of_htpy H
        ( is_equiv.construct
          (λ z, f_linv (g_linv z)) 
          ( htpy.concat 
            ( htpy.whisker_right (htpy.whisker_left f_linv g_islinv) f) 
            ( f_islinv)
          )
          (λ z, f_rinv (g_rinv z)) 
          ( htpy.concat 
            ( htpy.whisker_right (htpy.whisker_left g f_isrinv) g_rinv) 
            ( g_isrinv)
          )
        )
      )
    )

definition inv_of_is_equiv {A B : Type} {e : A → B} 
  : is_equiv e → (B → A) :=
  is_equiv.destruct (λ h is_retr g is_sec, g)

definition inv_of_invertible {A B : Type} {f : A → B}
  : invertible f → (B → A) :=
  invertible.destruct (λ g is_sec is_retr, g)

definition invertible_inv_of_invertible {A B : Type} {f : A → B}
  : Π (I : invertible f), invertible (inv_of_invertible I) :=
  invertible.destruct 
    ( λ g is_sec is_retr, invertible.construct f is_retr is_sec)

definition is_equiv_equiv_inv {A B : Type} {e : A → B} 
  : Π (H : is_equiv e), is_equiv (inv_of_is_equiv H) :=
  λ H, is_equiv_of_htpy 
    ( λ y, is_equiv.destruct ( λ h is_retr g is_sec, (Id.refl _)) H) 
    ( is_equiv_of_invertible _ 
      ( invertible_inv_of_invertible (invertible_of_is_equiv e H))
    )

/--
definition equiv_3for2_left {A B C : Type} {f : A → B} {g : B → C} {h : A → C} 
  {H : homotopy h (λ x, g (f x))}
  : is_equiv f → is_equiv h → is_equiv g :=
  is_equiv.destruct 
    ( λ fl is_retr fr is_sec, is_equiv.destruct
      ( λ hl is_retr hr is_sec, is_equiv.construct 
        _
        _
        _
        _
      )
    )
--/

namespace Sigma

definition eta {A : Type} {B : A → Type} 
  : Π (x : Sigma A B), Id x (pair (pr1 x) (pr2 x)) :=
  Sigma.rec (λ a b, Id.refl _)

/--
In the following we construct an equivalence computing the identity type of a Σ-type. 

--/

definition eq_of_pair {A : Type} {B : A → Type} {u v : Sigma A B}
  : Sigma (Id (pr1 u) (pr1 v)) 
          (λ p, Id (transport p (pr2 u)) (pr2 v)) 
  → Id u v :=
  Sigma.rec 
    ( λ y q, Sigma.rec 
      ( λ x p, Sigma.rec 
        ( λ bpath fpath, Id.rec (Id.rec (Id.refl _) bpath) fpath
        )
      ) u
    ) v

definition pair_of_eq {A : Type} {B : A → Type} (x y : Sigma A B)
  : (Id x y)
  → Sigma (Id (pr1 x) (pr1 y))
    (λ u, Id (transport u (pr2 x)) (pr2 y)) :=
  Id.rec (pair (Id.refl _) (Id.refl _))

definition base_path {A : Type} {B : A → Type} {x y : Sigma A B}
  : Id x y → Id (pr1 x) (pr1 y) :=
  λ p, pr1 (pair_of_eq _ _ p)

definition fiber_path {A : Type} {B : A → Type} {x y : Sigma A B}
  : Π (p : Id x y), Id (transport (base_path p) (pr2 x)) (pr2 y)
  :=
  λ p, pr2 (pair_of_eq _ _ p)

definition pair_of_eq_invertible {A : Type} {B : A → Type} (x y : Sigma A B) : invertible (pair_of_eq x y) :=
  invertible.construct
    ( eq_of_pair)
    ( Sigma.rec 
      ( Sigma.rec 
        (λ a b a' b' u, 
          Sigma.rec
            ( λ p q, Id.rec (Id.rec (Id.refl _) p) q) u) 
        x) y)
    ( Id.rec (Sigma.rec (Sigma.rec (λ a b a' b', Id.refl _) x) y))

definition pair_of_eq_is_equiv {A : Type} {B : A → Type} (x y : Sigma A B)
  : is_equiv (pair_of_eq x y) :=
  is_equiv_of_invertible (pair_of_eq x y) (pair_of_eq_invertible _ _)

end Sigma

definition is_contr (A : Type) : Type := Sigma A (λ a, Π (x : A), Id a x)

namespace is_contr

definition center {A : Type} (H : is_contr A) : A := Sigma.pr1 H

definition contraction {A : Type} (H : is_contr A) : homotopy (λ x, center H) (λ x, x) := 
  λ x, Sigma.pr2 H x

definition construct {A : Type} (a : A) (H : homotopy (λ x, a) (λ x, x))
  : is_contr A :=
  Sigma.pair a H

definition destruct {A : Type} {P : is_contr A → Type}
  (D : Π (a : A) (H : homotopy (λ x, a) (λ x, x)), P (construct a H))
  : Π (c : is_contr A), P c :=
  Sigma.rec D

end is_contr

definition is_contr_unit : is_contr unit :=
  Sigma.pair unit.tt (unit.rec (Id.refl _))

-- Exercise
definition is_contr_of_retr {A B : Type} (i : A → B) (r : B → A) 
  (H : homotopy (λ x, r (i x)) (λ x, x)) 
  : is_contr B → is_contr A :=
  is_contr.destruct 
    ( λ b q, is_contr.construct (r b) (λ x, Id.concat (ap r (q (i x))) (H x)))

-- Exercise
definition is_contr_of_equiv {A B : Type}
  : equiv A B → is_contr B → is_contr A :=
  Sigma.rec (λ e, Sigma.rec (Sigma.rec (λ r H T, is_contr_of_retr e r H)))

-- Exercise
definition is_contr_of_equiv' {A B : Type}
  : equiv A B → is_contr A → is_contr B :=
  Sigma.rec (λ e, Sigma.rec (λ T, Sigma.rec (λ i H, is_contr_of_retr i e H)))

definition fiber {A B : Type} (f : A → B) (b : B) := Sigma A (λ a, Id (f a) b)

definition fiber' {A B : Type} (f : A → B) (b : B) := Sigma A (λ a, Id b (f a))

namespace map

definition is_contr {A B : Type} (f : A → B) : Type := 
  Π (b : B), is_contr (fiber f b)

end map

definition is_equiv_of_is_contr {A B : Type} (f : A → B) 
  : map.is_contr f → is_equiv f :=
  λ H, is_equiv_of_invertible f 
    ( invertible.construct
      (λ b, Sigma.pr1 (is_contr.center (H b)))
      (λ b, Sigma.pr2 (is_contr.center (H b)))
      (λ a, @Sigma.base_path _ _ _ 
              ( Sigma.pair a (Id.refl (f a))) 
              ( is_contr.contraction (H (f a)) _))
    )

definition is_contr_of_invertible {A B : Type} (f : A → B)
  : invertible f → map.is_contr f :=
  invertible.destruct
    ( λ g is_section is_retraction b, is_contr.construct 
      ( Sigma.pair (g b) 
        ( Id.concat 
          ( Id.inv (ap (λ x, f (g x)) (is_section b))) 
          ( Id.concat (ap f (is_retraction (g b))) (is_section b))
        )
      )
      ( Sigma.rec 
        ( λ a, Id.rec 
          ( Sigma.eq_of_pair 
            ( Sigma.pair 
              ( is_retraction a) 
              ( Id.concat 
                ( tr.fun_rel _ _ _) 
                ( Id.inv_con'
                  ( Id.concat 
                    ( Id.inv_con' 
                      ( Id.inv
                        ( square.whisker_top 
                          ( retraction_swap is_section (f a)) 
                          ( square.whisker_left 
                            ( Id.inv 
                              ( ap (ap f) 
                                ( retraction_swap is_retraction a)
                              )
                            )
                            ( square.whisker_left 
                              ( ap.compose _ _ _) 
                              ( htpy.natural _ _)
                            )
                          )
                        )
                      )
                    ) 
                    ( Id.inv (Id.right_unit _))
                  ) 
                )
              )
            )
          )
        )
      )
    )

definition is_contr_of_is_equiv {A B : Type} (f : A → B)
  : is_equiv f → map.is_contr f :=
  λ H, is_contr_of_invertible f (invertible_of_is_equiv f H)

definition is_contr_idfun {A : Type} : map.is_contr (λ (x : A), x) :=
  is_contr_of_is_equiv (λ x, x) (is_equiv_idfun A)

definition is_contr_total_path {A : Type}
  : Π (a : A), is_contr (Sigma A (λ x, Id x a)) :=
  is_contr_idfun

/-------------------------------------------------------------------------------
  LECTURE 5. The fundamental theorem

-------------------------------------------------------------------------------/

definition fmap {A : Type} (B C : A → Type) : Type := Π (x : A), B x → C x

definition fmap_natural {A : Type} {B C : A → Type} (f : fmap B C) {x y : A}
  : Π (p : Id x y) (b : B x), 
    Id (f y (transport p b)) (transport p (f x b))
  := Id.rec (λ b, Id.refl _)

definition total {A : Type} {B C : A → Type} (f : Π (x : A), B x → C x)
  : Sigma A B → Sigma A C :=
  Sigma.rec (λ a b, Sigma.pair a (f a b))

definition fib_total_of_fib_fmap {A : Type} {B C : A → Type} 
  (f : fmap B C) (a : A) (c : C a)
  : fiber (f a) c → fiber (total f) (Sigma.pair a c) :=
  Sigma.rec
    ( λ b p, Sigma.pair 
      ( Sigma.pair a b) 
      ( Sigma.eq_of_pair (Sigma.pair (Id.refl a) p))
    )

definition fib_fmap_of_fib_total {A : Type} {B C : A → Type} 
  (f : fmap B C) (a : A) (c : C a)
  : fiber (total f) (Sigma.pair a c) → fiber (f a) c :=
  Sigma.rec
    ( Sigma.rec 
      ( λ x b p, Sigma.pair 
        ( transport (Sigma.base_path p) b)
        ( Id.concat (fmap_natural f _ _) (Sigma.fiber_path p) )
      )
    )

definition fib_total_is_retr {A : Type} {B C : A → Type} {f : fmap B C} {a : A}
  {c : C a}
  : homotopy 
     ( λ x, fib_fmap_of_fib_total f a c (fib_total_of_fib_fmap f a c x)) 
     ( λ x, x) :=
  Sigma.rec
    ( λ b, Id.rec (Sigma.eq_of_pair (Sigma.pair (Id.refl _) (Id.refl _))))

/--
definition fib_total_is_sec {A : Type} {B C : A → Type} {f : fmap B C} {a : A}
  {c : C a}
  : homotopy
      ( λ x, fib_total_of_fib_fmap f a c (fib_fmap_of_fib_total f a c x))
      ( λ x, x) :=
  Sigma.rec
    ( λ b, (retraction_precompose _ _)
    )
--/
