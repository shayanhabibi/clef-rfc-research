From Stdlib Require Import List ZArith QArith Qpower String Bool Lia.
Import ListNotations.

(**md # Measures

A measure such as `km/h` is a product of named units raised to integer powers. This module gives
measures a representation, says when two of them are equal, and proves the two facts the rest of
the RFC stands on:

- equality of measures can be computed, and
- a quantity defined unit by unit, such as a conversion factor, has the same value on equal
  measures.

Nothing here is specific to conversion. The module assumes nothing: a unit is named by an
identifier, and identifiers have a computed equality.
*)

(**md ## Representation *)

(** The name of a declared unit, such as `m` or `km`. *)
Definition uname : Type := string.

(** A measure: a list of units with integer exponents. `km/h` is `[(km, 1); (h, -1)]`. A unit may
    appear more than once, and the order carries no meaning. *)
Definition measure : Type := list (uname * Z).

(** Equality of unit names, as a computed test. *)
Definition ueqb (u v : uname) : bool := String.eqb u v.

(** The computed test agrees with equality. *)
Lemma ueqb_iff (u v : uname) : ueqb u v = true <-> u = v.
Proof.
  apply String.eqb_eq.
Qed.

(** A unit name equals itself under the computed test. *)
Lemma ueqb_refl (u : uname) : ueqb u u = true.
Proof.
  apply ueqb_iff. reflexivity.
Qed.

Open Scope Z_scope.

(** The total exponent of one unit in a measure.
    - [m:] the measure.
    - [u:] the unit. *)
Fixpoint expo (m : measure) (u : uname) : Z :=
  match m with
  | [] => 0
  | (v, z) :: r => (if ueqb v u then z else 0) + expo r u
  end.

(** Two measures are equal when every unit has the same total exponent in both. This is equality
    in the free abelian group on unit names, so `m/s`, `s^-1 m` and `m s / s^2` are equal. *)
Definition meq (a b : measure) : Prop := forall u, expo a u = expo b u.

(** The dimensionless measure, written `1`. *)
Definition mone : measure := [].

(** The product of two measures. *)
Definition mmul (a b : measure) : measure := a ++ b.

(** A measure raised to an integer power.
    - [k:] the power. *)
Definition mpow (k : Z) (m : measure) : measure := map (fun p => (fst p, k * snd p)) m.

(** The reciprocal of a measure. *)
Definition minv (m : measure) : measure := mpow (-1) m.

(** The quotient of two measures. *)
Definition mdiv (a b : measure) : measure := mmul a (minv b).

(**md ## The group laws *)

(** The exponent of a unit in a product is the sum of its exponents. *)
Lemma expo_mul (a b : measure) (u : uname) : expo (mmul a b) u = expo a u + expo b u.
Proof.
  unfold mmul. induction a as [| [v z] a IH]; simpl; [reflexivity | rewrite IH; lia].
Qed.

(** The exponent of a unit in a power is the power times its exponent. *)
Lemma expo_pow (k : Z) (m : measure) (u : uname) : expo (mpow k m) u = k * expo m u.
Proof.
  induction m as [| [v z] m IH]; simpl; [lia |].
  rewrite IH. destruct (ueqb v u); lia.
Qed.

(** Equality of measures is reflexive. *)
Lemma meq_refl (a : measure) : meq a a.
Proof.
  intro u. reflexivity.
Qed.

(** Equality of measures is symmetric. *)
Lemma meq_sym (a b : measure) : meq a b -> meq b a.
Proof.
  intros H u. symmetry. apply H.
Qed.

(** Equality of measures is transitive. *)
Lemma meq_trans (a b c : measure) : meq a b -> meq b c -> meq a c.
Proof.
  intros H1 H2 u. rewrite H1. apply H2.
Qed.

(** Products of equal measures are equal. *)
Lemma mmul_meq (a a' b b' : measure) : meq a a' -> meq b b' -> meq (mmul a b) (mmul a' b').
Proof.
  intros Ha Hb u. rewrite !expo_mul, Ha, Hb. reflexivity.
Qed.

(** Powers of equal measures are equal. *)
Lemma mpow_meq (k : Z) (a a' : measure) : meq a a' -> meq (mpow k a) (mpow k a').
Proof.
  intros Ha u. rewrite !expo_pow, Ha. reflexivity.
Qed.

(**md
**Measures form an abelian group under this equality.**

The product is associative and commutative, `1` is its identity, and every measure cancels against
its reciprocal. These are the laws the specification's measure arithmetic relies on, and they hold
for the representation used here.
*)
Theorem measure_group_laws (a b c : measure) :
  meq (mmul (mmul a b) c) (mmul a (mmul b c)) /\
  meq (mmul a b) (mmul b a) /\
  meq (mmul mone a) a /\
  meq (mmul a (minv a)) mone.
Proof.
  repeat split; intro u; unfold minv, mone; rewrite ?expo_mul, ?expo_pow; cbn [expo]; lia.
Qed.

(**md ## Equality is computed *)

(** The unit names a measure mentions. *)
Definition units (m : measure) : list uname := map fst m.

(** A unit a measure does not mention has exponent zero in it. *)
Lemma expo_absent (m : measure) (u : uname) : ~ In u (units m) -> expo m u = 0.
Proof.
  induction m as [| [v z] m IH]; simpl; [reflexivity |].
  intro N. destruct (ueqb v u) eqn:E.
  - apply ueqb_iff in E. exfalso. apply N. left. exact E.
  - rewrite IH; [reflexivity |]. intro H. apply N. right. exact H.
Qed.

(** Equality of measures as a computed test: compare the exponent of every unit either mentions. *)
Definition meqb (a b : measure) : bool :=
  forallb (fun u => expo a u =? expo b u) (units (a ++ b)).

(**md
**Equality of measures is decidable.**

The test compares exponents over the finitely many units the two measures mention. It answers
`true` exactly when the measures are equal, so the compiler can decide whether two annotations
name the same measure however they are written.
*)
Theorem meqb_iff (a b : measure) : meqb a b = true <-> meq a b.
Proof.
  unfold meqb. rewrite forallb_forall. split.
  - intros H u. destruct (in_dec string_dec u (units (a ++ b))) as [I | N].
    + apply Z.eqb_eq. apply H. exact I.
    + unfold units in N. rewrite map_app in N.
      rewrite !expo_absent; [reflexivity | |]; intro I; apply N; apply in_or_app; auto.
  - intros H u _. apply Z.eqb_eq. apply H.
Qed.

(**md ## Quantities defined unit by unit

A conversion factor is defined by giving each unit a number and multiplying through the measure.
A dimension is defined by giving each unit an exponent vector and adding through the measure. Both
must give the same answer on equal measures, or they would depend on how an annotation is spelled.

The proof removes one unit at a time: a measure in which every unit has exponent zero is shown to
have the neutral value by induction on its length.
*)

(** A measure with every entry for one unit removed. *)
Definition remove (u : uname) (m : measure) : measure :=
  filter (fun p => negb (ueqb (fst p) u)) m.

(** The removed unit has exponent zero in what is left. *)
Lemma expo_remove_same (u : uname) (m : measure) : expo (remove u m) u = 0.
Proof.
  induction m as [| [v z] m IH]; simpl; [reflexivity |].
  destruct (ueqb v u) eqn:E; simpl; [exact IH | rewrite E, IH; reflexivity].
Qed.

(** Removing one unit leaves the exponent of every other unit unchanged. *)
Lemma expo_remove_other (u v : uname) (m : measure) :
  v <> u -> expo (remove u m) v = expo m v.
Proof.
  intro N. induction m as [| [w z] m IH]; simpl; [reflexivity |].
  destruct (ueqb w u) eqn:E; simpl.
  - apply ueqb_iff in E. subst w. destruct (ueqb u v) eqn:F.
    + apply ueqb_iff in F. congruence.
    + rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** Removing a unit does not lengthen a measure. *)
Lemma length_remove (u : uname) (m : measure) : (List.length (remove u m) <= List.length m)%nat.
Proof.
  apply filter_length_le.
Qed.

(** The sum through a measure of a number given to each unit, weighted by exponent.
    - [g:] the number given to each unit. *)
Fixpoint lin (g : uname -> Z) (m : measure) : Z :=
  match m with
  | [] => 0
  | (u, z) :: r => z * g u + lin g r
  end.

(** The sum through a product is the sum of the sums. *)
Lemma lin_mul (g : uname -> Z) (a b : measure) : lin g (mmul a b) = lin g a + lin g b.
Proof.
  unfold mmul. induction a as [| [v z] a IH]; simpl; [reflexivity | rewrite IH; lia].
Qed.

(** The sum through a power is the power times the sum. *)
Lemma lin_pow (g : uname -> Z) (k : Z) (m : measure) : lin g (mpow k m) = k * lin g m.
Proof.
  induction m as [| [v z] m IH]; simpl; [lia | rewrite IH; ring].
Qed.

(** The sum splits into the part for one unit and the sum over the rest. *)
Lemma lin_split (g : uname -> Z) (u : uname) (m : measure) :
  lin g m = expo m u * g u + lin g (remove u m).
Proof.
  induction m as [| [v z] m IH]; simpl; [reflexivity |].
  rewrite IH. destruct (ueqb v u) eqn:E; simpl.
  - apply ueqb_iff in E. subst v. ring.
  - ring.
Qed.

(** A measure equal to `1` has sum zero. *)
Lemma lin_one (g : uname -> Z) (m : measure) : meq m mone -> lin g m = 0.
Proof.
  assert (G : forall n m, (List.length m <= n)%nat -> (forall u, expo m u = 0) -> lin g m = 0).
  { induction n as [| n IH]; intros [| [u z] r] L H; simpl in L; try reflexivity; try lia.
    rewrite (lin_split g u), H, Z.mul_0_l, Z.add_0_l. apply IH.
    - simpl. rewrite ueqb_refl. simpl. pose proof (length_remove u r). lia.
    - intro v. destruct (string_dec v u) as [-> | N].
      + apply expo_remove_same.
      + rewrite expo_remove_other by exact N. apply H. }
  intro H. apply (G (List.length m) m); [lia | exact H].
Qed.

(** Equal measures have equal sums. *)
Lemma lin_meq (g : uname -> Z) (a b : measure) : meq a b -> lin g a = lin g b.
Proof.
  intro H. assert (E : lin g (mmul a (minv b)) = 0).
  { apply lin_one. intro u. unfold minv. rewrite expo_mul, expo_pow, H. cbn [expo mone]. lia. }
  unfold minv in E. rewrite lin_mul, lin_pow in E. lia.
Qed.

Open Scope Q_scope.

(** The product through a measure of a rational given to each unit, raised to its exponent.
    - [f:] the rational given to each unit. *)
Fixpoint evalq (f : uname -> Q) (m : measure) : Q :=
  match m with
  | [] => 1
  | (u, z) :: r => f u ^ z * evalq f r
  end.

(** The product through a product of measures is the product of the products. *)
Lemma evalq_mul (f : uname -> Q) (a b : measure) :
  evalq f (mmul a b) == evalq f a * evalq f b.
Proof.
  unfold mmul. induction a as [| [v z] a IH]; simpl; [ring | rewrite IH; ring].
Qed.

(** The product through a power of a measure is the power of the product. *)
Lemma evalq_pow (f : uname -> Q) (k : Z) (m : measure) :
  evalq f (mpow k m) == evalq f m ^ k.
Proof.
  induction m as [| [v z] m IH]; simpl.
  - symmetry. apply Qpower_1.
  - rewrite IH, Qmult_power, Z.mul_comm, Qpower_mult. reflexivity.
Qed.

(** The product is positive when every unit is given a positive rational. *)
Lemma evalq_pos (f : uname -> Q) (m : measure) :
  (forall u, 0 < f u) -> 0 < evalq f m.
Proof.
  intro P. induction m as [| [v z] m IH]; simpl; [reflexivity |].
  apply Qmult_lt_0_compat; [apply Qpower_0_lt; apply P | exact IH].
Qed.

(** A positive rational is not zero. *)
Lemma Qpos_nonzero (q : Q) : 0 < q -> ~ q == 0.
Proof.
  intros P E. rewrite E in P. apply (Qlt_irrefl 0). exact P.
Qed.

(** The product splits into the part for one unit and the product over the rest. *)
Lemma evalq_split (f : uname -> Q) (u : uname) (m : measure) :
  (forall u, 0 < f u) -> evalq f m == f u ^ expo m u * evalq f (remove u m).
Proof.
  intro P. induction m as [| [v z] m IH]; simpl; [ring |].
  rewrite IH. destruct (ueqb v u) eqn:E; simpl.
  - apply ueqb_iff in E. subst v.
    rewrite Qpower_plus by (apply Qpos_nonzero; apply P). ring.
  - ring.
Qed.

(** A measure equal to `1` has product one. *)
Lemma evalq_one (f : uname -> Q) (m : measure) :
  (forall u, 0 < f u) -> meq m mone -> evalq f m == 1.
Proof.
  intro P.
  assert (G : forall n m, (List.length m <= n)%nat -> (forall u, expo m u = 0%Z) -> evalq f m == 1).
  { induction n as [| n IH]; intros [| [u z] r] L H; simpl in L; try reflexivity; try lia.
    rewrite (evalq_split f u) by exact P. rewrite H. simpl (f u ^ 0). rewrite Qmult_1_l.
    apply IH.
    - simpl. rewrite ueqb_refl. simpl. pose proof (length_remove u r). lia.
    - intro v. destruct (string_dec v u) as [-> | N].
      + apply expo_remove_same.
      + rewrite expo_remove_other by exact N. apply H. }
  intro H. apply (G (List.length m) m); [lia | exact H].
Qed.

(**md
**A factor defined unit by unit does not depend on how a measure is written.**

Give every unit a positive rational and multiply through a measure. Two measures that are equal
receive the same product. The conversion factor of the next module is such a product, so it is a
property of the measure and not of its spelling.

- [f:] the positive rational given to each unit.
*)
Theorem evalq_meq (f : uname -> Q) (a b : measure) :
  (forall u, 0 < f u) -> meq a b -> evalq f a == evalq f b.
Proof.
  intros P H. assert (E : evalq f (mmul a (minv b)) == 1).
  { apply evalq_one; [exact P |]. intro u. unfold minv.
    rewrite expo_mul, expo_pow, H. cbn [expo mone]. lia. }
  unfold minv in E. rewrite evalq_mul, evalq_pow in E.
  change (evalq f b ^ (-1)) with (/ evalq f b) in E.
  pose proof (Qpos_nonzero _ (evalq_pos f b P)) as Nz.
  rewrite <- (Qmult_1_l (evalq f b)), <- E. field. exact Nz.
Qed.
