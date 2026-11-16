From Stdlib Require Import List Bool.
Import ListNotations.
From Clef Require Import Spec.Types RFC0001.Constraints.

(**md # Regions of a type-case over several variables

The running example has three type variables. Two carry a closed-set constraint of
[RFC 0001](Clef.RFC0001.Constraints.html), and the third is constrained to be one of the other two:

```fsharp
let f<'A, 'B, 'T when 'A : (int | string)
                 and 'B : (string | float)
                 and 'T : ('A | 'B)> (x: 'T) =
    match x with
    | :? 'A & :? 'B -> ...
    | :? 'A -> ...
    | :? 'B -> ...
```

This module defines what an instantiation of the three variables is, what an arm tests, and how an
arm is selected. It then proves or refutes each claim the RFC makes about the match.

One question is left open on purpose: what `:? 'A` tests. Both answers are modelled, as a
`reading`, and every theorem says which reading it holds for.
*)

(**md ## Instantiations *)

(** One instantiation of the three variables by closed types. *)
Record inst3 : Type := Inst { iA : ty; iB : ty; iT : ty }.

(** Equality of closed types, as a computed test. *)
Definition tyeqb (x y : ty) : bool := if ty_eq_dec x y then true else false.

(** The computed test agrees with equality. *)
Lemma tyeqb_iff (x y : ty) : tyeqb x y = true <-> x = y.
Proof.
  unfold tyeqb. destruct (ty_eq_dec x y); split; intro H;
    try assumption; try reflexivity; try discriminate; contradiction.
Qed.

(** A type equals itself under the computed test. *)
Lemma tyeqb_refl (x : ty) : tyeqb x x = true.
Proof.
  apply tyeqb_iff. reflexivity.
Qed.

(** Different types fail the computed test. *)
Lemma tyeqb_false (x y : ty) : x <> y -> tyeqb x y = false.
Proof.
  intro N. unfold tyeqb. destruct (ty_eq_dec x y); [contradiction | reflexivity].
Qed.

(** Types that fail the computed test are different. *)
Lemma tyeqb_neq (x y : ty) : tyeqb x y = false -> x <> y.
Proof.
  intros H E. apply tyeqb_iff in E. congruence.
Qed.

(** An instantiation satisfies the three constraints when the first two variables are members of
    their sets and the third is equal to one of them.
    - [CA:] the member set of the first variable.
    - [CB:] the member set of the second variable.
    - [s:] the instantiation. *)
Definition valid (CA CB : cset) (s : inst3) : Prop :=
  sat (iA s) CA /\ sat (iB s) CB /\ (iT s = iA s \/ iT s = iB s).

(** The instantiations of the third variable for one choice of the first two. *)
Definition rows (a b : ty) : list inst3 :=
  if tyeqb a b then [Inst a b a] else [Inst a b a; Inst a b b].

(** Every instantiation the compiler must consider, as a list it can compute at the definition. *)
Definition table (CA CB : cset) : list inst3 :=
  flat_map (fun a => flat_map (rows a) CB) CA.

(**md
**The constraints describe a finite table of instantiations.**

The computed table holds exactly the instantiations that satisfy the three constraints. A check
that runs over the table has therefore considered every way the definition can be specialized, and
nothing else.
*)
Theorem table_iff_valid (CA CB : cset) (s : inst3) :
  In s (table CA CB) <-> valid CA CB s.
Proof.
  unfold table, valid, sat. rewrite in_flat_map. split.
  - intros [a [Ha H]]. apply in_flat_map in H. destruct H as [b [Hb H]].
    unfold rows in H. destruct (tyeqb a b); simpl in H.
    + destruct H as [<- | []]. simpl. intuition.
    + destruct H as [<- | [<- | []]]; simpl; intuition.
  - intros [Ha [Hb Ht]]. exists (iA s). split; [exact Ha |].
    apply in_flat_map. exists (iB s). split; [exact Hb |].
    destruct s as [a b t]. simpl in *. unfold rows. destruct (tyeqb a b) eqn:E.
    + apply tyeqb_iff in E. subst b. destruct Ht as [-> | ->]; left; reflexivity.
    + destruct Ht as [-> | ->]; simpl; auto.
Qed.

(**md ## Arms

An arm tests the type of the scrutinee, which is the third variable.
*)

(** What `:? 'A` tests. This is the open question of the RFC.
    `Equation` reads it as: the scrutinee's type is the type `'A` is instantiated to.
    `Membership` reads it as: the scrutinee's type is a member of the set `'A` is constrained to. *)
Inductive reading : Type :=
| Equation
| Membership.

(** The test of an arm: `:? 'A`, `:? 'B`, or a conjunction written with `&`. *)
Inductive test : Type :=
| IsA
| IsB
| Both (p q : test).

(** Whether an arm's test succeeds at an instantiation.
    - [r:] the reading of a test against a variable.
    - [s:] the instantiation.
    - [p:] the test. *)
Fixpoint matches (r : reading) (CA CB : cset) (s : inst3) (p : test) : bool :=
  match p with
  | IsA =>
      match r with
      | Equation => tyeqb (iT s) (iA s)
      | Membership => memb (iT s) CA
      end
  | IsB =>
      match r with
      | Equation => tyeqb (iT s) (iB s)
      | Membership => memb (iT s) CB
      end
  | Both p q => matches r CA CB s p && matches r CA CB s q
  end.

(** The arm a specialization uses: the first whose test succeeds, as
    [Patterns](https://clef-lang.com/spec/draft/patterns/) orders rules.
    - [arms:] the tests of the arms, in source order. *)
Definition select (r : reading) (CA CB : cset) (arms : list test) (s : inst3) : option test :=
  find (matches r CA CB s) arms.

(** When both variables' tests succeed, the scrutinee's type is in the intersection of the sets. *)
Lemma both_match_in_meet (r : reading) (CA CB : cset) (s : inst3) :
  valid CA CB s ->
  matches r CA CB s IsA = true -> matches r CA CB s IsB = true ->
  sat (iT s) (meet CA CB).
Proof.
  intros [Ha [Hb _]] HA HB. apply meet_sat. destruct r; simpl in HA, HB.
  - apply tyeqb_iff in HA. apply tyeqb_iff in HB. split.
    + rewrite HA. exact Ha.
    + rewrite HB. exact Hb.
  - apply memb_iff in HA. apply memb_iff in HB. split; assumption.
Qed.

(** A type in both sets gives a valid instantiation with all three variables equal. *)
Lemma diagonal_valid (CA CB : cset) (x : ty) :
  sat x CA -> sat x CB -> valid CA CB (Inst x x x).
Proof.
  intros HA HB. unfold valid. simpl. auto.
Qed.

(** At an instantiation with all three variables equal, both tests succeed. *)
Lemma diagonal_matches (r : reading) (CA CB : cset) (x : ty) :
  sat x CA -> sat x CB ->
  matches r CA CB (Inst x x x) IsA = true /\ matches r CA CB (Inst x x x) IsB = true.
Proof.
  intros HA HB. destruct r; simpl; split;
    try apply tyeqb_refl; apply memb_iff; assumption.
Qed.

(** A non-empty intersection has a member, which is in both sets. *)
Lemma meet_nonempty_witness (CA CB : cset) :
  meet CA CB <> [] -> exists x, sat x CA /\ sat x CB.
Proof.
  destruct (meet CA CB) as [| x l] eqn:E; intro H.
  - exfalso. apply H. reflexivity.
  - exists x. apply meet_sat. rewrite E. unfold sat. simpl. auto.
Qed.

(**md ## Coverage *)

(**md
**Testing both variables covers every instantiation.**

A match that has an arm for `'A` and an arm for `'B` selects an arm at every instantiation that
satisfies the constraints, under either reading and whatever other arms it has. No wildcard arm is
needed for exhaustiveness.
*)
Theorem coverage (r : reading) (CA CB : cset) (arms : list test) (s : inst3) :
  In IsA arms -> In IsB arms -> valid CA CB s ->
  select r CA CB arms s <> None.
Proof.
  intros HA HB [Ha [Hb Ht]] HN. unfold select in HN. destruct Ht as [Ht | Ht].
  - apply find_none with (x := IsA) in HN; [| exact HA]. destruct r; simpl in HN.
    + rewrite Ht, tyeqb_refl in HN. discriminate.
    + assert (M : memb (iT s) CA = true) by (apply memb_iff; rewrite Ht; exact Ha).
      rewrite M in HN. discriminate.
  - apply find_none with (x := IsB) in HN; [| exact HB]. destruct r; simpl in HN.
    + rewrite Ht, tyeqb_refl in HN. discriminate.
    + assert (M : memb (iT s) CB = true) by (apply memb_iff; rewrite Ht; exact Hb).
      rewrite M in HN. discriminate.
Qed.

(**md ## The three regions *)

(**md
**Under the equation reading, the three arms split the table by which variables are equal.**

With the intersection arm first, the arm selected at an instantiation says exactly which type
equations hold there. The first arm is selected where all three variables are the same type, the
second where the scrutinee is `'A` and `'A` differs from `'B`, and the third where the scrutinee is
`'B` and `'A` differs from `'B`. The body of each arm may assume the equations of its region.
*)
Theorem regions_partition (CA CB : cset) (s : inst3) :
  valid CA CB s ->
  let arms := [Both IsA IsB; IsA; IsB] in
  (select Equation CA CB arms s = Some (Both IsA IsB) <-> iT s = iA s /\ iA s = iB s) /\
  (select Equation CA CB arms s = Some IsA <-> iT s = iA s /\ iA s <> iB s) /\
  (select Equation CA CB arms s = Some IsB <-> iT s = iB s /\ iA s <> iB s).
Proof.
  intros [_ [_ Ht]] arms. subst arms. unfold select. cbn [find matches].
  destruct (tyeqb (iT s) (iA s)) eqn:EA; destruct (tyeqb (iT s) (iB s)) eqn:EB; simpl.
  - apply tyeqb_iff in EA. apply tyeqb_iff in EB.
    repeat split; intros; try discriminate; try congruence; intuition congruence.
  - apply tyeqb_iff in EA. apply tyeqb_neq in EB.
    repeat split; intros; try discriminate; try congruence; intuition congruence.
  - apply tyeqb_neq in EA. apply tyeqb_iff in EB.
    repeat split; intros; try discriminate; try congruence; intuition congruence.
  - apply tyeqb_neq in EA. apply tyeqb_neq in EB.
    destruct Ht; contradiction.
Qed.

(**md
**The intersection arm is reachable exactly when the member sets share a type.**

Some instantiation reaches the arm `:? 'A & :? 'B` if and only if the intersection of the two
member sets, the `meet` of RFC 0001, is not empty. This holds under both readings. So the compiler
can decide from the two constraints alone whether the arm is required or can never run.
*)
Theorem intersection_reachable_iff (r : reading) (CA CB : cset) :
  (exists s, valid CA CB s /\ matches r CA CB s (Both IsA IsB) = true) <-> meet CA CB <> [].
Proof.
  split.
  - intros [s [V M]] E.
    change (matches r CA CB s IsA && matches r CA CB s IsB = true) in M.
    apply andb_true_iff in M. destruct M as [MA MB].
    pose proof (both_match_in_meet r CA CB s V MA MB) as H. rewrite E in H. exact H.
  - intro N. destruct (meet_nonempty_witness CA CB N) as [x [HA HB]].
    exists (Inst x x x). split.
    + apply diagonal_valid; assumption.
    + change (matches r CA CB (Inst x x x) IsA && matches r CA CB (Inst x x x) IsB = true).
      destruct (diagonal_matches r CA CB x HA HB) as [-> ->]. reflexivity.
Qed.

(**md ## Why the intersection arm is required *)

(**md
**Without the intersection arm, the order of the two arms changes the program exactly when the sets overlap.**

A match with only the arms `:? 'A` and `:? 'B` selects the same arm in either order if and only if
the member sets share no type. When they do share one, swapping the arms silently changes which
body runs at the shared type. This is the case the intersection arm exists to handle.
*)
Theorem two_arms_order_matters_iff (r : reading) (CA CB : cset) :
  (forall s, valid CA CB s ->
     select r CA CB [IsA; IsB] s = select r CA CB [IsB; IsA] s)
  <-> meet CA CB = [].
Proof.
  split.
  - intro H. destruct (meet CA CB) as [| x l] eqn:E; [reflexivity |]. exfalso.
    assert (N : meet CA CB <> []) by (rewrite E; discriminate).
    destruct (meet_nonempty_witness CA CB N) as [z [HA HB]].
    specialize (H (Inst z z z) (diagonal_valid CA CB z HA HB)).
    destruct (diagonal_matches r CA CB z HA HB) as [MA MB].
    unfold select in H. cbn [find] in H. rewrite MA, MB in H. discriminate H.
  - intros E s V. unfold select. cbn [find].
    destruct (matches r CA CB s IsA) eqn:MA; destruct (matches r CA CB s IsB) eqn:MB;
      try reflexivity.
    exfalso. pose proof (both_match_in_meet r CA CB s V MA MB) as H.
    rewrite E in H. exact H.
Qed.

(** With the intersection arm first, the two arms after it may be written in either order. *)
Lemma intersection_first_order_free (r : reading) (CA CB : cset) (s : inst3) :
  select r CA CB [Both IsA IsB; IsA; IsB] s = select r CA CB [Both IsA IsB; IsB; IsA] s.
Proof.
  unfold select. cbn [find].
  change (matches r CA CB s (Both IsA IsB))
    with (matches r CA CB s IsA && matches r CA CB s IsB).
  destruct (matches r CA CB s IsA); destruct (matches r CA CB s IsB); reflexivity.
Qed.

(**md ## Specificity and the overlap check

The rule that makes the intersection arm required is not special to this example. It is a check on
any list of arms.
*)

(** One test is at least as specific as another when it succeeds only where the other does.
    The compiler computes this over the table.
    - [p:] the more specific test.
    - [q:] the more general test. *)
Definition le (r : reading) (CA CB : cset) (p q : test) : bool :=
  forallb (fun s => implb (matches r CA CB s p) (matches r CA CB s q)) (table CA CB).

(** The computed comparison agrees with its meaning over valid instantiations. *)
Lemma le_iff (r : reading) (CA CB : cset) (p q : test) :
  le r CA CB p q = true <->
  forall s, valid CA CB s -> matches r CA CB s p = true -> matches r CA CB s q = true.
Proof.
  unfold le. rewrite forallb_forall. split; intros H s Hs.
  - intro M. apply table_iff_valid in Hs. specialize (H s Hs).
    rewrite M in H. simpl in H. exact H.
  - apply table_iff_valid in Hs. destruct (matches r CA CB s p) eqn:M; simpl.
    + apply H; assumption.
    + reflexivity.
Qed.

(** A test is as specific as itself. *)
Lemma le_refl (r : reading) (CA CB : cset) (p : test) : le r CA CB p p = true.
Proof.
  apply le_iff. intros s _ M. exact M.
Qed.

(** A conjunction is at least as specific as its first part. *)
Lemma le_both_l (r : reading) (CA CB : cset) (p q : test) : le r CA CB (Both p q) p = true.
Proof.
  apply le_iff. intros s _ M. simpl in M. apply andb_true_iff in M. destruct M as [M _]. exact M.
Qed.

(** A conjunction is at least as specific as its second part. *)
Lemma le_both_r (r : reading) (CA CB : cset) (p q : test) : le r CA CB (Both p q) q = true.
Proof.
  apply le_iff. intros s _ M. simpl in M. apply andb_true_iff in M. destruct M as [_ M]. exact M.
Qed.

(** The overlap check. For each arm, and each instantiation its test succeeds at, the first
    earlier arm that also succeeds there must be at least as specific as this one. An arm that
    overlaps an earlier arm without being more general than it is rejected, unless a still earlier
    arm takes the instantiations they share.
    - [seen:] the arms before the ones being checked, in source order.
    - [arms:] the arms still to check. *)
Fixpoint ordered (r : reading) (CA CB : cset) (seen arms : list test) : bool :=
  match arms with
  | [] => true
  | q :: rest =>
      forallb
        (fun s =>
           implb (matches r CA CB s q)
             (match find (matches r CA CB s) seen with
              | None => true
              | Some p => le r CA CB p q
              end))
        (table CA CB)
      && ordered r CA CB (seen ++ [q]) rest
  end.

(** The first match in two lists joined is the first match in the first list, if it has one. *)
Lemma find_app {A : Type} (f : A -> bool) (l1 l2 : list A) :
  find f (l1 ++ l2) = match find f l1 with Some x => Some x | None => find f l2 end.
Proof.
  induction l1 as [| a l1 IH]; simpl; [reflexivity |].
  destruct (f a); [reflexivity | exact IH].
Qed.

(** The overlap check, for arms that follow a prefix already checked. *)
Lemma ordered_most_specific (r : reading) (CA CB : cset) (arms : list test) :
  forall (seen : list test) (s : inst3) (p q : test),
    ordered r CA CB seen arms = true ->
    valid CA CB s ->
    find (matches r CA CB s) (seen ++ arms) = Some p ->
    In q arms -> matches r CA CB s q = true ->
    le r CA CB p q = true.
Proof.
  induction arms as [| a rest IH]; intros seen s p q O V F Hq M; [destruct Hq |].
  simpl in O. apply andb_true_iff in O. destruct O as [O1 O2].
  destruct Hq as [-> | Hq].
  - rewrite forallb_forall in O1.
    specialize (O1 s (proj2 (table_iff_valid CA CB s) V)).
    rewrite M in O1. simpl in O1. rewrite find_app in F.
    destruct (find (matches r CA CB s) seen) as [p' |] eqn:Fs.
    + injection F as <-. exact O1.
    + simpl in F. rewrite M in F. injection F as <-. apply le_refl.
  - apply (IH (seen ++ [a]) s p q O2 V); [| exact Hq | exact M].
    rewrite <- app_assoc. exact F.
Qed.

(**md
**Under the overlap check, the first matching arm is the most specific matching arm.**

If a list of arms passes the check, then at every instantiation the arm selected by source order is
at least as specific as every other arm whose test succeeds there. So "the most specific arm is
chosen" and "the first matching arm is chosen" are the same rule, and the spec's first-match order
needs no change. This holds under both readings and for any list of arms.

- [p:] the arm selected.
- [q:] any other arm whose test succeeds.
*)
Theorem first_match_is_most_specific
  (r : reading) (CA CB : cset) (arms : list test) (s : inst3) (p q : test) :
  ordered r CA CB [] arms = true ->
  valid CA CB s ->
  select r CA CB arms s = Some p ->
  In q arms -> matches r CA CB s q = true ->
  le r CA CB p q = true.
Proof.
  intros O V F. exact (ordered_most_specific r CA CB arms [] s p q O V F).
Qed.

(**md
**Under the overlap check, the order of the arms does not change how specific the selected test is.**

Two lists holding the same tests, both passing the check, select equally specific tests at every
instantiation: each selected test succeeds exactly where the other does.

This is a statement about tests. It does not say the two selected arms are the same arm, and once
arms have bodies that difference matters: two arms with equivalent tests and different bodies pass
the check in either order. [Bodies](Clef.RFC0002.Bodies.html) refutes the stronger claim
(`ordered_order_irrelevant_falsified`) and proves the corrected one (`priority_glues`,
`glued_order_irrelevant`).

- [l1:] the arms in one order.
- [l2:] the same arms in another order.
*)
Theorem order_is_irrelevant
  (r : reading) (CA CB : cset) (l1 l2 : list test) (s : inst3) (p1 p2 : test) :
  ordered r CA CB [] l1 = true ->
  ordered r CA CB [] l2 = true ->
  (forall p, In p l1 <-> In p l2) ->
  valid CA CB s ->
  select r CA CB l1 s = Some p1 ->
  select r CA CB l2 s = Some p2 ->
  le r CA CB p1 p2 = true /\ le r CA CB p2 p1 = true.
Proof.
  intros O1 O2 P V F1 F2.
  pose proof F1 as G1. pose proof F2 as G2. unfold select in G1, G2.
  apply find_some in G1. apply find_some in G2.
  destruct G1 as [I1 M1]. destruct G2 as [I2 M2]. split.
  - apply (first_match_is_most_specific r CA CB l1 s p1 p2 O1 V F1); [apply P; exact I2 | exact M2].
  - apply (first_match_is_most_specific r CA CB l2 s p2 p1 O2 V F2); [apply P; exact I1 | exact M1].
Qed.

(**md
**The three-arm match passes the overlap check for every pair of member sets.**

With the intersection arm first, the match is accepted whatever the two constraints are, under
both readings. The author's pattern is therefore always a legal way to write the match.
*)
Theorem intersection_first_is_ordered (r : reading) (CA CB : cset) :
  ordered r CA CB [] [Both IsA IsB; IsA; IsB] = true.
Proof.
  cbn [ordered app]. rewrite !andb_true_iff. repeat split; try reflexivity;
    apply forallb_forall; intros s _; cbn [find];
    change (matches r CA CB s (Both IsA IsB))
      with (matches r CA CB s IsA && matches r CA CB s IsB);
    destruct (matches r CA CB s IsA); destruct (matches r CA CB s IsB);
    cbn [andb implb]; try reflexivity; try apply le_both_l; try apply le_both_r.
Qed.

(**md
**The overlap check rejects the two-arm match when the sets overlap.**

For `'A : (x | y)` and `'B : (y)` with `x` and `y` different types, the match with only the arms
`:? 'A` and `:? 'B` fails the check. The check is therefore not vacuous: it rejects the program
whose meaning `two_arms_order_matters_iff` shows to depend on arm order.

- [x:] a member of the first set only.
- [y:] the member the two sets share.
*)
Theorem unordered_overlap_rejected (x y : ty) :
  x <> y -> ordered Equation [x; y] [y] [] [IsA; IsB] = false.
Proof.
  intro N. destruct (ordered Equation [x; y] [y] [] [IsA; IsB]) eqn:O; [| reflexivity].
  exfalso.
  assert (V1 : valid [x; y] [y] (Inst y y y)) by (unfold valid, sat; simpl; intuition).
  assert (V2 : valid [x; y] [y] (Inst x y x)) by (unfold valid, sat; simpl; intuition).
  assert (L : le Equation [x; y] [y] IsA IsB = true).
  { apply (first_match_is_most_specific Equation [x; y] [y] [IsA; IsB] (Inst y y y) IsA IsB O V1).
    - unfold select. cbn [find matches iT iA]. rewrite tyeqb_refl. reflexivity.
    - simpl. auto.
    - cbn [matches iT iB]. apply tyeqb_refl. }
  apply N. apply tyeqb_iff.
  exact (proj1 (le_iff Equation [x; y] [y] IsA IsB) L (Inst x y x) V2 (tyeqb_refl x)).
Qed.

(**md ## The open question: what `:? 'A` tests

An arm `:? 'A as v` binds `v` at the type `'A`. That is sound only if the scrutinee's type is the
type `'A` stands for.
*)

(** The types at which an arm's binder is used: `'A` for `:? 'A`, `'B` for `:? 'B`, and both for a
    conjunction. *)
Fixpoint binder_types (s : inst3) (p : test) : list ty :=
  match p with
  | IsA => [iA s]
  | IsB => [iB s]
  | Both p q => binder_types s p ++ binder_types s q
  end.

(**md
**Under the equation reading, an arm's binder has the scrutinee's type.**

Where an arm's test succeeds, every type the arm binds its variable at is the scrutinee's own type.
Binding `v` at `'A` in the arm `:? 'A`, and at both `'A` and `'B` in the intersection arm, is
sound.
*)
Theorem equation_refines (CA CB : cset) (s : inst3) (p : test) :
  matches Equation CA CB s p = true ->
  forall u, In u (binder_types s p) -> u = iT s.
Proof.
  induction p as [| | p1 IH1 p2 IH2]; simpl; intros H u Hu.
  - destruct Hu as [<- | []]. apply tyeqb_iff in H. symmetry. exact H.
  - destruct Hu as [<- | []]. apply tyeqb_iff in H. symmetry. exact H.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    apply in_app_or in Hu. destruct Hu as [Hu | Hu].
    + exact (IH1 H1 u Hu).
    + exact (IH2 H2 u Hu).
Qed.

(**md
**Under the membership reading, an arm's binder need not have the scrutinee's type.**

The claim that the binder has the scrutinee's type is false under the membership reading whenever
two different types exist. With `'A : (x | y)`, `'B : (y)`, `'A` instantiated to `x` and the
scrutinee of type `y`, the arm `:? 'A` succeeds and would bind a value of type `y` at the type
`x`. Under this reading the arm can bind its variable only at the scrutinee's type, which is what
RFC 0001's arms over closed types already do.
*)
Theorem membership_refines_falsified (x y : ty) :
  x <> y ->
  ~ (forall (CA CB : cset) (s : inst3) (p : test),
       valid CA CB s ->
       matches Membership CA CB s p = true ->
       forall u, In u (binder_types s p) -> u = iT s).
Proof.
  intros N H. apply N. apply (H [x; y] [y] (Inst x y y) IsA).
  - unfold valid, sat. simpl. intuition.
  - cbn [matches iT]. apply memb_iff. unfold sat. simpl. auto.
  - simpl. auto.
Qed.

(** Where the sets share no type, a test succeeds under one reading exactly when it succeeds under
    the other. *)
Lemma matches_agree (CA CB : cset) (s : inst3) :
  meet CA CB = [] -> valid CA CB s ->
  forall p, matches Membership CA CB s p = matches Equation CA CB s p.
Proof.
  intros E [Ha [Hb Ht]] p. induction p as [| | p1 IH1 p2 IH2]; simpl.
  - destruct (tyeqb (iT s) (iA s)) eqn:Q.
    + apply tyeqb_iff in Q. apply memb_iff. rewrite Q. exact Ha.
    + destruct (memb (iT s) CA) eqn:M; [| reflexivity]. exfalso.
      apply tyeqb_neq in Q. destruct Ht as [Ht | Ht]; [contradiction |].
      apply memb_iff in M. apply (meet_empty CA CB E (iT s)).
      split; [exact M | rewrite Ht; exact Hb].
  - destruct (tyeqb (iT s) (iB s)) eqn:Q.
    + apply tyeqb_iff in Q. apply memb_iff. rewrite Q. exact Hb.
    + destruct (memb (iT s) CB) eqn:M; [| reflexivity]. exfalso.
      apply tyeqb_neq in Q. destruct Ht as [Ht | Ht]; [| contradiction].
      apply memb_iff in M. apply (meet_empty CA CB E (iT s)).
      split; [rewrite Ht; exact Ha | exact M].
  - rewrite IH1, IH2. reflexivity.
Qed.

(**md
**The two readings select the same arm when the member sets share no type.**

If the intersection of the two member sets is empty, every match selects the same arm at every
instantiation under either reading. The open question changes no program whose constraints are
disjoint.
*)
Theorem readings_agree_when_disjoint (CA CB : cset) (s : inst3) (arms : list test) :
  meet CA CB = [] -> valid CA CB s ->
  select Membership CA CB arms s = select Equation CA CB arms s.
Proof.
  intros E V. unfold select. induction arms as [| p l IH]; simpl; [reflexivity |].
  rewrite (matches_agree CA CB s E V p), IH. reflexivity.
Qed.

(**md
**The two readings select different arms when the member sets overlap.**

The claim that the readings always agree is false whenever two different types exist. With
`'A : (x | y)`, `'B : (y)`, `'A` instantiated to `x` and the scrutinee of type `y`, the equation
reading selects the arm `:? 'B` and the membership reading selects the intersection arm. The
question must be settled before overlapping constraints are allowed.
*)
Theorem readings_agree_falsified (x y : ty) :
  x <> y ->
  ~ (forall (CA CB : cset) (s : inst3) (arms : list test),
       valid CA CB s ->
       select Membership CA CB arms s = select Equation CA CB arms s).
Proof.
  intros N H.
  assert (V : valid [x; y] [y] (Inst x y y)) by (unfold valid, sat; simpl; intuition).
  specialize (H [x; y] [y] (Inst x y y) [Both IsA IsB; IsA; IsB] V).
  assert (M1 : memb y [x; y] = true) by (apply memb_iff; unfold sat; simpl; auto).
  assert (M2 : memb y [y] = true) by (apply memb_iff; unfold sat; simpl; auto).
  assert (Q : tyeqb y x = false) by (apply tyeqb_false; congruence).
  unfold select in H. cbn [find matches iT iA iB] in H.
  rewrite M1, M2, Q, tyeqb_refl in H. simpl in H. discriminate H.
Qed.
