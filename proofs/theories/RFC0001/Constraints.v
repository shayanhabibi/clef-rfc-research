From Stdlib Require Import List.
Import ListNotations.
From Clef Require Import Spec.Types.

(**md # Closed-set constraints

The constraint form, and the rules by which the solver decides it.

```fsgrammar
constraint :=
    ...
    typar : ( type | ... | type )  -- closed-set constraint
```

The parenthesised list holds at least two types. The form is told apart from a member constraint
and a default constructor constraint by its first token, which is never `member`, `static` or
`new`. A definition is not required to be `inline` on account of a closed-set constraint.
*)

(**md ## Member sets *)

(** The member set of a closed-set constraint: the closed types it lists. *)
Definition cset : Type := list ty.

(**md
A member set is well formed when no member is listed twice and there are at least two. Members are
closed types by construction, since `ty` has no type variable. Member identity is type identity, so
whatever distinguishes two types distinguishes two members.
*)
Definition well_formed (C : cset) : Prop :=
  NoDup C /\ 2 <= length C.

(**md
A member set is not a type. `cset` is not `ty`, and no constructor of `ty` holds one, so a member
set cannot appear in type position and no expression has one as its type.
*)

(**md ## Satisfaction *)

(** A closed type satisfies a constraint exactly when it is a member. Coercion plays no part.
    - [t:] the closed type.
    - [C:] the member set. *)
Definition sat (t : ty) (C : cset) : Prop := In t C.

(** Whether a closed type is a member, as the solver computes it. *)
Definition memb (t : ty) (C : cset) : bool :=
  if in_dec ty_eq_dec t C then true else false.

(** The computed test agrees with membership. *)
Lemma memb_iff (t : ty) (C : cset) : memb t C = true <-> sat t C.
Proof.
  unfold memb, sat. destruct (in_dec ty_eq_dec t C); split; intro H.
  - assumption.
  - reflexivity.
  - discriminate.
  - contradiction.
Qed.

(** Satisfaction is decidable, so a constraint on a concrete type is never left unresolved. *)
Lemma sat_decidable (t : ty) (C : cset) : {sat t C} + {~ sat t C}.
Proof.
  exact (in_dec ty_eq_dec t C).
Qed.

(**md ## Entailment *)

(** Whether every member of one set is a member of another, as the solver computes it. *)
Definition entailsb (C D : cset) : bool :=
  forallb (fun t => memb t D) C.

(** A variable constrained to one member set may be used where another member set is required
    exactly when the subset test passes.
    - [C:] the member set the variable has.
    - [D:] the member set required. *)
Definition entails (C D : cset) : Prop := entailsb C D = true.

(**md
**Entailment is exactly preservation of satisfaction.**

The subset test accepts a use of a constrained variable if and only if every type the variable can
be instantiated to satisfies the required constraint. It rejects nothing sound and accepts nothing
unsound.
*)
Theorem entails_iff_sat (C D : cset) :
  entails C D <-> forall t, sat t C -> sat t D.
Proof.
  unfold entails, entailsb. rewrite forallb_forall. split; intros H t Ht.
  - apply memb_iff. apply H. exact Ht.
  - apply memb_iff. apply H. exact Ht.
Qed.

(** A constraint entails itself. *)
Lemma entails_refl (C : cset) : entails C C.
Proof.
  apply entails_iff_sat. intros t H. exact H.
Qed.

(** Entailment chains. *)
Lemma entails_trans (C D E : cset) : entails C D -> entails D E -> entails C E.
Proof.
  rewrite !entails_iff_sat. intros H1 H2 t H. apply H2. apply H1. exact H.
Qed.

(**md ## Intersection

When unification gives one variable two closed-set constraints, they are replaced by one whose
member set is the intersection.
*)

(** The members of the first set that are also members of the second. *)
Definition meet (C D : cset) : cset :=
  filter (fun t => memb t D) C.

(**md
**Intersecting two constraints loses no information.**

A type satisfies the intersection if and only if it satisfies both constraints, so replacing two
constraints by their intersection changes no program's meaning.
*)
Theorem meet_sat (t : ty) (C D : cset) :
  sat t (meet C D) <-> sat t C /\ sat t D.
Proof.
  unfold meet, sat. rewrite filter_In. rewrite memb_iff. reflexivity.
Qed.

(**md
**The intersection is the weakest constraint that entails both.**

It entails each of the two constraints, and any constraint that entails both of them entails it.
The solver therefore makes the most general choice, which is what principal types need.

- [E:] any other constraint that entails both.
*)
Theorem meet_greatest (C D E : cset) :
  entails (meet C D) C /\ entails (meet C D) D /\
  (entails E C -> entails E D -> entails E (meet C D)).
Proof.
  split; [| split].
  - apply entails_iff_sat. intros t H. apply meet_sat in H. apply H.
  - apply entails_iff_sat. intros t H. apply meet_sat in H. apply H.
  - rewrite !entails_iff_sat. intros HC HD t H. apply meet_sat. split.
    + apply HC. exact H.
    + apply HD. exact H.
Qed.

(**md
**An empty intersection admits no type.**

When two constraints share no member, no instantiation satisfies both, so reporting an error is the
only sound outcome.
*)
Theorem meet_empty (C D : cset) :
  meet C D = [] -> forall t, ~ (sat t C /\ sat t D).
Proof.
  intros E t H. apply meet_sat in H. rewrite E in H. exact H.
Qed.

(**md
**An intersection of one type solves the variable.**

When exactly one type is left, every instantiation that satisfies both constraints is that type, so
the solver may replace the variable by it.
*)
Theorem meet_singleton (C D : cset) (t : ty) :
  meet C D = [t] -> forall u, sat u C -> sat u D -> u = t.
Proof.
  intros E u HC HD.
  assert (H : sat u (meet C D)) by (apply meet_sat; split; assumption).
  rewrite E in H. destruct H as [H | []]. symmetry. exact H.
Qed.

(** Intersection lists no member twice when its first argument lists none twice. *)
Lemma meet_nodup (C D : cset) : NoDup C -> NoDup (meet C D).
Proof.
  apply NoDup_filter.
Qed.

(**md ## Origin and signatures

Two rules of this section are stated in prose only.

- **Origin.** A closed-set constraint comes only from an explicit declaration. It is never
  synthesised from the operations a definition uses. It propagates through unification as other
  constraints do, and may appear in an inferred generalized type.
- **Signatures.** A closed-set constraint is part of a value's type and appears in its signature.
  Signature conformance requires equal member sets.
*)
