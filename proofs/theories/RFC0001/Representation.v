From Clef Require Import Spec.Types Spec.Runtime.

(**md # Representation

Why the member set is a constraint and not a type, and what a value of a constrained variable is at
run time.
*)

(**md ## A member set as an untagged type

Suppose `(int | string)` were a type whose values are the values of its members, stored as they
are. Code receiving such a value would have to find out which member it holds, from the
representation alone.
*)

(** A way to recover the type of any value from its representation.
    - [decode:] the function from a representation to the named type of the value it represents. *)
Definition discriminates (decode : bits -> tycon) : Prop :=
  forall (c : tycon) (x : atom c), decode (repr c x) = c.

(**md
**The claim that an untagged union can be told apart at run time is false.**

No function recovers the type of every value from its representation, because two values of
different types can share one. An untagged union type therefore cannot support a type test, and it
is excluded.
*)
Theorem untagged_union_discriminable_falsified :
  ~ exists decode, discriminates decode.
Proof.
  intros [decode H].
  destruct no_runtime_type_metadata as [c [d [x [y [Hne Heq]]]]].
  apply Hne. transitivity (decode (repr c x)).
  - symmetry. apply H.
  - rewrite Heq. apply H.
Qed.

(**md ## A tag restores the test

Storing the type beside the representation makes the test trivial. This is what a discriminated
union does, and what the tagged anonymous sum listed under Alternatives would do. It costs a tag in
every value.
*)

(** A tagged representation can always be told apart. *)
Lemma tagged_union_discriminable :
  exists decode : tycon * bits -> tycon,
    forall (c : tycon) (x : atom c), decode (c, repr c x) = c.
Proof.
  exists fst. reflexivity.
Qed.

(**md ## What this RFC does instead

A value whose type is a set-constrained variable has, in each specialization, exactly the
representation of the instantiating type. Nothing has to be recovered at run time, because each
specialization is compiled for one type. [TypeCase](Clef.RFC0001.TypeCase.html) shows that a
specialized body holds no type test, and `specialization_preserves_meaning` proves that it
computes the same result as a body that was told the type.

1. A definition with a set-constrained type variable is monomorphized as every generic definition
   is. An implementation produces at most one specialization per member for each such variable.
2. A static type-case emits no run-time test, no tag and no type metadata.
3. No layout, placement or lifetime rule of any representation chapter is altered.
*)
