From Clef Require Import Spec.Types Spec.Runtime.

(**md # Spec: operation witnesses

How an operation finds its implementation. A model of the witness resolution in
[Inference and Constraint Solving](https://clef-lang.com/spec/draft/inference-constraint-solving/):
statically resolved member constraints are solved against the native witness hierarchy, at compile
time.
*)

(** The operations a program can apply: operators and statically resolved members. *)
Parameter op : Type.

(**md
The result type of an operation at an argument type, or `None` where the type has no witness for
it. It is a function, so resolution has at most one answer.
*)
Parameter witness : op -> ty -> option ty.

(** What an operation computes on a value, or [None] where it is stuck. *)
Parameter apply : op -> val -> option val.

(**md
A witness is implemented, and its implementation has the type the witness declares. An operation
applied at a type with a witness returns a value of the witness's result type.
*)
Axiom witness_sound :
  forall (o : op) (a r : ty) (v : val),
    witness o a = Some r -> has_ty v a ->
    exists w, apply o v = Some w /\ has_ty w r.
