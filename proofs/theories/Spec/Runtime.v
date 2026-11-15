From Clef Require Import Spec.Types.

(**md # Spec: run-time values

What a value is at run time. A model of
[Native Type Mappings](https://clef-lang.com/spec/draft/native-type-mappings/) and
[Discriminated Union Representation](https://clef-lang.com/spec/draft/discriminated-union-representation/):
there is no `obj`, no boxing and no run-time type metadata.
*)

(**md ## Values *)

(** The values of a named type. *)
Parameter atom : tycon -> Type.

(** A run-time value: a value of a named type, or a pair of values. *)
Inductive val : Type :=
| VAtom (c : tycon) (x : atom c)
| VPair (a b : val).

(** A value has a closed type. No value has a function type here, since the models that use this
    module have no functions as values. *)
Inductive has_ty : val -> ty -> Prop :=
| HAtom (c : tycon) (x : atom c) : has_ty (VAtom c x) (TCon c)
| HPair (a b : val) (s t : ty) : has_ty a s -> has_ty b t -> has_ty (VPair a b) (TPair s t).

(**md ## Representation *)

(** What memory holds. *)
Parameter bits : Type.

(** The representation in memory of a value of a named type. *)
Parameter repr : forall c : tycon, atom c -> bits.

(**md
A representation carries nothing that names its type. Stated as its consequence: two values of
different types can have the same representation, as the `int32` zero and the `float32` zero do.

This is the formal reading used here of "no run-time type metadata". The specification does not
state it in this form.
*)
Axiom no_runtime_type_metadata :
  exists (c d : tycon) (x : atom c) (y : atom d), c <> d /\ repr c x = repr d y.
