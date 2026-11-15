From Stdlib Require Import List.
Import ListNotations.

(**md # Spec: types

The part of the Clef type algebra that RFC proofs share. It is a model of
[Type Representation Architecture](https://clef-lang.com/spec/draft/type-representation-architecture/),
read at `clef-lang-spec` commit `0ad783d`.

Everything declared with `Parameter` or `Axiom` in a `Spec` module is an assumption taken from the
specification. A theorem that depends on one shows it on its badge.
*)

(**md ## Type constructors *)

(** The named types of a program: primitives, records, unions and every instantiated generic.
    The spec's [TypeConRef]. *)
Parameter tycon : Type.

(**md
Type identity is identity of the constructor reference. The spec states it as "Two types are equal
iff their TypeConRefs are equal" (§2.1) and unifies by comparing the reference (§7). A comparison
that the compiler performs is a decidable one.
*)
Axiom tycon_eq_dec : forall a b : tycon, {a = b} + {a <> b}.

(**md ## Closed types

A closed type contains no type variable. After monomorphization every type in a program is closed,
so an applied generic such as `list<int>` is one `tycon` here. Function and pair types stay
structural, as `TFun` and `TTuple` are in the spec.
*)
Inductive ty : Type :=
| TCon (c : tycon)
| TFun (a b : ty)
| TPair (a b : ty).

(** Equality of closed types is decidable, given that constructor identity is. *)
Lemma ty_eq_dec : forall a b : ty, {a = b} + {a <> b}.
Proof.
  decide equality. apply tycon_eq_dec.
Defined.

(**md ## Types open in one variable

A definition that is generic in one type variable mentions that variable in its parameter and
result types. `OVar` is the variable.
*)
Inductive oty : Type :=
| OVar
| OCon (c : tycon)
| OFun (a b : oty)
| OPair (a b : oty).

(** The closed type obtained by putting a closed type in place of the variable.
    - [t:] the type the variable is instantiated to.
    - [o:] the open type. *)
Fixpoint inst (t : ty) (o : oty) : ty :=
  match o with
  | OVar => t
  | OCon c => TCon c
  | OFun a b => TFun (inst t a) (inst t b)
  | OPair a b => TPair (inst t a) (inst t b)
  end.
