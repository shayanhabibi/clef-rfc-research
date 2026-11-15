From Clef Require Import Spec.Types.

(**md # Design

Each rule of the design is a definition, and each claim about it is a theorem.
*)

(** Replace with a rule of the design, written as a function the compiler could run. *)
Definition rule (t : ty) : bool := true.

(**md
**Replace this line with the claim, in the words a reader of the RFC would use.**

Say what the claim means for the design. This statement is unproved, so it is listed as Open
until its proof is complete.
*)
Theorem claim : forall t : ty, rule t = true.
Admitted.
