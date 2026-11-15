---
title: Spec assumptions
---

The modules under `Clef.Spec` hold what every RFC may assume about Clef. They are a model of the specification, read at `clef-lang-spec` commit `0ad783d`.

| Module | Models | Assumes |
|---|---|---|
| [Spec.Types]({{base}}proofs/Clef.Spec.Types.html) | Closed types, and types open in one variable | A type of named type constructors, with decidable identity |
| [Spec.Runtime]({{base}}proofs/Clef.Spec.Runtime.html) | Run-time values and their representation | Values of each named type, a representation function, and that a representation does not name its type |
| [Spec.Witnesses]({{base}}proofs/Clef.Spec.Witnesses.html) | Operations and their witnesses | A set of operations, the witness table, what an operation computes, and that a witness is implemented at its declared type |

## Rules for an assumption

1. **It cites the specification.** The comment on an `Axiom` or `Parameter` names the chapter it comes from, and says so when it is this repository's reading and not the specification's wording.
2. **It is as weak as the proofs allow.** An axiom that says more than any proof needs is a risk with no return.
3. **It is shared.** An assumption about Clef belongs in a `Spec` module, where every RFC and every reader can see it. An RFC declares an assumption of its own only for the thing it proposes.
4. **It is consistent.** An axiom that contradicts another proves everything. Before adding one, describe a model in which all of them hold.

## A model of the current assumptions

The assumptions hold together when named types are the two types `int32` and `float32`, a value of either is a 32-bit word, the representation of a value is that word, the only operation is the identity with a witness at every type, and it computes its argument. Constructor identity is decidable, both zeroes are the same word, and the identity returns a value of its argument's type.

## What an assumption costs

Every theorem's badge on the [Guarantees page]({{base}}proofs/index.html) lists the axioms its proof used. A theorem with no axioms holds in the model alone. A theorem with axioms holds only as far as the specification says what the axioms say.
