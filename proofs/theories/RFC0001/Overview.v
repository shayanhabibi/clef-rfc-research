(**md # RFC 0001: Closed-set type constraints

| | |
|---|---|
| **Stage** | Draft |
| **Date** | 2026-11-15 |
| **Written against** | `clef-lang-spec` commit `0ad783d` (2026-09-26) |
| **Assumes** | [Spec.Types](Clef.Spec.Types.html), [Spec.Witnesses](Clef.Spec.Witnesses.html), [Spec.Runtime](Clef.Spec.Runtime.html) |
| **Process note** | Not yet submitted as a suggestion. Approval in principle is still required before this enters Review. |

## Summary

This RFC adds one constraint form, the *closed-set constraint*, which restricts a type variable to
an enumerated, finite set of types: `'T : (int | string)`. The constraint is resolved entirely at
compile time. The body of a constrained definition is checked once, at its definition, against
every type in the set, so an operation on a value of type `'T` is valid only when every member of
the set supports it. Where the members do not share an operation, the body either converts the
value to a common type or uses a *static type-case*, a `:?` pattern that is selected per
instantiation and emits no run-time test. No new type is added to the native type universe, no
value has a union type, and no representation rule changes.

## Motivation

Clef has two ways to write code that works over several types, and a gap between them.

- **Discriminated unions** handle a value whose case varies at run time. They require a declared
  type, a constructor at every injection site, and a tag in the value. That cost is correct when
  the variation is real at run time, and it is overhead when every call site already knows the
  type statically.
- **SRTP member constraints** handle the static case, but they are open. A function is constrained
  by the operations it uses, and any type with those operations qualifies. The author cannot say
  which types are meant, the constraint is not checked until a call site instantiates it, and the
  definition must be `inline`.

The gap is a function that accepts a small, known set of types, each call site knowing which:

```fsharp
// Today: one function per type, or an inline SRTP function whose
// admissible types are whatever happens to have the right members.
let describeInt (x: int) : string = formatInt x
let describeString (x: string) : string = x
```

Three concrete problems follow from the gap.

1. **Errors land at the call site.** An SRTP function that misuses an operation is accepted at its
   definition and rejected wherever it is instantiated with a type lacking the member.
2. **The admissible set is not part of the contract.** A signature cannot state which types a
   function is meant for, so a later change to the body silently changes the set.
3. **The `:?` pattern has no settled meaning.** The spec's
   [Dynamic Type-test Patterns](https://clef-lang.com/spec/draft/patterns/#dynamic-type-test-patterns)
   says it is resolved statically, yet its
   example takes a parameter of type `obj`, which the compiler must reject. No conforming program
   can reach the construct that section describes.

Type unions in the TypeScript or Scala 3 sense would close the gap, but an untagged union needs
run-time type discovery. [Representation](Clef.RFC0001.Representation.html) proves that this is
impossible under the spec's assumptions. A constraint on a type variable has no such need: it
relates types to a variable, never a value to a wider type.

## The proposal in one example

```fsharp
let double<'T when 'T : (int | float)> (x: 'T) : 'T = x + x
// (+) has a witness at int and at float: accepted.

let size<'T when 'T : (string | int)> (x: 'T) = x.Length
// int has no Length: rejected at this definition.

let describe<'T when 'T : (int | string)> (x: 'T) : string =
    match x with
    | :? int as i -> formatInt i
    | :? string as s -> s
```

## How to read this RFC

Each design rule is a definition in Rocq, and each claim about the design is a theorem checked by
Rocq. The prose between them is the RFC.

| Module | Holds |
|---|---|
| [Constraints](Clef.RFC0001.Constraints.html) | Member sets, satisfaction, entailment and intersection |
| [TypeCase](Clef.RFC0001.TypeCase.html) | Definition-site checking, the static type-case and specialization |
| [Representation](Clef.RFC0001.Representation.html) | Why a member set cannot be a type without a tag |
| [Laws](Clef.RFC0001.Laws.html) | An extension, not part of the proposal: laws a member set carries, rewriting by them, and library theorems instantiated per member |
| [Discussion](Clef.RFC0001.Discussion.html) | What the proofs do not cover, drawbacks, alternatives, impact and open questions |

The Guarantees page, which opens this reader, lists every titled theorem with the assumptions its
proof rests on.
*)
