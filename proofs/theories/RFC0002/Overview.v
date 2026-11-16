(**md # RFC 0002: Type-case over several constrained variables

| | |
|---|---|
| **Stage** | Draft |
| **Date** | 2026-11-15 |
| **Written against** | `clef-lang-spec` commit `0ad783d` (2026-09-26) |
| **Assumes** | [Spec.Types](Clef.Spec.Types.html), [Spec.Witnesses](Clef.Spec.Witnesses.html), [Spec.Runtime](Clef.Spec.Runtime.html), [RFC 0001 Constraints](Clef.RFC0001.Constraints.html), [RFC 0001 TypeCase](Clef.RFC0001.TypeCase.html) |
| **Process note** | Not yet submitted as a suggestion. Approval in principle is still required before this enters Review. |

## Summary

RFC 0001 constrains one type variable to a closed set of types. This RFC lets a definition have
several such variables, lets a variable be constrained to be one of the others, `'T : ('A | 'B)`,
and lets a static type-case test the scrutinee against a variable: `:? 'A`. The test succeeds when
the scrutinee's type is the type `'A` is instantiated to. Two arms that test
different variables overlap wherever those variables are instantiated to the same type. The RFC
adds one check on a match: an arm that overlaps an earlier arm must be more general than it, unless
a still earlier arm takes the instantiations they share. Under that check the first matching arm is
the most specific one, so the spec's first-match order needs no change. Arm selection stays static:
every variable is a closed type at each specialization.

## Motivation

```fsharp
let f<'A, 'B, 'T when 'A : (int | string)
                 and 'B : (string | float)
                 and 'T : ('A | 'B)> (x: 'T) =
    match x with
    | :? 'A & :? 'B -> ...   // 'T, 'A and 'B are the same type
    | :? 'A -> ...           // 'T is 'A, and 'A is not 'B
    | :? 'B -> ...           // 'T is 'B, and 'A is not 'B
```

`'A` and `'B` can both be `string`. At that instantiation the arms `:? 'A` and `:? 'B` both apply,
and neither is more specific than the other. With only those two arms the body that runs depends on
which arm is written first. The author's position is that the overlap must be handled by an arm of
its own, written first because it is the most specific.

## What is settled

The proofs in [Regions](Clef.RFC0002.Regions.html) settle these points.

- The constraints describe a finite table of instantiations, which the compiler can enumerate.
- The intersection arm is reachable exactly when the two member sets share a type.
- Without it, arm order changes the program exactly when the sets share a type.
- With the overlap check, the first matching arm is the most specific one.

The proofs in [Bodies](Clef.RFC0002.Bodies.html) give each arm a body and settle these.

- Under the equation reading, a definition whose arm bodies check returns a value of its declared
  type at every instantiation.
- The overlap check alone does not make arm order irrelevant: two arms with equivalent tests and
  different bodies pass it in either order. It does once no two arms test the same thing.
- There is a second way to make order irrelevant. Two overlapping arms may also be accepted when
  their bodies compute the same result, and then no intersection arm is needed.

The proofs in [Nested](Clef.RFC0002.Nested.html) allow a match anywhere in a body and settle these.

- A type-case nested to any depth is erased: a specialization computes what the body means and
  holds no type.
- A definition with nested matches that checks returns a value of its declared type at every
  instantiation.
- An inner match is checked against the region of the arm it is in. It need cover only that
  region, and its arms may use the outer arm's type equation.
- The intersection arm can be written as a test nested in another.
- The overlap check for an inner match is taken over the region of the arm it is in. Under it the
  order of the inner arms does not change the program. Taken over the whole table it would reject
  a correctly ordered match.
- The region of every inner match is computed by one walk over the body. A body that passes the
  resulting check means the same after any rearrangement of the arms of any of its matches.

## The reading of `:? 'A`

The RFC adopts the equation reading. The membership reading was the alternative. It stays in the
model as a second `reading`, so that each reason for rejecting it is a checked theorem.

| Reading | Status | `:? 'A` succeeds when | Binder of `:? 'A as v` |
|---|---|---|---|
| Equation | Adopted | the scrutinee's type is the type `'A` is instantiated to | Sound at `'A`: `equation_refines`, `checked_match_runs` |
| Membership | Rejected | the scrutinee's type is a member of `'A`'s set | Unsound at `'A`: `membership_refines_falsified`, `membership_binding_falsified` |

The readings agree on every program whose member sets are disjoint
(`readings_agree_when_disjoint`) and differ on overlapping sets (`readings_agree_falsified`).

## How to read this RFC

| Module | Holds |
|---|---|
| [Regions](Clef.RFC0002.Regions.html) | Instantiations, arm tests under both readings, selection, the overlap check and the theorems |
| [Bodies](Clef.RFC0002.Bodies.html) | Arm bodies, the check of a definition, what it computes, and the two ways overlapping arms are glued |
| [Nested](Clef.RFC0002.Nested.html) | A match anywhere in a body: typing, specialization, erasure, safety, what an inner match knows about the arm it is in, and the overlap check for inner matches with the region of each computed from the body |
| [Discussion](Clef.RFC0002.Discussion.html) | What the proofs do not cover, the reasons for the adopted reading, the relation to the verification tiers, drawbacks and alternatives |
*)
