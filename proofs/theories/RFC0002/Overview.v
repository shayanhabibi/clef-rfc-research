(**md # RFC 0002: Type-case over several constrained variables

| | |
|---|---|
| **Stage** | Draft |
| **Date** | 2026-11-15 |
| **Written against** | `clef-lang-spec` commit `0ad783d` (2026-09-26) |
| **Assumes** | [Spec.Types](Clef.Spec.Types.html), [RFC 0001 Constraints](Clef.RFC0001.Constraints.html) |
| **Process note** | Not yet submitted as a suggestion. One design question is open, and this RFC is written to inform it. |

## Summary

RFC 0001 constrains one type variable to a closed set of types. This RFC lets a definition have
several such variables, lets a variable be constrained to be one of the others, `'T : ('A | 'B)`,
and lets a static type-case test the scrutinee against a variable: `:? 'A`. Two arms that test
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

## What is settled and what is open

The proofs in [Regions](Clef.RFC0002.Regions.html) settle these points.

- The constraints describe a finite table of instantiations, which the compiler can enumerate.
- The intersection arm is reachable exactly when the two member sets share a type.
- Without it, arm order changes the program exactly when the sets share a type.
- With the overlap check, first match and most specific match are the same arm, and arm order
  stops mattering.

One point is left open: what `:? 'A` tests. Both readings are modelled.

| Reading | `:? 'A` succeeds when | Binder of `:? 'A as v` |
|---|---|---|
| Equation | the scrutinee's type is the type `'A` is instantiated to | Sound at `'A`: `equation_refines` |
| Membership | the scrutinee's type is a member of `'A`'s set | Unsound at `'A`: `membership_refines_falsified` |

The readings agree on every program whose member sets are disjoint
(`readings_agree_when_disjoint`) and differ on overlapping sets (`readings_agree_falsified`).

## How to read this RFC

| Module | Holds |
|---|---|
| [Regions](Clef.RFC0002.Regions.html) | Instantiations, arm tests under both readings, selection, the overlap check and the theorems |
| [Discussion](Clef.RFC0002.Discussion.html) | What the proofs do not cover, the evidence on the open question, drawbacks and alternatives |
*)
