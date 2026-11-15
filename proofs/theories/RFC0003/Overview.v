(**md # RFC 0003: Convertible units of measure

| | |
|---|---|
| **Stage** | Draft (exploratory) |
| **Date** | 2026-11-15 |
| **Written against** | `clef-lang-spec` commit `0ad783d` (2026-09-26) |
| **Assumes** | Nothing. The model is self-contained |
| **Process note** | Not a proposal. The author is not convinced of the idea as it stands and records it for the parts worth considering further. |

## Status of this RFC

This RFC is an exploration. The idea came out of asking whether a type-case could branch on a unit
of measure, and it is kept because the proofs show some parts of it are sound and simple, and show
where the rest is not. Read the theorems as facts about the model, and the design around them as
unsettled. [Discussion](Clef.RFC0003.Discussion.html) lists the reasons for doubt and the parts
that look worth keeping.

## Summary

Units of measure are declared with their size relative to other units. Two measures of the same
dimension are then *convertible*, and the compiler inserts a scaling where a value in one measure
reaches a position that expects another. The factor is computed from the declarations. Units of
different dimensions remain a type error, and a program with no unit mismatch is unchanged.

For integers a conversion is exact only when the factor is a whole number. An integer operation on
two units is inferred at the finer one, and a conversion to a coarser unit loses resolution, which
a position must accept explicitly.

## Motivation

```fsharp
[<Measure>] type m
[<Measure>] type s
[<Measure>] type km = 1000 m
[<Measure>] type h  = 3600 s

let speed (d: float<m>) (t: float<s>) : float<m/s> = d / t

let v = speed 12.0<km> 0.5<h>
```

Today `km` and `m` are unrelated, so the call is a type error and the author writes the factors by
hand. Nothing checks them. With the declarations above the compiler knows both factors, and the
call means what it says.

A dimension can also be named, and defined from others, so that a signature says what it accepts
without fixing the unit of the caller:

```fsharp
[<Dimension>] type distance = m
[<Dimension>] type time     = s
[<Dimension>] type speed    = distance / time

let f (v: speed<km/h>) = ...     // accepts any speed, holds it in km/h
```

## What the proofs establish

| Point | Where |
|---|---|
| Equality of measures is decidable, and a factor defined unit by unit respects it | [Measures](Clef.RFC0003.Measures.html) |
| Convertibility is a decidable equivalence, and the factor does not depend on the path | [Conversion](Clef.RFC0003.Conversion.html) |
| Compound measures and quotient dimensions need no declarations of their own | [Conversion](Clef.RFC0003.Conversion.html) |
| The choice of base unit changes no conversion | [Conversion](Clef.RFC0003.Conversion.html) |
| Inserted conversions preserve the meaning of the program, over rationals | [Elaboration](Clef.RFC0003.Elaboration.html) |
| Integer conversion is exact in one direction, and the finer unit is the inferred one | [Integers](Clef.RFC0003.Integers.html) |
| An accepted loss of resolution is less than one unit of the target | [Integers](Clef.RFC0003.Integers.html) |

## How to read this RFC

| Module | Holds |
|---|---|
| [Measures](Clef.RFC0003.Measures.html) | Measures as products of units, their equality, and quantities defined unit by unit |
| [Conversion](Clef.RFC0003.Conversion.html) | Declarations, dimension, scale, convertibility and the conversion factor |
| [Elaboration](Clef.RFC0003.Elaboration.html) | Where a scaling is inserted, and the proof that it preserves meaning |
| [Integers](Clef.RFC0003.Integers.html) | Exact conversion, the finer unit, and accepted loss of resolution |
| [Discussion](Clef.RFC0003.Discussion.html) | What the proofs do not cover, why the idea is unsettled, alternatives and open questions |
*)
