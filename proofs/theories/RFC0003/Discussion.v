(**md # Discussion

## What the proofs cover

The model has measures, unit declarations, and two small expression languages: one over rationals
and one over unbounded integers. Each has literals, arithmetic and a position that expects a
measure. There are no variables, no functions, no type variables and no inference. A call is
represented by the positions of its arguments.

| Claim | Status |
|---|---|
| Measures form an abelian group under their equality | Proved: `measure_group_laws` |
| Equality of measures is decidable | Proved: `meqb_iff` |
| A factor defined unit by unit does not depend on how a measure is written | Proved: `evalq_meq`, `readings_well_defined` |
| Convertibility is decidable, and an equivalence that contains equality | Proved: `convb_iff`, `conv_equivalence` |
| The conversion factor does not depend on the path | Proved: `coherence` |
| Equal measures convert with factor one | Proved: `cfactor_equal` |
| Compound measures need no declarations of their own | Proved: `compound` |
| A dimension defined as a quotient accepts every quotient of its parts | Proved: `quotient_dimension` |
| The choice of base unit does not change any conversion | Proved: `base_independent` |
| Inserted conversions preserve the meaning of the program | Proved over rationals: `elab_preserves_meaning` |
| A conversion never changes the dimension of a quantity | Proved: `elab_keeps_dimension` |
| The path a value took does not show in the result | Proved over rationals: `elab_path_independent`, `elab_fuses` |
| Whether an integer conversion is exact is decidable | Proved: `int_factor_iff`, `int_factor_none` |
| Exact conversion orders units from coarse to fine | Proved: `int_conv_order` |
| An integer operation on two units is inferred at the finer one | Proved: `int_join_finest` |
| An integer program that checks without accepting loss is exact | Proved for unbounded integers: `ielab_exact` |
| An accepted loss is less than one unit of the target | Proved for one conversion: `truncate_bound`, `truncate_exact` |
| Accepting loss changes nothing in a program that has none | Proved: `ielab_lossy_conservative` |
| The equality used here is the least one satisfying the group laws | Not proved. It is the standard presentation of the free abelian group |
| Floating-point targets compute the same result | Not proved, and false in general. See below |
| Fixed-width integers do not overflow under an inserted scaling | Not proved. Integers are unbounded in the model |
| The error of a program with several accepted losses is bounded | Not proved. The bound is for one conversion |
| Inference with conversions keeps principal types | Not proved. No inference is modelled |
| Conversion commutes with calling a function | Not proved. No functions are modelled |
| Offset units such as Celsius and Fahrenheit | Not modelled. They are excluded |

No theorem here depends on an axiom or on a `Spec` module.

## Why the idea is unsettled

The proofs show the arithmetic of conversion is sound. They do not show the feature is a good one.
These are the reasons for doubt.

1. **The cost is invisible.** A call that looks like a plain call performs a multiplication, and
   for integers may lose resolution or overflow. The exact and lossy cases are separated here, and
   the lossy one must be accepted at the position. Overflow is not handled at all.
2. **Floating point is not exact.** `elab_path_independent` and `elab_fuses` hold over rationals.
   Over floats, scaling by 1000 and then by 1/3600 is not the same number as scaling once by 5/18,
   so fusing two scalings changes results in the last bits. The compiler would have to fix one
   evaluation order and say so.
3. **Operators are left strict for rationals.** `km + m` over floats is still an error, because
   neither unit is the expected one. For integers the finer unit is forced by exactness, and
   `int_join_finest` shows it is the right choice. Nothing forces a choice for floats. Adopting
   the finer unit there as well is consistent, but it is a convention and not a theorem.
4. **Some integer pairs have no common unit.** Where neither factor is whole, as with miles and
   kilometres, the integer rule gives no unit and the addition is an error. A finer unit both
   convert to may not be declared.
5. **It interacts with inference.** A conversion is a coercion. This RFC inserts one only between
   two closed measures at a position whose expected measure is known. What happens when either
   side is still a type variable is not worked out.
6. **It removes a guarantee.** Today a unit-polymorphic function cannot depend on the size of its
   unit. A function with a parameter `distance<km>` is not unit-polymorphic: it fixes the unit it
   computes in. That is intended, but it is a loss of the invariance units of measure give.

## The parts that look worth keeping

- **One scale per unit, not pairwise formulas.** `coherence` holds because every factor is a
  quotient of two scales. A design with a table of pairwise formulas would need a consistency
  check on every cycle.
- **Dimension as the unit of checking.** `conv_equivalence` and `elab_keeps_dimension` say the
  type error worth keeping is a mismatch of dimension, and that it survives conversion.
- **Exactness as an order on units.** `int_conv_order` turns the integer question into a
  comparison the compiler can make, and `int_join_finest` gives inference a determinate answer.
- **Named and related dimensions.** `quotient_dimension` shows a definition such as
  `speed = distance / time` is free: it adds no declarations that could disagree.
- **The checker reports the hazard.** Whether a conversion is exact is computed, so a simple use
  needs no ceremony and a lossy one is reported at the position that causes it.

## Relation to the Tier 1 dimensional sheaf

The Clef design documents describe checking as a sheaf over the compilation stages: Source, the
program graph, the MLIR levels and the native binary. At Tier 1 the fact attached to a stage is an
integer exponent vector over the declared base measures, the maps between stages compose, and a
program is consistent when the facts agree along every adjacent step. The specification makes
every Tier 1 check an equality. `ntu-dimensional-architecture.md` §7.2 says identity is exact on
the unit, that no component is subtyped, and "There are no seals and no conversion sites."

This section records how the RFC meets that structure. It is a reading of the documents, and
nothing in it is proved here beyond the theorems it names. The sheaf description comes from the
design documents and the preprint *Fixed-Point Scaffolding in the Clef Programming Language*, not
from the specification commit this RFC is written against.

**What fits in Tier 1.**

- *Dimension is a quotient of the exponent vector.* Today `km` and `m` are independent
  generators. `dim` is a homomorphism from units to base units (`dim_mul`, `dim_pow`), and
  convertibility is equality after applying it (`convb_iff`). The check stays an equality in an
  abelian group.
- *Scale is a second homomorphism.* `scale` maps measures to the positive rationals under
  multiplication (`scale_mul`, `scale_div`), and `coherence` says a factor is the difference of
  two images. The positive rationals are a free abelian group on the primes, so a scale is itself
  an exponent vector. That last fact is standard and is not proved here.
- *Meaning preservation is one step of the gluing condition.* `elab_preserves_meaning` shows the
  step from source to elaborated program commutes with the meaning. The later steps, through MLIR
  to the binary, are not modelled.

**What conflicts.**

- *An inserted conversion is a conversion site.* The position that expects a measure coerces the
  unit, which §7.2 rules out in both of its clauses.
- *A measure gains runtime content.* Today a measure can be released without touching the value.
  With conversion a difference of measure is a multiplication, which the lowering must emit and
  account for.
- *The integer rule needs an order.* §7.2 says no ordering is needed. Choosing the finer unit is a
  divisibility check. For closed measures it is a computation. With measure variables it would
  likely be integer linear arithmetic, which the tiers place in Tier 2.
- *Operators.* `units-of-measure.md` requires matching measures for addition. The integer rule
  changes that signature. The rational half of this RFC does not.
- *Retention.* The specification requires the program graph to retain the measure of each value.
  The target language here erases measures, so the model is coarser than the graph.

**A shape that would fit.** §7.2 has a precedent. A `ReadWrite` handle becomes `ReadOnly` only
through `Ptr.asReadOnly`, which is a node in the graph. The same pattern for units is:

1. Tier 1 keeps unit identity exact. Dimension and scale are derived facts on the same vector.
2. A conversion is an explicit node in the graph that carries both measures and the factor.
   Identity is exact on each side of it.
3. Exactness, overflow and rounding are Tier 2 obligations on that node, discharged from range
   information. Width inference sees the scaling as ordinary arithmetic.

Whether the node is written by the author or inserted by elaboration is then the one remaining
choice. Written, it needs no change to §7.2. Inserted, §7.2 must be amended.

## Alternatives

- **Explicit conversion only.** Keep units unrelated to the type checker, and derive a `convert`
  function from the declarations. The factor is still computed and still coherent, and no cost is
  hidden. This keeps most of what the proofs establish.
- **Type-case on a measure.** A static type-case that branches on a measure variable, as RFC 0002
  does on types. The arm then holds a factor written by hand, which nothing checks. This RFC
  started as a way to avoid that.
- **Status quo.** Units with no declared relation, and factors written by hand.

## Impact and migration

A program that declares no unit sizes is unchanged: every unit is then its own base with size one,
so a conversion between equal measures has factor one by `cfactor_equal`. A program that adds
sizes to existing units accepts calls that were errors before.

## Unresolved questions

1. **Dimension-generic definitions.** A library function written over dimensions, such as an
   operator on a speed and a distance, and tied to concrete units at each call site. This needs
   functions and measure variables in the model. It may be a closed-set constraint in the sense of
   RFC 0001, with the dimension as the member set of a measure variable.
2. **Overflow.** Whether an inserted integer scaling must be shown not to overflow, and from what
   range information.
3. **Syntax for accepting loss.** How a position such as `distance<km>` says it accepts a loss of
   resolution for integers, and whether the default is an error or a warning.
4. **Floats and operators.** Whether `km + m` over floats is inferred at the finer unit, as it is
   for integers.
5. **Floating-point semantics.** Which evaluation order of scalings is specified, and whether
   fusing is allowed.
6. **Offset units.** Whether temperatures can be supported in positions that are not multiplied.
7. **Irrational and fractional factors.** Degrees and radians need an irrational factor, and a
   square root gives a fractional exponent, whose factor is a root.
8. **Inference.** The rule for a position whose measure is not yet closed.
9. **Written or inserted.** Whether the conversion node is written by the author, which leaves
   `ntu-dimensional-architecture.md` §7.2 as it is, or inserted by elaboration, which amends it.
*)
