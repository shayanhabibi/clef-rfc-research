(**md # Discussion

## What the proofs cover

The model is small on purpose. It has one type variable, closed member types, operations with one
argument, pairs, `let` and the type-case. It has no functions as values, no inference and no
evaluation.

| Claim | Status |
|---|---|
| Satisfaction of a closed-set constraint is decidable | Proved: `sat_decidable` |
| Entailment is the subset rule, sound and complete | Proved: `entails_iff_sat` |
| Intersection on unification is the most general choice | Proved: `meet_sat`, `meet_greatest` |
| An empty intersection is an error, and one type solves the variable | Proved: `meet_empty`, `meet_singleton` |
| A definition that checks is well typed at every member | Proved: `derived_satisfaction`, `check_complete` |
| Narrowing a constraint, and calling through entailment, are sound | Proved: `check_narrowing`, `call_through_entailment` |
| An operation needs a witness at every member | Proved: `shared_operation` |
| A body with no type-case is uniform | Proved: `case_free_uniform` |
| Complete arms give code for every member | Proved: `coverage_total` |
| An untagged union cannot be tested at run time | Proved from an assumption: `untagged_union_discriminable_falsified` |
| A specialized body evaluates without a run-time type test | Holds by construction: specialized terms have no type-case. No evaluation is modelled |
| Inference with closed-set constraints keeps principal types | Not proved. `meet_greatest` is the lemma it would need |
| The local type equation of an arm is sound with inference | Not proved. No inference is modelled |
| An unconstrained variable stays parametric | Not proved. The rule is stated in prose |
| Several constrained variables in one definition | Not modelled |

Two assumptions come from the specification, and both are in the `Spec` modules:
`tycon_eq_dec` and `no_runtime_type_metadata`. The second is this repository's reading of the spec
and is not a quotation from it.

## Drawbacks

- **Non-parametric generic code.** A static type-case lets a generic body behave differently per
  type. `case_free_uniform` confines the loss to bodies that use one, but the declared type of
  such a function no longer implies the free theorems an unconstrained signature does.
- **Local type refinement in the checker.** An arm adds a local type equation, the mechanism GADT
  pattern matching needs. It interacts with inference, which is why the result type must be known
  in advance. This is the largest implementation cost in the proposal.
- **Code size.** A definition with several set-constrained variables has up to the product of
  their set sizes in specializations. The bound is finite and visible in the signature, but it is
  multiplicative.
- **A third mechanism.** Authors must choose among a discriminated union, an SRTP constraint and a
  closed-set constraint. The dividing rule is simple (run-time variation, open static set, closed
  static set) but it is one more rule.
- **Pressure toward union types.** The syntax resembles a union type. Users will ask for
  `int | string` in type position, and each such request must be declined on the grounds proved in
  [Representation](Clef.RFC0001.Representation.html).

## Alternatives

- **Status quo.** Use one function per type, a discriminated union, or an `inline` SRTP function.
  This leaves the three problems under Motivation in place.
- **Tagged anonymous sum type.** Add a structural sum to `NativeType`, dual to `TAnon`, laid out as
  a discriminated union. `tagged_union_discriminable` shows it is sound. It gives run-time
  heterogeneity, which this RFC does not. It was not chosen because it needs a new type
  constructor, a canonical member order for wire tags, a rule for type variables inside the sum,
  and either explicit injection or a subsumption rule. It remains open as a separate proposal and
  is not blocked by this one.
- **Untagged union type.** Excluded by `untagged_union_discriminable_falsified`.
- **Ad hoc overloading of module functions.** Permit several definitions of one name at different
  types. This gives the call-site convenience but not a single body or a single signature, and it
  complicates name resolution and inference more than a constraint does.
- **Nominal traits.** Declare a trait and implement it for each admitted type. This is the approach
  the SRTP design avoids, and it yields an open set unless a sealing mechanism is added as well.
- **Per-instantiation checking.** Keep the closed set but check the body at each instantiation, as
  templates do. Rejected because it gives up `derived_satisfaction`, which is the main benefit a
  closed set has over open SRTP.

## Impact and migration

**Existing code.** The change is additive. The new grammar alternative was a syntax error before,
so no conforming program changes meaning.

**Specification chapters.**

| Chapter | Change |
|---|---|
| Types and Type Constraints | New grammar alternative, a new subsection on closed-set constraints, and a replacement for the example that uses `obj` |
| Inference and Constraint Solving | A new subsection on solving closed-set constraints, with derived satisfaction added to the member, equality and comparison rules |
| Patterns | Static type-case rules added to dynamic type-test patterns |
| Namespace and Module Signatures | A conformance rule for member sets |
| Error Handling | New diagnostics: ill-formed member set, empty intersection, operation not shared by all members, test against a non-member, type test on an unconstrained variable |
| Program Semantic Graph | Saturation reduces static type-cases per specialization |

No representation chapter changes.

**Toolchain.** CCS needs the constraint form, the solver rules, local refinement and the coverage
check. Baker's saturation needs the type-case reduction. Alex and the backends are unaffected,
since nothing new reaches them.

## Unresolved questions

1. **Syntax.** Whether `'T : (int | string)` is the right surface form, or whether a keyword form
   is clearer and leaves the bar free in constraint position.
2. **Generic members.** Whether a member may mention type variables of the enclosing definition
   under a pairwise non-unifiability rule. This draft requires closed members, and the model
   depends on it.
3. **Named member sets.** Whether a member set can be abbreviated and reused, and whether such a
   name would be mistaken for a type.
4. **Expression form.** Whether a type test as a Boolean expression is admitted on a
   set-constrained variable, where it would be a constant per specialization.
5. **Constructed inputs.** Whether a static type-case may take an input whose type is constructed
   from the variable.
6. **Exact inference rule for refinement.** The precise condition under which an inference
   variable counts as local to an arm.
7. **Separate compilation.** Whether an implementation may, or must, pre-generate every
   specialization of an exported set-constrained definition.
8. **Foreign types.** Whether `JsValue` and `JsRef` may be members. They support no operations, so
   a member set containing one admits almost no shared operation.
*)
