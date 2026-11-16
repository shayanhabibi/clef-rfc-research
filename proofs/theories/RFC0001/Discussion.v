(**md # Discussion

## What the proofs cover

The model is small on purpose. It has one type variable, closed member types, operations with one
argument, pairs, `let` and the type-case, with typing and evaluation for both source and
specialized terms. It has no functions as values and no inference.

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
| A specialized body evaluates without a run-time type test, and returns what the source returns | Proved: `specialization_preserves_meaning` |
| A typed specialization evaluates to a value of its type | Proved from an assumption: `specialization_is_safe` |
| A definition that checks runs at every member | Proved from an assumption: `checked_definition_runs` |
| A body with no type-case cannot observe its instantiation | Proved: `case_free_parametric` |
| Extension: the obligations of a set and a list of laws are a finite list | Proved: `obligations_exact` |
| Extension: evidence for a law moves to narrower sets and to intersections | Proved: `law_narrowing`, `meet_carries`, `carries_member` |
| Extension: rewriting a specialization by a law the member satisfies keeps its result | Proved from an assumption: `rewrite_sound`, `law_iff_rewrite` |
| Extension: a checked definition rewritten by the laws its set carries keeps its meaning | Proved from an assumption: `rewritten_definition_keeps_meaning` |
| Extension: a law derived by rewriting holds wherever its premises do | Proved from an assumption: `derived_law`, `reversal_from_commutativity`, `theorem_per_member` |
| Extension: evidence for a law depends only on the witnesses the law uses | Proved: `evidence_survives_unrelated_change` |
| Extension: a law holds or fails at a particular type, such as `int` or `float` | Not modelled. Operations are assumptions of the model |
| Extension: a rewritten specialization still has its declared type | Not proved |
| Inference with closed-set constraints keeps principal types | Not proved. `meet_greatest` is the lemma it would need |
| The local type equation of an arm is sound with inference | Not proved. No inference is modelled |
| An unconstrained variable stays parametric | Not proved. The rule is stated in prose |
| Several constrained variables in one definition | Not modelled |

Three assumptions come from the specification, and all are in the `Spec` modules:
`tycon_eq_dec`, `witness_sound` and `no_runtime_type_metadata`. The last is this repository's
reading of the spec and is not a quotation from it.

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

## Relation to the verification tiers

The specification organises checking into
[tiers](https://clef-lang.com/spec/draft/terms-and-definitions/#verification).

| Tier | Covers | Evidence |
|---|---|---|
| 1 | Structural inference: dimensions and declared structural relationships | A substitution or a derivation under the declared laws |
| 2 | Local analysis and supported solver fragments: range, layout, arithmetic | The checked condition and an analysis result or solver proof |
| 3 | Parameterised domain and system theorems | A checked library theorem instance with its premises discharged |
| 4 | Relational judgments about executions | A derivation in an admitted relational logic |

The design documents describe checking as facts attached to the compilation stages (source, the
program graph, the MLIR levels, the native binary) that must agree along every step.
[NTU Dimensional Architecture §7.2](https://clef-lang.com/spec/draft/ntu-dimensional-architecture/#72-dimensional-type-identity)
adds that every Tier 1 check is an equality and that no
ordering is needed.

The research note
[RFC 0001 and RFC 0002 against the verification tiers](https://shayanhabibi.github.io/clef-rfc-research/research/tier-placement-and-extensions/)
gives the sources and the full argument. This section records the conclusions for this RFC. They
are a reading of the specification and the design documents, and none is a theorem.

| Piece | Tier | Reason |
|---|---|---|
| Satisfaction (`sat_decidable`) | 1 | Membership is equality against a finite list of closed types |
| Entailment (`entails_iff_sat`) | 1, with an order | The subset test is finite and decidable, but it is an order and not an equality |
| Intersection on unification (`meet_sat`, `meet_greatest`, `meet_empty`) | 1 | The member set of a variable is a lattice element. Unification takes the meet, and the empty set is a contradiction located at that variable |
| Definition-site checking (`derived_satisfaction`, `shared_operation`) | 1 | One witness lookup per member: a finite conjunction of Tier 1 checks |
| Coverage (`coverage_total`) | 1 | A finite cover check |
| Specialisation (`specialization_preserves_meaning`) | 1, one step | The commuting condition for the saturation step. After it the constraint is discharged and nothing reaches MLIR |
| Untagged unions (`untagged_union_discriminable_falsified`) | The last stage | The native stage holds no type fact, so a type test cannot be decided there |
| Extension: a law at a member (`carries`, `rewrite_sound`) | 2 | One obligation per member, about what an operation computes. An analysis or a solver discharges it |
| Extension: a library theorem at a member (`theorem_per_member`) | 3 | A theorem proved once, instantiated at a member with its premises discharged |

Three points follow.

- **The member set is a fact of a kind Tier 1 already carries.** The design documents place escape
  classifications, which come from an ordered domain, beside dimensions. A member set is an
  element of the lattice of finite sets of closed types.
- **Principal types plausibly survive, and this is not proved.** A closed-set constraint is a
  disjunction of equations, and disjunction is what usually ends principality. With sets on single
  variables and equations between types, a solver can keep one member set per class of unified
  variables and intersect on each merge. `meet_greatest` is the lemma that argument needs.
- **The untagged-union theorem is a statement about a stage.** The type of a value is a fact at
  the source and graph stages and is absent at the native stage. A type test must be decided where
  the fact is still present, which is what the static type-case does: it is reduced at saturation.

The one conflict with the letter of [§7.2](https://clef-lang.com/spec/draft/ntu-dimensional-architecture/#72-dimensional-type-identity) is that
entailment is an order. It is mild: §7.2 speaks of
the components of a type, and a member set is a constraint on a variable, not a component of a
type.

## Possible extensions

These are not part of the RFC. They are recorded because the tier placement points at them, and
the research note gives each in more detail. Items 4 and 5 are modelled in
[Laws](Clef.RFC0001.Laws.html). The others are not modelled.

1. **Member sets over other sorts (Tier 1).** [Constraints](Clef.RFC0001.Constraints.html) uses one
   fact about types: equality is decidable. The same theory would hold over measures, memory
   spaces, access kinds and regions.
   [§7.2](https://clef-lang.com/spec/draft/ntu-dimensional-architecture/#72-dimensional-type-identity) forbids subtyping on those components, and a closed-set
   constraint gives bounded polymorphism over them without it, as in
   `'a : (ReadOnly | ReadWrite)`.
2. **Member sets as fibres of a map (Tier 1).** A dimension in
   [RFC 0003](Clef.RFC0003.Conversion.html) is every measure with the same image under a map. That
   is a member set with infinitely many members and a decidable test. An enumerated set is the
   finite case. This is the route to RFC 0003's dimension-generic functions.
3. **Patterns as members (Tier 1).** Members that mention type variables, ordered by the overlap
   check of [RFC 0002](Clef.RFC0002.Regions.html) with unification as the overlap. This addresses
   unresolved questions 2 and 5.
4. **Laws per member (Tier 2).** A member set could carry declared laws, each checked once per
   member. Integer addition passes associativity and floating-point addition fails it, which is
   the reassociation hazard
   [Numeric Selection §10.5.1](https://clef-lang.com/spec/draft/numeric-selection/#1051-obligations-by-arithmetic-family)
   names. A body may then rewrite by the laws its set carries. [Laws](Clef.RFC0001.Laws.html)
   models this. A rewrite by a law is sound exactly when the law holds at the member
   (`law_iff_rewrite`), and a checked definition rewritten by the laws its set carries keeps its
   meaning at every member (`rewritten_definition_keeps_meaning`).
5. **Theorems per member (Tier 3).** A library theorem stated over `'T : C` is instantiated once
   per member with its premises discharged. This is available only because the set is closed: an
   open member constraint has instances the compiler cannot enumerate. `derived_satisfaction` is
   this pattern for typing, and `call_through_entailment` is the rule that moves the evidence to a
   narrower set. [Laws](Clef.RFC0001.Laws.html) models a library theorem as a derivation of one
   law from others (`derived_law`, `theorem_per_member`), with `law_narrowing` as the rule that
   moves evidence to a narrower set.

**What the model of items 4 and 5 settles, and what it leaves.**

| Question | Answer |
|---|---|
| How many obligations a set has | One per member and law: `obligations_exact`, `obligations_count` |
| What a member added to a set costs | Its own obligations, and no evidence is lost: `carries_member` |
| What removing a member, or unifying two sets, costs | Nothing: `law_narrowing`, `meet_carries` |
| What a law permits | Rewriting a specialization at a member where it holds, with arguments of the member's type: `rewrite_sound` |
| Whether the law is needed | Yes. Where it fails, some rewrite by it changes a result: `law_iff_rewrite` |
| How a library theorem is proved once | As a sequence of rewrite steps: `derived_law`, with `reversal_from_commutativity` as the example |
| What must be discharged again when an operation's implementation changes | Only laws that use that operation at that argument type: `evidence_survives_unrelated_change` |

The last row is the invalidation rule of
[Conformance §6.1](https://clef-lang.com/spec/draft/conformance/#61-verification-evidence-and-composition),
item 6, for this kind of evidence.

Three things are left. The model does not decide a law: operations are assumptions of the model,
so "integer addition is associative and floating-point addition is not" is the motivating example
and is not a theorem here. It gives no syntax for declaring a law on a member set. And it proves
a rewritten specialization returns the same value, but does not prove the rewritten term is still
typed by the checker, which needs each law to have one type on both sides.
6. **Equivalent arms (Tier 4).** A type-case whose arms are proved to compute the same result
   behaves like one function. That would recover, up to the equivalence, the uniformity
   `case_free_parametric` proves for bodies with no type-case, and it answers the first drawback
   above. [RFC 0002](Clef.RFC0002.Bodies.html) models the rule for overlapping arms.

Extension 5 changes what the feature is for. The motivation above is about typing: errors at the
definition, and the admitted set in the signature. A closed set also turns a statement about every
admitted type into a finite list of obligations, which is a stronger reason for the feature than
convenience.

## Impact and migration

**Existing code.** The change is additive. The new grammar alternative was a syntax error before,
so no conforming program changes meaning.

**Specification chapters.**

| Chapter | Change |
|---|---|
| [Types and Type Constraints](https://clef-lang.com/spec/draft/types-and-type-constraints/) | New grammar alternative, a new subsection on closed-set constraints, and a replacement for the example that uses `obj` |
| [Inference and Constraint Solving](https://clef-lang.com/spec/draft/inference-constraint-solving/) | A new subsection on solving closed-set constraints, with derived satisfaction added to the member, equality and comparison rules |
| [Patterns](https://clef-lang.com/spec/draft/patterns/) | Static type-case rules added to dynamic type-test patterns |
| [Namespace and Module Signatures](https://clef-lang.com/spec/draft/namespace-and-module-signatures/) | A conformance rule for member sets |
| [Error Handling](https://clef-lang.com/spec/draft/error-handling/) | New diagnostics: ill-formed member set, empty intersection, operation not shared by all members, test against a non-member, type test on an unconstrained variable |
| [Program Semantic Graph](https://clef-lang.com/spec/draft/program-semantic-graph/) | Saturation reduces static type-cases per specialization |

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
