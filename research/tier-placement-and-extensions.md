# RFC 0001 and RFC 0002 against the verification tiers

Research note for RFC 0001 (closed-set type constraints) and RFC 0002 (type-case over several constrained variables). Written 2026-11-16.

This note asks two questions. Where do the two RFCs sit in the tier system of the Dimensional Type System (DTS)? And what further capabilities could they carry? The second question is not limited to changes that keep the language as it is, so several ideas here are academic.

Nothing in this note is proved. Where it names a theorem, the theorem is in this repository and says what its own page says. Everything else is a reading or a proposal, and is marked as such.

Sources read for this note:

- RFC 0001 and RFC 0002 as modelled in `proofs/theories/RFC0001/*.v`, `proofs/theories/RFC0002/*.v` and `proofs/theories/Spec/*.v`.
- The Clef specification clone at commit `26207e0`: `spec/terms-and-definitions.md` (the entry *tier*), `spec/ntu-dimensional-architecture.md` §3.2 and §7.2, `spec/units-of-measure.md`, `spec/conformance.md` §6.1.
- **[fetched, summarised]** *The Compilation Sheaf*, <https://clef-lang.pages.dev/docs/design/categorical-foundations/the-compilation-sheaf/>. Read through a summarising fetch, not verbatim. Statements about it should be checked against the page before they are quoted in an RFC.
- **[fetched, summarised]** Haynes, *Fixed-Point Scaffolding in the Clef Programming Language*, arXiv 2606.02854. Same caveat.
- **[not re-read]** Eisenberg, Vytiniotis, Peyton Jones, Weirich, *Closed Type Families with Overlapping Equations*, POPL 2014. Cited from memory.

The word *sheaf* does not occur in the specification clone. The sheaf description comes from the design documents and the preprint.

## Short answer

1. **RFC 0001 fits inside Tier 1.** Its checks are equality against a finite list, its member set behaves like the ordered facts Tier 1 already carries, and its one semantic theorem is the commuting condition for one compilation step.
2. **RFC 0002 sits at the edge of Tier 1.** Its checks are finite and need no solver, but they are not polynomial in the number of variables and they are not pure equality.
3. **The tier discipline favours the equation reading of `:? 'A`**, the open question of RFC 0002. That reading is an equality check. The membership reading is a set test.
4. **Six extensions follow.** The strongest rests on one property: a closed set turns a statement about all admitted types into a finite conjunction, which an open constraint cannot do.

## 1. The tier system, as used here

The specification defines a tier as an organisational level of the verification architecture:

| Tier | Covers | Evidence |
|---|---|---|
| 1 | Admitted structural inference: dimensions and declared structural relationships | A kinded substitution or a derivation under the declared laws |
| 2 | Local analysis and supported solver fragments (`QF_LIA`, `QF_LRA`, `QF_BV`): range, layout, arithmetic | The checked condition, its assumptions, and an analysis result or solver proof |
| 3 | Parameterised domain and system theorems | A checked library theorem instance with its premises discharged |
| 4 | Relational judgments about executions, distributions or realisations | A derivation in an admitted relational logic |

A tier does not by itself establish decidability or a latency bound. Evidence may compose between tiers under `spec/conformance.md` §6.1.

The design documents describe checking as facts attached to the compilation stages (Source, the program graph, the MLIR levels, the native binary), with translations between stages that compose. A program is consistent when one choice of fact per stage agrees along every adjacent step. At Tier 1 the fact for a dimension is an integer exponent vector. `spec/ntu-dimensional-architecture.md` §7.2 adds that identity is exact on every dimensional component, that nothing is subtyped, and that "The enumeration sort needs no ordering; every check is equality".

## 2. Where RFC 0001 sits

| Piece of RFC 0001 | Tier | Reason |
|---|---|---|
| Satisfaction (`sat_decidable`) | 1 | Membership is equality against a finite list of closed types |
| Entailment (`entails_iff_sat`) | 1, with an order | The subset test. Decidable and finite, but it is an order, not an equality |
| Intersection on unification (`meet_sat`, `meet_greatest`, `meet_empty`, `meet_singleton`) | 1 | The member set of a variable is a lattice element. Unification takes the meet, and the empty set is a located contradiction |
| Definition-site checking (`derived_satisfaction`, `shared_operation`) | 1 | One witness lookup per member: a finite conjunction of Tier 1 checks |
| Coverage of a type-case (`coverage_total`) | 1 | A finite cover check |
| Specialisation (`specialization_preserves_meaning`) | 1, one step | The commuting condition for the saturation step. After it the constraint is discharged and nothing reaches MLIR |
| Untagged unions (`untagged_union_discriminable_falsified`) | Last stage | The native stage holds no type fact, so a type test cannot be decided there |

Three observations.

**The member set is a fact of the same kind Tier 1 already carries.** The design documents place escape classifications, which come from an ordered domain, beside dimensions. A member set is an element of the lattice of finite sets of closed types. It is not an abelian group, but it is finite, and its operations are intersection and inclusion.

**Principal types plausibly survive for one-variable sets, and this is not proved.** The DTS paper claims inference that is polynomial, complete and principal. A closed-set constraint is a disjunction of equations, `'T = int` or `'T = string`, and disjunction is what usually ends principality. With only unary sets and equations between types, the solver can keep one member set per class of unified variables and intersect on each merge. The principal answer is then the class together with its remaining set. `meet_greatest` is the lemma this argument needs. RFC 0001 lists the claim as not proved.

**The untagged-union theorem is a statement about a stage.** In the staged picture, the type of a value is a fact at the source and graph stages and is absent at the native stage. A type test must therefore be decided at a stage where the fact is still present, which is what the static type-case does: it is reduced at saturation.

### Tension with §7.2

RFC 0001 conflicts with the letter of §7.2 in one place: entailment is an order. The conflict is mild. §7.2 speaks of the components of a dimensional type, and a member set is a constraint on a variable, not a component of a type. `Constraints.v` says the same from its side: a member set is not a type.

## 3. Where RFC 0002 sits

| Piece of RFC 0002 | Tier | Reason |
|---|---|---|
| The instantiation table (`table_iff_valid`) | Edge of 1 | The set of joint solutions of the constraints. Finite and computable, with size up to the product of the set sizes |
| Coverage and reachability (`coverage`, `intersection_reachable_iff`) | Edge of 1 | Decided by enumeration of the table |
| The overlap check (`first_match_is_most_specific`, `order_is_irrelevant`) | Edge of 1 | Up to 2ⁿ − 1 regions for n tested variables, and the check compares arms by generality, an order |
| Binder typing (`equation_refines`) | 1 | Under the equation reading the arm learns a type equation |

**The constraint `'T : ('A | 'B)` is a disjunction of equations between variables.** This is a different kind of constraint from RFC 0001's. A unary set narrows one variable. This one relates three, and it has several incomparable solutions where abelian-group unification has one most general solution.

**Inferring such constraints is probably NP-hard. This is a sketch and has not been checked with care.** Take two distinct closed types `tt` and `ff`. For each Boolean variable take type variables `'X` and `'N`, both constrained to `(tt | ff)`, and a variable `'P` constrained to `((tt * ff) | (ff * tt))` and unified with `'X * 'N` by a use. Then `'N` is forced to differ from `'X`. For a clause over three literals take `'D : ('L2 | 'L3)` and `'C : ('L1 | 'D)`, and unify `'C` with `tt`. The constraints have a solution exactly when the formula is satisfiable. The sketch uses tuple types as members and unification of a constrained variable with a constructed type. If it holds, a solver that must decide whether such a system has any solution does the work of a SAT solver, which is outside the polynomial bound claimed for Tier 1.

This supports the restriction RFC 0002 already lists as unresolved question 5: these constraints are declared and never inferred. The compiler then checks a given table. It does not search for one.

**If a solver were used, the fragment is not one the specification lists.** Disjunctive type equations over constructed types belong to equality with datatypes. The Tier 2 entry names `QF_LIA`, `QF_LRA` and `QF_BV`.

### Evidence on the open question

RFC 0002 leaves open what `:? 'A` tests. Under the equation reading the test is "the scrutinee's type equals the type `'A` is instantiated to". Under the membership reading it is "the scrutinee's type is in `'A`'s set". The first is an equality between two types, which is the only kind of check §7.2 admits. The second is a set test. The tier discipline therefore points the same way as `equation_refines` and `membership_refines_falsified`. This is supporting evidence and not a proof.

## 4. Extensions

Each extension names the tier it would live in and what is missing.

### 4.1 Member sets over other sorts (Tier 1)

`Constraints.v` uses one fact about types: equality is decidable. The same definitions and theorems would hold over any sort with decidable equality. Candidates are measures, memory spaces, access kinds and regions.

```fsharp
let read<'a when 'a : (ReadOnly | ReadWrite)> (p: Ptr<int, 'a>) = ...
```

§7.2 forbids subtyping on these components. A closed-set constraint gives bounded polymorphism over them without subtyping: each call site is still an exact identity, and the definition is checked once against every member.

Missing: for measures, equality is the group equality and not syntactic identity, so membership must compare normal forms or use the computed equality of RFC 0003 (`meqb`). The compiler does not specialise on measures today, as the note `multi-variable-union-constraints.md` records.

### 4.2 Member sets as fibres of a map (Tier 1)

RFC 0003 defines a dimension as all measures with the same image under the map `dim`. That is a member set with infinitely many members and a decidable membership test: apply the map and compare. An enumerated set is the special case where the map has finitely many fibres of interest.

A constraint could then be written `'m : distance`, meaning every measure whose dimension is length. Entailment is equality of images. A body cannot enumerate arms over such a set, but it can be uniform in the member and take the computed factor as an input. This is the route to the dimension-generic library functions that RFC 0003 lists as its first unresolved question.

Missing: a model with measure variables and functions. A type-case over an infinite set needs a catch-all arm or a uniform body.

### 4.3 Agreement on overlaps in place of priority (Tier 1 or Tier 4)

RFC 0002 requires an intersection arm where two arms overlap. In the staged picture the arms are local definitions over regions of the instantiation table, and the function body is the result of gluing them. RFC 0002 glues by priority: the most specific arm wins. The other standard rule is agreement: two overlapping arms are accepted when their bodies are equal on the overlap.

On the overlap of `:? 'A` and `:? 'B` all three variables are the same type, so both bodies are typed at that one type and can be compared.

- If the two specialised bodies are identical, the check is structural and belongs to Tier 1.
- If they are proved to compute the same result, the check is a relational judgment and belongs to Tier 4.

Closed type families in Haskell use the first rule under the name *compatibility*, as recalled from Eisenberg et al.

This would answer unresolved question 2 of RFC 0002, whether one arm may cover several regions. It needs a model of arm bodies, which is unresolved question 4.

### 4.4 Patterns as members (Tier 1)

RFC 0001 requires closed members. Its unresolved questions 2 and 5 ask about members and inputs that mention type variables, and the note `overlapping-type-patterns.md` studies `list<'a>` against `'a`.

The overlap check of RFC 0002 covers this case if the overlap of two patterns is computed by unification. The overlap of `list<'a>` and `'a` is `list<'a>`, which is itself an arm, and it is the more specific one. `first_match_is_most_specific` is stated for any list of arms over a table. Unification is equality solving, so the check stays in Tier 1.

Missing: the theorem is proved over a finite table. A pattern has infinitely many instances, so the proof must be redone over a lattice of patterns.

### 4.5 Arms decided by a solver (Tier 2)

An arm could carry a guard over compile-time facts such as range, size or alignment.

```fsharp
match x with
| :? int when fits<u8>  -> ...
| :? int                -> ...
```

Coverage becomes the validity of the disjunction of the guards. Overlap becomes the satisfiability of a conjunction. The rule of RFC 0002, that a later overlapping arm must be more general unless an earlier arm takes the shared part, becomes a set of implications between guards. These are queries in the fragments Tier 2 names.

Missing: the same as 4.4. The proofs enumerate a table, and a guard ranges over infinitely many values.

A caveat applies to one tempting use. A type-case over the selected representation, `f32` against `f64`, would let a body specialise per representation. The specification makes the representation of a bare float unobservable, and a type-case is an observation. Such a case would be sound only if its arms were proved equivalent up to the rounding contract, which is 4.3 at Tier 4.

### 4.6 Laws and theorems per member (Tier 2 and Tier 3)

`derived_satisfaction` says a definition is checked once, against every member, and every call site inherits the result. The same shape applies to verification evidence.

**Laws.** A member set could carry declared laws.

```fsharp
type Additive = (int | float) with assoc (+), unit (+) 0
```

Each law is one obligation per member, discharged once. Integer addition passes associativity. Floating-point addition fails it, which is the reassociation hazard `spec/numeric-selection.md` §10 already names. A body may then rewrite by the laws its set carries, for example to reduce in parallel.

**Theorems.** A library theorem stated over `'T : C` is instantiated once per member, with its premises discharged. This is the Tier 3 pattern, and it is available only because the set is closed: an open member constraint has instances the compiler cannot enumerate, so a statement about all of them can never be discharged by cases.

**Transport.** `call_through_entailment` moves a checked definition along set inclusion. For evidence, that is the reuse rule `spec/conformance.md` §6.1 regulates: evidence established for a set holds for every subset.

Missing: a model of obligations attached to members, and the invalidation rule §6.1 requires when a member or a law changes.

## 5. What this suggests for the RFCs

- **RFC 0002 should model arm bodies next.** Its own unresolved question 4 asks for it, and 4.3 needs it. With bodies, the choice between priority and agreement can be stated and compared.
- **RFC 0001's largest drawback has a possible answer.** The RFC lists non-parametric generic code first among its drawbacks, and `case_free_parametric` confines the loss to bodies with a type-case. Under 4.3 with proved equivalence, a body with a type-case would be parametric up to that equivalence.
- **4.6 changes what the feature is for.** RFC 0001 is motivated by typing: errors at the definition, and the admitted set in the signature. A closed set that also makes proof obligations finite is a stronger argument for the feature than convenience.
- **The equation reading should be adopted**, on the combined evidence of RFC 0002 and section 3.

## 6. Not established

- That one-variable closed sets keep principal types.
- The NP-hardness sketch in section 3.
- That `first_match_is_most_specific` and `order_is_irrelevant` hold over patterns or solver predicates.
- Any of the extensions. None is modelled.
- The exact wording of the design documents, which were read through a summarising fetch.
