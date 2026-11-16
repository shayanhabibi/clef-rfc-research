# Closed-set constraints over several type variables

Research note for RFC 0001 (closed-set type constraints). Written 2026-11-15.

Sources read for this note:

- RFC 0001 as modelled in `proofs/theories/RFC0001/*.v` and `proofs/theories/Spec/*.v` of this repository.
- The Clef specification at a local clone of `clef-lang-spec`, directory `spec/` (repository HEAD `26207e0`; the RFC states it was written against `0ad783d`). Cited below as `spec/<file>`, with the heading.
- The compiler sources at a local clone of `clef`, directory `src/Compiler/`. Cited as `clef/src/Compiler/<path>`.
- Web sources fetched during this task are marked **[fetched]**. Papers cited from memory and not re-read during this task are marked **[not re-read]**; their titles and venues should be checked before they are quoted in an RFC.

The companion note `research/overlapping-type-patterns.md` (written concurrently by another agent) covers specificity ordering of overlapping *structural* patterns such as `list<'a>` against `'a`. This note covers only the overlap that comes from two *variables* being instantiated to the same type, and does not repeat that material.

## Short answer

1. **The request is coherent and the Clef type system can support it, without run-time type information.** Every generic definition is monomorphized, so at each specialization every type variable is a closed type and "is `'T` the same type as `'A`?" is decided by the compiler's ordinary type equality. Nothing in the specification contradicts this, with one exception to resolve: measure parameters are not part of the specialization key (see 2.6).

2. **The precise meaning is a finite table.** A set of closed-set constraints over variables `'A`, `'B`, `'T` denotes the finite set of instantiations (rows) that satisfy all of them. For `'A : (int | string)`, `'B : (string | float)`, `'T : ('A | 'B)` the table has 7 rows. The three arms `:? 'A & 'B`, `:? 'A`, `:? 'B` split the rows by which equations hold: `'T = 'A = 'B` (1 row), `'T = 'A ≠ 'B` (3 rows), `'T = 'B ≠ 'A` (3 rows). The split is always a partition.

3. **The intersection arm is reachable exactly when the member sets of `'A` and `'B` share a type**, and its instantiations are exactly the intersection RFC 0001 already computes when two constrained variables unify (`meet` in `Constraints.v`). That is the sense in which the arm "handles the unification".

4. **Recommended rule: require the intersection arm when it is reachable, and reject it when it is not.** The match keeps the specification's existing top-to-bottom selection, and a static check rejects two arms that overlap without either containing the other unless an earlier arm covers the overlap. This is the "lattice rule" that Rust's specialization RFC describes but did not adopt, and it matches how C++ makes incomparable partial specializations an error until a more specialized one is added. Under this check, first-match selection and most-specific selection give the same answer, which is a theorem worth proving.

5. **No new syntax is needed for the arm.** The specification already has conjunctive patterns (`pat & pat`), so `:? 'A & :? 'B` is already grammatical. `:? 'A & 'B` can be accepted as shorthand. The type grammar has no `&` form and does not need one.

6. **The smallest useful step is smaller than the author's example.** It is: several independently constrained variables in one definition, plus a type test of one constrained variable against another (`match (x: 'A) with :? 'B as y -> ...`). `'T : ('A | 'B)` and the three-arm match are a second step built on it. A third step, constraints that relate variables by an explicit table, gives finite type-level functions (result type determined by argument types).

7. **Two things in the author's sentence need a decision from the author.** First, whether `:? 'A` means "`'T` is the type `'A` was instantiated to" (the reading used here) or "`'T` is one of the types in `'A`'s member set" (a Venn-diagram reading that RFC 0001 can already express with one variable). They differ: with `'A = int`, `'B = string`, `'T = string`, the first reading selects the `'B` arm and the second selects the `'A & 'B` arm. Second, whether "implicit" means the compiler supplies the arm. It cannot synthesise a body; what it can do is not require the arm when it is unreachable, and accept an or-pattern `:? 'A | :? 'B` whose single body is checked in all three regions.

## Part 1. The Clef type system as specified

### 1.1 Type universe and representation

- Types are compile-time only. "Clef resolves all type information at compile time through CCS" and type tests "are resolved statically where possible, or generate compile-time errors" ([`types-and-type-constraints.md`](https://clef-lang.com/spec/draft/types-and-type-constraints/), opening Clef Note).
- The internal representation is one algebra, `NativeType`, with constructors `TForall`, `TApp`, `TTuple`, `TFun`, `TVar`, `TMeasure`, `TAnon`, `TUnion`, `TByref`, `TNativePtr`, `TError` ([`type-representation-architecture.md`](https://clef-lang.com/spec/draft/type-representation-architecture/), §3 "NativeType Definition"). There is no union-of-types or intersection-of-types constructor.
- Named types are nominal: "Two types are equal iff their TypeConRefs are equal" (same file, [§2.1](https://clef-lang.com/spec/draft/type-representation-architecture/#21-why-this-pattern)). Unification of named types compares the constructor reference and recurses on arguments ([§7 "Unification"](https://clef-lang.com/spec/draft/type-representation-architecture/#7-unification)). Anonymous records (`TAnon`) are structural ([§3.2](https://clef-lang.com/spec/draft/type-representation-architecture/#32-anonymous-records-vs-named-records)).
- There is no universal base type, no `obj`, no boxing, no run-time type metadata: "Native binaries do not carry type metadata. There is no mechanism to inspect a value's type at runtime" ([`native-type-mappings.md`, "Why `obj` Cannot Exist in Native Compilation"](https://clef-lang.com/spec/draft/native-type-mappings/#why-obj-cannot-exist-in-native-compilation)); "There is no boxing, no `System.Type`, and no runtime type discovery" ([`types-and-type-constraints.md`, "Type Conversions"](https://clef-lang.com/spec/draft/types-and-type-constraints/#type-conversions)).
- `int` and `int32` are distinct types even where they have the same width ([`types-and-type-constraints.md`, "Expanding Abbreviations and Inference Equations"](https://clef-lang.com/spec/draft/types-and-type-constraints/#expanding-abbreviations-and-inference-equations)). Type identity is therefore not representation identity, which is what RFC 0001's `no_runtime_type_metadata` axiom relies on.

### 1.2 Type variables

- Three written forms: `'ident`, `_`, and `^ident` (statically resolved). A `^ident` variable "can be generalized only at `inline` definitions" ([`types-and-type-constraints.md`, "Variable Types"](https://clef-lang.com/spec/draft/types-and-type-constraints/#variable-types)).
- A variable that refers to an explicit type parameter is *rigid* and has a definition site; others are inference variables (same file, "Type Variables and Definition Sites").
- In the compiler a type parameter is a record with a mutable `Constraints: Constraint list` and a union-find parent (`clef/src/Compiler/NativeTypedTree/NativeTypes.fs`, `TypeParam`, about line 1472). Its kind is `Type`, `Measure` or `Carrier`; `Carrier` is a variable that ranges only over numeric kinds (`TypeParamKind`, about line 1286).

### 1.3 Constraint forms that exist today

The grammar ([`types-and-type-constraints.md`](https://clef-lang.com/spec/draft/types-and-type-constraints/), opening grammar, `constraint :=`) lists: coercion `typar :> type`; nullness (rejected, CCS8010); member constraint `static-typars : (member-sig)`; default constructor; `struct`; `not struct`; `enum<type>`; `unmanaged`; `equality`; `comparison`. The delegate constraint is listed in the prose and rejected ("Delegate Constraints"). Constraints are joined with `and` (`typar-constraints := when constraint and ... and constraint`).

Points that matter for this note:

- **There is no intersection or conjunction syntax in types or constraints.** The type and constraint grammar contains no `&`. F#'s later `'T & #IFoo` shorthand is not in the Clef grammar. Conjunction of constraints is `and` only.
- **There is no user-written equation between type variables.** Equations `typar = type` exist only as inference constraints produced by checking ([`inference-constraint-solving.md`, "Solving Equational Constraints"](https://clef-lang.com/spec/draft/inference-constraint-solving/#solving-equational-constraints)).
- **One existing constraint already ranges over several variables with an "or".** A member constraint has a support set, `(^a or ^b) : (static member (+) : ^a * ^b -> ^c)`, and "is satisfied if one of the types in the support set" has the member ([`types-and-type-constraints.md`, "Member Constraints"](https://clef-lang.com/spec/draft/types-and-type-constraints/#member-constraints); [`inference-constraint-solving.md`, "Solving Member Constraints"](https://clef-lang.com/spec/draft/inference-constraint-solving/#solving-member-constraints)). This is a precedent for a disjunctive constraint over two variables. It is kept tractable by requiring `^` variables, so it is only ever solved against named types at an inlined use.
- **Subtype constraints and flexible types `#type` are in the grammar** ("Constrained Types", "Subtype Constraints"), but the compiler's solver treats a subtype constraint as equality (`clef/src/Compiler/NativeTypedTree/Unify.fs`, `solveConstraint`, the `Constraint.Subtype` case, about line 481) and the cast-checking code states "there is no subtyping" (`clef/src/Compiler/NativeTypedTree/Expressions/TypeOperations.fs`, comment on `refuseCast`, about line 24). The specification and the compiler disagree here; the specification text is largely inherited from F#.
- **Equality and comparison** are "resolved through SRTP ... against the native witness hierarchy" ([`types-and-type-constraints.md`, "Equality and Comparison Constraints"](https://clef-lang.com/spec/draft/types-and-type-constraints/#equality-and-comparison-constraints), Clef Note).
- **The compiler's constraint type is small**: `Equals`, `HasMember` (one type, no support set), `Subtype`, `OperandOf` (`NativeTypes.fs`, `Constraint`, about line 1492). `OperandOf` is described as a "kind dispatch ... which fires when the variable binds (numeric or string, else CCS8000)". That is a built-in closed set attached to a variable and discharged when the variable is bound, the same shape as RFC 0001's constraint.

### 1.4 Solving, generalization, `inline`

- Solving is incremental normalisation: each new constraint is reduced to primitive constraints on variables; an equation eliminates a variable and its other constraints are solved again ([`inference-constraint-solving.md`, "Constraint Solving"](https://clef-lang.com/spec/draft/inference-constraint-solving/#constraint-solving), "Solving Equational Constraints").
- The specification restricts constraint shapes in two places "to simplify type inference": a variable may not carry two instantiations of the same named type as subtype constraints, and may not be in two member constraints with the same name and support set; in both cases the solver forces equality instead of keeping alternatives ([`types-and-type-constraints.md`, "Subtype Constraints"](https://clef-lang.com/spec/draft/types-and-type-constraints/#subtype-constraints) and "Member Constraints"). The specification already prefers forcing a single answer over carrying a disjunction.
- Generalization happens at function, value and member definitions; `^` variables are generalized only at `inline` definitions; "a declaration that includes explicit generic parameters will not be generalized beyond those generic parameters" ([`inference-constraint-solving.md`, "Generalization"](https://clef-lang.com/spec/draft/inference-constraint-solving/#generalization)).
- The specification says type inference is Hindley-Milner with let-polymorphism and that the design "maintains principal types throughout type inference" ([`types-and-type-constraints.md`, "Unified Type Representation"](https://clef-lang.com/spec/draft/types-and-type-constraints/#unified-type-representation)). Any extension has to say how it keeps that claim.
- `inline` "enables body expansion at call sites" and has an additional escape-analysis role ([`special-attributes-and-types.md`, "Inline and Optimization Attributes"](https://clef-lang.com/spec/draft/special-attributes-and-types/#inline-and-optimization-attributes)).

### 1.5 Specialization and witnesses

- "Monomorphization, the instantiation of polymorphic types with concrete types, occurs during PSG saturation" ([`types-and-type-constraints.md`, "Unified Type Representation"](https://clef-lang.com/spec/draft/types-and-type-constraints/#unified-type-representation)). "Generic type parameters are monomorphized (specialized at each call site)" ([`native-type-mappings.md`, "Why `obj` Cannot Exist in Native Compilation"](https://clef-lang.com/spec/draft/native-type-mappings/#why-obj-cannot-exist-in-native-compilation), item 3). Generic unions "SHALL be fully monomorphized; no runtime type parameters" ([`discriminated-union-representation.md`](https://clef-lang.com/spec/draft/discriminated-union-representation/), normative list near the end).
- The specification of the pass itself is thin. [`program-semantic-graph.md` §12](https://clef-lang.com/spec/draft/program-semantic-graph/#12-psg-saturation) describes saturation in terms of sequence state machines and match decomposition and does not state a rule for specialization keys. The implementation does: `clef/src/Compiler/Nanopass/Monomorphization.fs` clones a generic module-level function "for every distinct type-argument tuple found at its use sites" (file header comment).
- Operator and member resolution is recorded per node as a `WitnessResolution` with the operator, the argument type and the resolved member ([`program-semantic-graph.md`](https://clef-lang.com/spec/draft/program-semantic-graph/), §3.3 "SRTP Resolution"). Types are attached to every node when it is built ([§3.2 "Type Attachment"](https://clef-lang.com/spec/draft/program-semantic-graph/#32-type-attachment)).

### 1.6 `:?`, patterns and exhaustiveness

- The specification's text for `:?` is the F# text: a "dynamic type-test pattern matches any value whose runtime type is `type` or a subtype" ([`patterns.md`, "Dynamic Type-test Patterns"](https://clef-lang.com/spec/draft/patterns/#dynamic-type-test-patterns)), together with a Clef statement that `:?` is "resolved statically" illustrated by an example that takes `obj` ([`types-and-type-constraints.md`](https://clef-lang.com/spec/draft/types-and-type-constraints/), "No Dynamic Type Tests"). RFC 0001 already identifies this as unreachable by a conforming program.
- **The compiler rejects every `:?` today.** The pattern form produces CCS8401 with "type tests have no native graph form" (`clef/src/Compiler/NativeTypedTree/Expressions/Patterns.fs`, the `SynPat.IsInst` case, about line 246); the expression form is refused the same way (`TypeOperations.fs`, `checkTypeTest`). So the static type-case has no existing behaviour to stay compatible with.
- Rules "are attempted in order from top to bottom and left to right" ([`patterns.md`](https://clef-lang.com/spec/draft/patterns/), opening paragraph). The existing selection rule is first-match.
- Conjunctive patterns `pat & pat` and disjunctive patterns `pat | pat` exist; a disjunctive pattern requires that "both patterns must bind the same set of variables with the same types" ([`patterns.md`, "Conjunctive Patterns"](https://clef-lang.com/spec/draft/patterns/#conjunctive-patterns), "Disjunctive Patterns").
- A redundant type-test rule gets a "never matched" warning ("Dynamic Type-test Patterns").
- Exhaustiveness: [`native-type-universe.md`](https://clef-lang.com/spec/draft/native-type-universe/) says "Pattern matching is verified exhaustive at compile time. Missing cases produce warnings/errors" (the paragraph headed "Exhaustiveness" under the discriminated-union part), while [`patterns.md`, "Exhausted Match Rules"](https://clef-lang.com/spec/draft/patterns/#exhausted-match-rules), specifies run-time termination when no rule matches. The specification does not state one rule for when an incomplete match is an error. RFC 0001's coverage rule (every member tested) is stricter than both and is the right model for a construct with no run-time fallback.

### 1.7 Measures and range facts

- Measures are a separate kind with their own equational theory and "contribute to a type's dimensional identity" ([`units-of-measure.md`](https://clef-lang.com/spec/draft/units-of-measure/), opening paragraph).
- The nearest thing to refinement typing is value-range analysis: "Clef infers numeric representation from the value's range" with stated lineage from "F\*'s refinement-typed machine integers" ([`width-inference.md`](https://clef-lang.com/spec/draft/width-inference/), §1 "Overview"). These are facts about values recorded on the graph, not types, and they do not give type-level computation.
- `static-parameter` appears once, in the `type-arg` grammar, and is not elaborated anywhere else in the specification (searched for the term across `spec/*.md`).
- The specification has no dependent types, no type-level functions and no type families (searched for those terms; no hits).

### 1.8 Existing mechanisms that could carry the feature

| Mechanism | Where | What it offers |
|---|---|---|
| Monomorphization per type-argument tuple | `Monomorphization.fs`; [`native-type-mappings.md`](https://clef-lang.com/spec/draft/native-type-mappings/) | Every variable is closed at each specialization, so type equality between variables is decidable there |
| Decidable type identity | [`type-representation-architecture.md` §2.1](https://clef-lang.com/spec/draft/type-representation-architecture/#21-why-this-pattern), [§7](https://clef-lang.com/spec/draft/type-representation-architecture/#7-unification) | The test that selects an arm |
| "Definitely equivalent" and "feasibly equivalent" | [`types-and-type-constraints.md`, "Type Equivalence"](https://clef-lang.com/spec/draft/types-and-type-constraints/#type-equivalence) | Vocabulary for "this arm is reachable" (the tested type is feasibly equivalent to the input type under the constraints) |
| Constraints stored on the type parameter, re-solved on binding | `NativeTypes.fs` `TypeParam.Constraints`, `OperandOf` | The place a member set lives. A constraint over several variables does not fit a per-variable list and needs a shared constraint object |
| Support-set member constraints `(^a or ^b)` | [`types-and-type-constraints.md`, "Member Constraints"](https://clef-lang.com/spec/draft/types-and-type-constraints/#member-constraints) | Precedent for one constraint mentioning two variables |
| Conjunctive and disjunctive patterns | [`patterns.md`](https://clef-lang.com/spec/draft/patterns/) | Surface syntax for the intersection arm and for one arm covering several regions |
| "Never matched" warning | [`patterns.md`, "Dynamic Type-test Patterns"](https://clef-lang.com/spec/draft/patterns/#dynamic-type-test-patterns) | Where an unreachable intersection arm is reported |
| Saturation | [`program-semantic-graph.md` §12](https://clef-lang.com/spec/draft/program-semantic-graph/#12-psg-saturation) | Where a type-case is reduced to its selected arm |

## Part 2. Design analysis

### 2.1 Which reading the type system supports

Four readings of the author's sentence were considered.

- **R1. A third variable ranging over the two.** `'A : (int | string)`, `'B : (string | float)`, `'T : ('A | 'B)`, a value `x : 'T`, arms `:? 'A & 'B`, `:? 'A`, `:? 'B`. Members of `'T`'s set are variables. This is the reading analysed below. It is the only one in which all three arms are needed and in which "handling the unification" has a literal meaning: the first arm is the case where `'A` and `'B` are the same type.
- **R2. Two values matched jointly.** `(x: 'A, y: 'B)` matched with a tuple of type tests. This needs only several constrained variables and RFC 0001's existing arms; the rows are the product of the two sets. It does not produce an `'A & 'B` arm, so it does not explain the author's syntax, but it falls out of the same model for free (2.8, example 1).
- **R3. Member sets as regions.** `'A` and `'B` name sets, and `:? 'A & 'B` means "the type lies in both sets". With the example sets the regions are `{string}`, `{int}`, `{float}`. RFC 0001 can already say this with one variable `'T : (int | string | float)` and three arms; it needs named member sets (RFC 0001, unresolved question 3) and nothing else. No type equation between variables is involved.
- **R4. A direct test of one variable against another.** `x : 'A` matched with `:? 'B`. This is the core of R1 with the third variable removed. It is the smallest construct that makes "the two variables are the same type" observable.

R1 and R3 disagree on real programs (see short answer, item 7). The type system supports R4 and R2 with the least new machinery, R1 with one more rule, and R3 with none. The rest of this note develops R1 on top of R4.

### 2.2 Semantics: a finite table of instantiations

Let the definition have type variables `V`. An *instantiation* is a map σ from `V` to closed types. A constraint `X : (m1 | ... | mk)`, where each `mi` is a closed type or a variable of `V`, is satisfied by σ when σ(X) is one of σ(m1), ..., σ(mk), reading σ(mi) = mi for a closed member. A constraint system is satisfied by σ when every constraint is. The *table* Σ of a system is the set of satisfying instantiations.

Σ is finite when every variable has a constraint and the "member-of" dependency between variables is acyclic (each variable's members bottom out in closed types). Then every σ(X) is drawn from the finite set of closed leaf types reachable from X.

For the running example the table is:

| `'A` | `'B` | `'T` | Equations | Region |
|---|---|---|---|---|
| int | string | int | T=A≠B | only `'A` |
| int | string | string | T=B≠A | only `'B` |
| int | float | int | T=A≠B | only `'A` |
| int | float | float | T=B≠A | only `'B` |
| string | string | string | T=A=B | `'A & 'B` |
| string | float | string | T=A≠B | only `'A` |
| string | float | float | T=B≠A | only `'B` |

In general the row count here is 2·|C_A|·|C_B| − |C_A ∩ C_B|, where C_X is the member set of X.

A pattern `:? 'A` on input of type `'T` matches the rows with σ(T) = σ(A). Write M_A for that row set and M_B likewise. `:? 'A & :? 'B` matches M_A ∩ M_B. Because every row has σ(T) ∈ {σ(A), σ(B)}, the three sets

- M_A ∩ M_B (T = A = B),
- M_A \ M_B (T = A, A ≠ B),
- M_B \ M_A (T = B, A ≠ B)

are pairwise disjoint and cover Σ. That is the partition the author's three arms describe.

**What each arm may assume.** In the `'A & 'B` arm the equations `'T = 'A` and `'A = 'B` hold; in the `'A` arm `'T = 'A` holds and, if the intersection arm precedes it, also the disequation `'A ≠ 'B`; symmetrically for `'B`. Assuming an equation inside a branch is the GADT mechanism: Xi, Chen and Chen, "Guarded recursive datatype constructors", POPL 2003 **[not re-read]** introduced typing a match arm under type equalities determined by the constructor; Peyton Jones, Vytiniotis, Weirich and Washburn, "Simple unification-based type inference for GADTs", ICFP 2006 **[not re-read]** gave the rigid-type discipline for it; and OutsideIn(X) states the problem plainly: "Local type assumptions often result in the lack of principal types" (Vytiniotis, Peyton Jones, Schrijvers, Sulzmann, "OutsideIn(X): Modular type inference with local assumptions", JFP 2011, abstract, **[fetched]** from https://www.microsoft.com/en-us/research/publication/outsideinx-modular-type-inference-with-local-assumptions/).

A disequation cannot be used by a unifier. It matters only for deciding which rows an arm must be checked at, and the table gives that directly.

**Two ways to check an arm, and which one is the definition.** RFC 0001's model does not use local equations at all. Its check is `forallb (instance_ok G e r) C`: specialize and type the body once per member (`TypeCase.v`, `check`). The multi-variable analogue is: specialize and type the body once per row. Under that definition an arm's "local equations" are simply true of the closed substitution being checked, and no GADT-style inference is required for soundness. A compiler may instead check an arm once, symbolically, under the equations (cost independent of the row count), but that is an optimisation whose correctness condition is agreement with the per-row check. The RFC should define the rule per row and permit the symbolic implementation.

### 2.3 Is the intersection arm reachable, and is it required?

**Reachability.** M_A ∩ M_B is non-empty exactly when some closed type is in both member sets, that is when `meet C_A C_B` is non-empty. The types the unified variable can take in that arm are exactly `meet C_A C_B`, by `meet_sat`. If the sets are disjoint the arm matches no row and should be reported with the existing "never matched" diagnostic ([`patterns.md`, "Dynamic Type-test Patterns"](https://clef-lang.com/spec/draft/patterns/#dynamic-type-test-patterns)); given that a static type-case has no run-time fallback, an error is defensible. The "only" regions are always reachable once the intersection is handled, because a well-formed member set has at least two members (`Constraints.v`, `well_formed`), so the other variable can always differ.

**Requirement.** There are two candidate rules.

- **Rule F (first match only).** Arms are tried top to bottom, as every Clef match is ([`patterns.md`](https://clef-lang.com/spec/draft/patterns/), opening paragraph). `:? 'A | :? 'B` in two arms is then exhaustive: every row is in M_A or M_B. On the overlap the first-listed arm runs. Both bodies are well typed there, because on those rows `'A` and `'B` are the same type, so the choice is invisible to the type checker and is purely a behavioural choice made by textual order. This is what Haskell closed type families do ("equations are tried in order, from top to bottom", GHC User's Guide §6.4.10.2.3 "Closed type families", **[fetched]** from https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/type_families.html) and what Scala 3 match types do ("Sequentially consider each pattern", Scala 3 Reference, "Match Types", match type reduction, **[fetched]** from https://docs.scala-lang.org/scala3/reference/new-types/match-types.html).
- **Rule L (lattice).** Two arms whose row sets overlap, with neither containing the other, are an error unless an earlier arm (or earlier arms together) covers the overlap. Then `:? 'A` and `:? 'B` alone are rejected when the sets intersect, and the author's three-arm form is the minimal accepted one. This is the rule Rust's specialization RFC calls the lattice rule: partial overlap is allowed provided "there is an additional impl that covers precisely the area of overlap (the intersection)". The RFC did **not** adopt it; it "sticks with the simple chain rule for now", under which of two overlapping impls one must be more specific (RFC 1210, "Defining the precedence rules" and "Alternatives: The lattice rule", **[fetched]** from https://rust-lang.github.io/rfcs/1210-impl-specialization.html). C++ reaches the same place from the other side: when several partial specializations match and none is more specialized than all others, "the use of the template is ambiguous and the program is ill-formed" ([temp.spec.partial.match] paragraph 1, **[fetched]** from https://eel.is/c++draft/temp.spec.partial.match); the programmer fixes it by adding a specialization for the intersection. C++ diagnoses at the use; Clef can diagnose at the definition because the table is known there.

**Which is consistent with "most specific first".** Order arms by inclusion of their row sets. M_A ∩ M_B is below both M_A and M_B; M_A and M_B are incomparable when the sets overlap and each has a member outside the other. Rule L together with first-match gives: the selected arm at every row is the unique smallest arm containing that row. So Rule L is exactly the condition under which "first match" and "most specific" coincide, and under which reordering incomparable arms does not change the program. Rule F alone is consistent with the specification's pattern rule but not with the author's requirement, and it makes an overlap easy to miss when a member is later added to one set.

**Recommendation.** Keep first-match as the selection rule, because that is what [`patterns.md`](https://clef-lang.com/spec/draft/patterns/) says for every match, and add Rule L as a static check. Writing the intersection arm after `:? 'A` then triggers the "never matched" diagnostic, which forces it first.

**What "implicit" can mean.** The compiler cannot invent the body of the intersection arm. Three things can be implicit: the arm is not demanded when the sets are disjoint; an or-pattern `:? 'A | :? 'B -> e` is accepted as covering all three regions when `e` checks at every row, which is the author's way of saying "the choice does not matter"; and a wildcard arm covers whatever is left.

### 2.4 More than two variables

With `'T : ('X1 | ... | 'Xn)` a row falls in the region named by the non-empty set S of indices i with σ(T) = σ(Xi). There are up to 2^n − 1 regions. Region S is reachable exactly when the member sets of the variables in S have a common type (the others can always differ, as above). Under Rule L the arms required are the intersection arms for the reachable regions with |S| ≥ 2, so the worst case is exponential in n: three variables sharing one type need seven arms.

Options, in order of preference:

1. Require only reachable intersections. In practice sets overlap in few types.
2. Let one arm cover several regions: or-patterns and the wildcard. The body is checked at every row the arm is selected for.
3. Treat an or-pattern over all the variables as an explicit statement that overlap is immaterial.
4. Cap n, or leave Rule L as a warning that can be promoted.

A finer partition also exists: which of the `'Xi` equal each other, regardless of `'T` (set partitions, counted by Bell numbers). The arms above never need it, because a test on `'T` observes only the set S.

### 2.5 Decidability and cost

With closed leaf members everything is a finite computation on tables.

- **Satisfaction** of a system by a closed instantiation: evaluate each constraint; decidable because type equality is (`Spec/Types.v`, `ty_eq_dec`).
- **Definition check**: specialize and type the body at every row. The cost is the row count times the body size. The row count is bounded by the product of the leaf-set sizes; two variables of four types give 16 rows, four variables of eight give 4096. RFC 0001 already accepts a product bound for code size (`Discussion.v`, "Code size"). Checking cost can be kept well below the product by checking a subterm once per distinct projection of the rows onto the type variables that occur in the types of that subterm; a subterm that mentions only `'A` is checked |C_A| times however many other variables exist. Per-region symbolic checking (2.2) is the further optimisation. Neither changes what is accepted.
- **Entailment** generalises from subset of sets to subset of tables: a caller's table, mapped through the instantiation of the callee's variables, must be contained in the callee's table. `entails_iff_sat` generalises directly.
- **Unification** generalises from `meet` to selection and join. Unifying a constrained variable with a closed type keeps the rows that agree. Unifying two variables keeps the rows where they are equal and merges the columns. Two constraint systems sharing variables combine by natural join. `meet_sat`, `meet_greatest`, `meet_empty` and `meet_singleton` all have table versions; in particular, when a selection leaves every remaining row with the same value for a variable, that variable is solved.

**What breaks with generic members.** If a member is `list<'U>` with `'U` unconstrained, the table is infinite, per-row checking is no longer an algorithm, and the check must become symbolic: reachability becomes unifiability, disjointness becomes apartness, and the questions in `research/overlapping-type-patterns.md` apply in full. Haskell's closed type families show the cost: an equation is selected only when GHC "is sure that no incompatible previous equation will ever apply", which needs a conservative apartness check (GHC User's Guide §6.4.10.2.5, **[fetched]**). RFC 0001 already defers generic members (unresolved question 2). Variable members whose own sets are closed, as in `'T : ('A | 'B)`, do not have this problem: the table stays finite.

### 2.6 Static resolution, and one point where the implementation disagrees

At each specialization σ is fixed, so each test `:? 'A` on `'T` is the closed comparison σ(T) = σ(A), decided at compile time by constructor identity ([`type-representation-architecture.md` §2.1](https://clef-lang.com/spec/draft/type-representation-architecture/#21-why-this-pattern)). Saturation keeps the selected arm and drops the others, exactly as `spec` does in `TypeCase.v`. No tag, no type argument and no test reaches the backend. The specification's statements on monomorphization (1.5) support this and none contradicts it.

Two cautions:

- **Measures are not specialization keys.** In the compiler, "Measure-kinded parameters do not split physical bodies" and "a physical specialization can still be polymorphic in measures" (`clef/src/Compiler/Nanopass/Monomorphization.fs`, comments about lines 346 and 385), while the specification says a measure is part of a type's identity ([`units-of-measure.md`](https://clef-lang.com/spec/draft/units-of-measure/), opening paragraph). If `float<m>` and `float<s>` are two members, or if `'A = float<m>` and `'B = float<s>`, the selected arm differs between instantiations that share one physical body. Either members must be compared with measures erased (and member sets that differ only by measure rejected), or a set-constrained variable must add its measure arguments to the specialization key. RFC 0001 has the same gap with one variable; several variables make it easier to hit.
- **Specialization count.** The key for a definition is the row, so the bound is the row count, not "one per member for each variable" as RFC 0001's representation rule 1 says. Only rows that occur at use sites need be generated.

### 2.7 Inference

**The problem.** Unify `'T`, constrained by `'T : ('A | 'B)`, with `string`. The constraint becomes "`'A = string` or `'B = string`". Neither substitution is more general than the other, so there is no most general unifier. This is the general situation with union constraints: in the set-theoretic setting the solution of a constraint problem is a finite *set* of substitutions and not a single principal one (Castagna, Nguyen, Xu and Abate, "Polymorphic functions with set-theoretic types. Part 2: local type inference and type reconstruction", POPL 2015, the "tallying" problem, **[not re-read]**). OutsideIn(X) makes the matching point for local equalities (2.2). The Clef specification itself avoids alternatives in the two places they could arise in F# (1.4).

**Why tables rescue it for declared constraints.** If the solver's state is a substitution *and a residual table*, then selecting rows is a deterministic operation with a unique result, and the residual table is the most general description of what remains. `meet_greatest` is this fact for one variable. Constrained type systems in the HM(X) family obtain principal types this way, by making the constraint part of the type (Odersky, Sulzmann and Wehr, "Type inference with constrained types", TAPOS 1999, **[not re-read]**). A variable is replaced by a type only when every remaining row agrees on it.

**Restrictions that keep this simple.**

1. Closed-set constraints are never inferred from use; they come only from declarations (RFC 0001, "Origin"). A definition that declares one declares its full type-parameter list and its parameter and result types.
2. A set-constrained variable may be unified with another variable or with a closed type. Unifying it with a type that still contains inference variables is deferred until that type is closed, and is an error if it is not closed by the end of the enclosing definition. This stops a table from spreading onto fresh inference variables.
3. Inside a type-case arm, equations are between rigid variables and closed types only, and RFC 0001's locality rule applies unchanged: the result type of the match is fixed before the arms are checked. With per-row checking (2.2) this rule is needed only by a compiler that checks symbolically.
4. At a use site, the table is instantiated with fresh variables and solved by selection as argument types become known. If rows remain that disagree on a variable not otherwise determined, the use is ambiguous and needs an annotation.

### 2.8 What becomes expressible

All examples use closed leaf members. Syntax for the relation form in example 3 is illustrative.

**1. Joint match on two independently constrained values (R2).** No new arm form, only several variables.

```fsharp
let describe2<'A, 'B when 'A : (int | string) and 'B : (int | string)>
        (x: 'A) (y: 'B) : string =
    match x, y with
    | (:? int as i), (:? int as j)       -> formatInt (i + j)
    | (:? int as i), (:? string as s)    -> formatInt i + s
    | (:? string as s), (:? int as j)    -> s + formatInt j
    | (:? string as s), (:? string as t) -> s + t
```

RFC 0001's scope rule says the pattern input "has the type of the constrained variable itself, not a type constructed from it". A tuple pattern whose components are type tests satisfies it component by component; the rule should say so.

**2. A same-type fast path (R4).** The equation `'A = 'B` is available in the first arm, so `y` can be returned at type `'B`.

```fsharp
let widen<'A, 'B when 'A : (int | float) and 'B : (int | float)> (x: 'A) (toB: 'A -> 'B) : 'B =
    match x with
    | :? 'B as y -> y          // rows where 'A = 'B: no conversion
    | _          -> toB x
```

**3. A result type determined by the argument types.** A constraint over a tuple of variables is an explicit table. At a call the argument types select one row and the result variable is solved, which is a finite functional dependency (Jones, "Type classes with functional dependencies", ESOP 2000, **[not re-read]**) or a closed type family with closed equations (Eisenberg, Vytiniotis, Peyton Jones and Weirich, "Closed type families with overlapping equations", POPL 2014, **[not re-read]**).

```fsharp
let add<'A, 'B, 'R
        when ('A, 'B, 'R) : ( (int, int, int) | (int, float, float)
                            | (float, int, float) | (float, float, float) )>
        (a: 'A) (b: 'B) : 'R =
    match a, b with
    | (:? int as i),   (:? int as j)   -> i + j
    | (:? int as i),   (:? float as g) -> float i + g
    | (:? float as f), (:? int as j)   -> f + float j
    | (:? float as f), (:? float as g) -> f + g
```

Each arm is checked at the one row it selects, where `'R` is known, so the body type is checked against a closed type.

**4. The author's form (R1).**

```fsharp
let pick<'A, 'B, 'T
        when 'A : (int | string) and 'B : (string | float) and 'T : ('A | 'B)>
        (onA: 'A -> string) (onB: 'B -> string) (x: 'T) : string =
    match x with
    | :? 'A & :? 'B as v -> onA v + onB v   // 'A = 'B = 'T = string
    | :? 'A as a         -> onA a
    | :? 'B as b         -> onB b
```

A limitation shows in examples 2 and 3: a body can dispatch on a constrained variable only through a value of that type. A function whose *result* type is constrained and which has no argument of that type has nothing to match on. RFC 0001 leaves the expression form open (unresolved question 4); several variables make that question more pressing.

### 2.9 Related systems

| System | What it offers | Run-time type information |
|---|---|---|
| Semantic subtyping: Frisch, Castagna, Benzaken, "Semantic subtyping", JACM 2008 **[not re-read]** | Types as sets of values; union, intersection, negation; subtyping is set inclusion; a type-case expression whose branches are typed under the tested type and its negation | Required. The type-case inspects the value. This is the model RFC 0001's `Representation.v` rules out for Clef |
| Polymorphic set-theoretic types: Castagna et al., POPL 2014 (Part 1) and POPL 2015 (Part 2) **[not re-read]** | Adds type variables; Part 1 gives semantics and evaluation of polymorphic functions with type-case, Part 2 gives inference by tallying | Required for type-case. Part 1's evaluation has to account for type substitutions precisely because type-case makes instantiation observable **[not re-read; verify before quoting]** |
| Elixir: Castagna, Duboc, Valim, "The Design Principles of the Elixir Type System", 2023 **[not re-read]** | Set-theoretic types fitted to an existing dynamic language, with guards as the narrowing construct | Required. Guards are run-time tests on tagged values |
| TypeScript narrowing | Control-flow narrowing of union types; exhaustiveness through `never` | Required. `typeof` gives "information about the type of values we have at runtime" and a check on it "is a type guard" (TypeScript Handbook, "Narrowing", sections "`typeof` type guards" and "Exhaustiveness checking", **[fetched]** from https://www.typescriptlang.org/docs/handbook/2/narrowing.html) |
| Scala 3 union and intersection types, match types | Untagged unions over JVM values; match types are type-level functions reduced case by case, moving past a case only with a disjointness proof; a match expression can be typed by a match type when its patterns are typed patterns (Scala 3 Reference, "Match Types", **[fetched]**) | Required at the value level: a typed pattern is a class test. The type-level reduction itself is static |
| Haskell `a ~ b` and closed type families | Equality constraints as first-class givens and wanteds; closed families are ordered type-level functions (GHC User's Guide §6.4.10.2.3, **[fetched]**) | None. Types are erased, and for that reason a function cannot branch on a type without a class dictionary or a singleton value. Clef gets the branch from specialization instead |
| C++ templates, Rust specialization | Per-instantiation selection among overlapping definitions, ordered by specificity (2.3) | None. Selection happens at instantiation |

The useful comparison is this. The set-theoretic systems give the right *vocabulary*: regions as Boolean combinations, exhaustiveness as covering, the first arm's complement as the type of the second. They all discharge the type-case with a run-time test. The template and specialization systems give the right *mechanism*: selection at instantiation, with no test. The proposal here is the first vocabulary on the second mechanism, restricted to finite tables so that the definition can be checked once, which C++ and Rust do not attempt.

## Part 3. Proposal

### 3.1 Rules

Numbered as extensions to RFC 0001. "Row" means an instantiation that satisfies the definition's constraint system.

**M1. Several constrained variables.** A definition may declare any number of type variables with closed-set constraints. The constraint system denotes the table of 2.2. The definition is checked at every row; RFC 0001's rules are the case of one variable.

**M2. Variable members.** A member of a closed-set constraint may be a type variable of the same definition that itself has a closed-set constraint. Well-formedness: the "is a member of" relation between variables is acyclic; no member is listed twice; closed members are pairwise distinct; at least two members. A member that is a constructed type containing a variable remains excluded.

**M3. Relation constraints (optional, later).** `('X1, ..., 'Xn) : ((t11, ..., t1n) | ... | (tk1, ..., tkn))` with closed `tij`. It denotes the listed rows. M1 is the special case where the table is a product.

**M4. Satisfaction, entailment, unification.** As in 2.5: membership of a row; containment of tables under the instantiation map; selection, equi-selection and join. A variable is solved when all remaining rows agree on it. An empty table is an error.

**M5. Admissible tests.** In a static type-case whose input has the type of a set-constrained variable `'X`, a rule may test a closed type or a set-constrained variable `'Y` of the same definition. The test `:? 'Y` matches the rows with σ(X) = σ(Y). A test that matches no row is an error. A conjunctive pattern of tests matches the rows matched by both; `:? 'Y & 'Z` abbreviates `:? 'Y & :? 'Z`.

**M6. Arm typing.** A rule is checked at each row it is selected for. `:? 'Y as v` gives `v` the type `'Y`. In a conjunctive test either tested type may be used, since they are equal at every selected row. In an or-pattern the bound identifier has the type of the input variable.

**M7. Selection.** Rules are tried in source order, as for every match. At a row, the first rule whose pattern matches is selected.

**M8. Exhaustiveness.** Every row is matched by some rule. There is no run-time fallback.

**M9. Overlap (the intersection arm).** For any two rules whose matched row sets overlap with neither containing the other, every row in the overlap must be selected by an earlier rule. A rule that is selected at no row is reported as never matched. Consequence: with `'T : ('A | 'B)`, the arm `:? 'A & :? 'B` is required, and must come first, exactly when the member sets of `'A` and `'B` intersect; it is rejected when they do not.

**M10. Specialization.** A specialization is keyed by a row. Saturation replaces each type-case by the rule selected at that row. No test, tag or type argument is emitted. Measure arguments: see 2.6; the RFC must choose between erasing measures in member comparison and adding them to the key.

**M11. Inference restrictions.** As in 2.7, items 1 to 4.

### 3.2 Smallest version worth doing first

M1, M5 restricted to closed types and to one variable tested against another, M6 to M10. That is: several constrained variables; tuple scrutinee of type tests; the test `:? 'B` on `x : 'A`. It needs no variable members and no relation syntax, it already contains the overlap question (the test `:? 'B` followed by `:? int` overlaps when `'B` can be `int`), and it lets the Rocq model move from one variable to an environment of variables, which every later step needs. M2 is the second step and gives the author's example. M3 is the third.

### 3.3 Risks

- **Row explosion** in checking time and code size. Mitigated by projection-keyed checking (2.5) and by generating only used rows, but the worst case is multiplicative and M9 is exponential in the number of variable members.
- **Symbolic checking drifting from per-row checking.** A compiler that checks arms under equations instead of per row needs the locality discipline and can reject programs the definition accepts.
- **Measures** (2.6).
- **Order sensitivity.** M9 removes it between incomparable arms; guards reintroduce it, since a guarded rule may fall through. Guards on static type-case rules should either be excluded from the overlap computation (treated as possibly failing) or be disallowed at first.
- **Signature size and conformance.** Signature conformance "requires equal member sets" (RFC 0001, "Signatures"); with tables it requires equal tables up to variable renaming, which needs a canonical form.
- **Non-parametricity spreads.** With R4, a function over two "unrelated" variables can observe that they are equal. `case_free_parametric` still confines this to bodies with a type-case.
- **Pressure for a value-less type-case** (2.8, closing paragraph).
- **Specification inconsistencies inherited from F#** (subtyping text, `obj` example, two exhaustiveness statements; see 1.3 and 1.6) make "consistent with the specification" a moving target.

### 3.4 Statements worth proving in Rocq

Each is over an extended model: a finite list of type variables, an environment mapping each to its member list (closed types or earlier variables), terms as in `TypeCase.v` with a type-case whose arms test a closed type, a variable, or a conjunction, a reference evaluator that receives the row, and specialized terms with no type-case. None is true by unfolding one definition; the proof method is noted.

1. **The table is exactly the set of satisfying instantiations.** A computed enumeration `rows` of the constraint system contains σ if and only if σ satisfies every constraint, and lists no row twice. Induction over the variable list in dependency order. Corollary: the row count formula of 2.2 for the two-variable case.
2. **Regions partition the table.** For `'T` with variable members, the function sending a row to the set S of members equal to σ(T) is total with non-empty value, and the regions are its fibres. Stated for n members, proved by induction on the member list; the three-region statement is the instance n = 2.
3. **Reachability of the intersection is non-emptiness of `meet`.** Some row has σ(T) = σ(A) = σ(B) if and only if `meet C_A C_B <> []`; and the types taken there are exactly the members of the meet. Uses `meet_sat` and well-formedness (to build the witness row).
4. **Unique most specific arm.** If a type-case passes the exhaustiveness check (M8) and the overlap check (M9), then at every row the arm selected by first-match is matched, and its row set is contained in the row set of every other arm that matches that row. Induction over the arm list with the overlap check as invariant.
5. **Order independence.** Under M8 and M9, permuting the arms into any order that still passes M9 does not change the selected arm at any row, hence not the reference meaning. Follows from 4 by uniqueness of the least element; the content is that M9 is preserved in the right form.
6. **First-match without M9 is order dependent.** A concrete two-arm type-case and a row at which swapping the arms changes the evaluated result. A falsifying example, which shows M9 is not vacuous.
7. **Local equations are sound.** If an arm with pattern `:? 'Y` (or a conjunction) is selected at row σ, then σ(X) = σ(Y) for every tested `'Y`; and if an earlier arm tested `'Z` and was not selected, σ(X) ≠ σ(Z). Consequently substituting `'Y` for `'X` in the arm's typing context does not change its specialization at that row. Induction on arm selection.
8. **Derived satisfaction for several variables.** If the definition check passes, the body is well typed at every row, and conversely a failed check yields a failing row. The multi-variable `derived_satisfaction` and `check_complete`; induction over the enumerated table from statement 1.
9. **Specialization preserves meaning.** For every row and every input environment, the reference evaluator at that row and the evaluator of the specialized term agree. Structural induction on terms, as in `specialization_preserves_meaning`, with the arm-selection lemma from 4.
10. **A checked definition runs at every row.** Combination of 8, 9 and `specialization_is_safe`.
11. **Table entailment is sound and complete, and join is the greatest lower bound.** The multi-variable `entails_iff_sat` and `meet_greatest`; and the solved-variable rule: if all rows of a selection agree on a variable, every satisfying instantiation maps it to that type (`meet_singleton` for tables).
12. **Projection-keyed checking is equivalent to per-row checking.** If a subterm's typing depends only on a subset of variables, checking once per distinct projection accepts exactly when checking at every row does. Worth proving only if the optimisation is specified.

Since this note was written, RFC 0002 has proved statements 9 and 10 for its three-variable model, with matches nested to any depth, in its [Nested](https://shayanhabibi.github.io/clef-rfc-research/proofs/Clef.RFC0002.Nested.html) module (`nested_specialization_preserves_meaning`, `checked_nested_runs`). The part of statement 7 about equations of a selected arm is `equation_refines` in Regions, and Nested shows an inner match may rely on them (`arm_checked_where_it_matches`, `nested_match_checked_in_its_region`). Statements 4 and 5 are proved there for an inner match as well, with the overlap check taken over the region of the enclosing arms (`inner_first_match_is_most_specific`, `inner_order_is_irrelevant`), and for a whole body with the region of each match computed from it (`reordering_arms_changes_nothing`). Agreement, the second way of gluing overlapping arms, is stated there for an inner match and for a whole body (`inner_glued_order_irrelevant`, `glued_body_means_the_same_reordered`). The whole-body overlap check does not imply that gluing condition (`ordered_body_glues_falsified`); a condition that keeps priority where one arm is strictly more specific extends the overlap check and still makes arm order irrelevant (`ordered_body_glues_with_priority_kept`, `priority_kept_body_means_the_same_reordered`). RFC 0002 adopts that condition. An arm that no instantiation selects is reported by a computed check that names exactly those arms (`arm_passes_report_iff_selected_somewhere`); a body with no such arm that satisfies agreement between any two overlapping arms satisfies the adopted condition (`glued_body_with_no_arm_to_report_keeps_priority`), and one whose tests are ordered passes the whole-body overlap check (`ordered_tests_and_no_arm_to_report_pass_the_overlap_check`). The statements over a general list of variables are not proved.

### 3.5 Questions for the author

1. R1 or R3 (short answer, item 7)?
2. Should omitting a reachable intersection arm be an error (M9 as written) or a warning with first-match as the fallback?
3. Is an or-pattern `:? 'A | :? 'B` the intended way to say "handle the overlap implicitly"?
4. Are measures part of member identity?
5. Is the relation form (M3) wanted, or is `'T : ('A | 'B)` the full extent of the request?

## Verification status

- Verified by reading in this task: every `spec/` and `clef/src/Compiler/` citation, and the RFC 0001 Rocq sources. Line numbers for compiler files are approximate.
- Verified by fetching: Rust RFC 1210, C++ [temp.spec.partial.match], GHC User's Guide type families, OutsideIn(X) abstract, Scala 3 match types, TypeScript Handbook narrowing. Quotations are short extracts returned by the fetch; the C++ quotation is two fragments of one paragraph.
- Not re-read: Xi, Chen and Chen 2003; Peyton Jones et al. 2006; Frisch, Castagna and Benzaken 2008; Castagna et al. 2014 and 2015; Castagna, Duboc and Valim 2023; Eisenberg et al. 2014; Jones 2000; Odersky, Sulzmann and Wehr 1999. Claims attributed to them are from memory of their content and are stated at the level of their well-known results.
- Where the specification is silent: the specialization key, a single exhaustiveness rule, any multi-variable closed constraint, `static-parameter`. Where it contradicts the compiler: subtyping, and the `:?` example over `obj`. Where the implementation contradicts the reading used here: measures are not part of the specialization key.
- `Discussion.v` says "no evaluation" is modelled, but `TypeCase.v` defines `seval` and `eval` and proves `specialization_preserves_meaning`; the discussion table appears to be out of date.
