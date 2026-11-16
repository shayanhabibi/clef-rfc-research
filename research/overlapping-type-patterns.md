# Overlapping type patterns ordered by specificity

Research note for RFC 0001 (closed-set type constraints), Unresolved question 2 ("Generic members").
Date: 2026-11-15. Sources are specs, official docs, papers and compiler source. Each claim cites a
URL or a file path with its heading. Section 9 lists what could not be verified from a primary
source.

Notation: `p ≤ q` means "pattern `p` is at least as specific as pattern `q`".

## 1. Short answer

1. **"Most specific wins" is standard, but not in the form the author states it.** C++ partial
   specialization, GHC overlapping instances and Rust specialization all select the most specific
   candidate. In all three the rule is independent of declaration order, specificity is a partial
   order, and an overlapping pair that is not ordered is an error. None of them says "the most
   specific is first".
2. **"First arm wins" is the other standard, and it is the one Clef already has.** Clef patterns,
   F# static optimization conditionals and Haskell closed type families all try arms top to
   bottom. None of them orders by specificity. The Clef spec has no rule that orders match arms by
   specificity.
3. **The two coincide only under two extra checks.** If no arm is an instance of an earlier arm,
   and every pair of arms that can match a common type is comparable, then the first matching arm
   is the unique most specific matching arm. The compiler has to enforce both checks. Sorting does
   not replace them, because incomparable overlapping patterns exist, such as `('a * int)` and
   `(int * 'b)` at `int * int`.
4. **Selection cannot be made while the type is still a variable.** A catch-all arm may be chosen
   only when the scrutinee type cannot unify with any earlier arm. Matching alone is not enough.
   This is the apartness condition of closed type families. Under whole-program monomorphization
   the simple sound rule is to select only at full specialization.
5. **A catch-all member `'a` ends the closed set.** A member set that contains `'a` admits every
   type. The constraint then says nothing, and the RFC's prose rule "an unconstrained type variable
   stays parametric" no longer holds for that definition. This contradicts the RFC's summary
   ("an enumerated, finite set of types").
6. **Recommendation.** Separate the two things. Constraint members become linear patterns that are
   pairwise non-unifiable. Type-case arms may overlap, with first-match semantics and the two
   checks from point 3. A catch-all arm is a default arm over the declared members. A catch-all
   member is a separate decision and should not be bundled into this change.

## 2. Findings per source

### 2.1 Clef specification

Working copy a local clone of `clef-lang-spec`, directory `spec/`, at commit `26207e0`.

- **Arm order is first match.** `patterns.md`, chapter introduction: "Rules are attempted in order
  from top to bottom and left to right." No heading in `patterns.md` or `expressions.md`
  ("Pattern-Matching Expressions and Functions") orders rules by specificity.
- **Redundant type tests give a warning.** `patterns.md`, "Dynamic Type-test Patterns": "A warning
  is issued if an expression contains a redundant dynamic type-test pattern". The example puts
  `:? System.IComparable` before `:? string` and reports the second rule as "never matched". So
  the existing rule for a general arm placed before a specific one is a warning, and the general
  arm wins.
- **`:?` is resolved statically, but the text is inconsistent.** `expressions.md`, "Dynamic
  Type-Test Expressions": "No runtime type inspection is performed", and an undeterminable
  relationship is a compile-time error. `types-and-type-constraints.md`, "No Dynamic Type Tests",
  gives an example over `obj`. `introduction.md` says `:?` and `obj` "are not available in Clef".
  `patterns.md` still describes run-time subtype matching, inherited from F#. RFC 0001 Motivation
  item 3 already records this.
- **Overload resolution has a "more specific" rule, and it is not pattern specificity.**
  `inference-application-resolution.md`, "Method Application Resolution", step 7. Criterion 5:
  "prefer any candidate that has the more specific actual argument types", defined by "feasibly
  subsumes", which is a coercion relation. Criterion 8: "Prefer candidates that are not generic
  over candidates that are generic". Then: "Report an error if steps 1) through 8) do not result
  in the selection of a unique better method." This is a partial preference with an ambiguity
  error. It has no rule that prefers `list<'a>` over `'a` between two generic candidates.
- **SRTP.** `inference-constraint-solving.md`, "Solving Member Constraints": a constraint is
  satisfied when a type in the support set has the member. There is no ordering and no
  specificity. `program-semantic-graph.md` §3.3 records one resolved member per site.
- **Monomorphization.** `types-and-type-constraints.md` (text before "Named Types"):
  "Monomorphization ... occurs during PSG saturation". `native-type-mappings.md`: "Generic type
  parameters are monomorphized (specialized at each call site)."

Conclusion: no existing Clef rule orders by specificity. The principles that do exist are
first-match with a "never matched" warning, and overload preference with an ambiguity error.

### 2.2 F#

- **Overload resolution.** F# language spec, "Method Application Resolution", step 7
  (<https://github.com/fsharp/fslang-spec/blob/main/spec/inference-procedures.md>). It has the same
  eight criteria as the Clef text, with a `System.Func` clause added to criterion 5. It has no
  "more concrete generic instantiation" criterion. The proposal to add one is
  <https://github.com/fsharp/fslang-suggestions/issues/905> ("Most concrete" tiebreaker for
  generic overloads). When fetched it was open and approved in principle, with no RFC linked.
  **This is contrary to the task's premise** that F# §14.4 prefers more specific generic
  instantiations. It prefers non-generic over generic, and coercion-specific over
  coercion-general.
- **Static optimization conditionals.** This is the closest prior art. All references are to
  `dotnet/fsharp`, branch `main`, at `59c7477`.
  - Syntax: a fallback expression followed by `when 'T : ty = expr` clauses. See
    `src/FSharp.Core/prim-types.fs`, for example `GenericEqualityFast` (line 1955) and `(+)`
    (line 4625). The grammar is `staticOptimization` in `src/Compiler/pars.fsy` (line 3469).
  - Ordered, first match. `mkSynBindingRhs` in `src/Compiler/SyntaxTree/SyntaxTreeOps.fs`
    (line 791) folds the clauses into nested `LibraryOnlyStaticOptimization(c, e1, e2)` nodes. The
    first clause is outermost and the generic fallback is innermost.
  - Three-valued decision. `decideStaticOptimizationConstraint` in
    `src/Compiler/TypedTree/TypedTreeOps.Remapping.fs` (line 1516) returns `Yes`, `No` or
    `Unknown`. Its comment says: "Both types must be nominal for a definite result". A type
    variable gives `Unknown`. The test compares head type constructors only.
  - When the type is still a variable. The optimizer (`src/Compiler/Optimize/Optimizer.fs`,
    line 2894) takes the branch on `Yes`, takes the fallback on `No`, and keeps the whole
    conditional on `Unknown`. The conditional is decided later, after inlining has substituted the
    type. If it is still undecided at code generation, `GenStaticOptimization`
    (`src/Compiler/CodeGen/IlxGen.fs`, line 8305) emits the fallback.
  - No typing guarantee. `TcExprStaticOptimization`
    (`src/Compiler/Checking/Expressions/CheckExpressions.fs`, line 6650) says: "Do not force the
    types of the two expressions to be equal. This means uses of this construct have to be very
    carefully written". The construct is restricted to FSharp.Core (error 817: "Static
    optimization conditionals are only for use within the F# library").
  - Lesson for Clef. F# gets away with "undecided means fallback" because the fallback is a
    run-time generic implementation that is meant to be observationally equal to the fast paths.
    Clef has no run-time fallback and the arms are not equal by intent, so an undecided test must
    stay undecided until specialization.

### 2.3 Haskell

- **Closed type families.** Eisenberg, Vytiniotis, Peyton Jones, Weirich, "Closed type families
  with overlapping equations", POPL 2014 (<https://richarde.dev/papers/2014/axioms/axioms.pdf>).
  - §2.3: "the equations are tried in order".
  - §3.2 shows that match-only selection is unsound. `Equal Bool d` matches the catch-all equation
    `Equal a b = False`, but simplifying it is wrong, "because the choice of which equation to
    match depends on how d is instantiated". The example ends in a crash (`segFault`).
  - Candidate Rule 2 (§3.2) and Rule 9 (§3.4): an equation fires if the target matches it and each
    earlier equation is apart from the target, or is compatible with the firing equation.
  - Definition 6 (§3.3): apartness is failure of unification, after flattening.
  - Property 12 (§5.1): "Apartness is stable under type substitution".
  - §2.2: non-linear patterns such as `Equal a a` are supported. They "make the metatheory much
    harder".
  - §6.1: with non-terminating families, `(a, a)` must not count as apart from `([b], b)`, even
    though unification fails on the occurs check. §6.2 fixes this with unification over infinite
    types.
  - §7.5, "Lack of inequality evidence": in the body after a failed earlier case, "the type system
    has no evidence that ... the type variable a cannot be Int". A catch-all gets no negative
    information.
  - §8.3: for term-level selection (instance chains), a flaw "may lead to incoherent behavior ...
    but it cannot violate type safety", because no type equalities are produced.
  - The GHC User's Guide, "Closed type families"
    (<https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/type_families.html>), says
    the same: equations are "tried in order, from top to bottom", GHC selects one "only when it is
    sure that no incompatible previous equation will ever apply", and a bare `F a` does not
    simplify.
- **Overlapping instances.** GHC User's Guide §6.8.8.5
  (<https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/instances.html>).
  - Definition: "IY is a substitution instance of IX but not vice versa".
  - Algorithm: find the instances that match, eliminate the less specific ones, and fail "if more
    than one non-incoherent candidate remains". Then find instances that "unify with the target
    constraint, but do not match it". Unless those are all incoherent, the search fails.
  - With a rigid type variable, GHC "does not commit to instance (C), because in a particular call
    of f, b might be instantiated to Int". Without a signature it infers the constraint and
    "postpones the question ... to the call site".
  - Declaration order is irrelevant. Incomparable overlap fails at the use site.

### 2.4 C++

- [temp.spec.partial.match] ¶1 (<https://eel.is/c++draft/temp.spec.partial.match>). If exactly
  one partial specialization matches, it is used. If several match, the most specialized is used.
  Otherwise "the use of the template is ambiguous and the program is ill-formed". If none match,
  the primary template is used, which is the catch-all. ¶2: matching is deduction of the
  specialization's parameters from the actual arguments. It is one-way.
- [temp.spec.partial.order] ¶1 (<https://eel.is/c++draft/temp.spec.partial.order>; named
  [temp.class.order] in older standards). Ordering is defined by rewriting to function templates.
- [temp.func.order] ¶3 and [temp.deduct.partial] ¶8, ¶10 (<https://eel.is/c++draft/temp.func.order>,
  <https://eel.is/c++draft/temp.deduct.partial>). The rules "synthesize a unique type" for each
  parameter and deduce against the other template. "F is more specialized than G if F is at least
  as specialized as G and G is not at least as specialized as F."
- This is exactly `p ≤ q` iff `p` is a substitution instance of `q`. It is independent of
  declaration order. Ambiguity is reported at the instantiation that hits it, and not at the
  declaration. Selection happens only on instantiation with concrete arguments.

### 2.5 Rust specialization

- RFC 1210 (<https://rust-lang.github.io/rfcs/1210-impl-specialization.html>).
  - Order: "`I <= J` if `apply(I)` is a subset of `apply(J)`".
  - Overlap: overlapping impls must be strictly ordered ("one must be truly more specific than the
    other"). The lattice rule, where an impl for the intersection permits partial overlap, is
    described and deferred: "since the lattice rule can be added later, the RFC sticks with the
    simple chain rule for now."
  - Selection: "at monomorphization time ... there will always be a unique, smallest impl in
    specialization order." During type checking a `default` item is opaque. Generic code may not
    assume which impl's associated type it gets.
  - Lifetimes: "dispatch cannot depend on lifetime information", because by code generation
    "lifetime information has been erased".
- Soundness. The tracking issue <https://github.com/rust-lang/rust/issues/31844> labels the
  feature unsound: it "can cause Undefined Behavior without `unsafe` code". The cause is described
  in <https://aturon.github.io/tech/2017/07/08/lifetime-dispatch/>: "typeck and trans disagree".
  The type checker sees lifetimes and may pick the specialized impl. Code generation has erased
  them and picks the other.
- `min_specialization` (<https://github.com/rust-lang/rust/pull/68970>) restricts a specializing
  impl. No `'static` may appear. Each generic parameter may appear at most once in the matched
  arguments, so repeated parameters are excluded. Every bound on the specializing impl must also
  be on the base impl.
- Does this apply to Clef? The Rust holes need both of these:
  1. some type information the checker sees and the specializer does not (lifetimes);
  2. a selection that changes a type (associated types).

  RFC 0001 has neither as drafted. Specialization sees full closed types, and prose rule 2
  (Locality) fixes the result type of the `match` before the arms are checked. The hazard returns
  if either changes. See risks R3 and R4.

### 2.6 Parametricity and type-case

- Harper and Morrisett, "Compiling polymorphism using intensional type analysis", POPL 1995
  (<https://www.cs.cmu.edu/~rwh/papers/intensional/popl95.pdf>).
  - §1.2: when the analysed type "is known at compile-time (or link-time), then the overhead of
    the case analysis can be eliminated by duplicating and specializing".
  - §2.2: the target language "allows non-parametric functions to be defined by intensional
    analysis of types".
  - Later: "The presence of typerec violates parametricity to achieve a more flexible programming
    language."
  - Their `typecase` has one arm per type constructor (`int`, `string`, `×`, `→`). Arms are
    exhaustive and never overlap. There is no default arm and no specificity rule.
- Crary, Weirich and Morrisett, "Intensional polymorphism in type-erasure semantics" (ICFP 1998,
  JFP 2002; abstract at <https://www.cs.cornell.edu/talc/papers/typepass-abstract.html>).
  Run-time type information is "represented by ordinary terms". Only the abstract was read. No
  statement about default arms or coherence was verified from the body.

## 3. What "more specific" means

A type pattern is a type that may contain pattern variables. `_` is a fresh variable.

- **Matching.** A closed type `t` matches `p` when there is a substitution `σ` with `σ(p) = t`.
  The substitution applies to the pattern only.
- **Specificity.** `p ≤ q` when `p = σ(q)` for some `σ`. This is the definition used by GHC
  ("substitution instance") and by C++ (one-way deduction). It agrees with Rust's subset
  definition on patterns, given the freshness assumption in statement S3.
- **It is a preorder, and a partial order up to renaming.** `list<'a>` and `list<'b>` are each an
  instance of the other. They are one pattern.
- **It is not total.** Overlapping pairs that are incomparable:

  | Pattern 1 | Pattern 2 | Common instance |
  |---|---|---|
  | `('a * int)` | `(int * 'b)` | `int * int` |
  | `('a * 'a)` | `(int * 'b)` | `int * int` |
  | `(list<'a> * 'b)` | `('a * list<'b>)` | `list<int> * list<int>` |

- **Overlap is unifiability.** Two patterns, renamed apart, have a common instance exactly when
  they unify. The common instances are the instances of the most general unifier.
- **Non-linear patterns.** `('a * 'a) ≤ ('a * 'b)`, strictly. Matching `('a * 'a)` needs type
  equality on the two components. That is decidable on closed types (`ty_eq_dec` in
  `proofs/theories/Spec/Types.v`), but equality must mean what the specializer sees after
  abbreviations are expanded and anything erased is removed. See R4.

## 4. Options for incomparable overlap

| Option | Rule | Who does it |
|---|---|---|
| (a) Reject | Overlapping arms must be comparable. Optional lattice extension: or their intersection is covered by a more specific arm. | Rust RFC 1210 at the declaration (chain rule adopted, lattice deferred). C++ and GHC use the same order but report at the use that hits the ambiguity. |
| (b) Textual first match | Arms are tried in order. A later arm fires only when earlier ones cannot. Unreachable arms are diagnosed. | Closed type families (with apartness), F# static optimization conditionals, ML and Clef patterns (warning "never matched"). |
| (c) Compiler sorts | The compiler reorders arms by specificity. | None of the surveyed sources reorders a user-written ordered list. In C++, GHC and Rust the declarations are unordered, so nothing is sorted. |

Option (c) does not solve the problem. A partial order has many linearizations. Two incomparable
overlapping arms would get an arbitrary order, so the meaning of the program would depend on the
sort.

**Recommendation.** Use (b) as the semantics and add (a) as a well-formedness check. The semantics
then stays the one Clef patterns already have. The check makes the author's statement true as a
theorem: wherever two arms can both match, the earlier one is strictly more specific. The compiler
rejects a misordered or ambiguous arm list. It does not reorder it.

## 5. When selection is decided

For a scrutinee type `τ` that may contain type variables of the enclosing definition, and arms
`p1 … pn`, define three outcomes.

- **Selected `i`.** `τ` is an instance of `pi`, and `τ` does not unify with any earlier `pk`.
- **No arm.** `τ` unifies with no arm.
- **Stuck.** Anything else.

Consequences:

- At a closed type the outcome is never stuck. Unification of a closed type with a pattern is
  matching.
- A selected outcome is stable. Every substitution instance of `τ` selects the same arm
  (statement S5). The checker may therefore reduce a type-case early when it is selected, for
  example `list<'u>` against arms `list<_>`, `'a`.
- A stuck outcome must not be resolved to the catch-all. With `'T` abstract and arms `list<_>`,
  `'a`, the outcome is stuck. Picking `'a` is the closed-type-family §3.2 error and the Rust
  typeck/trans disagreement.
- Under whole-program monomorphization, leaving a stuck type-case in the body and reducing it at
  saturation is sound, given two conditions:
  1. every arm was checked at the definition site, so whichever arm is selected later is well
     typed;
  2. the result type of the `match` does not depend on the arm (RFC prose rule 2, Locality).
- A constrained generic that calls another with a still-abstract type argument needs no selection
  at that point. The callee's type-case stays in the callee's body and is reduced when the caller
  is specialized. The caller only needs the constraint to hold. See section 6, entailment.

**What the catch-all arm body may assume.** Nothing about the variable beyond its declared
constraint. It is checked once, with the variable abstract. No negative information such as "not a
list" is available (closed type families §7.5). None is needed for soundness, because the body is
valid at every type and so is valid at the types that reach it.

**What a pattern arm body may assume.** Inside `:? list<'e> as xs`, the local equation is
`'T = list<'e>` with `'e` rigid and unconstrained. The body is checked once, generically in `'e`.
A type-case on `'e` inside that arm is an error under prose rule 3, unless pattern variables can
carry constraints. See R5.

## 6. Effect on RFC 0001's rules

| RFC 0001 today | With pattern members and arms |
|---|---|
| `cset := list ty`, closed types, `NoDup`, at least two (`Constraints.v`) | A list of patterns. The set denoted is the union of their closed instances. It is finite only when every member is closed. `list<'a>` is an infinite family. `'a` is every type. |
| `sat t C := In t C`, decided by `ty_eq_dec` | `t` matches some member. Decidable by matching. For an open type `τ` the answer is yes (`τ` is an instance of a member), no (`τ` unifies with none), or deferred. |
| Well-formed: no duplicates | Members pairwise non-unifiable (the rule floated in Unresolved question 2). This keeps "which member" a function of the type. |
| `entails C D`: subset test, sound and complete (`entails_iff_sat`) | Every member of `C` is an instance of some member of `D`. Sound. Complete only if fresh type constructors are always available (S3). |
| `meet C D`: filter by membership | The most general unifiers of all unifiable pairs `(c, d)`. `meet_sat` should carry over (S4). `meet_singleton` changes: a single non-closed pattern does not solve the variable to a closed type. It refines it to that pattern with fresh variables. |
| `check`: `forallb` over members, by specializing the body at each (`TypeCase.v`) | Not possible for an infinite family. Each arm is checked generically in its pattern variables. Code outside any type-case is checked with the variable abstract, using only operations shared by all members. Derived satisfaction then needs a substitution lemma (S6). |
| `pick`: first arm equal to the type | First arm the type matches. At closed types this is a function (S1). |
| `covered`: every member appears as an arm | Every member pattern is an instance of some arm pattern. Sufficient. Complete under the same freshness assumption as S3. A catch-all arm covers everything. |
| `shared_operation`: a witness at every member | A witness at every instance of every member pattern. This needs witness resolution to be stable under substitution on open types. `Spec/Witnesses.v` does not state that. |
| Code size "finite and visible in the signature" (Discussion, Drawbacks) | No longer bounded by the signature. It is bounded by the instantiations the program uses, as for any generic. |
| Unresolved question 7 (pre-generating all specializations) | Cannot be "must" for an infinite family. |
| Prose rule 1: the tested type is a member | The arm pattern must unify with some member. Otherwise it is unreachable. |
| Prose rule 3: an unconstrained variable stays parametric | Unchanged if catch-all is allowed only as an arm. Void for any definition whose member set contains `'a`. |

A member `'a` makes the constraint degenerate. Every type satisfies it. Every other constraint
entails it. It entails nothing except another catch-all. A signature `'T : (list<_> | 'a)` then
admits the same types as an unconstrained `'T`, and promises nothing about `'T` to a reader.

## 7. Recommendation

Separate the constraint from the type-case.

**Constraint members**

1. A member is a linear type pattern. Its variables are local to the member and are written `_` or
   named. A closed type is the special case.
2. Members are pairwise non-unifiable. There is no catch-all member in this RFC.
3. Satisfaction at a closed type is matching. Entailment is "each member is an instance of a
   member". Intersection is pairwise unification.
4. For an open type argument `τ`:
   - an instance of a member: satisfied;
   - unifies with no member: error;
   - anything else: the constraint is deferred onto the variables of `τ` where that is expressible,
     and is otherwise an error that asks for an annotation.

**Type-case arms**

5. An arm is `:? pattern as ident`, or a final default arm `_`. Arm patterns may overlap. Each arm
   must unify with at least one member.
6. Semantics: first arm that the closed instantiating type matches. Selection happens at
   saturation. Earlier reduction is permitted only when the outcome is "selected" in the sense of
   section 5.
7. Well-formedness, checked at the definition:
   - **No shadowing.** No arm is an instance of an earlier arm. This is an error, not the warning
     of `patterns.md`, because a dead arm in a static type-case is always a mistake.
   - **Chain rule.** If two arms unify, the earlier is strictly more specific than the later.
   - **Coverage.** Every member is an instance of some arm, or a default arm is present.
8. Each arm body is checked once, generically in the arm's pattern variables, under the local
   equation between the constrained variable and the pattern. The default arm body is checked with
   the variable abstract under its declared constraint. No negative information is assumed.
9. The result type of the `match` is fixed before the arms are checked (prose rule 2). An arm
   never determines a type that is visible outside it.
10. Pattern variables carry no constraints in this RFC. Non-linear arm patterns are deferred. See
    R4 and R5.

With rules 6 and 7 the author's sentence is a theorem, not a convention: if the type is a list it
takes `list<_>`, otherwise it takes the later, more general arm, and the compiler rejects any arm
list where "first" and "most specific" could differ.

**If the author also wants a catch-all for an otherwise unconstrained `'T`.** This is a
statically resolved typecase with a default over all types. It is implementable and sound under
monomorphization. The costs are that the signature must still show that the definition is
non-parametric (for example a distinguished member `_`), that the name "closed-set" no longer
fits, and that prose rule 3 must be restated as "parametric unless the signature says otherwise".
This should be its own unresolved question, or its own RFC.

## 8. Open risks

- **R1. Parametricity.** The RFC already lists non-parametric generic code as a drawback
  (`Discussion.v`). With a default arm over an open family, the set of types that get special
  behaviour is no longer enumerable from the signature. Free theorems fail for every such
  definition (Harper and Morrisett).
- **R2. Deferred constraints on compound types.** `f<'T : ((int * _) | (string * _))>` called at
  `('u * bool)` unifies with two members and is an instance of neither. The obligation is on
  `'u`, namely `'u : (int | string)`. In general it is not expressible as a constraint on one
  variable. The draft would need either non-variable constraint subjects or an error.
- **R3. Early selection.** Any implementation path that reduces a stuck type-case in the checker,
  or uses the selected arm to solve an outer inference variable, reintroduces the closed type
  family §3.2 unsoundness and the Rust typeck/trans split. Unresolved question 6 (the exact
  inference rule for refinement) is where this would enter.
- **R4. Erased or normalized distinctions.** Matching must see exactly what saturation sees. The
  candidates in Clef are type abbreviations, units of measure (`float<m>` against `float`),
  width-inferred numeric types, and any coercion or subtyping relation (`:>` constraints exist in
  `types-and-type-constraints.md`). If the checker distinguishes two types that saturation
  identifies, or the reverse, then non-linear patterns and patterns that mention such types
  behave like Rust's lifetime dispatch. Whether measures are erased before saturation was not
  verified.
- **R5. Recursion over type structure.** A function that recurses into the element type, for
  example `| :? list<'e> as xs -> ... depth<'e> ...`, needs `'e` to satisfy the function's own
  constraint. With a catch-all member this is trivial. With pairwise-disjoint members it needs
  constrained pattern variables (`list<'e> when 'e : C`), which makes satisfaction a recursive
  check and brings in the bound-dependent matching that `min_specialization` restricts. This is
  an argument from the rules above. It is not from a source.
- **R6. Specialization termination.** If a constrained generic may call itself at a larger type
  (`f<list<'T>>` from `f<'T>`), saturation does not terminate. This risk exists for any
  monomorphized generic, but structural patterns make such code natural to write. Whether Clef
  already forbids polymorphic recursion was not found in the spec.
- **R7. Witnesses on open types.** Checking an arm generically requires operator witnesses at
  open types such as `list<'e>`, and requires that the witness chosen there is the one chosen at
  every instance. If witness resolution is itself type-directed with overlap, it needs the same
  apartness discipline.
- **R8. Signature conformance.** "Equal member sets" (`Constraints.v`, Origin and signatures)
  becomes "equal up to renaming of pattern variables and order".

## 9. Not verified from a primary source

- The body of Crary, Weirich and Morrisett. Only the abstract was read.
- That no surveyed language sorts arms. This rests on the sources read, which describe unordered
  declarations or ordered first-match. It is not an exhaustive survey.
- The current status of fslang-suggestions #905 beyond the page as fetched on 2026-11-15.
- Clef's treatment of polymorphic recursion, of measure erasure relative to saturation, and of
  abbreviation expansion at saturation.
- Risks R2, R5, R6 and R7 and the completeness claims in section 6 are reasoning in this note.
  They are candidates for proof, not cited results.
- C++ quotations are from the current working draft at eel.is, not from a published standard.

## 10. Statements worth proving in Rocq

Model: extend `oty` to patterns with several variables, and define `matches`, `unifies` and `inst`.

- **S1. Selection is a function.** For closed `t` and any arm list, first-match `pick t arms`
  yields at most one arm. With coverage it yields exactly one.
- **S2. First match is most specific.** Under no-shadowing and the chain rule, for every closed
  `t`, the arm picked is strictly more specific than every other arm that `t` matches. So
  first-match equals the unique minimum, and the result does not change under any reordering of
  the arms that still satisfies the two rules.
- **S3. Entailment.** If every member of `C` is an instance of some member of `D`, then
  `sat t C -> sat t D` for all closed `t`. The converse holds given a type constructor that does
  not occur in `D`.
- **S4. Meet.** For members renamed apart, `sat t (meet C D) <-> sat t C /\ sat t D`, where
  `meet` collects most general unifiers. The greatest-lower-bound property of `meet_greatest`
  carries over. If `C` and `D` each have pairwise non-unifiable members, so does `meet C D`.
- **S5. Stability under substitution.** If open `τ` is an instance of arm `i` and unifies with no
  earlier arm, then for every closed substitution `σ`, `pick (σ τ) arms` is arm `i`. This is the
  counterpart of closed type families Property 12.
- **S6. Derived satisfaction, generic form.** If each arm body is well typed generically in its
  pattern variables, and the rest of the body is well typed with the variable abstract, then for
  every closed `t` that satisfies the constraint the specialization at `t` exists and has the
  declared type. This replaces `derived_satisfaction` and `check_complete`. It needs a
  substitution lemma for `mtype`, and the assumption that `witness` commutes with substitution.
- **S7. Coverage.** If every member is an instance of some arm, then `spec t e` is defined for
  every `t` that satisfies the constraint. This replaces `coverage_total`.
- **S8. Unique member.** Under pairwise non-unifiable members, each closed `t` matches at most
  one member.
- **S9. Stuck is necessary.** A counterexample lemma: with arms `[list<_>; 'a]`, there are two
  closed instances of a variable that pick different arms. So no selection at the variable is
  stable.
- **S10. Chain rule is necessary.** A counterexample lemma: arms `('a * int)` and `(int * 'b)`
  pass no-shadowing in either order, and the two orders pick different arms at `int * int`.
- **S11. Case-free uniformity is kept.** `case_free_uniform` should hold unchanged, since it does
  not depend on the form of members.
