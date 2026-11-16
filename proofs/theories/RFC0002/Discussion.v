(**md # Discussion

## What the proofs cover

The model has three type variables: two with closed-set constraints and one constrained to be
either of them. An arm is a test and a body. The model says which arm a specialization selects,
types the body of an arm, and evaluates it. In [Regions](Clef.RFC0002.Regions.html) and
[Bodies](Clef.RFC0002.Bodies.html) a body is a term of RFC 0001 with no type-case of its own.
[Nested](Clef.RFC0002.Nested.html) allows a match anywhere in a body, on any scrutinee, under the
equation reading. Member types are closed, as in RFC 0001.

| Claim | Status |
|---|---|
| The constraints describe a finite, computable table of instantiations | Proved: `table_iff_valid` |
| Arms for both variables cover every instantiation | Proved, both readings: `coverage` |
| The three arms split the table by which variables are equal | Proved, equation reading: `regions_partition` |
| The intersection arm is reachable exactly when the sets share a type | Proved, both readings: `intersection_reachable_iff` |
| Without the intersection arm, arm order matters exactly when the sets share a type | Proved, both readings: `two_arms_order_matters_iff` |
| Under the overlap check, the first matching arm is the most specific | Proved, both readings, any arms: `first_match_is_most_specific` |
| Under the overlap check, arm order does not change how specific the selected test is | Proved, both readings, any arms: `order_is_irrelevant` |
| Under the overlap check, arm order does not change what the program computes | Refuted: `ordered_order_irrelevant_falsified` |
| Under the overlap check, with no two arms testing the same thing, arm order does not change what the program computes | Proved, both readings: `priority_glues`, `glued_order_irrelevant` |
| Arms whose bodies agree where they overlap may be written in any order | Proved, both readings: `glued_order_irrelevant` |
| Agreement accepts a match the overlap check rejects | Proved for one family of constraints: `agreement_accepts_what_priority_rejects` |
| The three-arm match always passes the overlap check | Proved, both readings: `intersection_first_is_ordered` |
| The overlap check rejects the two-arm match on overlapping sets | Proved for one family of constraints: `unordered_overlap_rejected` |
| An arm's binder has the scrutinee's type | Proved under the equation reading: `equation_refines`. Refuted under the membership reading: `membership_refines_falsified` |
| A definition whose arm bodies check runs to a value of its declared type | Proved from an assumption under the equation reading: `checked_match_runs`. Refuted under the membership reading: `membership_binding_falsified` |
| The two readings select the same arm | Proved for disjoint sets: `readings_agree_when_disjoint`. Refuted in general: `readings_agree_falsified` |
| The overlap check accepts a match that agreement rejects | Not proved. The three-arm match with three different bodies is the expected example |
| Specialization preserves meaning with several variables and nested matches | Proved, equation reading: `nested_specialization_preserves_meaning` |
| A body with nested matches that has a type specializes, at that type | Proved, equation reading: `typed_body_specializes` |
| A definition with nested matches that checks runs to a value of its declared type | Proved from an assumption, equation reading: `checked_nested_runs` |
| An arm of a nested match is checked and run only where its test succeeds | Proved: `arm_checked_where_it_matches` |
| A conjunction of tests is a nested test | Proved, for a match with one arm: `conjunction_is_nesting` |
| An inner match need cover only the region of the arm it is in | Proved for one definition, with every pair of member sets: `nested_match_checked_in_its_region` |
| The model of nested matches agrees with Bodies where there is no nesting | Proved, one direction for the check: `nested_extends_bodies` |
| The overlap check, stated over any set of instantiations and any scrutinee, is the check of Regions over the whole table | Proved: `ordered_in_table` |
| Under the check over a set, the first matching arm of an inner match is the most specific one there | Proved: `inner_first_match_is_most_specific` |
| A match accepted over the whole table is accepted over every region | Proved: `check_over_larger_set_is_stricter` |
| The check over the region accepts an inner match the check over the table rejects | Proved for one family of constraints: `region_check_accepts_what_table_check_rejects` |
| Under the check over its region, with no two arms equally specific there, the order of an inner match's arms changes neither its type nor its value | Proved: `inner_order_is_irrelevant` |
| Inside an arm of the three-arm match, a test on a scrutinee of variable type is constant | Proved: `inner_tests_decided_in_a_region` |
| The set computed for an arm is exactly where that arm is selected | Proved: `reach_is_where_the_arm_is_selected` |
| A body that passes the whole-body overlap check means the same after any rearrangement of the arms of any of its matches | Proved: `reordering_arms_changes_nothing` |
| A definition and its rearrangement that both pass the check type-check alike and return the same result | Proved: `reordered_definition_means_the_same` |
| The whole-body check accepts some match in both orders | Proved for one family of constraints: `check_accepts_both_orders` |
| A bound on the work the whole-body check does | Not proved |
| Inner arms that glue over a set of instantiations may be written in any order | Proved from an assumption: `inner_glued_order_irrelevant` |
| The overlap check over a region, with no two arms equally specific there, glues | Proved: `inner_priority_glues` |
| Two inner arms with the same body and the same number of binders glue | Proved, any region, any scrutinee: `inner_same_body_glues` |
| Agreement accepts an inner match the overlap check over its region rejects | Proved for one family of constraints: `inner_agreement_accepts_what_region_check_rejects` |
| A body that glues means the same after any rearrangement of the arms of any of its matches | Proved from an assumption: `glued_body_means_the_same_reordered` |
| A definition and its rearrangement that both glue type-check alike and return the same result | Proved from an assumption: `glued_definition_means_the_same_reordered` |
| The gluing condition accepts in both orders a definition the whole-body overlap check rejects | Proved for one family of constraints: `gluing_accepts_what_overlap_check_rejects` |
| A body that passes the whole-body overlap check satisfies the gluing condition | Not proved. The two examine an arm's body over different sets |
| Under agreement, an arm's body need be examined only where the arm is selected | Not settled. Neither proved nor refuted |
| Agreement of two arms in Bodies gives agreement of the same arms as inner arms | Not proved |
| A computed check that implies the gluing condition | Not modelled |
| A nested match under the membership reading | Not modelled |
| Inference with a constraint `'T : ('A or 'B)` keeps principal types | Not proved. The research note argues it does not, without a restriction |
| More than two tested variables, and generic members | Not modelled |

`checked_match_runs` and `checked_nested_runs` rest on `witness_sound`, the assumption that every
witness is implemented at its declared type. So do the three theorems on gluing in a nested
body, `inner_glued_order_irrelevant`, `glued_body_means_the_same_reordered` and
`glued_definition_means_the_same_reordered`: agreement is asked only for scrutinees of the right
type, and that a scrutinee evaluates to one is the safety theorem. No other theorem here uses an assumption beyond decidable equality of type
constructors, `tycon_eq_dec`. The refutations hold whenever two different closed types exist, or,
for the two about evaluation, whenever some type has a value.

## The reading of `:? 'A`

The RFC adopts the equation reading. The alternative was the membership reading.

- **Equation.** The scrutinee's type is the type `'A` is instantiated to.
- **Membership.** The scrutinee's type is a member of the set `'A` is constrained to.

The proofs give these reasons.

1. **The question matters only for overlapping sets.** Where the member sets share no type, both
   readings select the same arm of every match (`readings_agree_when_disjoint`).
2. **On overlapping sets the readings differ** (`readings_agree_falsified`). With `'A : (x | y)`
   and `'B : (y)`, `'A` instantiated to `x` and a scrutinee of type `y`, the equation reading
   selects `:? 'B` and the membership reading selects the intersection arm.
3. **Only the equation reading lets the arm bind at the variable's type.** Under it, `:? 'A as v`
   may give `v` the type `'A` (`equation_refines`), and a definition checked that way is safe to
   run (`checked_match_runs`). Under the membership reading the same check accepts a definition
   that returns a value of the wrong type (`membership_binding_falsified`), so `v` can only have
   the scrutinee's type.
4. **The membership reading adds nothing to RFC 0001.** Its test depends only on the scrutinee's
   type and a fixed set of closed types, which is a list of RFC 0001's closed arms.
5. **The equation reading is the one the tier discipline admits.** It is an equality between two
   types. The membership reading is a set test. See the tiers section below.
6. **Everything else is the same.** Coverage, reachability of the intersection arm, the effect of
   arm order, the overlap check and both ways of gluing hold under both readings.

The equation reading is adopted on these grounds. It is the one under which the intersection arm means
"the two variables unify", and the one under which an arm learns a type equation that a checked
body can rely on. The membership reading stays in the model as the
rejected alternative, so that each reason above remains a checked theorem.

## Two ways to glue overlapping arms

[Bodies](Clef.RFC0002.Bodies.html) states one condition, *gluing*, under which arm order cannot
change what a definition computes: at every instantiation the selected arm is strictly more
specific than each other arm that matches, or computes the same result as it. Two rules imply it.

| Rule | Requires | Accepts | Rejects |
|---|---|---|---|
| Priority | The overlap check, and no two arms with equivalent tests | The three-arm match with any bodies, where its three tests differ | The two-arm match on overlapping sets, even when both bodies are the same |
| Agreement | Overlapping arms compute the same result on the overlap | The two-arm match when both bodies are the same | Any overlap whose arms differ, including the three-arm match with different bodies |

Neither rule contains the other, and a compiler may use both: an overlap is accepted if it passes
either. That is what the gluing condition says, and `glued_order_irrelevant` covers the mixture.

Agreement has a cost priority does not. Whether two bodies compute the same result is not
decidable in general. Two checks are available. Identical bodies with the same binders agree, which
is a structural check (`same_body_glues` is this case). Otherwise the equality is a proof
obligation about two programs. Haskell's closed type families use the structural form, under the
name compatibility.

The model's agreement asks for equal results on every scrutinee of the type `'T` is instantiated
to, with the other parameters unrestricted. That is stronger than needed, since the other
parameters also have known types, and a rule that used them would accept more.

Both rules carry over to a match nested in an arm. The section on nested matches below gives the
statements.

## Relation to the verification tiers

The specification organises checking into
[tiers](https://clef-lang.com/spec/draft/terms-and-definitions/#verification).
Tier 1 is structural inference whose checks are equalities
([NTU Dimensional Architecture §7.2](https://clef-lang.com/spec/draft/ntu-dimensional-architecture/#72-dimensional-type-identity)). Tier 2 is local analysis and solver fragments. Tier 3 is the application of library
theorems. Tier 4 is relational judgments about executions. The research note
[RFC 0001 and RFC 0002 against the verification tiers](https://shayanhabibi.github.io/clef-rfc-research/research/tier-placement-and-extensions/)
gives the sources and the full argument. This section records the conclusions for this RFC. They
are a reading of the specification and the design documents, and none is a theorem.

| Piece | Tier | Reason |
|---|---|---|
| The instantiation table | Edge of 1 | It is the set of joint solutions of the constraints. It is finite and computable, and its size is up to the product of the set sizes |
| Coverage and reachability | Edge of 1 | Decided by enumerating the table |
| The overlap check | Edge of 1 | Up to 2ⁿ − 1 regions for n tested variables. It compares arms by generality, which is an order, where Tier 1 checks are equalities |
| Binder typing under the equation reading | 1 | The arm learns an equation between types |
| Agreement by identical bodies | 1 | A structural comparison |
| A nested match (`ncheck`) | Edge of 1 | Each test is an equality between two closed types at an instantiation. The check still enumerates the table |
| The overlap check for an inner match (`ordered_in`) | Edge of 1 | The same enumeration as the overlap check, over part of the table. It compares arms by generality, as that check does |
| The whole-body overlap check (`nordered`) | Edge of 1 | One walk over the body. At each arm the set of instantiations is filtered by equalities between closed types |
| Agreement of inner arms by identical bodies (`inner_same_body_glues`) | 1 | A structural comparison, with a count of binders. It does not look at the region |
| The gluing condition of a whole body (`nglued`) | 1 to 4 | It is a statement and not a procedure. Its tier is that of the rule used for each overlap: priority, identical bodies, or a proof |
| Agreement by proved equivalence | 4 | A relation between two programs |

**The constraint is a disjunction of equations between variables.** `'T : ('A | 'B)` says `'T` is
`'A` or `'T` is `'B`. A set of closed types narrows one variable. This relates three, and it has
several incomparable solutions where the unification Tier 1 relies on has one most general
solution. The research note sketches an encoding of Boolean satisfiability into such constraints.
If the sketch holds, a compiler that had to infer them would be doing a solver's work. That
supports unresolved question 4: these constraints are declared and never inferred, so the compiler
checks a given table and does not search for one.

**In the staged picture, arms are local definitions and the body is their gluing.** The design
documents describe a program as facts attached to stages that must agree along every step. The
same shape appears here inside one definition. Each arm defines the function over a region of the
table, and the regions overlap. Priority and agreement are the two standard ways to obtain one
function from overlapping pieces: let the smallest piece win, or require the pieces to agree.

## Nested matches

[Nested](Clef.RFC0002.Nested.html) answers what was unresolved question 3: a type-case nested in an arm
body, with the equations of the outer region in scope.

1. **A nested type-case is erased.** A specialization of a body with matches at any depth
   computes what the body means and holds no type (`nested_specialization_preserves_meaning`).
   The proof uses no assumption.
2. **A checked definition is safe.** `checked_nested_runs` is `checked_match_runs` with matches
   allowed anywhere in a body.
3. **The outer equations are in scope because of where an arm is checked.** An arm's body is
   typed and run only at instantiations where its test succeeds
   (`arm_checked_where_it_matches`). No rule adds the outer equation to a context. An inner arm
   is simply never examined where an enclosing test fails.
4. **Coverage of an inner match is relative to its region.** A one-arm inner match that would be
   rejected as a definition of its own is accepted inside the arm whose test makes it exhaustive
   (`nested_match_checked_in_its_region`).
5. **The intersection arm is a nested test.** `:? 'A & :? 'B -> b` and
   `:? 'A as a -> (match a with :? 'B -> b)` have the same type and value
   (`conjunction_is_nesting`). The forms differ when more arms follow: a conjunction that fails
   falls through to the next arm, and an inner match that fails has no arm.

One difference from Bodies is deliberate and is stated on the module's page. The check types
the arm selected at each instantiation, where Bodies types every arm that matches. That is enough
for safety, and for the result on arm order below.

**Arm order in an inner match.** The overlap check is stated in [Nested](Clef.RFC0002.Nested.html) over
any set of instantiations and for any scrutinee (`ordered_in`), and the check of Regions is the
case of the whole table (`ordered_in_table`). The question was which set an inner match is
compared over. The proofs give this answer.

1. **Both candidates are sound.** A match that passes over the whole table passes over every
   region (`check_over_larger_set_is_stricter`), and under the check over any set that contains
   the instantiations the match runs at, reordering its arms changes neither its type nor its
   value (`inner_order_is_irrelevant`). The second needs no two arms to be equally specific over
   the set, which is the requirement `priority_glues` already makes.
2. **The whole table is too strict.** For `'A : (x | y)` and `'B : (y)`, an inner match on a
   scrutinee of type `'T`, in an arm `:? 'A` written first, with arms `:? 'B` then `:? 'A`, is
   correctly ordered in its region and is rejected over the table
   (`region_check_accepts_what_table_check_rejects`).
3. **So the check is taken over the region.** It accepts everything the other accepts, rejects
   nothing whose order is safe where it runs, and costs no more: it enumerates fewer
   instantiations.
4. **The region is computed by one walk over the body.** The check `nordered` starts from the
   whole table and, at each match, hands each arm's body the instantiations at which that arm is
   selected. That set is exact (`reach_is_where_the_arm_is_selected`). A body that passes, and
   passes again with the arms of any of its matches rearranged, has the same type and value at
   every instantiation (`reordering_arms_changes_nothing`,
   `reordered_definition_means_the_same`). No region is supplied from outside.
5. **In this model the question rarely arises.** Inside an arm of the three-arm match, every test
   on a scrutinee whose type is one of the variables is constant
   (`inner_tests_decided_in_a_region`). Such an inner match needs one arm. The check decides
   something only for an inner match in an arm that overlaps a later arm, or on a scrutinee whose
   type is not a variable. With more than two tested variables the regions are coarser and the
   question would arise more often. That case is not modelled.

**Agreement in an inner match.** [Nested](Clef.RFC0002.Nested.html) states agreement and the gluing
condition for an inner match, over the region of the match. The proofs give these points.

1. **Both ways of gluing carry over.** Arms that glue over a set containing the instantiations
   the match runs at may be written in any order (`inner_glued_order_irrelevant`). The overlap
   check over the set with no two arms equally specific is one way to glue
   (`inner_priority_glues`). Two arms with the same body and the same number of binders is
   another, in every region and on every scrutinee (`inner_same_body_glues`).
2. **Agreement must include the type.** The check of a nested body types the arm selected. Two
   arms that return the same value could still have bodies of different types where only one is
   typed. So agreement of inner arms asks for the same type and the same value. In Bodies the
   check types every matching arm, and agreement there asks for the value only.
3. **Agreement accepts what priority rejects, in a region.** For `'A : (x | y)` and `'B : (y)`,
   an inner match in an arm `:? 'A` with arms `:? 'A` then `:? 'B` and one body is rejected by
   the overlap check over its region and glues
   (`inner_agreement_accepts_what_region_check_rejects`). Priority accepts these two arms only in
   the other order.
4. **Under agreement an arm's body is examined wherever its test succeeds.** Under priority the
   arm selected is the same in every accepted order, so the whole-body check examines an arm's
   body where the arm is selected. Under agreement either of two agreeing arms may be first, so
   either body can run on the overlap. The gluing condition of a whole body, `nglued`, examines
   an arm's body at every instantiation of the region where its test succeeds. A body that
   glues, and glues again with the arms of any of its matches rearranged, has the same type and
   value at every instantiation (`glued_body_means_the_same_reordered`,
   `glued_definition_means_the_same_reordered`), and a definition priority rejects meets the
   hypotheses in both orders (`gluing_accepts_what_overlap_check_rejects`).
5. **The two whole-body conditions are not yet related.** A body that passes `nordered` is not
   shown to satisfy `nglued`, because the sets differ and neither condition is preserved when
   its set changes. Whether `nglued` could use the smaller set is not settled either. Both are
   listed in the table above.

## Possible extensions

These are not part of the RFC. They are recorded because the model points at them. The research
note gives each in more detail.

1. **Patterns as members.** With the overlap of two patterns computed by unification, the overlap
   check covers `list<'a>` against `'a`: their overlap is `list<'a>`, which is itself an arm and
   the more specific one. `first_match_is_most_specific` is proved over a finite table and would
   have to be proved again over a lattice of patterns.
2. **Arms decided by a solver.** An arm could carry a guard over compile-time facts such as range,
   size or alignment. Coverage becomes the validity of a disjunction and the overlap rule a set of
   implications between guards, which are Tier 2 queries. The proofs here enumerate a table and do
   not cover it.
3. **Agreement as a proof obligation.** Where two overlapping arms differ in text and agree in
   result, the agreement could be discharged by a relational proof. A type-case all of whose
   overlaps agree behaves like one function, which is the property RFC 0001 loses when it admits
   the type-case.

## Drawbacks

- **The number of regions grows quickly.** With n tested variables there can be up to 2ⁿ − 1
  regions. The overlap check asks only for the intersections that are reachable, which
  `intersection_reachable_iff` shows the compiler can decide.
- **The check runs over a table.** Its size is bounded by the product of the member-set sizes.
- **Arms carry type equations.** An arm that may assume `'A = 'B` is a local type refinement, which
  is where inference usually loses principal types.
- **Equivalent tests need their own diagnostic.** Two arms that test the same thing pass the
  overlap check and make the result depend on order. The compiler must reject one of them, as it
  would an unreachable rule.

## Alternatives

- **First match with no check.** The two-arm match is then accepted and picks whichever arm is
  first on the overlap. `two_arms_order_matters_iff` shows the cost: reordering arms changes the
  program.
- **Reject overlapping constraints.** Requiring the member sets of tested variables to be disjoint
  removes the intersection arm and the choice of reading together, and removes the feature's point.
- **Sort the arms by specificity.** Sorting cannot order two arms where neither is more specific,
  which is the case this RFC is about.
- **The membership reading of a test.** Rejected for the reasons given above: a binder typed at
  the tested variable is unsound under it, and without that binding it adds nothing to RFC 0001.
- **Agreement only.** Drop the overlap check and require every overlap to agree. This rejects the
  author's three-arm match whenever the intersection arm does something of its own, which is the
  reason to write it.

## Impact and migration

Nothing in a program without a closed-set constraint changes. The RFC depends on RFC 0001.

## Unresolved questions

1. Whether agreement is admitted beside priority, and in which form: identical bodies only, or
   bodies proved equivalent. An arm such as `:? 'A | :? 'B` covering several regions is the
   surface form of the first. The model now supports either answer for an inner match as well as
   for the outer one. If agreement is admitted, an arm's body has to be checked wherever its test
   succeeds, and whether that can be narrowed to where the arm is selected is open.
2. Whether a missing reachable intersection arm is an error. The overlap check as modelled makes it
   one, unless the overlapping arms agree.
3. What the whole-body overlap check costs. [Nested](Clef.RFC0002.Nested.html) computes the region
   of every inner match by filtering the table once for each arm, and proves the check does its
   job. No bound on that work is proved.
4. Constraints declared but never inferred, as the restriction that keeps inference principal.
5. The diagnostic for two arms with equivalent tests.
*)
