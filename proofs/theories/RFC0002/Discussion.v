(**md # Discussion

## What the proofs cover

The model has three type variables: two with closed-set constraints and one constrained to be
either of them. An arm is a test, and the model says which arm a specialization selects. Arm bodies
are not modelled, so there is no typing or evaluation of what an arm does. Member types are closed,
as in RFC 0001.

| Claim | Status |
|---|---|
| The constraints describe a finite, computable table of instantiations | Proved: `table_iff_valid` |
| Arms for both variables cover every instantiation | Proved, both readings: `coverage` |
| The three arms split the table by which variables are equal | Proved, equation reading: `regions_partition` |
| The intersection arm is reachable exactly when the sets share a type | Proved, both readings: `intersection_reachable_iff` |
| Without the intersection arm, arm order matters exactly when the sets share a type | Proved, both readings: `two_arms_order_matters_iff` |
| Under the overlap check, the first matching arm is the most specific | Proved, both readings, any arms: `first_match_is_most_specific` |
| Under the overlap check, arm order does not change the program | Proved, both readings, any arms: `order_is_irrelevant` |
| The three-arm match always passes the overlap check | Proved, both readings: `intersection_first_is_ordered` |
| The overlap check rejects the two-arm match on overlapping sets | Proved for one family of constraints: `unordered_overlap_rejected` |
| An arm's binder has the scrutinee's type | Proved under the equation reading: `equation_refines`. Refuted under the membership reading: `membership_refines_falsified` |
| The two readings select the same arm | Proved for disjoint sets: `readings_agree_when_disjoint`. Refuted in general: `readings_agree_falsified` |
| A definition whose arm bodies check runs at every instantiation | Not proved. Arm bodies are not modelled |
| Specialization preserves meaning with several variables | Not proved. RFC 0001 proves it for one variable |
| Inference with a constraint `'T : ('A or 'B)` keeps principal types | Not proved. The research note argues it does not, without a restriction |
| More than two tested variables, and generic members | Not modelled |

The two refutations hold whenever two different closed types exist. No theorem here uses an
assumption beyond decidable equality of type constructors, `tycon_eq_dec`.

## The open question

What does `:? 'A` test?

- **Equation.** The scrutinee's type is the type `'A` is instantiated to.
- **Membership.** The scrutinee's type is a member of the set `'A` is constrained to.

The proofs give this evidence.

1. **The question matters only for overlapping sets.** Where the member sets share no type, both
   readings select the same arm of every match (`readings_agree_when_disjoint`).
2. **On overlapping sets the readings differ** (`readings_agree_falsified`). With `'A : (x | y)`
   and `'B : (y)`, `'A` instantiated to `x` and a scrutinee of type `y`, the equation reading
   selects `:? 'B` and the membership reading selects the intersection arm.
3. **Only the equation reading lets the arm bind at the variable's type.** Under it, `:? 'A as v`
   may give `v` the type `'A` (`equation_refines`). Under the membership reading that binding is
   unsound (`membership_refines_falsified`), so `v` can only have the scrutinee's type.
4. **The membership reading adds nothing to RFC 0001.** Its test depends only on the scrutinee's
   type and a fixed set of closed types, which is a list of RFC 0001's closed arms.
5. **Everything else is the same.** Coverage, reachability of the intersection arm, the effect of
   arm order and the overlap check hold under both readings.

The evidence favours the equation reading: it is the one under which the intersection arm means
"the two variables unify", and the one under which an arm learns a type equation. The RFC does not
adopt it yet.

## Drawbacks

- **The number of regions grows quickly.** With n tested variables there can be up to 2ⁿ − 1
  regions. The overlap check asks only for the intersections that are reachable, which
  `intersection_reachable_iff` shows the compiler can decide.
- **The check runs over a table.** Its size is bounded by the product of the member-set sizes.
- **Arms carry type equations.** An arm that may assume `'A = 'B` is a local type refinement, which
  is where inference usually loses principal types.

## Alternatives

- **First match with no check.** The two-arm match is then accepted and picks whichever arm is
  first on the overlap. `two_arms_order_matters_iff` shows the cost: reordering arms changes the
  program.
- **Reject overlapping constraints.** Requiring the member sets of tested variables to be disjoint
  removes the intersection arm and the open question together, and removes the feature's point.
- **Sort the arms by specificity.** Sorting cannot order two arms where neither is more specific,
  which is the case this RFC is about.

## Impact and migration

Nothing in a program without a closed-set constraint changes. The RFC depends on RFC 0001.

## Unresolved questions

1. The reading of `:? 'A`, above.
2. Whether one arm may cover several regions, as `:? 'A | :? 'B` would, when its body checks in
   each. The compiler cannot write an arm body, so this is the nearest thing to implicit handling.
3. Whether a missing reachable intersection arm is an error. The overlap check as modelled makes it
   one.
4. A model of arm bodies, so that the type equations of a region are used by a typing judgement and
   the soundness of a checked definition is proved, as RFC 0001 does for one variable.
5. Constraints declared but never inferred, as the restriction that keeps inference principal.
*)
