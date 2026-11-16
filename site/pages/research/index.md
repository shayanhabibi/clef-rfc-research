---
title: Research notes
---

These notes hold the analysis behind the RFCs: what was read, what follows from it, and what is still unsettled. A note is not a proof. Where a note names a theorem, the theorem is on the RFC's own pages and says what its page says. Every other statement in a note is a reading or a proposal.

Each note lists its sources and marks how each was read.

| Note | About |
|---|---|
| [Closed-set constraints over several type variables](multi-variable-union-constraints.md) | The meaning of a constraint such as `'T : ('A or 'B)`, the regions of a type-case over it, and inference. Behind RFC 0002 |
| [Overlapping type patterns](overlapping-type-patterns.md) | Ordering arms such as `list<'a>` and `'a` by specificity. Behind RFC 0001 |
| [RFC 0001 and RFC 0002 against the verification tiers](tier-placement-and-extensions.md) | Where the two RFCs sit in the tier system of the Dimensional Type System, and what they could be extended to carry |

The source of every note is in the `research` directory of the repository.
