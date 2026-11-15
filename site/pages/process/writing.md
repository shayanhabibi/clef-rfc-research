---
title: Writing an RFC
---

## Start from the template

From the repository root, with the next free number:

```bash
bash proofs/new-rfc.sh 0002 "Tagged anonymous sums"
```

This copies `proofs/template` to `proofs/theories/RFC0002`, fills in the number and title, and adds the modules to `proofs/_CoqProject`. The modules are named `Clef.RFC0002.Overview`, `Clef.RFC0002.Design` and `Clef.RFC0002.Discussion`. Rename `Design`, or add modules beside it, and keep `_CoqProject` in dependency order.

The home page finds an RFC by its `Overview` module, and reads the title from the first heading and the stage from the header table. Keep both in the form the template gives them.

## Prose

Prose is written in Markdown comments, which open with the `md` marker:

```rocq
(**md ## Entailment

A variable constrained to one member set may be used where another is required
when the first is a subset of the second.
*)
```

Inside a Markdown comment, a name in backticks links to its declaration, and a link to another module is `[Constraints](Clef.RFC0001.Constraints.html)`. Fenced blocks marked `fsharp` and `rocq` are coloured.

A double quote inside a comment opens a Rocq string, so quotes must come in pairs, and the text between a pair must not hold a comment closer.

## A claim

A `Theorem` whose comment opens with a line wholly in bold appears on the Guarantees page under that line. Write the line as the claim a reader of the RFC would recognise, and follow it with what the claim means for the design:

```rocq
(**md
**A definition that checks is well typed at every instantiation.**

When the check passes at the definition, every type that satisfies the
constraint yields a specialization with the declared type.

- [C:] the member set of the variable.
*)
Theorem derived_satisfaction (C : cset) (G : list oty) (e : tm) (r : oty) :
  check C G e r = true -> forall t, sat t C -> well_typed_at t G e r.
```

An entry `- [name:] text` documents a binder of the statement. Naming something that is not a binder fails the site build.

Use `Lemma` for a step that a reader of the RFC does not need. A lemma never appears on the Guarantees page.

## Before opening a pull request

1. Compile, capture the facts and build the site, as [Building](building.md) describes.
2. Commit the `.glob` files and `proofs/facts.json` with the sources. The site is built from them, without Rocq.
3. Fill in the table in `Discussion` that lists each claim as proved, assumed or not proved.
