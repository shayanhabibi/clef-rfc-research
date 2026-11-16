---
title: How an RFC is built
---

An RFC in this repository is a directory of Rocq modules. The prose of the RFC is written in the comments of those modules, and the site renders both together.

## The parts of an RFC

| Module | Holds |
|---|---|
| `Overview` | The header table, summary, motivation, and a guide to the other modules. It has no code |
| One module per topic | Definitions for the design rules, and theorems for the claims |
| `Discussion` | What the proofs cover and do not cover, drawbacks, alternatives, impact and unresolved questions |

These are the sections the [specification's change process](https://clef-lang.com/spec/draft/change-process-management/) requires of an RFC: summary, motivation, detailed design, drawbacks, alternatives, impact and migration, and unresolved questions. The detailed design is the topic modules.

## The standard a claim must meet

1. **A design rule is a definition.** A rule the compiler would run is written as a function that computes, such as a check returning `bool`. A theorem then relates it to the property it is meant to decide.
2. **A claim is a theorem.** A statement about what the design guarantees is proved, and its proof ends in `Qed`.
3. **A proof is not a restatement.** A theorem that holds by unfolding its own definition proves nothing about the design. The central claims of an RFC are about behaviour, and they need a model of behaviour: typing, evaluation, or both.
4. **An assumption is declared.** A fact taken from the specification is an `Axiom` or `Parameter` in a `Spec` module, with the chapter it comes from. See [Spec assumptions](assumptions.md).
5. **An unproved claim is visible.** A claim that is stated and not yet proved ends in `Admitted`, and appears in the Open group of the Guarantees page. A claim that is not stated in Rocq is listed in the RFC's Discussion as not proved.
6. **A refuted alternative is a theorem too.** Where the RFC rejects an alternative because it cannot work, the impossibility is proved, under a name ending in `_falsified`.

## How readers see it

The [Guarantees page]({{base}}proofs/index.html) lists every titled theorem of every RFC, grouped by module. Each entry carries a badge saying which assumptions its proof depends on, taken from Rocq's own `Print Assumptions`.

| Group | Meaning |
|---|---|
| Guarantees | Proved |
| Open | Stated, and ends in `Admitted` |
| Falsified | A proof that a claim is false |

## Stages

An RFC's header table gives its stage, using the stages of the [specification's change process](https://clef-lang.com/spec/draft/change-process-management/): Draft, Review, Final review, then Accepted, Rejected, Postponed or Withdrawn. The home page reads the stage from the header.
