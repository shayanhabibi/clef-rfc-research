---
title: Clef RFC research
description: Proposals for the Clef language whose claims are theorems checked by Rocq.
layout: splash
---

<section class="rfc-hero">
<h1 class="rfc-hero__title">Clef RFC research</h1>
<p class="rfc-hero__line">Proposals for the <a href="https://clef-lang.com/spec/">Clef language</a> whose claims are theorems. Each RFC is a Rocq development: the design rules are definitions, and what the design promises is proved from them.</p>
<div class="rfc-hero__actions">
<a class="rfc-button rfc-button--primary" href="{{base}}proofs/index.html">Read the guarantees</a>
<a class="rfc-button" href="{{base}}process/">How an RFC is built</a>
</div>
</section>

## RFCs

<!-- rfcs -->

A theorem is a claim the RFC makes to its readers, and a lemma is a step toward one. **Unproved** counts statements that end in `Admitted`. **Own assumptions** counts axioms and parameters the RFC declares for itself, beyond the {{spec-assumptions}} taken from the specification in the shared [`Spec` modules](process/assumptions.md).

## What a proof here does and does not show

A proof shows that a claim follows from the model and the assumptions. It does not show that the model matches the compiler, or that an assumption reads the specification correctly. Each RFC says what its model leaves out, and every theorem lists the assumptions its proof used.

This site is research. It is not part of the Clef specification, and nothing here is accepted until it goes through the [specification's change process](https://clef-lang.com/spec/draft/change-process-management/).
