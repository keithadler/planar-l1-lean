# planar-l1-lean

A **conditional** Lean 4 / Mathlib formalisation of selected lemmas from OpenAI's preprint
*Planar Graph Metrics Embed into $L_1$ with Constant Distortion* (23 September 2026)
([PDF](https://github.com/openai/math/blob/main/preprints/Planar-Graph-Metrics-Embed-into-L1-with-Constant-Distortion-September-23-2026/paper.pdf)).
Companion notes for human readers: [`planar-l1-companion`](https://github.com/keithadler/planar-l1-companion).

## What this is, and is not

* It formalises **parts of Sections 3, 5 and 6** only (below). It is **not** a proof of the paper's main theorem, and Sections 2, 4, 6.3, 7, 8 and 9 are not formalised.
* Everything a formalised lemma needs from an unformalised part (Theorem 4.1, Lemmas 2.11 and 2.12, …) is an **explicit hypothesis** (a structure field or an argument). There is no `sorry`, no new `axiom`, no `native_decide`.
* A compile shows the *formal statement* follows from its *hypotheses*. Whether a statement matches the paper's, and whether the hypotheses hold, needs a human; each theorem's docstring quotes the paper and lists the differences.
* **No expert has reviewed this.** The Lean files were written by Claude (AI) with Keith Adler, and compiled and audited independently by the same pair; the proofs are checked by Lean's kernel, the statements were read against the paper by the authors only.

## Contents

| File | Paper | Contents |
|---|---|---|
| `PlanarL1/Chart.lean` | §3.1, Lemma 3.1 | identity (5); nesting and the vertical-length equality; rebasing and the law of $Z'$ with a fresh sign (on $\mathbb R\times\{\pm1\}$ and on the paper's $\mathbb R\times\{\pm1\}^{\mathbb N}$) |
| `PlanarL1/Refinement.lean` | §3.2, Lemma 3.2 | component refinement (domination, same upper bound, separation clause 2) and exact gluing |
| `PlanarL1/Constants.lean` | §5.1 | the explicit constants and every inequality later used from them; a nonempty `Choice` structure for $a_1,a_2$ |
| `PlanarL1/Update.lean` | §6.1–6.2 | Lemma 6.1, Definition 6.2, Lemma 6.3, Corollary 6.4, Lemma 6.5, formula (29) |

## Checking it

Toolchain `leanprover/lean4:v4.34.1`, Mathlib pinned in `lake-manifest.json`. With a built Mathlib: `lake env lean PlanarL1/Chart.lean` (and likewise for the other files; `Update.lean` imports `Constants`). To audit axioms, add `#print axioms <name>` for any declaration; every declaration in the four files depends only on `propext`, `Classical.choice` and `Quot.sound` (checked for all 342 declarations by an automated pass).

## Licence

Copyright 2026 Keith Adler. Licensed under the [Apache License, Version 2.0](LICENSE), the licence Mathlib uses. The paper formalised here is OpenAI's; this repository contains only original statements and proofs that reference it.
