# planar-l1-lean

[![License: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean-v4.34.1-6b4fbb.svg)](lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-pinned-2f6fdd.svg)](lake-manifest.json)
![status](https://img.shields.io/badge/status-conditional%20%26%20unreviewed-orange.svg)

A **conditional** Lean 4 / Mathlib formalisation of selected lemmas of OpenAI's preprint
[*Planar Graph Metrics Embed into $L_1$ with Constant Distortion*](https://github.com/openai/math/blob/main/preprints/Planar-Graph-Metrics-Embed-into-L1-with-Constant-Distortion-September-23-2026/paper.pdf) (23 September 2026).
It exists to support a **human reader's own verification** of that paper; for plain-language notes on every section see the companion repository
[**planar-l1-companion**](https://github.com/keithadler/planar-l1-companion).

> **Read this first.** This repository does **not** prove the paper's main theorem, and it does not say the theorem is true or false.
> It formalises parts of Sections 3, 5 and 6, and takes everything those parts need from other sections as **explicit hypotheses**
> (never as axioms, never as `sorry`). A successful compile shows that a *formal statement* follows from *stated hypotheses*;
> whether a statement says what the paper says, and whether the hypotheses hold, still needs a human.
> **No expert has reviewed this work.**

## At a glance

| File | Paper | What is formalised | Declarations |
|---|---|---|---|
| [`PlanarL1/Chart.lean`](PlanarL1/Chart.lean) | §3.1, Lemma 3.1 | the cut-distance identity (5); nesting and the vertical-length equality; rebasing, with the law of $Z'$ and a fresh sign, on $\mathbb R\times\{\pm1\}$ and on the paper's $\mathbb R\times\{\pm1\}^{\mathbb N}$ | 50 |
| [`PlanarL1/Refinement.lean`](PlanarL1/Refinement.lean) | §3.2, Lemma 3.2 | component refinement (domination, the same upper bound, the separation clause "$=2$") and **exact gluing** | 149 |
| [`PlanarL1/Constants.lean`](PlanarL1/Constants.lean) | §5.1 | the explicit constants and every inequality later used from them; a nonempty `Choice` structure for $a_1,a_2$ | 59 |
| [`PlanarL1/Update.lean`](PlanarL1/Update.lean) | §6.1–6.2 | Lemma 6.1, Definition 6.2, Lemma 6.3 (raise or descend), Corollary 6.4, Lemma 6.5, formula (29) | 84 |
| [`PlanarL1/CrossCheck.lean`](PlanarL1/CrossCheck.lean) | §5.1 | a cross-check: OpenAI's concrete widths $a_1=10^{-100}$, $a_2=10^{-160}$ satisfy our `Choice` hypotheses | 14 |

356 declarations in all. Every one of them depends only on `propext`, `Classical.choice` and `Quot.sound` (checked by an automated audit of *every* theorem and definition, not only the headline ones).
A statement-by-statement map from the paper to Lean is in [`docs/theorem-map.md`](docs/theorem-map.md).

## OpenAI's own Lean formalisation

OpenAI published a Lean 4 formalisation of this very theorem alongside the paper: the formal statement is
[`lean/ComparatorChallenges/PlanarL1.lean`](https://github.com/openai/math/blob/main/lean/ComparatorChallenges/PlanarL1.lean)
and the proof is in [`lean/OAI/Combinatorics/PlanarL1/`](https://github.com/openai/math/tree/main/lean/OAI/Combinatorics/PlanarL1)
(63 files; the top-level theorem is `OAI.PlanarL1.planar_graph_metrics_embed_L1` in `Embedding.lean`). We have **not** compiled it. A text scan of those 63 files found no `sorry`, `axiom` declaration, `native_decide` or `unsafe`, which says nothing about whether it builds.

**This repository is a much smaller, independent cross-check, not the main verification.** Its files were written from the paper's PDF alone, **before** anyone on this project read any of OpenAI's Lean ("clean room" with respect to their code). Only afterwards were three things read from OpenAI's repository: the statement file above, the top-level `Embedding.lean`, and the two concrete widths in their `Parameters.lean` (used in `CrossCheck.lean`). The numerical constants of Section 5.1 agree between the two independent readings of the paper.

The most useful quick human check is whether OpenAI's roughly 40-line `MainStatement` says what Theorem 1.1 says.

## What is assumed, and what is not formalised

Each formalised lemma takes the following as hypotheses (structure fields or arguments), stated in its docstring:

| Taken from | Used by | Form in Lean |
|---|---|---|
| Definition 2.1 (column model: compact switch sets, noncrossing links, terminal tips) | Lemma 3.2, gluing | `ColumnModel` structure |
| the label law $\mu\{\sigma=s,\ a\le Z<b\}=\tfrac12(b-a)$ | gluing | `ChartLabels` |
| Theorem 4.1 (interpolation): inequality (23) and the $1$-Lipschitz property of $F_C$ | Lemmas 6.1, 6.3 | `Setup` structure; `Setup.of_thm41` builds one from a Theorem 4.1 output |
| Lemma 2.11 (cell diameter $\le10D$, compact frontier) and Lemma 2.12 (padding $d(w,z)>0.01D$) | Lemmas 6.1, 6.3 | `Setup` fields and arguments |
| Lemma 3.2 (per-label contribution $\ge2$) | Lemma 6.5, formula (29) | hypothesis `hL32` (not yet connected to `Refinement.lean`) |

**Not formalised:** Section 2 (geometry of the circular order, portals, cells), Section 4 (the interpolation theorem), §6.3 (the packing bound), Sections 7, 8 and 9 (ordered fields, the secondary update, the probability argument and the schedule), Section 10.

## How to read the code

Every theorem and definition has a docstring in this shape:

* the paper's statement **quoted** with its number;
* `Lean:` how the formal statement reads;
* `Difference:` every way it differs from the paper (e.g. $\kappa L\le1$ instead of $<1$; one sign coordinate instead of $\{\pm1\}^{\mathbb N}$; $[0,\infty]$-valued integrals instead of subtracting a reference vector).

Helper lemmas are labelled *auxiliary* and say they are not statements of the paper. Start with the module docstring at the top of each file.

## Building and checking

You need [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.34.1`) and the Mathlib revision are pinned.

```bash
git clone https://github.com/keithadler/planar-l1-lean
cd planar-l1-lean
lake exe cache get      # download the prebuilt Mathlib; do not build Mathlib from source
lake build              # builds the four files
```

To check a single file: `lake env lean PlanarL1/Chart.lean` (and likewise for the others; `Update.lean` imports `Constants`).

> **Tested how:** the four files were each compiled with `lake env lean` against an existing Mathlib build at the pinned revision (about 8 to 40 seconds each), and the aggregator `PlanarL1.lean` was checked to import all four. A full `lake build` from a fresh clone has **not** been run by the authors; if it fails for you, please open an issue.

**Audit the axioms of every declaration in a file** by appending this to a copy of the file; it reports any dependency outside the three standard axioms (a stray `sorry` would show up as `sorryAx`):

```lean
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total := 0
  let mut bad : Array String := #[]
  for (n, ci) in env.constants.map₂.toList do
    if n.isInternal then continue
    unless (ci matches .thmInfo _ | .defnInfo _) do continue
    total := total + 1
    for a in (← collectAxioms n) do
      unless allowed.contains a do bad := bad.push s!"{n} uses {a}"
  logInfo m!"{total} declarations; non-standard axioms: {bad.size} {bad}"
```

For an independent second check of the kernel, the project can also be re-verified with [Tenet](https://github.com/keithadler/tenet) (a separate implementation of Lean's type checker); that has not been run on these files.

## Repository layout

```
PlanarL1.lean            imports the four files
PlanarL1/Chart.lean      Section 3.1
PlanarL1/Refinement.lean Section 3.2
PlanarL1/Constants.lean  Section 5.1
PlanarL1/Update.lean     Sections 6.1-6.2
docs/theorem-map.md      paper statement -> Lean name, with line links
TASKS.md                 the original work list and rules
CITATION.cff             how to cite
```

## Provenance and honesty

The Lean files were written by Claude (an AI) subagents for Keith Adler, following the rules in [`TASKS.md`](TASKS.md), then compiled and audited in a separate Claude session. The proofs are checked by Lean's kernel. The statements were read against the paper only by that session. Two things were found and fixed along the way: the task specification claimed that the rebased coordinate $Z'$ keeps the joint law with the *old* sign (it does not: it is independent of a *fresh* sign, as in the paper), and a measurability proof that timed out.

## Contributing

Corrections are very welcome, above all **a statement that differs from the paper**: please open an issue quoting the paper's line and the Lean declaration. Pull requests should follow Mathlib's style, add no `sorry` or axiom, and keep the `Lean:` / `Difference:` docstring convention.

## Citation and licence

See [`CITATION.cff`](CITATION.cff). Copyright 2026 Keith Adler. Licensed under the [Apache License, Version 2.0](LICENSE), the licence Mathlib uses. The paper formalised here is OpenAI's; this repository contains only original statements and proofs that reference it.
