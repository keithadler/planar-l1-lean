# Work list and rules

## Rules (all tasks)
1. **No `sorry`, no new `axiom`, no `native_decide`.** An assumption from another section is a *hypothesis of the theorem*
   (a structure field or an explicit argument), never an axiom. State it in the docstring and say which lemma/theorem of the paper it is.
2. **Fidelity.** Every Lean theorem has a docstring quoting the paper's statement (number and a short paraphrase, and the
   paper's own equation numbers), saying exactly how the Lean statement differs (specialisations, generalisations).
   Do not weaken a statement silently. If the paper's statement is ambiguous, write the stronger reading AND say so.
3. **Fetch the paper yourself** from the URL in README.md (it is public). Do not commit the PDF or its text.
4. Toolchain `leanprover/lean4:v4.34.1`, Mathlib pinned in `lake-manifest.json`. Run `lake exe cache get` first; never build Mathlib from source.
5. Before finishing: `lake build` clean with warnings-as-errors off but no `sorry` warnings; `#print axioms` for every main theorem
   must list only `propext`, `Classical.choice`, `Quot.sound`. Put those `#print axioms` lines in the file as comments with the output.
6. One branch per task (`task/<name>`), open a PR to `main` in this repo, list in the PR body: what is proved, what is assumed, what is NOT done.
7. Report failures honestly: a lemma you could not prove stays out of the build, listed in the PR body as open.

## Task A: `PlanarL1/Chart.lean` (Section 3.1, Lemma 3.1)
Label space `Ω = ℝ × Bool` with measure `volume.prod (½(δ_true + δ_false))` (the paper uses `ℝ × {−1,1}^ℕ`; state why one sign suffices
or use the product space if it is not much harder). For `Z, σ` and fields: `A_v = {ω | Z ω < h v + σ ω * κ * P v}`.
1. Identity (5): `μ(A_v △ A_w) = max{|h v − h w|, κ |P v − P w|}` for `κ > 0`.
2. Nesting: if `κ * Lip_vert(P) < 1` the sets are increasing in `h` on a column interval and the symmetric difference has measure equal to the vertical length.
3. Rebasing: for `ψ : ℝ → ℝ` Lipschitz with `κ Lip ψ < 1`, `φ_σ(H) = H + σ κ ψ(H)` are increasing bijections; `Z' = φ_σ⁻¹(Z)` has Lebesgue pushforward and is independent of a *fresh* sign `σ'` (not of the old `σ`: given `σ = b`, `Z'` has law `(φ_b⁻¹)_* Lebesgue`, which depends on `b`); and `{Z < φ_σ(h)} = {Z' < h}`.

## Task B: `PlanarL1/Refinement.lean` (Section 3.2, Lemma 3.2 and the gluing invariant)
Abstract the column model: a finite set of columns, switches `(i, j, height)`, a noncrossing circular order given as a hypothesis,
sets nested increasingly on each column, respecting switches, symmetric-difference measure at most vertical length.
1. Lemma 3.2: the component-refined pseudometric dominates the original one and has the same upper bound; a non-neighbour link with
   inactive tip separating two active points contributes exactly 2 for that label.
2. Exact gluing (Section 3.2): replacing the old field by `max(old, proposal)` where the proposal lies strictly below the old field on
   the domain boundary preserves nesting, switch agreement and the vertical-length bound (the three-step comparison in the paper).

## Task C: `PlanarL1/Update.lean` and `PlanarL1/Constants.lean` (Sections 5, 6.1–6.2)
1. `Constants.lean`: the numerical choices of Section 5.1 and every inequality the paper later uses from them (e.g. `ζ_A d₀ + 7 E_A < ε`,
   `a₂ ≤ 10⁻⁶ min{a₁, κ_A j}`, `E_A ≤ j/4`, `a₂ ≤ κ_A j/4`, `h-plateau` bounds). `norm_num`-style, but each stated as a named theorem.
2. `Update.lean`: Lemma 6.1 (the replacement `s' = max{s, min{F_C, p_{h,C}(h)}}` respects the frontier and band-end margins; `0 ≤ s'−s ≤ 1+10D`),
   Lemma 6.3 (raise by more than `2E_A` unless a descending path exists, with (23) and Lemma 2.12's padding bound as hypotheses),
   Corollary 6.4, Lemma 6.5 and formula (29). Work in an abstract metric space with a Lipschitz field and a frontier set.
   Theorem 4.1 (interpolation) and Lemmas 2.11/2.12 are HYPOTHESES (structure fields), stated exactly.
