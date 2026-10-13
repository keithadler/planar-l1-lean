# Theorem map: paper statement to Lean declaration

Generated from the docstrings in `PlanarL1/*.lean`. Each row is a declaration whose docstring is labelled with a statement of the paper; the docstring quotes the paper and lists exactly how the Lean statement differs. Helper lemmas whose docstring says they are not statements of the paper (72 of them) are omitted. Line numbers link to the source.

| File | Paper statement | Lean name | Line |
|---|---|---|---|
| `Chart` | Lemma 3.1, identity (5) | `measure_symmDiff_thrSet` | [123](../PlanarL1/Chart.lean#L123) |
| `Chart` | Lemma 3.1, identity (5), in the paper's point notation | `measure_symmDiff_chartSet` | [165](../PlanarL1/Chart.lean#L165) |
| `Chart` | Lemma 3.1, nesting (second assertion) | `chartSet_subset_of_le` | [190](../PlanarL1/Chart.lean#L190) |
| `Chart` | Lemma 3.1, vertical length (third assertion) | `measure_symmDiff_chartSet_eq_vertical` | [217](../PlanarL1/Chart.lean#L217) |
| `Chart` | Lemma 3.1, nesting plus vertical length, in the form used later | `measure_diff_chartSet_eq_vertical` | [234](../PlanarL1/Chart.lean#L234) |
| `Chart` | Lemma 3.1, rebasing: the set identity `{Z < ϕ_σ(h)} = {Z' < h}` | `rebase_lt_iff` | [348](../PlanarL1/Chart.lean#L348) |
| `Chart` | Lemma 3.1, rebasing: a height-only branch is the same set with field zero | `chartSet_rebase` | [363](../PlanarL1/Chart.lean#L363) |
| `Chart` | Lemma 3.1, rebasing: the new coordinate has the right law | `rebase_chartLabels` | [425](../PlanarL1/Chart.lean#L425) |
| `Chart` | Section 3.1, the paper's label space `Ω = ℝ × {-1,1}^ℕ`, `μ = L ⊗ ν` | `chartLabels_paper` | [506](../PlanarL1/Chart.lean#L506) |
| `Refinement` | Lemma 3.2, domination | `symmDist_le_refDist` | [308](../PlanarL1/Refinement.lean#L308) |
| `Refinement` | Lemma 3.2, same upper bound | `refDist_le_of_reach` | [330](../PlanarL1/Refinement.lean#L330) |
| `Refinement` | Lemma 3.2, the separation clause, for one label | `labelDist_eq_two_of_inactive_tip` | [416](../PlanarL1/Refinement.lean#L416) |
| `Refinement` | Lemma 3.2, separation clause, integrated | `two_mul_measure_le_refDist` | [432](../PlanarL1/Refinement.lean#L432) |
| `Refinement` | Lemma 3.2, refined pseudometric dominated by `d` | `refDist_le_colDist` | [450](../PlanarL1/Refinement.lean#L450) |
| `Refinement` | Lemma 3.2, first sentence | `symmDist_le_colDist` | [454](../PlanarL1/Refinement.lean#L454) |
| `Refinement` | Exact gluing, global invariant on one column | `nested_length` | [777](../PlanarL1/Refinement.lean#L777) |
| `Refinement` | Exact gluing, switch agreement | `respects_switch` | [821](../PlanarL1/Refinement.lean#L821) |
| `Update` | Lemma 6.3, last assertion, (26) | `descending_path_bound` | [91](../PlanarL1/Update.lean#L91) |
| `Update` | Theorem 4.1 | `Setup.of_thm41` | [441](../PlanarL1/Update.lean#L441) |
| `Update` | Lemma 6.1, frontier part | `Setup.frontier_margin` | [484](../PlanarL1/Update.lean#L484) |
| `Update` | Lemma 6.1, band-end part | `Setup.band_end_margin` | [507](../PlanarL1/Update.lean#L507) |
| `Update` | Lemma 6.1, size part | `Setup.raise_bounds` | [539](../PlanarL1/Update.lean#L539) |
| `Update` | Lemma 6.1, last sentence | `Setup.label_change_le` | [568](../PlanarL1/Update.lean#L568) |
| `Update` | Lemma 6.1, "different cell prescriptions agree at common quotient points" | `newField_agree_on_common_frontier` | [589](../PlanarL1/Update.lean#L589) |
| `Update` | Lemma 6.1, vertical part | `Setup.repl_vert_lip` | [603](../PlanarL1/Update.lean#L603) |
| `Update` | Lemma 6.3 | `Setup.main_raise_or_descending` | [649](../PlanarL1/Update.lean#L649) |
| `Update` | Corollary 6.4 | `main_test_separation` | [725](../PlanarL1/Update.lean#L725) |
| `Update` | Lemma 6.5, first assertion | `label_mass_at_tip` | [812](../PlanarL1/Update.lean#L812) |
| `Update` | Formula (29) | `refined_separation_final` | [877](../PlanarL1/Update.lean#L877) |
| `Update` | Lemma 6.5, second assertion | `lemma65` | [925](../PlanarL1/Update.lean#L925) |
