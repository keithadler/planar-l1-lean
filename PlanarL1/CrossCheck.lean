/-
Copyright (c) 2026 Keith Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler (with Claude)
-/

import PlanarL1.Constants

/-!
# Cross-check: OpenAI's concrete width choice satisfies our `Choice` hypotheses

Section 5.1 of the paper leaves two widths `a₁, a₂` free, subject to upper bounds. Our
`PlanarL1/Constants.lean` was written from the paper's PDF alone, keeping `a₁, a₂` abstract in the
structure `Constants.Choice`.

OpenAI's published Lean file `lean/OAI/Combinatorics/PlanarL1/Parameters.lean` fixes them at the concrete
values `a₁ = 10^-100` and `a₂ = 10^-160`. This file checks, **after the fact**, that those two values satisfy
every hypothesis of our `Choice`, so that all theorems of `Constants.lean` and `Update.lean` apply to them.

**Provenance.** Only the two numbers were read from OpenAI's file, after `Constants.lean` and
`Update.lean` were finished and audited. None of OpenAI's proofs was consulted when writing any file of this
repository. The file is therefore a *cross-check* of two independent readings of the paper, not a source for
ours.
-/

namespace PlanarL1
namespace Constants

/-- **Cross-check.** OpenAI's concrete widths `a₁ = 10^-100`, `a₂ = 10^-160` form a valid `Choice`: they
satisfy the Theorem 4.1 width bounds for `(ζ_A, E_A)` and `(ζ_B, E_B)`, `a₁ ≤ 10^-6 E_A`, and
`a₂ ≤ 10^-6 min{a₁, κ_A j}`.

Lean: the four inequalities are discharged by `norm_num`. Difference: none from the paper; the paper only
requires *some* admissible choice, which `Choice.nonempty` already provides abstractly. -/
noncomputable def openAIChoice : Choice where
  a1 := 1 / 10 ^ 100
  a2 := 1 / 10 ^ 160
  a1_pos := by norm_num
  a2_pos := by norm_num
  a1_thm41 := by norm_num [thm41Width, zetaA, EA, eps]
  a1_le := by norm_num [EA, eps]
  a2_thm41 := by norm_num [thm41Width, zetaB, EB, R]
  a2_le := by
    have h : (1 / 10 ^ 100 : ℝ) / 10 ^ 6 * j ≤ 1 / 10 ^ 100 := by norm_num [j]
    rw [min_eq_right h]
    norm_num [j]

/-- With OpenAI's widths, the vertical-Lipschitz condition of Lemma 6.1 holds: this is the general theorem
`Choice.kappaA_mul_maxLip_lt_one` applied to `openAIChoice`. -/
theorem openAIChoice_vertical_A :
    openAIChoice.kappaA * max 1 (3 / (0.09 * openAIChoice.a1)) < 1 :=
  openAIChoice.kappaA_mul_maxLip_lt_one

/-- With OpenAI's widths, `κ_B · 5 ≤ 1` (the condition that a chart field of Lipschitz constant `< 5` keeps the
sets nested in system `B`). -/
theorem openAIChoice_kappaB_five : openAIChoice.kappaB * 5 ≤ 1 := by
  norm_num [Choice.kappaB, openAIChoice]

end Constants
end PlanarL1
