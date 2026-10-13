import Mathlib

/-!
# The numerical choices of Section 5.1 and the inequalities the paper draws from them

Source: OpenAI, *Planar Graph Metrics Embed into L1 with Constant Distortion* (23 Sep 2026), Section 5.1
("Fixed constants and scales"), and the places in Sections 5.2, 6.1 and 6.2 that use these constants.

The paper fixes

    R = 10^-8, D = 10^-3, g = 10^-14, j = 10^-20, ε = 10^-24, E_A = ε/1000, E_B = 10^-3 R,
    ζ_A = ε/100, ζ_B = 1/10, K = 100, λ = R/(10^12 K),

then chooses `a₁ > 0` "within the width bound of Theorem 4.1 for (ζ_A, E_A), within the bounds of
Lemmas 2.11 and 2.12 for D and g, and with a₁ ≤ 10^-6 E_A", sets `κ_A = a₁/10^6`, chooses `a₂ > 0`
"within the bound of Theorem 4.1 for (ζ_B, E_B) and with a₂ ≤ 10^-6 min{a₁, κ_A j}", and sets
`κ_B = a₂/10^6`.

In Lean the eleven explicit numbers are definitions.  The two free choices `a₁, a₂` are fields of the
structure `Choice`, together with exactly the hypotheses the paper imposes on them.  The Theorem 4.1
width bound is `a ≤ a₀ = 10^-6 ζ δ` with `δ = E/8` (Theorem 4.1, display (6)); it is a *field* of
`Choice` (not an axiom), as the paper leaves `a₁, a₂` to be chosen small enough for it.
The bounds of Lemmas 2.11 / 2.12 for `D` and `g` (`a ≤ D/1000`, and the same with `g`) are not fields:
they follow from `a₁ ≤ 10^-6 E_A` and are proved below (`Choice.a1_le_D_div_1000`, `Choice.a1_le_g_div_1000`).

Every inequality is a named theorem.
-/

namespace PlanarL1
namespace Constants

/-! ### The fixed numbers -/

/-- `R = 10^-8`, the secondary update radius. -/
noncomputable def R : ℝ := 1 / 10 ^ 8
/-- `D = 10^-3`, the main radial cell width. -/
noncomputable def D : ℝ := 1 / 10 ^ 3
/-- `g = 10^-14`, the radial width for grouping seeds. -/
noncomputable def g : ℝ := 1 / 10 ^ 14
/-- `j = 10^-20`, the detectable drop at a separating tip. -/
noncomputable def j : ℝ := 1 / 10 ^ 20
/-- `ε = 10^-24`, the error in a descending path (the paper's `ϵ`). -/
noncomputable def eps : ℝ := 1 / 10 ^ 24
/-- `E_A = ε/1000`, the interpolation error of system A. -/
noncomputable def EA : ℝ := eps / 1000
/-- `E_B = 10^-3 R`, the interpolation error of system B. -/
noncomputable def EB : ℝ := R / 1000
/-- `ζ_A = ε/100`. -/
noncomputable def zetaA : ℝ := eps / 100
/-- `ζ_B = 1/10`. -/
noncomputable def zetaB : ℝ := 1 / 10
/-- `K = 100`, the Lipschitz bound reserved for the auxiliary field of system B. -/
noncomputable def K : ℝ := 100
/-- `λ = R/(10^12 K)`, the size of the auxiliary correction in system B. -/
noncomputable def lam : ℝ := R / (10 ^ 12 * K)

/-! ### The order of magnitude `ε ≪ j ≪ g ≪ R ≪ D ≪ 1` and the other numerical facts -/

/-- Paper §5.1: all fixed constants are positive. -/
theorem fixed_constants_pos :
    0 < R ∧ 0 < D ∧ 0 < g ∧ 0 < j ∧ 0 < eps ∧ 0 < EA ∧ 0 < EB ∧ 0 < zetaA ∧ 0 < zetaB ∧ 0 < K ∧
      0 < lam := by
  unfold R D g j eps EA EB zetaA zetaB lam K R eps
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- Paper §5.1: the hierarchy `ε < j < g < R < D < 1` (the "≪" chain of the table, as honest `<`). -/
theorem hierarchy : eps < j ∧ j < g ∧ g < R ∧ R < D ∧ D < 1 := by
  unfold eps j g R D
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- Paper §5.1: `E_A < ε`. -/
theorem EA_lt_eps : EA < eps := by
  unfold EA eps; norm_num

/-- Paper §6.2, proof of Lemma 6.5: `E_A ≤ j/4`. -/
theorem EA_le_j_div_four : EA ≤ j / 4 := by
  unfold EA eps j; norm_num

/-- Paper §5.1: `E_B < R`; also `E_B = 10^-3 R`. -/
theorem EB_lt_R : EB < R := by
  unfold EB R; norm_num

/-- Paper §5.1: `λ = R/(10^12 K) = 10^-22`, and `λ < R`, `10^12 K λ = R`. -/
theorem lam_facts : lam = 1 / 10 ^ 22 ∧ lam < R ∧ 10 ^ 12 * K * lam = R := by
  unfold lam R K
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- Paper §6.1, proof of Lemma 6.3: the width `10 D` of a cell's weak diameter is below `0.02`
(the upper end of the range of a descending path, Definition 6.2), and below `1`
(used in Corollary 6.4: "a cell has d-diameter at most `10D < 1`"). -/
theorem ten_D_lt : 10 * D < 0.02 ∧ 10 * D < 1 := by
  unfold D; constructor <;> norm_num

/-- Paper §6.1, proof of Lemma 6.3: "`d₀ ≥ 0.01 D = 10^-5`". -/
theorem one_hundredth_D : 0.01 * D = 1 / 10 ^ 5 := by
  unfold D; norm_num

/-- Paper §6.1 (Definition 6.2 and §6.2): `ϵ < 10^-5`, so "a constant field cannot satisfy (25) with
`d₀ ≥ 10^-5 > ϵ`". -/
theorem eps_lt_inv_pow5 : eps < 1 / 10 ^ 5 := by
  unfold eps; norm_num

/-- Paper §6.1, proof of Lemma 6.3: for every `d₀ ≤ 10 D` (indeed any `0 ≤ d₀ ≤ 10 D`),
`ζ_A d₀ + 7 E_A ≤ (ϵ/100)(10D) + 7ϵ/1000 < ϵ`.  (The paper displays the middle step with `d₀` replaced
by its upper bound `10 D`; the Lean statement is for arbitrary `d₀ ≤ 10 D`, which is what is used.) -/
theorem zetaA_mul_d0_add_seven_EA_lt_eps {d₀ : ℝ} (_h0 : 0 ≤ d₀) (h1 : d₀ ≤ 10 * D) :
    zetaA * d₀ + 7 * EA ≤ (eps / 100) * (10 * D) + 7 * eps / 1000 ∧
      (eps / 100) * (10 * D) + 7 * eps / 1000 < eps ∧ zetaA * d₀ + 7 * EA < eps := by
  have hz : zetaA = eps / 100 := rfl
  have hE : EA = eps / 1000 := rfl
  have hD : D = 1 / 10 ^ 3 := rfl
  have he : (0 : ℝ) < eps := by unfold eps; norm_num
  have hDpos : (0 : ℝ) < D := by rw [hD]; norm_num
  have hz0 : 0 ≤ zetaA := by rw [hz]; positivity
  have hmid : (eps / 100) * (10 * D) + 7 * eps / 1000 < eps := by
    rw [hD]; nlinarith
  have hle : zetaA * d₀ + 7 * EA ≤ (eps / 100) * (10 * D) + 7 * eps / 1000 := by
    rw [hz, hE]; nlinarith [mul_le_mul_of_nonneg_left h1 hz0]
  exact ⟨hle, hmid, lt_of_le_of_lt hle hmid⟩

/-- Paper §6.1, proof of Lemma 6.1 and 6.3 (height branch): `10 D + E_A < 1`, so
`p_{h,C} ≤ s − 1 + 10D + E_A < s` at the band endpoints. -/
theorem ten_D_add_EA_lt_one : 10 * D + EA < 1 := by
  unfold D EA eps; norm_num

/-- Paper §6.1, proof of Lemma 6.3: the plateau of `p_{h,C}` satisfies `s + 2 − 10D > s + 2 E_A`,
i.e. `2 − 10 D > 2 E_A`. -/
theorem plateau_margin : 2 * EA < 2 - 10 * D := by
  unfold EA eps D; norm_num

/-- Paper §6.1, proof of Lemma 6.1: `s_C + 1 − 3E_A ≤ s + 1 + 10D` needs only `0 ≤ 3 E_A`; and the
constant branch `s_C + 1` of `p_C` strictly exceeds `s(w) + 7 E_A` once `s_C + 1 > s(w) + 7E_A`,
which holds when `s_C ≥ s(w) − 10D` because `7 E_A + 10 D < 1`. -/
theorem seven_EA_add_ten_D_lt_one : 7 * EA + 10 * D < 1 := by
  unfold EA eps D; norm_num

/-- Paper §5.2: "each of the two height tests has failure probability at most 0.21, and each radial
test, for two vertices together, has failure probability at most 0.081"; there are two height tests
and two radial tests (widths `D` and `g`), so the failure probabilities add to `< 3/4`, leaving
probability `≥ 1/4` for the interior event (the remaining allowance covers column-width and grid
errors).  The Lean statement is just the arithmetic `2·0.21 + 2·0.081 ≤ 3/4`. -/
theorem interior_probability_allowance : 2 * (0.21 : ℝ) + 2 * 0.081 ≤ 3 / 4 := by
  norm_num

/-- Paper §6.2 (last paragraph): "The full system-B fields vary by at most `50 g`, since their old-chart
Lipschitz constants are less than 5": `5 · 10 g = 50 g`. -/
theorem fifty_g : 5 * (10 * g) = 50 * g := by ring

/-! ### The free choices `a₁`, `a₂` -/

/-- Theorem 4.1, display (6): the width bound `a₀ = 10^-6 ζ δ` with `δ = E/8`. -/
noncomputable def thm41Width (ζ E : ℝ) : ℝ := 1 / 10 ^ 6 * ζ * (E / 8)

/-- The free choices of Section 5.1 with exactly the hypotheses the paper imposes.

* `a1_thm41`: "`a₁` within the width bound of Theorem 4.1 for `(ζ_A, E_A)`".
* `a1_le`: "`a₁ ≤ 10^-6 E_A`".
* `a2_thm41`: "`a₂` within the bound of Theorem 4.1 for `(ζ_B, E_B)`".
* `a2_le`: "`a₂ ≤ 10^-6 min{a₁, κ_A j}`" where `κ_A = a₁/10^6`.

The paper's remaining wording ("within the bounds of Lemmas 2.11 and 2.12 for D and g"; "if necessary
decrease `a₁, a₂` further to meet the explicit thin-band hypotheses of the geometric lemmas") is not a
field: the Lemma 2.11/2.12 bounds are consequences of `a1_le` (proved below) and decreasing further only
shrinks `a₁, a₂`, which no theorem below can obstruct (all are monotone in `a₁, a₂` from above). -/
structure Choice where
  a1 : ℝ
  a2 : ℝ
  a1_pos : 0 < a1
  a2_pos : 0 < a2
  a1_thm41 : a1 ≤ thm41Width zetaA EA
  a1_le : a1 ≤ 1 / 10 ^ 6 * EA
  a2_thm41 : a2 ≤ thm41Width zetaB EB
  a2_le : a2 ≤ 1 / 10 ^ 6 * min a1 ((a1 / 10 ^ 6) * j)

namespace Choice

variable (c : Choice)

/-- `κ_A = a₁/10^6`. -/
noncomputable def kappaA : ℝ := c.a1 / 10 ^ 6
/-- `κ_B = a₂/10^6`. -/
noncomputable def kappaB : ℝ := c.a2 / 10 ^ 6

/-- Paper §5.1: `κ_A, κ_B > 0`. -/
theorem kappa_pos : 0 < c.kappaA ∧ 0 < c.kappaB := by
  unfold kappaA kappaB
  exact ⟨by have := c.a1_pos; positivity, by have := c.a2_pos; positivity⟩

/-- Paper §5.2: "Interior in the broad band implies containment of the narrow band because
`a₂ ≤ 10^-6 a₁`." -/
theorem a2_le_a1 : c.a2 ≤ 1 / 10 ^ 6 * c.a1 := by
  have h := c.a2_le
  have h2 : min c.a1 ((c.a1 / 10 ^ 6) * j) ≤ c.a1 := min_le_left _ _
  nlinarith

/-- Paper §5.1: `a₂ ≤ 10^-6 κ_A j`. -/
theorem a2_le_kappaA_j : c.a2 ≤ 1 / 10 ^ 6 * (c.kappaA * j) := by
  have h := c.a2_le
  have h2 : min c.a1 ((c.a1 / 10 ^ 6) * j) ≤ (c.a1 / 10 ^ 6) * j := min_le_right _ _
  unfold kappaA
  nlinarith

/-- Paper §6.2, proof of Lemma 6.5: "`a₂ ≤ κ_A j/4`". -/
theorem a2_le_kappaA_j_div_four : c.a2 ≤ c.kappaA * j / 4 := by
  have h := c.a2_le_kappaA_j
  have hk : 0 < c.kappaA * j := by
    have := c.kappa_pos.1
    have : (0 : ℝ) < j := fixed_constants_pos.2.2.2.1
    positivity
  nlinarith

/-- Paper §5.1 (via the choice `a₁ ≤ 10^-6 E_A`): `a₁ < E_A`, hence `a₁ < ε` and `a₁ < j`. -/
theorem a1_lt_EA : c.a1 < EA := by
  have h := c.a1_le
  have : (0 : ℝ) < EA := fixed_constants_pos.2.2.2.2.2.1
  nlinarith

/-- Paper §5.1: the bound of Lemma 2.11 (`a ≤ D/1000`) holds for `a₁`. -/
theorem a1_le_D_div_1000 : c.a1 ≤ D / 1000 := by
  have h := c.a1_lt_EA
  have h6 : EA < D / 1000 := by
    unfold EA eps D; norm_num
  linarith

/-- Paper §5.1: the bound of Lemma 2.12 (`a ≤ g/1000`, used for the width-`g` cells) holds for `a₁`. -/
theorem a1_le_g_div_1000 : c.a1 ≤ g / 1000 := by
  have h := c.a1_lt_EA
  have h6 : EA < g / 1000 := by
    unfold EA eps g; norm_num
  linarith

/-- Paper §6.2, proof of Lemma 6.5: `κ_A (j − E_A) − a₂ ≥ κ_A j/2`, from `E_A ≤ j/4` and
`a₂ ≤ κ_A j/4`. -/
theorem kappaA_sub_ge : c.kappaA * j / 2 ≤ c.kappaA * (j - EA) - c.a2 := by
  have h1 := c.a2_le_kappaA_j_div_four
  have h2 := EA_le_j_div_four
  have hk := c.kappa_pos.1
  nlinarith

/-- Paper §6.1, proof of Lemma 6.1: "The parameter choice makes its product with `κ_A` strictly less
than 1": `κ_A · 3/(0.09 a₁) < 1` (the vertical Lipschitz constant of the height branch is
`3/(0.09 a₁)`, and `κ_A = a₁/10^6`). -/
theorem kappaA_mul_heightLip_lt_one : c.kappaA * (3 / (0.09 * c.a1)) < 1 := by
  have h := c.a1_pos
  unfold kappaA
  rw [show c.a1 / 10 ^ 6 * (3 / (0.09 * c.a1)) = (3 / 0.09) / 10 ^ 6 by field_simp]
  norm_num

/-- Paper §6.1: `κ_A · max{1, 3/(0.09 a₁)} < 1`, so `κ_A` times the vertical Lipschitz constant of the
replacement `s'` of (24) (the max of the constants of its constituents) is below 1. -/
theorem kappaA_mul_maxLip_lt_one : c.kappaA * max 1 (3 / (0.09 * c.a1)) < 1 := by
  have h := c.kappaA_mul_heightLip_lt_one
  have h1 : c.kappaA * 1 < 1 := by
    have := c.a1_lt_EA
    have hE : EA < 1 := by
      have : EA < eps := EA_lt_eps
      have : eps < 1 := by unfold eps; norm_num
      linarith
    unfold kappaA; linarith [c.a1_pos]
  rcases le_total 1 (3 / (0.09 * c.a1)) with hh | hh
  · rwa [max_eq_right hh]
  · rwa [max_eq_left hh]

/-- Paper §6.1 (end of proof of Lemma 6.1, and Corollary 6.4): `κ_A (1 + 10 D) ≤ 2 κ_A`; a main update
moves a label set by at most `κ_A (1+10D) < 2κ_A`. -/
theorem kappaA_one_add_ten_D_lt : c.kappaA * (1 + 10 * D) < 2 * c.kappaA := by
  have := c.kappa_pos.1
  have : 10 * D < 1 := ten_D_lt.2
  nlinarith

/-- Paper §5.1: `κ_B = a₂/10^6 < a₂`. -/
theorem kappaB_lt_a2 : c.kappaB < c.a2 := by
  have := c.a2_pos
  unfold kappaB; linarith

end Choice

/-- Sanity check that the hypotheses of the paper's choice in Section 5.1 are jointly satisfiable (so the
structure `Choice` is not vacuous): take `a₁` equal to the Theorem 4.1 width bound for `(ζ_A, E_A)` and
`a₂` the minimum of the Theorem 4.1 bound for `(ζ_B, E_B)` and `10^-6 min{a₁, κ_A j}`.  This is the
paper's own recipe ("All inequalities in this choice are upper bounds on a newly chosen positive
number"); it does not check the *further* thin-band hypotheses of the geometric lemmas, which the
paper leaves unspecified ("decrease `a₁, a₂` further"). -/
theorem Choice.nonempty : Nonempty Choice := by
  have hA : 0 < thm41Width zetaA EA := by unfold thm41Width zetaA EA eps; norm_num
  have hB : 0 < thm41Width zetaB EB := by unfold thm41Width zetaB EB R; norm_num
  have hj : (0 : ℝ) < j := fixed_constants_pos.2.2.2.1
  set a1 := thm41Width zetaA EA with ha1
  have hm : 0 < 1 / 10 ^ 6 * min a1 ((a1 / 10 ^ 6) * j) := by
    have : 0 < min a1 ((a1 / 10 ^ 6) * j) := lt_min hA (by positivity)
    positivity
  refine ⟨⟨a1, min (thm41Width zetaB EB) (1 / 10 ^ 6 * min a1 ((a1 / 10 ^ 6) * j)), hA,
    lt_min hB hm, le_rfl, ?_, min_le_left _ _, min_le_right _ _⟩⟩
  rw [ha1]
  unfold thm41Width zetaA EA eps
  norm_num

end Constants
end PlanarL1

/-! ### Axiom audit

Real output of `#print axioms` (Lean v4.34.1, run with `lake env lean` on a file importing `PlanarL1.Update`),
for every theorem of this file.  Only the three standard axioms occur; no `sorryAx`.

```
-- PlanarL1.Constants.fixed_constants_pos : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.hierarchy : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.EA_lt_eps : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.EA_le_j_div_four : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.EB_lt_R : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.lam_facts : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.ten_D_lt : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.one_hundredth_D : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.eps_lt_inv_pow5 : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.zetaA_mul_d0_add_seven_EA_lt_eps : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.ten_D_add_EA_lt_one : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.plateau_margin : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.seven_EA_add_ten_D_lt_one : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.interior_probability_allowance : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.fifty_g : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.kappa_pos : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.a2_le_a1 : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.a2_le_kappaA_j : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.a2_le_kappaA_j_div_four : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.a1_lt_EA : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.a1_le_D_div_1000 : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.a1_le_g_div_1000 : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.kappaA_sub_ge : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.kappaA_mul_heightLip_lt_one : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.kappaA_mul_maxLip_lt_one : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.kappaA_one_add_ten_D_lt : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.kappaB_lt_a2 : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Constants.Choice.nonempty : [propext, Classical.choice, Quot.sound]
```
-/
