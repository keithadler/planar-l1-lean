/-
Copyright (c) 2026 Keith Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler (with Claude)
-/

import Mathlib

/-!
# Charts: threshold sets and the cut-distance identity (Section 3.1, Lemma 3.1)

Formalisation of Section 3.1 ("Charts on a fixed label space") and Lemma 3.1 ("Vertical control and
rebasing") of OpenAI's preprint *Planar Graph Metrics Embed into L1 with Constant Distortion*
(23 September 2026).

A point `v` of a column carries a height `h v` and a field value `P v`. A label is a pair
`ω = (Z, σ)` of a real `Z` and a sign `σ`; the point's set is `{ω | Z ω < h v + σ ω * κ * P v}`
(paper, equation (4)).

## Modelling choices (apply to every statement below)

* **Label space.** The paper uses `Ω = ℝ × {-1,1}^ℕ` with `L ⊗ ν`. Here `Ω` is an *arbitrary*
  measurable space with a measure `μ`, together with measurable `Z : Ω → ℝ` and `σ : Ω → Bool`
  whose joint law is `volume.prod fairSign` (this is exactly the paper's requirement that
  "the joint pushforward measure is Lebesgue measure times a fair sign"). The concrete space
  `ℝ × Bool` (identity coordinates) and the paper's `ℝ × (ℕ → Bool)` (first sign coordinate)
  are both instances; see `chartLabels_concrete`, `chartLabels_paper` and `rebase_chartLabels_paper`. Only one sign is
  needed for a set `A_v`, since `A_v` depends on `ω` only through `(Z ω, σ ω)`.
* **Signs** are `Bool`, read as real numbers by `sgn true = 1`, `sgn false = -1`.
* **Switches** are not modelled here (they belong to the column graph, Task B). The hypothesis
  "`P` respects switches" of the paper's Lemma 3.1 plays no role in the chart-level statements
  proved here (nesting is a statement about one column interval).
* **Column interval** is modelled as a set `S` of points on which `P` is `L`-Lipschitz in height,
  `|P v - P w| ≤ L * |h v - h w|` for `v w ∈ S`.
* Measures take values in `ℝ≥0∞`; a real number `x` is written `ENNReal.ofReal x`.
-/

open MeasureTheory Set
open scoped ENNReal symmDiff

namespace PlanarL1

/-- The fair sign measure on `Bool`: mass `1/2` on `true` (sign `+1`) and `1/2` on `false`
(sign `-1`). -/
noncomputable def fairSign : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fairSign := by
  refine ⟨?_⟩
  simp [fairSign]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by simp) (by simp)

/-- Real value of a sign: `true ↦ 1`, `false ↦ -1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Auxiliary lemma `sgn_mul_self` for Section 3.1 (Lemma 3.1); not a statement of the paper. -/
lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

/-- Auxiliary lemma `abs_sgn` for Section 3.1 (Lemma 3.1); not a statement of the paper. -/
lemma abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

/-- Auxiliary lemma `lintegral_fairSign` for Section 3.1 (Lemma 3.1); not a statement of the paper. -/
lemma lintegral_fairSign (f : Bool → ℝ≥0∞) :
    ∫⁻ b, f b ∂fairSign = 2⁻¹ * (f true + f false) := by
  simp [fairSign, lintegral_smul_measure, lintegral_add_measure, mul_add]

/-- Label data of a chart: measurable `Z : Ω → ℝ` and `σ : Ω → Bool` whose joint pushforward
is Lebesgue measure times a fair sign. (Paper, Section 3.1.) -/
structure ChartLabels {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℝ) (σ : Ω → Bool) : Prop where
  measurable_Z : Measurable Z
  measurable_σ : Measurable σ
  map_eq : μ.map (fun ω => (Z ω, σ ω)) = volume.prod fairSign

/-- The threshold set `A_v = {ω | Z ω < h v + σ ω * κ * P v}` of equation (4), written for a
point with height `H` and field value `p`. -/
def thrSet {Ω : Type*} (Z : Ω → ℝ) (σ : Ω → Bool) (κ H p : ℝ) : Set Ω :=
  {ω | Z ω < H + sgn (σ ω) * κ * p}

/-- The set `A_v` of equation (4) for a point `v` with height `h v` and field value `P v`. -/
def chartSet {Ω X : Type*} (Z : Ω → ℝ) (σ : Ω → Bool) (κ : ℝ) (h P : X → ℝ) (v : X) : Set Ω :=
  thrSet Z σ κ (h v) (P v)

/-- Auxiliary lemma `volume_Iio_symmDiff_Iio` for Section 3.1 (Lemma 3.1); not a statement of the paper. -/
lemma volume_Iio_symmDiff_Iio (x y : ℝ) :
    volume (Iio x ∆ Iio y) = ENNReal.ofReal |x - y| := by
  rcases le_total x y with hxy | hxy
  · have : Iio x ∆ Iio y = Ico x y := by
      ext t; simp only [mem_symmDiff, mem_Iio, mem_Ico]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> [exact absurd (lt_of_lt_of_le h1 hxy) h2; exact ⟨not_lt.1 h2, h1⟩]
      · rintro ⟨h1, h2⟩; exact Or.inr ⟨h2, not_lt.2 h1⟩
    rw [this, Real.volume_Ico, abs_sub_comm, abs_of_nonneg (by linarith)]
  · have : Iio x ∆ Iio y = Ico y x := by
      ext t; simp only [mem_symmDiff, mem_Iio, mem_Ico]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> [exact ⟨not_lt.1 h2, h1⟩; exact absurd (lt_of_lt_of_le h1 hxy) h2]
      · rintro ⟨h1, h2⟩; exact Or.inl ⟨h2, not_lt.2 h1⟩
    rw [this, Real.volume_Ico, abs_of_nonneg (by linarith)]

/-- Auxiliary lemma `half_abs_add_sub` for Section 3.1 (Lemma 3.1); not a statement of the paper. -/
lemma half_abs_add_sub (a b : ℝ) : (|a + b| + |a - b|) / 2 = max |a| |b| := by
  rcases abs_cases a with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
  rcases abs_cases (a + b) with ⟨hab, _⟩ | ⟨hab, _⟩ <;>
  rcases abs_cases (a - b) with ⟨hab', _⟩ | ⟨hab', _⟩ <;>
  simp only [ha, hb, hab, hab'] <;>
  (rw [max_def]; split_ifs <;> linarith)

/-- Auxiliary lemma `measurableSet_thr` for Section 3.1 (Lemma 3.1); not a statement of the paper. -/
lemma measurableSet_thr (κ H p : ℝ) : MeasurableSet {x : ℝ × Bool | x.1 < H + sgn x.2 * κ * p} :=
  measurableSet_lt measurable_fst (by fun_prop)

/-- **Lemma 3.1, identity (5).**

Paper: "For two points whose sets are expressed in common chart variables,
`µ(A_v △ A_w) = max{|h(v) − h(w)|, κ|P(v) − P(w)|}`."

Lean: the same identity, with `μ` the measure on an arbitrary label space carrying chart labels
`(Z, σ)` (`ChartLabels μ Z σ`), and the real number on the right written through
`ENNReal.ofReal`. It is stated for `κ ≥ 0` (the paper has `κ > 0`, so this is slightly more
general). -/
theorem measure_symmDiff_thrSet {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z : Ω → ℝ} {σ : Ω → Bool} (hl : ChartLabels μ Z σ) {κ : ℝ} (hκ : 0 ≤ κ)
    (H₁ p₁ H₂ p₂ : ℝ) :
    μ (thrSet Z σ κ H₁ p₁ ∆ thrSet Z σ κ H₂ p₂) =
      ENNReal.ofReal (max |H₁ - H₂| (κ * |p₁ - p₂|)) := by
  have hm : Measurable (fun ω => (Z ω, σ ω)) := hl.measurable_Z.prodMk hl.measurable_σ
  have hS : MeasurableSet ({x : ℝ × Bool | x.1 < H₁ + sgn x.2 * κ * p₁} ∆
      {x : ℝ × Bool | x.1 < H₂ + sgn x.2 * κ * p₂}) :=
    (measurableSet_thr _ _ _).symmDiff (measurableSet_thr _ _ _)
  have h1 : thrSet Z σ κ H₁ p₁ ∆ thrSet Z σ κ H₂ p₂ =
      (fun ω => (Z ω, σ ω)) ⁻¹' ({x : ℝ × Bool | x.1 < H₁ + sgn x.2 * κ * p₁} ∆
      {x : ℝ × Bool | x.1 < H₂ + sgn x.2 * κ * p₂}) := by
    ext ω; simp [thrSet, mem_symmDiff]
  rw [h1, ← Measure.map_apply hm hS, hl.map_eq, Measure.prod_apply_symm hS, lintegral_fairSign]
  have h2 : ∀ b : Bool, volume ((fun x : ℝ => (x, b)) ⁻¹' ({x : ℝ × Bool | x.1 < H₁ + sgn x.2 * κ * p₁} ∆
      {x : ℝ × Bool | x.1 < H₂ + sgn x.2 * κ * p₂})) =
      ENNReal.ofReal |(H₁ - H₂) + sgn b * (κ * (p₁ - p₂))| := by
    intro b
    have : (fun x : ℝ => (x, b)) ⁻¹' ({x : ℝ × Bool | x.1 < H₁ + sgn x.2 * κ * p₁} ∆
      {x : ℝ × Bool | x.1 < H₂ + sgn x.2 * κ * p₂}) =
        Iio (H₁ + sgn b * κ * p₁) ∆ Iio (H₂ + sgn b * κ * p₂) := by
      ext x; simp [mem_symmDiff]
    rw [this, volume_Iio_symmDiff_Iio]
    congr 2; ring
  rw [h2, h2]
  have e1 : (H₁ - H₂) + sgn true * (κ * (p₁ - p₂)) = (H₁ - H₂) + κ * (p₁ - p₂) := by simp [sgn]
  have e2 : (H₁ - H₂) + sgn false * (κ * (p₁ - p₂)) = (H₁ - H₂) - κ * (p₁ - p₂) := by
    simp [sgn]; ring
  rw [e1, e2, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  have e3 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [e3, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  have := half_abs_add_sub (H₁ - H₂) (κ * (p₁ - p₂))
  rw [abs_mul, abs_of_nonneg hκ] at this
  linarith

/-- **Lemma 3.1, identity (5), in the paper's point notation.**

Paper: `µ(A_v △ A_w) = max{|h(v) − h(w)|, κ|P(v) − P(w)|}` (5).

Lean: `A_v` is `chartSet Z σ κ h P v`; same differences as `measure_symmDiff_thrSet`. -/
theorem measure_symmDiff_chartSet {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z : Ω → ℝ} {σ : Ω → Bool} (hl : ChartLabels μ Z σ) {κ : ℝ} (hκ : 0 ≤ κ)
    (h P : X → ℝ) (v w : X) :
    μ (chartSet Z σ κ h P v ∆ chartSet Z σ κ h P w) =
      ENNReal.ofReal (max |h v - h w| (κ * |P v - P w|)) :=
  measure_symmDiff_thrSet hl hκ _ _ _ _

/-! ### Nesting and vertical length -/

/-- `P` is `L`-Lipschitz in height on the set `S` of points of a column interval. -/
def VertLip {X : Type*} (h P : X → ℝ) (S : Set X) (L : ℝ) : Prop :=
  ∀ v ∈ S, ∀ w ∈ S, |P v - P w| ≤ L * |h v - h w|

/-- **Lemma 3.1, nesting (second assertion).**

Paper: "If `κ Lip_vert(P) < 1` and `P` respects switches, the sets are nested increasingly on
each column interval in the chart."

Lean: for points `v, w` of a set `S` on which `P` is `L`-Lipschitz in height (`VertLip h P S L`,
`0 ≤ L`), with `0 ≤ κ` and `κ * L ≤ 1`, `h v ≤ h w` implies `A_v ⊆ A_w` (pointwise, for every
label, no measure needed). Differences: "column interval" is modelled by the set `S` and
`L` is any vertical Lipschitz bound (so `L = Lip_vert(P)` is an instance); the hypothesis
"respects switches" is not used and not modelled here (switches belong to the column graph;
nesting is a statement about one column interval). Slightly more general: `κ * L ≤ 1` suffices,
which is what the proof gives, though `< 1` is what the paper assumes. -/
theorem chartSet_subset_of_le {Ω X : Type*} (Z : Ω → ℝ) (σ : Ω → Bool) {κ : ℝ} (hκ : 0 ≤ κ)
    {h P : X → ℝ} {S : Set X} {L : ℝ} (hL : κ * L ≤ 1) (hS : VertLip h P S L)
    {v w : X} (hv : v ∈ S) (hw : w ∈ S) (hvw : h v ≤ h w) :
    chartSet Z σ κ h P v ⊆ chartSet Z σ κ h P w := by
  intro ω hω
  simp only [chartSet, thrSet, mem_ofPred_eq] at hω ⊢
  have h1 := hS v hv w hw
  rw [abs_of_nonpos (by linarith : h v - h w ≤ 0)] at h1
  have h3 : κ * |P v - P w| ≤ h w - h v := by
    calc κ * |P v - P w| ≤ κ * (L * -(h v - h w)) := mul_le_mul_of_nonneg_left h1 hκ
      _ = (κ * L) * (h w - h v) := by ring
      _ ≤ 1 * (h w - h v) := mul_le_mul_of_nonneg_right hL (by linarith)
      _ = h w - h v := one_mul _
  have h4 : sgn (σ ω) * κ * (P v - P w) ≤ κ * |P v - P w| := by
    have : |sgn (σ ω) * κ * (P v - P w)| = κ * |P v - P w| := by
      rw [abs_mul, abs_mul, abs_sgn, abs_of_nonneg hκ, one_mul]
    linarith [le_abs_self (sgn (σ ω) * κ * (P v - P w))]
  nlinarith

/-- **Lemma 3.1, vertical length (third assertion).**

Paper: "If `κ Lip_vert(P) < 1` ... Their symmetric-difference measure there equals the vertical
length."

Lean: for `v, w ∈ S` with `VertLip h P S L`, `0 ≤ κ` and `κ * L ≤ 1`,
`μ(A_v △ A_w) = |h v - h w|` (as `ENNReal.ofReal`). Same differences as
`chartSet_subset_of_le` (including `κ L ≤ 1` rather than `< 1`). -/
theorem measure_symmDiff_chartSet_eq_vertical {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z : Ω → ℝ} {σ : Ω → Bool} (hl : ChartLabels μ Z σ) {κ : ℝ} (hκ : 0 ≤ κ)
    {h P : X → ℝ} {S : Set X} {L : ℝ} (hL : κ * L ≤ 1) (hS : VertLip h P S L)
    {v w : X} (hv : v ∈ S) (hw : w ∈ S) :
    μ (chartSet Z σ κ h P v ∆ chartSet Z σ κ h P w) = ENNReal.ofReal |h v - h w| := by
  rw [measure_symmDiff_chartSet hl hκ]
  congr 1
  apply max_eq_left
  have h1 := hS v hv w hw
  calc κ * |P v - P w| ≤ κ * (L * |h v - h w|) := mul_le_mul_of_nonneg_left h1 hκ
    _ = (κ * L) * |h v - h w| := by ring
    _ ≤ 1 * |h v - h w| := mul_le_mul_of_nonneg_right hL (abs_nonneg _)
    _ = |h v - h w| := one_mul _

/-- **Lemma 3.1, nesting plus vertical length, in the form used later**: for `h v ≤ h w` on a
column interval, `A_v ⊆ A_w` and `μ(A_w \ A_v) = h w - h v`. Hypotheses and differences as in
`chartSet_subset_of_le` and `measure_symmDiff_chartSet_eq_vertical`. -/
theorem measure_diff_chartSet_eq_vertical {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z : Ω → ℝ} {σ : Ω → Bool} (hl : ChartLabels μ Z σ) {κ : ℝ} (hκ : 0 ≤ κ)
    {h P : X → ℝ} {S : Set X} {L : ℝ} (hL : κ * L ≤ 1) (hS : VertLip h P S L)
    {v w : X} (hv : v ∈ S) (hw : w ∈ S) (hvw : h v ≤ h w) :
    μ (chartSet Z σ κ h P w \ chartSet Z σ κ h P v) = ENNReal.ofReal (h w - h v) := by
  have hsub := chartSet_subset_of_le Z σ hκ hL hS hv hw hvw
  have := measure_symmDiff_chartSet_eq_vertical hl hκ hL hS hv hw
  rw [symmDiff_of_le hsub, abs_sub_comm, abs_of_nonneg (by linarith)] at this
  exact this

/-! ### Rebasing -/

/-- `ϕ_σ(H) = H + σ κ ψ(H)` (paper, proof of Lemma 3.1), for the sign `b`. -/
def phi (κ : ℝ) (ψ : ℝ → ℝ) (b : Bool) (H : ℝ) : ℝ := H + sgn b * κ * ψ H

section Rebase

variable {κ : ℝ} {Lψ : NNReal} {ψ : ℝ → ℝ}

/-- Auxiliary lemma `phi_sub_ge` for Section 3.1 (Lemma 3.1); not a statement of the paper. -/
lemma phi_sub_ge (hκ : 0 ≤ κ) (hψ : LipschitzWith Lψ ψ) (b : Bool) {x y : ℝ} (hxy : x ≤ y) :
    (1 - κ * Lψ) * (y - x) ≤ phi κ ψ b y - phi κ ψ b x := by
  have h1 : |ψ y - ψ x| ≤ Lψ * (y - x) := by
    have := hψ.dist_le_mul y x
    rwa [Real.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ y - x)] at this
  have h2 : |sgn b * κ * (ψ y - ψ x)| ≤ κ * (Lψ * (y - x)) := by
    rw [abs_mul, abs_mul, abs_sgn, abs_of_nonneg hκ, one_mul]
    exact mul_le_mul_of_nonneg_left h1 hκ
  have h3 := neg_abs_le (sgn b * κ * (ψ y - ψ x))
  simp only [phi]
  nlinarith

/-- Auxiliary lemma `phi_strictMono` for Section 3.1 (Lemma 3.1); not a statement of the paper. -/
lemma phi_strictMono (hκ : 0 ≤ κ) (hc : κ * Lψ < 1) (hψ : LipschitzWith Lψ ψ) (b : Bool) :
    StrictMono (phi κ ψ b) := by
  intro x y hxy
  have := phi_sub_ge hκ hψ b hxy.le
  have h2 : 0 < (1 - κ * Lψ) * (y - x) := mul_pos (by linarith) (by linarith)
  linarith

/-- Auxiliary lemma `phi_continuous` for Section 3.1 (Lemma 3.1); not a statement of the paper. -/
lemma phi_continuous (hψ : LipschitzWith Lψ ψ) (b : Bool) : Continuous (phi κ ψ b) := by
  unfold phi
  have := hψ.continuous
  fun_prop

/-- Auxiliary lemma `phi_surjective` for Section 3.1 (Lemma 3.1); not a statement of the paper. -/
lemma phi_surjective (hκ : 0 ≤ κ) (hc : κ * Lψ < 1) (hψ : LipschitzWith Lψ ψ) (b : Bool) :
    Function.Surjective (phi κ ψ b) := by
  apply (phi_continuous hψ b).surjective
  · refine Filter.tendsto_atTop_mono' _ ?_ (Filter.tendsto_atTop_add_const_left _ (phi κ ψ b 0)
      (Filter.Tendsto.const_mul_atTop (by linarith : 0 < 1 - κ * Lψ) Filter.tendsto_id))
    filter_upwards [Filter.eventually_ge_atTop 0] with x hx
    have := phi_sub_ge hκ hψ b hx
    simp only [id]; linarith
  · refine Filter.tendsto_atBot_mono' _ ?_ (Filter.tendsto_atBot_add_const_left _ (phi κ ψ b 0)
      (Filter.Tendsto.const_mul_atBot (by linarith : 0 < 1 - κ * Lψ) Filter.tendsto_id))
    filter_upwards [Filter.eventually_le_atBot 0] with x hx
    have := phi_sub_ge hκ hψ b hx
    simp only [id]; linarith

/-- **Lemma 3.1, rebasing: `ϕ_σ` are increasing bijections of `ℝ`.**

Paper: "For rebasing put `ϕ_σ(H) = H + σκψ(H)`. These are increasing bijections of `ℝ`."
(under `ψ : ℝ → ℝ` Lipschitz with `κ Lip(ψ) < 1`).

Lean: `phiEquiv κ ψ b` is the order isomorphism `ℝ ≃o ℝ` with underlying function
`phi κ ψ b`, for `0 ≤ κ`, `ψ` `Lψ`-Lipschitz (`Lψ : ℝ≥0`, so `Lip(ψ) = Lψ` is an instance),
`κ * Lψ < 1`. -/
noncomputable def phiEquiv (hκ : 0 ≤ κ) (hc : κ * Lψ < 1) (hψ : LipschitzWith Lψ ψ) (b : Bool) :
    ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ (phi_strictMono hκ hc hψ b) (phi_surjective hκ hc hψ b)

/-- Auxiliary lemma `phiEquiv_apply` for Section 3.1 (Lemma 3.1); not a statement of the paper. -/
lemma phiEquiv_apply (hκ : 0 ≤ κ) (hc : κ * Lψ < 1) (hψ : LipschitzWith Lψ ψ) (b : Bool) (H : ℝ) :
    phiEquiv hκ hc hψ b H = phi κ ψ b H := rfl

/-- The pushforward of Lebesgue measure by `ϕ_b⁻¹`, for the sign `b`, evaluated on a measurable
set `B`: this is `vol(ϕ_b B)`-type quantity; averaging over `b` gives Lebesgue measure. -/
lemma average_map_symm (hκ : 0 ≤ κ) (hc : κ * Lψ < 1) (hψ : LipschitzWith Lψ ψ) :
    (2⁻¹ : ℝ≥0∞) • ((volume : Measure ℝ).map (phiEquiv hκ hc hψ true).symm +
      (volume : Measure ℝ).map (phiEquiv hκ hc hψ false).symm) = volume := by
  have hmeas : ∀ b, Measurable (phiEquiv hκ hc hψ b).symm := fun b =>
    (phiEquiv hκ hc hψ b).symm.continuous.measurable
  have hIoc : ∀ (b : Bool) (a c : ℝ), (phiEquiv hκ hc hψ b).symm ⁻¹' Ioc a c =
      Ioc (phi κ ψ b a) (phi κ ψ b c) := by
    intro b a c; ext t
    simp only [mem_preimage, mem_Ioc, OrderIso.lt_symm_apply, OrderIso.symm_apply_le,
      phiEquiv_apply]
  refine (Measure.ext_of_Ioc volume _ fun a c hac => ?_).symm
  simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.map_apply (hmeas _) measurableSet_Ioc, hIoc, Real.volume_Ioc]
  have e3 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have hnn : ∀ b : Bool, 0 ≤ phi κ ψ b c - phi κ ψ b a := fun b => by
    have := phi_strictMono hκ hc hψ b hac; linarith
  rw [← ENNReal.ofReal_add (hnn _) (hnn _), e3, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  simp only [phi, sgn]
  simp
  ring

/-- The rebased coordinate `Z'(ω) = ϕ_{σ(ω)}⁻¹(Z(ω))` (paper, proof of Lemma 3.1). -/
noncomputable def rebaseZ (hκ : 0 ≤ κ) (hc : κ * Lψ < 1) (hψ : LipschitzWith Lψ ψ)
    {Ω : Type*} (Z : Ω → ℝ) (σ : Ω → Bool) : Ω → ℝ :=
  fun ω => (phiEquiv hκ hc hψ (σ ω)).symm (Z ω)

/-- **Lemma 3.1, rebasing: the set identity `{Z < ϕ_σ(h)} = {Z' < h}`.**

Paper: "for every label, `{Z < ϕ_σ(h)} = {Z' < h}`", where `Z' = ϕ_σ⁻¹ ∘ Z`.

Lean: exactly this, pointwise for every label `ω` and every real `H` (which plays the role of
`h`), under `0 ≤ κ`, `ψ` `Lψ`-Lipschitz, `κ * Lψ < 1`. (No measure, no `σ'` involved: the
identity uses the *old* sign `σ`.) -/
theorem rebase_lt_iff (hκ : 0 ≤ κ) (hc : κ * Lψ < 1) (hψ : LipschitzWith Lψ ψ)
    {Ω : Type*} (Z : Ω → ℝ) (σ : Ω → Bool) (ω : Ω) (H : ℝ) :
    Z ω < phi κ ψ (σ ω) H ↔ rebaseZ hκ hc hψ Z σ ω < H := by
  unfold rebaseZ
  rw [OrderIso.symm_apply_lt, phiEquiv_apply]

/-- **Lemma 3.1, rebasing: a height-only branch is the same set with field zero.**

Paper: "A branch `P(v) = ψ(h(v))` ... can be represented by a fresh constant chart without
changing any sets." and "This describes exactly the same sets by a chart with field zero."

Lean: for every point `v`, the set `A_v` of the chart `(Z, σ)` with field `ψ ∘ h` equals the set
of the chart `(Z', τ)` (any sign `τ`) with field `0`, namely `{Z' < h v}`. Differences: the
fresh sign `τ` is arbitrary here because the field-zero set does not depend on it; the
statement that `(Z', τ)` is a legitimate chart (correct joint law) is `rebase_chartLabels`. -/
theorem chartSet_rebase (hκ : 0 ≤ κ) (hc : κ * Lψ < 1) (hψ : LipschitzWith Lψ ψ)
    {Ω X : Type*} (Z : Ω → ℝ) (σ τ : Ω → Bool) (h : X → ℝ) (v : X) :
    chartSet Z σ κ h (fun x => ψ (h x)) v =
      chartSet (rebaseZ hκ hc hψ Z σ) τ κ h (fun _ => 0) v := by
  ext ω
  simp only [chartSet, thrSet, mem_ofPred_eq, mul_zero, add_zero]
  exact rebase_lt_iff hκ hc hψ Z σ ω (h v)

/-- Abstract form of the law computation in the rebasing proof: if a family `e b : ℝ ≃o ℝ` of
order isomorphisms has the property that `(ρ₊ + ρ₋)/2` is Lebesgue measure (`ρ_b` the pushforward
of Lebesgue measure by `(e b).symm`), then `(z, s, t) ↦ ((e s).symm z, t)` pushes
`Lebesgue ⊗ fair ⊗ fair` to `Lebesgue ⊗ fair`. -/
lemma map_rebase_prod {e : Bool → ℝ ≃o ℝ}
    (havg : (2⁻¹ : ℝ≥0∞) • ((volume : Measure ℝ).map (e true).symm +
      (volume : Measure ℝ).map (e false).symm) = volume) :
    (volume.prod (fairSign.prod fairSign)).map
      (fun q : ℝ × Bool × Bool => ((e q.2.1).symm q.1, q.2.2)) = volume.prod fairSign := by
  have hF : Measurable (fun p : ℝ × Bool => (e p.2).symm p.1) :=
    measurable_from_prod_countable_left fun b => (e b).symm.continuous.measurable
  have hq : Measurable (fun q : ℝ × Bool × Bool => (q.1, q.2.1)) := by fun_prop
  have hGm : Measurable (fun q : ℝ × Bool × Bool => ((e q.2.1).symm q.1, q.2.2)) := by
    refine Measurable.prodMk (hF.comp hq) ?_
    fun_prop
  ext S hS
  rw [Measure.map_apply hGm hS, Measure.prod_apply_symm (hGm hS), Measure.prod_apply_symm hS,
    lintegral_prod _ (Measurable.of_discrete.aemeasurable), lintegral_fairSign,
    lintegral_fairSign, lintegral_fairSign]
  have hSt : ∀ t : Bool, MeasurableSet ((fun z : ℝ => (z, t)) ⁻¹' S) := fun t =>
    measurable_prodMk_right hS
  have hρ : ∀ (s t : Bool), volume ((fun z : ℝ => (z, (s, t))) ⁻¹'
      ((fun q : ℝ × Bool × Bool => ((e q.2.1).symm q.1, q.2.2)) ⁻¹' S)) =
      (volume : Measure ℝ).map (e s).symm ((fun z : ℝ => (z, t)) ⁻¹' S) := by
    intro s t
    rw [Measure.map_apply (e s).symm.continuous.measurable (hSt t)]
    rfl
  have hv : ∀ t : Bool, volume ((fun z : ℝ => (z, t)) ⁻¹' S) = 2⁻¹ *
      ((volume : Measure ℝ).map (e true).symm ((fun z : ℝ => (z, t)) ⁻¹' S) +
       (volume : Measure ℝ).map (e false).symm ((fun z : ℝ => (z, t)) ⁻¹' S)) := by
    intro t
    conv_lhs => rw [← havg]
    simp [Measure.smul_apply, Measure.add_apply, mul_add]
  rw [lintegral_fairSign]
  simp only [hρ, hv]
  ring

/-- **Lemma 3.1, rebasing: the new coordinate has the right law.**

Paper: "`Z'(ω) = ϕ_{σ(ω)}⁻¹(Z(ω))`. Its pushforward measure is Lebesgue measure, since for
`a < b`, `µ{a < Z' < b} = (ϕ₊(b) − ϕ₊(a) + ϕ₋(b) − ϕ₋(a))/2 = b − a. Choose a sign coordinate
unused anywhere earlier in this execution. It is independent of `Z'`. Thus `(Z', σ')` has the
required joint pushforward."

Lean: the label space carries `Z`, the old sign `σ` and the *fresh sign* `τ` (the paper's `σ'`),
with `(Z, σ, τ)` having law `Lebesgue ⊗ fair ⊗ fair` (this is the formal content of "a sign
coordinate unused anywhere earlier"; it holds on the paper's `ℝ × {-1,1}^ℕ` taking `τ` = a
later sign coordinate). Conclusion: `(Z', τ)` has law `Lebesgue ⊗ fair`, i.e. `ChartLabels μ Z' τ`.

IMPORTANT difference from the task statement in `TASKS.md`: it is NOT true that `Z'` has a
Lebesgue pushforward *jointly with the old sign `σ`* (the conditional law of `Z'` given `σ = b`
is `ϕ_b⁻¹ₓ Lebesgue`, which depends on `b` unless `ψ` is constant). Only the marginal of `Z'`
is Lebesgue, and the joint law with a *fresh independent* sign is the product; this is what
the paper proves and what is formalised. -/
theorem rebase_chartLabels (hκ : 0 ≤ κ) (hc : κ * Lψ < 1) (hψ : LipschitzWith Lψ ψ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → ℝ} {σ τ : Ω → Bool}
    (hZ : Measurable Z) (hσ : Measurable σ) (hτ : Measurable τ)
    (hl : μ.map (fun ω => (Z ω, σ ω, τ ω)) = volume.prod (fairSign.prod fairSign)) :
    ChartLabels μ (rebaseZ hκ hc hψ Z σ) τ := by
  have hF : Measurable (fun p : ℝ × Bool => (phiEquiv hκ hc hψ p.2).symm p.1) :=
    measurable_from_prod_countable_left fun b =>
      (phiEquiv hκ hc hψ b).symm.continuous.measurable
  have hm : Measurable (fun ω => (Z ω, σ ω, τ ω)) := hZ.prodMk (hσ.prodMk hτ)
  have hmeasZ' : Measurable (rebaseZ hκ hc hψ Z σ) := by
    have h2 : rebaseZ hκ hc hψ Z σ =
        (fun p : ℝ × Bool => (phiEquiv hκ hc hψ p.2).symm p.1) ∘ (fun ω => (Z ω, σ ω)) := by
      funext ω; rfl
    have hZσ : Measurable (fun ω => (Z ω, σ ω)) := hZ.prodMk hσ
    rw [h2]
    exact Measurable.comp (g := fun p : ℝ × Bool => (phiEquiv hκ hc hψ p.2).symm p.1)
      (f := fun ω => (Z ω, σ ω)) hF hZσ
  refine ⟨hmeasZ', hτ, ?_⟩
  have hGm : Measurable (fun q : ℝ × Bool × Bool =>
      ((phiEquiv hκ hc hψ q.2.1).symm q.1, q.2.2)) := by
    have hq : Measurable (fun q : ℝ × Bool × Bool => (q.1, q.2.1)) := by fun_prop
    have h1 : Measurable (fun q : ℝ × Bool × Bool => (phiEquiv hκ hc hψ q.2.1).symm q.1) :=
      Measurable.comp (g := fun p : ℝ × Bool => (phiEquiv hκ hc hψ p.2).symm p.1)
        (f := fun q : ℝ × Bool × Bool => (q.1, q.2.1)) hF hq
    exact Measurable.prodMk h1 (by fun_prop)
  have hcomp : (fun ω => (rebaseZ hκ hc hψ Z σ ω, τ ω)) =
      (fun q : ℝ × Bool × Bool => ((phiEquiv hκ hc hψ q.2.1).symm q.1, q.2.2)) ∘
        (fun ω => (Z ω, σ ω, τ ω)) := rfl
  rw [hcomp, ← Measure.map_map hGm hm, hl]
  exact map_rebase_prod (average_map_symm hκ hc hψ)

end Rebase

/-! ### The paper's label space and the concrete instances -/

section Instances

/-- The paper's sign measure `ν` on `{-1,1}^ℕ` (here `ℕ → Bool`): the product of fair signs. -/
noncomputable def paperSigns : Measure (ℕ → Bool) := Measure.infinitePi fun _ : ℕ => fairSign

instance : IsProbabilityMeasure paperSigns := by unfold paperSigns; infer_instance

/-- Joint law of two distinct sign coordinates of `ν` is two independent fair signs. -/
lemma paperSigns_map_two {i j : ℕ} (hij : i ≠ j) :
    paperSigns.map (fun x => (x i, x j)) = fairSign.prod fairSign := by
  have hm : Measurable (fun x : ℕ → Bool => (x i, x j)) := by fun_prop
  refine Measure.ext_of_singleton fun ab => ?_
  obtain ⟨a, b⟩ := ab
  have hs : MeasurableSet ({(a, b)} : Set (Bool × Bool)) := measurableSet_singleton _
  rw [Measure.map_apply hm hs]
  have hpre : (fun x : ℕ → Bool => (x i, x j)) ⁻¹' {(a, b)} =
      Set.pi ({i, j} : Finset ℕ) (fun k => ({if k = i then a else b} : Set Bool)) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, Finset.coe_insert,
      Finset.coe_singleton, mem_pi, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      forall_eq]
    simp [hij.symm]
  rw [hpre, paperSigns, Measure.infinitePi_pi _ (fun k _ => measurableSet_singleton _),
    Finset.prod_pair hij]
  have hs1 : fairSign {a} = 2⁻¹ := by
    simp [fairSign, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply']
    cases a <;> simp
  have hs2 : fairSign {b} = 2⁻¹ := by
    simp [fairSign, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply']
    cases b <;> simp
  have hp : (fairSign.prod fairSign) {(a, b)} = fairSign {a} * fairSign {b} := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [hij.symm, hp, hs1, hs2]

/-- Auxiliary lemma `paperSigns_map_one` for Section 3.1 (Lemma 3.1); not a statement of the paper. -/
lemma paperSigns_map_one (i : ℕ) : paperSigns.map (fun x => x i) = fairSign :=
  Measure.infinitePi_map_eval _ i

/-- Concrete label space `ℝ × Bool` with `Z = fst`, `σ = snd`. -/
theorem chartLabels_concrete :
    ChartLabels (volume.prod fairSign) (fun ω : ℝ × Bool => ω.1) (fun ω => ω.2) :=
  ⟨measurable_fst, measurable_snd, by simp⟩

/-- **Section 3.1, the paper's label space `Ω = ℝ × {-1,1}^ℕ`, `μ = L ⊗ ν`**: with `Z` the
Lebesgue coordinate and `σ` the sign coordinate `i`, `(Z, σ)` has joint law Lebesgue times a fair
sign, i.e. is a chart's label data. (The paper's initial chart uses `i = 0`.) -/
theorem chartLabels_paper (i : ℕ) :
    ChartLabels (volume.prod paperSigns) (fun ω : ℝ × (ℕ → Bool) => ω.1)
      (fun ω => ω.2 i) := by
  refine ⟨measurable_fst, by fun_prop, ?_⟩
  have h := Measure.map_prod_map (volume : Measure ℝ) paperSigns (f := id)
    (g := fun x : ℕ → Bool => x i) measurable_id (by fun_prop)
  rw [Measure.map_id, paperSigns_map_one] at h
  exact h.symm

/-- Rebasing on the paper's label space (first sign `σ = x i`, fresh sign `τ = x j`, `i ≠ j`). -/
theorem rebase_chartLabels_paper {κ : ℝ} {Lψ : NNReal} {ψ : ℝ → ℝ} (hκ : 0 ≤ κ)
    (hc : κ * Lψ < 1) (hψ : LipschitzWith Lψ ψ) {i j : ℕ} (hij : i ≠ j) :
    ChartLabels (volume.prod paperSigns)
      (rebaseZ hκ hc hψ (fun ω : ℝ × (ℕ → Bool) => ω.1) (fun ω => ω.2 i))
      (fun ω => ω.2 j) := by
  apply rebase_chartLabels hκ hc hψ (measurable_fst) (by fun_prop) (by fun_prop)
  have h := Measure.map_prod_map (volume : Measure ℝ) paperSigns (f := id)
    (g := fun x : ℕ → Bool => (x i, x j)) measurable_id (by fun_prop)
  rw [Measure.map_id, paperSigns_map_two hij] at h
  exact h.symm

end Instances

/-! ### Axiom check

Output of `lake env lean PlanarL1/Chart.lean` with `#print axioms <name>` for each:

* `PlanarL1.measure_symmDiff_thrSet` depends on axioms: [propext, Classical.choice, Quot.sound]
* `PlanarL1.measure_symmDiff_chartSet` depends on axioms: [propext, Classical.choice, Quot.sound]
* `PlanarL1.chartSet_subset_of_le` depends on axioms: [propext, Classical.choice, Quot.sound]
* `PlanarL1.measure_symmDiff_chartSet_eq_vertical` depends on axioms: [propext, Classical.choice, Quot.sound]
* `PlanarL1.measure_diff_chartSet_eq_vertical` depends on axioms: [propext, Classical.choice, Quot.sound]
* `PlanarL1.phiEquiv` depends on axioms: [propext, Classical.choice, Quot.sound]
* `PlanarL1.rebase_lt_iff` depends on axioms: [propext, Classical.choice, Quot.sound]
* `PlanarL1.chartSet_rebase` depends on axioms: [propext, Classical.choice, Quot.sound]
* `PlanarL1.rebase_chartLabels` depends on axioms: [propext, Classical.choice, Quot.sound]
* `PlanarL1.chartLabels_paper` depends on axioms: [propext, Classical.choice, Quot.sound]
* `PlanarL1.rebase_chartLabels_paper` depends on axioms: [propext, Classical.choice, Quot.sound]
-/

end PlanarL1
