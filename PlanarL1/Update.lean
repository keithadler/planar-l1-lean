import Mathlib
import PlanarL1.Constants

/-!
# The main update of system A (Sections 6.1 and 6.2)

Source: OpenAI, *Planar Graph Metrics Embed into L1 with Constant Distortion* (23 Sep 2026), Sections 6.1
and 6.2: Lemma 6.1, Definition 6.2, Lemma 6.3, Corollary 6.4, Lemma 6.5 and formula (29).

## Abstract setting

The paper works on the quotient space of a band `J₁` of columns, with its intrinsic metric `d_{J₁}`.  Here
`X` is any pseudo-metric space (the points of the quotient, so "respects switches" is automatic: a
function on `X` is a function on the quotient), `s : X → ℝ` is a 1-Lipschitz function (the old ordinary
field, (20)), `h : X → ℝ` is the height, and a *cell* is a set `C ⊆ X` with a *frontier* `Fr ⊆ C`.

## What is assumed (never as an `axiom`; always as hypotheses / structure fields)

* Lemma 2.11 (cells): weak diameter `≤ 10 D`, compact frontier (fields of `Setup`).
* Lemma 2.12 (padding): `d(w, z) > 0.01 D` for an interior point `w` and a frontier point `z`
  (hypothesis `hpad` of `Setup.main_raise_or_descending` and `main_test_separation`).
* Theorem 4.1 (interpolation): only its conclusions (23) and 1-Lipschitzness of `F_C` enter, as the fields
  `F_lip`, `h23` of `Setup` (`Setup.of_thm41` derives them from a `Thm41Output`: 1-Lipschitz, `|p̃ − p| ≤ E_A`).
* Existence of intrinsic shortest paths between a point and a frontier point of its cell ("availability").
* Lemma 3.2 (component refinement): in `refined_separation_final`.

## What is NOT modelled

Charts, identifiers, "admit ordinary charts on every new branch", rebasing of height branches, the
"vertical replacement and gluing rule" that turns the vertical Lipschitz bound into nesting (that is
Section 3.2, Task B), the switch structure of the column quotient, and the probability space of the whole
step (only the two cell coins of Corollary 6.4 are modelled).  The label measure of Section 3.1 is modelled
concretely (`labelMeasure`, label space `ℝ × Bool` with a single sign coordinate) and the symmetric-difference
measure of two label sets is computed exactly (`labelMeasure_symmDiff_thresholds`); Lemma 6.1's last
sentence, Corollary 6.4 and Lemma 6.5 are stated on it.  Lemma 3.2 enters Lemma 6.5/(29) as a hypothesis.
-/

open MeasureTheory

namespace PlanarL1
namespace Update

open Constants

section Basics

variable {X : Type*} [PseudoMetricSpace X]

/-- `Lip L f`: `f` is `L`-Lipschitz for the metric of `X` (stated with a real constant). -/
def Lip (L : ℝ) (f : X → ℝ) : Prop := ∀ v w, |f v - f w| ≤ L * dist v w

/-- Auxiliary (no paper counterpart): a Lipschitz function is continuous; used to attain the infimum in (21). -/
theorem Lip.continuous {L : ℝ} {f : X → ℝ} (hL : 0 ≤ L) (hf : Lip L f) : Continuous f := by
  have : LipschitzWith ⟨L, hL⟩ f := LipschitzWith.of_dist_le_mul fun v w => by
    rw [Real.dist_eq]; exact hf v w
  exact this.continuous

/-- The sign `±1` of a Boolean coin: `true ↦ 1`, `false ↦ −1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Auxiliary: `|±1| = 1`. -/
theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

/-- Auxiliary: `(±1)² = 1`, used for "restrict labels to `σ = τ`" in Lemma 6.5. -/
theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

/-- `IsShortestPath γ d₀ w z`: `γ : ℝ → X` restricted to `[0, d₀]` is an arclength-parametrised shortest
path from `w` to `z` (an isometric embedding of `[0, d₀]`). -/
def IsShortestPath (γ : ℝ → X) (d₀ : ℝ) (w z : X) : Prop :=
  γ 0 = w ∧ γ d₀ = z ∧ ∀ t ∈ Set.Icc 0 d₀, ∀ t' ∈ Set.Icc 0 d₀, dist (γ t) (γ t') = |t - t'|

/-- **Definition 6.2** (Descending path).  "A descending path at a point `w` is a shortest path in `J₁`, of
length `d₀ ∈ [10^-5, 0.02]`, whose terminal point `z` satisfies `s(z) ≤ s(w) − d₀ + ϵ` (25)."
Lean: `ε` is a parameter (the paper's `ϵ`; use `Constants.eps`); the path is a map `γ : ℝ → X` with
`γ 0 = w`, isometric on `[0, d₀]`; "lies in the old chart band" is automatic in the abstract space. -/
structure DescendingPath (s : X → ℝ) (ε : ℝ) (w : X) (γ : ℝ → X) (d₀ : ℝ) : Prop where
  len_ge : 1 / 10 ^ 5 ≤ d₀
  len_le : d₀ ≤ 0.02
  shortest : IsShortestPath γ d₀ w (γ d₀)
  descent : s (γ d₀) ≤ s w - d₀ + ε

/-- **Lemma 6.3, last assertion, (26).**  "Every descending path satisfies
`s(γ(t)) ≤ s(w) − t + ϵ` for `0 ≤ t ≤ d₀`."
Lean: exactly this, for a 1-Lipschitz `s`; the hypothesis `Lip 1 s` is "the old field's Lipschitz bound". -/
theorem descending_path_bound {s : X → ℝ} (hs : Lip 1 s) {ε : ℝ} {w : X} {γ : ℝ → X} {d₀ : ℝ}
    (hγ : DescendingPath s ε w γ d₀) {t : ℝ} (ht : t ∈ Set.Icc 0 d₀) :
    s (γ t) ≤ s w - t + ε := by
  obtain ⟨_, hz, hiso⟩ := hγ.shortest
  have hd0 : (0 : ℝ) ≤ d₀ := le_trans ht.1 ht.2
  have hdist : dist (γ t) (γ d₀) = d₀ - t := by
    rw [hiso t ht d₀ ⟨hd0, le_rfl⟩, abs_of_nonpos (by linarith [ht.2])]; ring
  have h1 := hs (γ t) (γ d₀)
  rw [hdist, one_mul] at h1
  have h2 := (abs_le.mp h1).2
  have h3 := hγ.descent
  linarith

/-! ### The functions `p_C` (21), the height profile `p_{h,C}`, and the replacement (24) -/

/-- The infimum in (21): `inf_{z ∈ ∂C} s(z) + (1 − ζ) d(v, z)`.  (Meaningful for nonempty `Fr`; the empty
case is handled in `pC`, because `sInf ∅ = 0` in `ℝ`.) -/
noncomputable def frontierInf (s : X → ℝ) (ζ : ℝ) (Fr : Set X) (v : X) : ℝ :=
  sInf ((fun z => s z + (1 - ζ) * dist v z) '' Fr)

open Classical in
/-- Display (21): `p_C(v) = min{ s_C + 1, inf_{z ∈ ∂C} s(z) + (1 − ζ_A) d_{J₁}(v, z) }`, "the infimum over an
empty frontier is `+∞`".  Lean: `Fr` is the frontier `∂C`, `sC = s(v_C)`, and `ζ` a parameter
(`Constants.zetaA` below). -/
noncomputable def pC (s : X → ℝ) (ζ : ℝ) (Fr : Set X) (sC : ℝ) (v : X) : ℝ :=
  if Fr.Nonempty then min (sC + 1) (frontierInf s ζ Fr v) else sC + 1

/-- Display (21): `p_C ≤ s_C + 1` (the constant branch of the minimum; also holds for an empty frontier). -/
theorem pC_le_const (s : X → ℝ) (ζ : ℝ) (Fr : Set X) (sC : ℝ) (v : X) :
    pC s ζ Fr sC v ≤ sC + 1 := by
  unfold pC
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- Auxiliary: continuity of `z ↦ s(z) + (1 − ζ) d(v, z)`. -/
private theorem cont_aux {s : X → ℝ} (hs : Lip 1 s) (ζ : ℝ) (v : X) :
    Continuous (fun z => s z + (1 - ζ) * dist v z) := by
  have := Lip.continuous zero_le_one hs
  fun_prop

/-- Display (21): the infimum is at most each frontier term `s(z) + (1 − ζ) d(v, z)` (compact frontier, so bounded below). -/
theorem frontierInf_le {s : X → ℝ} {ζ : ℝ} {Fr : Set X} (hFr : IsCompact Fr) (hs : Lip 1 s)
    {z : X} (hz : z ∈ Fr) (v : X) : frontierInf s ζ Fr v ≤ s z + (1 - ζ) * dist v z :=
  csInf_le ((hFr.image (cont_aux hs ζ v)).bddBelow) ⟨z, hz, rfl⟩

/-- Paper after (21): "The frontier is a finite union of compact column intervals, so that a finite infimum is attained."  Lean: compact nonempty frontier and 1-Lipschitz `s`. -/
theorem exists_frontierInf_attained {s : X → ℝ} {ζ : ℝ} {Fr : Set X} (hFr : IsCompact Fr)
    (hne : Fr.Nonempty) (hs : Lip 1 s) (v : X) :
    ∃ z ∈ Fr, frontierInf s ζ Fr v = s z + (1 - ζ) * dist v z := by
  have hc := hFr.image (cont_aux hs ζ v)
  have := hc.sInf_mem (hne.image _)
  obtain ⟨z, hz, hzeq⟩ := this
  exact ⟨z, hz, hzeq.symm⟩

/-- Display (21): `p_C(v) ≤ s(z) + (1 − ζ) d(v, z)` for each frontier point `z` (the term with source `z`). -/
theorem pC_le_frontier {s : X → ℝ} {ζ : ℝ} {Fr : Set X} (hFr : IsCompact Fr) (hs : Lip 1 s)
    {z : X} (hz : z ∈ Fr) (sC : ℝ) (v : X) :
    pC s ζ Fr sC v ≤ s z + (1 - ζ) * dist v z := by
  have hne : Fr.Nonempty := ⟨z, hz⟩
  simp only [pC, hne, ↓reduceIte]
  exact le_trans (min_le_right _ _) (frontierInf_le hFr hs hz v)

/-- Paper, after (21): "The function `p_C` is `(1 − ζ_A)`-Lipschitz for `d_{J₁}`."  Lean: for
`0 ≤ ζ ≤ 1`, compact frontier and 1-Lipschitz `s`.  This is what makes Theorem 4.1 applicable to `p_C`. -/
theorem pC_lip {s : X → ℝ} {ζ : ℝ} (hζ1 : ζ ≤ 1) {Fr : Set X} (hFr : IsCompact Fr)
    (hs : Lip 1 s) (sC : ℝ) : Lip (1 - ζ) (pC s ζ Fr sC) := by
  intro v w
  have h1ζ : 0 ≤ 1 - ζ := by linarith
  by_cases hne : Fr.Nonempty
  · have key : ∀ v w : X, frontierInf s ζ Fr v - frontierInf s ζ Fr w ≤ (1 - ζ) * dist v w := by
      intro v w
      obtain ⟨z, hz, hzeq⟩ := exists_frontierInf_attained hFr hne hs w
      have h2 := frontierInf_le (ζ := ζ) hFr hs hz v
      have h3 : dist v z ≤ dist v w + dist w z := dist_triangle _ _ _
      rw [hzeq]
      nlinarith [mul_le_mul_of_nonneg_left h3 h1ζ]
    have hab : |frontierInf s ζ Fr v - frontierInf s ζ Fr w| ≤ (1 - ζ) * dist v w := by
      rw [abs_le]
      refine ⟨?_, key v w⟩
      have := key w v
      rw [dist_comm] at this
      linarith
    simp only [pC, hne, ↓reduceIte]
    calc |min (sC + 1) (frontierInf s ζ Fr v) - min (sC + 1) (frontierInf s ζ Fr w)|
        ≤ max |(sC + 1) - (sC + 1)| |frontierInf s ζ Fr v - frontierInf s ζ Fr w| :=
          abs_min_sub_min_le_max _ _ _ _
      _ ≤ (1 - ζ) * dist v w := by
          apply max_le
          · simp only [sub_self, abs_zero]; exact mul_nonneg h1ζ dist_nonneg
          · exact hab
  · simp only [pC, hne, ↓reduceIte, sub_self, abs_zero]
    exact mul_nonneg h1ζ dist_nonneg

/-- The height profile `p_{h,C}` of Section 6.1: "`s_C − 1 + α_C` at either endpoint of `J₁`,
`s_C + 2 + α_C` on the interval obtained by deleting the outer portions of width `0.09 a₁`, and linear
on the two remaining portions; extended constantly beyond the two endpoints".  Lean: `J₁ = [H0, H0 + a₁]`
and the closed formula `s_C − 1 + α + 3 · min{1, max{0, min{H − H0, H0 + a₁ − H}} / (0.09 a₁)}`. -/
noncomputable def hProfile (a1 H0 sC α H : ℝ) : ℝ :=
  sC - 1 + α + 3 * min 1 (max 0 (min (H - H0) (H0 + a1 - H)) / (0.09 * a1))

/-- Section 6.1: `p_{h,C}` equals `s_C − 1 + α_C` at the left endpoint of `J₁`. -/
theorem hProfile_left {a1 : ℝ} (ha : 0 < a1) (H0 sC α : ℝ) :
    hProfile a1 H0 sC α H0 = sC - 1 + α := by
  unfold hProfile
  have : min (H0 - H0) (H0 + a1 - H0) = 0 := by
    rw [sub_self, add_sub_cancel_left]; exact min_eq_left ha.le
  rw [this]; simp

/-- Section 6.1: `p_{h,C}` equals `s_C − 1 + α_C` at the right endpoint of `J₁`. -/
theorem hProfile_right {a1 : ℝ} (ha : 0 < a1) (H0 sC α : ℝ) :
    hProfile a1 H0 sC α (H0 + a1) = sC - 1 + α := by
  unfold hProfile
  have : min (H0 + a1 - H0) (H0 + a1 - (H0 + a1)) = 0 := by
    rw [sub_self, add_sub_cancel_left]; exact min_eq_right ha.le
  rw [this]; simp

/-- Section 6.1: `p_{h,C} = s_C + 2 + α_C` on the plateau (outer portions of width `0.09 a₁` deleted). -/
theorem hProfile_plateau {a1 : ℝ} (ha : 0 < a1) (H0 sC α H : ℝ)
    (h1 : H0 + 0.09 * a1 ≤ H) (h2 : H ≤ H0 + a1 - 0.09 * a1) :
    hProfile a1 H0 sC α H = sC + 2 + α := by
  unfold hProfile
  have hpos : 0 < 0.09 * a1 := by positivity
  have h3 : 0.09 * a1 ≤ min (H - H0) (H0 + a1 - H) := le_min (by linarith) (by linarith)
  have h4 : 1 ≤ max 0 (min (H - H0) (H0 + a1 - H)) / (0.09 * a1) := by
    rw [le_div_iff₀ hpos, one_mul]
    exact le_trans h3 (le_max_right _ _)
  rw [min_eq_left h4]; ring

/-- The height profile is `3/(0.09 a₁)`-Lipschitz in the height ("Its Lipschitz constant is
`3/(0.09 a₁)`"). -/
theorem hProfile_lip {a1 : ℝ} (ha : 0 < a1) (H0 sC α H H' : ℝ) :
    |hProfile a1 H0 sC α H - hProfile a1 H0 sC α H'| ≤ 3 / (0.09 * a1) * |H - H'| := by
  have hpos : 0 < 0.09 * a1 := by positivity
  unfold hProfile
  set u := fun H => min (H - H0) (H0 + a1 - H) with hu
  have hu1 : |u H - u H'| ≤ |H - H'| := by
    have := abs_min_sub_min_le_max (H - H0) (H0 + a1 - H) (H' - H0) (H0 + a1 - H')
    refine le_trans this (max_le ?_ ?_)
    · apply le_of_eq; congr 1; ring
    · rw [show H0 + a1 - H - (H0 + a1 - H') = -(H - H') by ring, abs_neg]
  have hv : |max 0 (u H) - max 0 (u H')| ≤ |H - H'| := by
    refine le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le ?_ hu1)
    simp
  have hq : |max 0 (u H) / (0.09 * a1) - max 0 (u H') / (0.09 * a1)| ≤ |H - H'| / (0.09 * a1) := by
    rw [← sub_div, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right hv hpos.le
  have hm : |min 1 (max 0 (u H) / (0.09 * a1)) - min 1 (max 0 (u H') / (0.09 * a1))|
      ≤ |H - H'| / (0.09 * a1) := by
    refine le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le ?_ hq)
    simp; positivity
  have : sC - 1 + α + 3 * min 1 (max 0 (u H) / (0.09 * a1)) -
      (sC - 1 + α + 3 * min 1 (max 0 (u H') / (0.09 * a1))) =
      3 * (min 1 (max 0 (u H) / (0.09 * a1)) - min 1 (max 0 (u H') / (0.09 * a1))) := by ring
  show |sC - 1 + α + 3 * min 1 (max 0 (u H) / (0.09 * a1)) -
      (sC - 1 + α + 3 * min 1 (max 0 (u H') / (0.09 * a1)))| ≤ _
  rw [this, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  calc 3 * |min 1 (max 0 (u H) / (0.09 * a1)) - min 1 (max 0 (u H') / (0.09 * a1))|
      ≤ 3 * (|H - H'| / (0.09 * a1)) := by gcongr
    _ = 3 / (0.09 * a1) * |H - H'| := by ring

end Basics

section Labels

variable {X : Type*}

/-- The label measure of Section 3.1 restricted to a single sign coordinate: the fair sign
`½(δ_true + δ_false)` on `Bool` (`true ↔ +1`). -/
noncomputable def signMeasure : Measure Bool :=
  (1 / 2 : ENNReal) • (Measure.dirac true + Measure.dirac false)

/-- The label measure `μ = Lebesgue ⊗ ½(δ_{+1} + δ_{−1})` on `ℝ × Bool` (`ω = (Z, σ)`), as in Section 3.1
(the paper's label space has further sign coordinates; Task A discusses why one sign suffices). -/
noncomputable def labelMeasure : Measure (ℝ × Bool) := volume.prod signMeasure

/-- The fair sign gives each Boolean mass `1/2` (auxiliary). -/
theorem signMeasure_singleton (b : Bool) : signMeasure {b} = 1 / 2 := by
  cases b <;> simp [signMeasure]

/-- The threshold `T_v = h(v) + σ κ P(v)` with `P = C₀ + τ s` (Section 3.1 and 6). -/
def thr {X : Type*} (κ : ℝ) (h s : X → ℝ) (C0 : ℝ) (τ σ : Bool) (v : X) : ℝ :=
  h v + sgn σ * κ * (C0 + sgn τ * s v)

/-- The label set `A_v = {ω = (Z, σ) | Z < h(v) + σ κ P(v)}` of a point (Section 3.1). -/
def labelSet {X : Type*} (κ : ℝ) (h s : X → ℝ) (C0 : ℝ) (τ : Bool) (v : X) : Set (ℝ × Bool) :=
  {ω | ω.1 < thr κ h s C0 τ ω.2 v}

/-- Paper, proof of Lemma 6.5: "restrict labels to the sign `σ = τ`.  On this half of the label space the
threshold at `v` is `T_v = h(v) + κ_A τ C₀ + κ_A s(v)`." -/
theorem thr_same_sign {X : Type*} (κ : ℝ) (h s : X → ℝ) (C0 : ℝ) (τ : Bool) (v : X) :
    thr κ h s C0 τ τ v = h v + κ * C0 * sgn τ + κ * s v := by
  unfold thr
  have := sgn_mul_self τ
  calc h v + sgn τ * κ * (C0 + sgn τ * s v)
      = h v + κ * C0 * sgn τ + κ * s v * (sgn τ * sgn τ) := by ring
    _ = _ := by rw [this]; ring




/-- Auxiliary: `z` lies strictly below exactly one of `a, b` iff `min a b ≤ z < max a b`. -/
theorem key_slice (a b Z : ℝ) :
    ((Z < a ∧ ¬ Z < b) ∨ (Z < b ∧ ¬ Z < a)) ↔ (min a b ≤ Z ∧ Z < max a b) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd h1 (by linarith [not_lt.mp h2])
      · exact ⟨not_lt.mp h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨h2, not_lt.mpr h1⟩
  · rw [min_eq_right hab, max_eq_left hab]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨not_lt.mp h2, h1⟩
      · exact absurd h1 (by linarith [not_lt.mp h2])
    · rintro ⟨h1, h2⟩
      exact Or.inl ⟨h2, not_lt.mpr h1⟩

/-- Exact measure of the symmetric difference of two label sets given by thresholds `f σ`, `g σ`:
the slice over each sign `σ` is the interval between `f σ` and `g σ`, and each sign has mass `1/2`.
(This is the computation behind identity (5) of the paper, in the one-sign label space used here:
`μ = ½ Σ_σ |f σ − g σ|`.) -/
theorem labelMeasure_symmDiff_thresholds (f g : Bool → ℝ) :
    labelMeasure (symmDiff {ω : ℝ × Bool | ω.1 < f ω.2} {ω : ℝ × Bool | ω.1 < g ω.2}) =
      ENNReal.ofReal ((|f true - g true| + |f false - g false|) / 2) := by
  have hset : symmDiff {ω : ℝ × Bool | ω.1 < f ω.2} {ω : ℝ × Bool | ω.1 < g ω.2} =
      (Set.Ico (min (f true) (g true)) (max (f true) (g true)) ×ˢ ({true} : Set Bool)) ∪
      (Set.Ico (min (f false) (g false)) (max (f false) (g false)) ×ˢ ({false} : Set Bool)) := by
    ext ⟨Z, σ⟩
    cases σ
    · simp only [Set.mem_symmDiff, Set.mem_union, Set.mem_prod, Set.mem_Ico,
        Set.mem_singleton_iff, Bool.false_eq_true, and_false, and_true, false_or, Set.mem_ofPred_eq]
      exact key_slice (f false) (g false) Z
    · simp only [Set.mem_symmDiff, Set.mem_union, Set.mem_prod, Set.mem_Ico,
        Set.mem_singleton_iff, Bool.true_eq_false, and_false, and_true, or_false, Set.mem_ofPred_eq]
      exact key_slice (f true) (g true) Z
  rw [hset, measure_union]
  · unfold labelMeasure
    rw [Measure.prod_prod, Measure.prod_prod, signMeasure_singleton, signMeasure_singleton,
      Real.volume_Ico, Real.volume_Ico, max_sub_min_eq_abs', max_sub_min_eq_abs']
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    have h2 : ENNReal.ofReal 2 = 2 := by simp
    rw [h2, ENNReal.add_div]
    simp only [div_eq_mul_inv]
    ring
  · rw [Set.disjoint_left]
    rintro ⟨Z, σ⟩ ⟨_, h1⟩ ⟨_, h2⟩
    simp at h1 h2
    simp_all
  · exact measurableSet_Ico.prod (MeasurableSet.singleton _)

/-- Same, for fields `P = C₀ + τ s` and `P' = C₀ + τ s'` (same chart variables `C₀, τ`), at two points
with heights `h v`, `h' w`: with `μ` the label measure,
`μ(A_v △ A'_w) = (|Δh + κ τ Δs| + |Δh − κ τ Δs|)/2` where `Δh = h v − h' w`, `Δs = s v − s' w`
(`= max{|Δh|, κ|Δs|}`, the paper's (5)). -/
theorem labelMeasure_symmDiff_labelSet (κ : ℝ) (h h' s s' : X → ℝ) (C0 : ℝ) (τ : Bool) (v w : X) :
    labelMeasure (symmDiff (labelSet κ h s C0 τ v) (labelSet κ h' s' C0 τ w)) =
      ENNReal.ofReal ((|(h v - h' w) + κ * sgn τ * (s v - s' w)| +
        |(h v - h' w) - κ * sgn τ * (s v - s' w)|) / 2) := by
  have := labelMeasure_symmDiff_thresholds (fun σ => thr κ h s C0 τ σ v)
    (fun σ => thr κ h' s' C0 τ σ w)
  unfold labelSet
  convert this using 3
  unfold thr
  have e1 : ∀ σ, h v + sgn σ * κ * (C0 + sgn τ * s v) - (h' w + sgn σ * κ * (C0 + sgn τ * s' w)) =
      (h v - h' w) + sgn σ * (κ * sgn τ * (s v - s' w)) := fun σ => by ring
  simp only [e1]
  have t : sgn true = 1 := by simp [sgn]
  have f : sgn false = -1 := by simp [sgn]
  rw [t, f]
  rw [show (h v - h' w) + -1 * (κ * sgn τ * (s v - s' w)) =
      (h v - h' w) - κ * sgn τ * (s v - s' w) by ring,
    show (h v - h' w) + 1 * (κ * sgn τ * (s v - s' w)) =
      (h v - h' w) + κ * sgn τ * (s v - s' w) by ring]

/-- Lower bound: `μ(A_v △ A'_w) ≥ κ |s v − s' w|` for `κ ≥ 0` (any heights). -/
theorem labelMeasure_symmDiff_ge {κ : ℝ} (hκ : 0 ≤ κ) (h h' s s' : X → ℝ) (C0 : ℝ) (τ : Bool)
    (v w : X) :
    ENNReal.ofReal (κ * |s v - s' w|) ≤
      labelMeasure (symmDiff (labelSet κ h s C0 τ v) (labelSet κ h' s' C0 τ w)) := by
  rw [labelMeasure_symmDiff_labelSet]
  apply ENNReal.ofReal_le_ofReal
  set u := h v - h' w
  set t := κ * sgn τ * (s v - s' w)
  have ht : |t| = κ * |s v - s' w| := by
    simp only [t, abs_mul, abs_of_nonneg hκ, abs_sgn, mul_one]
  have : |t| ≤ (|u + t| + |u - t|) / 2 := by
    have h1 : |(u + t) - (u - t)| ≤ |u + t| + |u - t| := abs_sub _ _
    rw [show (u + t) - (u - t) = 2 * t by ring, abs_mul, abs_two] at h1
    linarith
  linarith

/-- Equality at equal heights: if `h v = h' w` then `μ(A_v △ A'_w) = κ |s v − s' w|` (`κ ≥ 0`). -/
theorem labelMeasure_symmDiff_eq_of_height {κ : ℝ} (hκ : 0 ≤ κ) (h h' s s' : X → ℝ) (C0 : ℝ)
    (τ : Bool) {v w : X} (hh : h v = h' w) :
    labelMeasure (symmDiff (labelSet κ h s C0 τ v) (labelSet κ h' s' C0 τ w)) =
      ENNReal.ofReal (κ * |s v - s' w|) := by
  rw [labelMeasure_symmDiff_labelSet, hh, sub_self, zero_add, zero_sub, abs_neg, abs_mul, abs_mul,
    abs_of_nonneg hκ, abs_sgn, mul_one]
  congr 1
  ring

end Labels

section Cell

variable {X : Type*} [PseudoMetricSpace X]

/-- The data of one cell `C` of width `D` (Section 6.1): the cell, its frontier `∂C`, the base point `v_C`,
the offset `α_C ∈ [0, E_A]`, and the function `F_C = p̃_C − 4 E_A` of (22). -/
structure CellData (X : Type*) where
  C : Set X
  Fr : Set X
  vC : X
  alpha : ℝ
  F : X → ℝ

/-- Theorem 4.1 (Thin-band interpolation), the two properties of the output used in Section 6:
item 1, "`Q` is 1-Lipschitz for `d_J` and satisfies `|Q(v) − p(v)| ≤ 6δ < E`".  Lean: `|Q − p| ≤ E`
(weaker than the paper's `< E`; it is all that is used).  This is a *hypothesis*, not proved here. -/
def Thm41Output (E : ℝ) (p Q : X → ℝ) : Prop := Lip 1 Q ∧ ∀ v, |Q v - p v| ≤ E

/-- The standing hypotheses of Section 6.1 on one available cell `C`:

* `s_lip`: (20), the old field is 1-Lipschitz (`|s(v) − s(w)| ≤ d_{J₁}(v,w)`);
* `Fr_sub`, `Fr_compact`, `diam`: Lemma 2.11 (frontier compact and inside the cell, weak diameter `≤ 10 D`);
* `alpha_nonneg`, `alpha_le`: `α_C ∈ [0, E_A]`;
* `F_lip`: `F_C` is 1-Lipschitz (Theorem 4.1, item 1, minus a constant, by (22));
* `h23`: **the paper's inequality (23)**, `p_C − 5E_A ≤ F_C ≤ p_C − 3E_A`, stated exactly as a hypothesis
  (as the task requires).  It follows from Theorem 4.1 item 1 and (22): `Setup.of_thm41` builds a `Setup`
  from a Theorem 4.1 output, so nothing is lost by taking (23) as the hypothesis.
The structure uses `ζ_A = Constants.zetaA`, `E_A = Constants.EA`, `D = Constants.D`. -/
structure Setup (s : X → ℝ) (cell : CellData X) : Prop where
  s_lip : Lip 1 s
  Fr_sub : cell.Fr ⊆ cell.C
  Fr_compact : IsCompact cell.Fr
  vC_mem : cell.vC ∈ cell.C
  diam : ∀ v ∈ cell.C, ∀ w ∈ cell.C, dist v w ≤ 10 * D
  alpha_nonneg : 0 ≤ cell.alpha
  alpha_le : cell.alpha ≤ EA
  F_lip : Lip 1 cell.F
  h23 : ∀ v, pC s zetaA cell.Fr (s cell.vC) v - 5 * EA ≤ cell.F v ∧
    cell.F v ≤ pC s zetaA cell.Fr (s cell.vC) v - 3 * EA

/-- Display (22) and (23) from **Theorem 4.1**: if `p̃_C` is a Theorem 4.1 output for `p_C` with error
`E_A` (hypothesis `Thm41Output`: 1-Lipschitz and `|p̃_C − p_C| ≤ E_A`; `p_C` is `(1 − ζ_A)`-Lipschitz by
`pC_lip` and the width condition is `Choice.a1_thm41`) and `F_C = p̃_C − 4E_A` (22), then `F_C` is
1-Lipschitz and satisfies (23).  Hence a `Setup` exists whenever Theorem 4.1 applies. -/
theorem Setup.of_thm41 {s : X → ℝ} {cell : CellData X} (hs : Lip 1 s) (hsub : cell.Fr ⊆ cell.C)
    (hcpt : IsCompact cell.Fr) (hv : cell.vC ∈ cell.C)
    (hdiam : ∀ v ∈ cell.C, ∀ w ∈ cell.C, dist v w ≤ 10 * D) (h0 : 0 ≤ cell.alpha)
    (h1 : cell.alpha ≤ EA)
    (hthm : Thm41Output EA (pC s zetaA cell.Fr (s cell.vC)) (fun v => cell.F v + 4 * EA)) :
    Setup s cell where
  s_lip := hs
  Fr_sub := hsub
  Fr_compact := hcpt
  vC_mem := hv
  diam := hdiam
  alpha_nonneg := h0
  alpha_le := h1
  F_lip := fun v w => by
    have := hthm.1 v w
    simpa using this
  h23 := fun v => by
    have := abs_le.mp (hthm.2 v)
    constructor <;> linarith [this.1, this.2]

/-- Display (24): `s'(v) = max{ s(v), min{ F_C(v), p_{h,C}(h(v)) } }` (the kept replacement on `C`). -/
noncomputable def repl (c : Choice) (s h : X → ℝ) (H0 : ℝ) (cell : CellData X) (v : X) : ℝ :=
  max (s v) (min (cell.F v) (hProfile c.a1 H0 (s cell.vC) cell.alpha (h v)))

open Classical in
/-- The new field of a cell `C` with coin `keep`: (24) on `C` if the coin is kept, the old field otherwise
("Otherwise leave the cell unchanged"; points outside `C` are unchanged). -/
noncomputable def newField (c : Choice) (s h : X → ℝ) (H0 : ℝ) (cell : CellData X) (keep : Bool)
    (v : X) : ℝ :=
  if keep = true ∧ v ∈ cell.C then repl c s h H0 cell v else s v

variable {c : Choice} {s h : X → ℝ} {H0 : ℝ} {cell : CellData X}

/-- Paper (20) applied to `v, v_C ∈ C`: `|s(v) − s(v_C)| ≤ 10 D`. -/
theorem Setup.s_sub_sC (hset : Setup s cell) {v : X} (hv : v ∈ cell.C) :
    |s v - s cell.vC| ≤ 10 * D :=
  le_trans (by simpa using hset.s_lip v cell.vC) (hset.diam v hv cell.vC hset.vC_mem)

/-- **Lemma 6.1, frontier part.**  "At a frontier point `z`, the term with source `z` in (21) gives
`p_C(z) ≤ s(z)`.  Thus `F_C(z) ≤ s(z) − 3E_A`. ... The replacement therefore equals the old field on every
frontier ... with a strict margin in the proposed branch."
Lean: `F_C(z) ≤ s(z) − 3E_A < s(z)`, hence both the replacement (24) and `newField` (for either coin) equal
the old field `s(z)` at every frontier point. -/
theorem Setup.frontier_margin (hset : Setup s cell) {z : X} (hz : z ∈ cell.Fr) :
    cell.F z ≤ s z - 3 * EA ∧ cell.F z < s z ∧ repl c s h H0 cell z = s z ∧
      ∀ keep, newField c s h H0 cell keep z = s z := by
  have h1 := pC_le_frontier hset.Fr_compact hset.s_lip hz (s cell.vC) z (ζ := zetaA)
  rw [dist_self, mul_zero, add_zero] at h1
  have h2 := (hset.h23 z).2
  have hE : 0 < EA := fixed_constants_pos.2.2.2.2.2.1
  have h3 : cell.F z ≤ s z - 3 * EA := by linarith
  have h4 : cell.F z < s z := by linarith
  have h5 : repl c s h H0 cell z = s z := by
    unfold repl
    exact max_eq_left (le_trans (min_le_left _ _) h4.le)
  refine ⟨h3, h4, h5, fun keep => ?_⟩
  unfold newField
  split_ifs
  · exact h5
  · rfl

/-- **Lemma 6.1, band-end part.**  "At either endpoint of the height band, (20) gives
`p_{h,C} ≤ s − 1 + 10D + E_A < s`.  The replacement therefore equals the old field ... at every height
endpoint, with a strict margin in the proposed branch."
Lean: for `v ∈ C` at height `H0` or `H0 + a₁` (the two ends of `J₁`) with `a₁ > 0` (from `Choice`),
`p_{h,C}(h(v)) ≤ s(v) − 1 + 10 D + E_A < s(v)`, and both (24) and `newField` equal `s(v)`. -/
theorem Setup.band_end_margin (hset : Setup s cell) {v : X} (hv : v ∈ cell.C)
    (hend : h v = H0 ∨ h v = H0 + c.a1) :
    hProfile c.a1 H0 (s cell.vC) cell.alpha (h v) ≤ s v - 1 + 10 * D + EA ∧
      hProfile c.a1 H0 (s cell.vC) cell.alpha (h v) < s v ∧
      repl c s h H0 cell v = s v ∧ ∀ keep, newField c s h H0 cell keep v = s v := by
  have hp : hProfile c.a1 H0 (s cell.vC) cell.alpha (h v) = s cell.vC - 1 + cell.alpha := by
    rcases hend with he | he <;> rw [he]
    · exact hProfile_left c.a1_pos _ _ _
    · exact hProfile_right c.a1_pos _ _ _
  have hd := hset.s_sub_sC hv
  have hα := hset.alpha_le
  have hle : s cell.vC - 1 + cell.alpha ≤ s v - 1 + 10 * D + EA := by
    have := (abs_le.mp hd).1
    linarith
  have hlt : s cell.vC - 1 + cell.alpha < s v := by
    have := ten_D_add_EA_lt_one
    have := (abs_le.mp hd).1
    linarith
  have h5 : repl c s h H0 cell v = s v := by
    unfold repl
    rw [hp]
    exact max_eq_left (le_trans (min_le_right _ _) hlt.le)
  refine ⟨by rw [hp]; exact hle, by rw [hp]; exact hlt, h5, fun keep => ?_⟩
  unfold newField
  split_ifs
  · exact h5
  · rfl

/-- **Lemma 6.1, size part.**  "Finally, the replacement never decreases `s`, and
`F_C ≤ s_C + 1 − 3E_A ≤ s + 1 + 10D`.  Consequently `0 ≤ s' − s ≤ 1 + 10D`."
Lean: exactly this, for every point `v` and every coin (outside `C`, or with the coin suppressed, the
difference is `0`). -/
theorem Setup.raise_bounds (hset : Setup s cell) (keep : Bool) (v : X) :
    0 ≤ newField c s h H0 cell keep v - s v ∧ newField c s h H0 cell keep v - s v ≤ 1 + 10 * D := by
  have hD : 0 < D := fixed_constants_pos.2.1
  have hE : 0 < EA := fixed_constants_pos.2.2.2.2.2.1
  unfold newField
  split_ifs with hc
  · refine ⟨?_, ?_⟩
    · unfold repl
      linarith [le_max_left (s v) (min (cell.F v) (hProfile c.a1 H0 (s cell.vC) cell.alpha (h v)))]
    · have hd := (abs_le.mp (hset.s_sub_sC hc.2)).1
      have hFle : cell.F v ≤ s cell.vC + 1 - 3 * EA := by
        have h1 := (hset.h23 v).2
        have h2 := pC_le_const s zetaA cell.Fr (s cell.vC) v
        linarith
      unfold repl
      have : max (s v) (min (cell.F v) (hProfile c.a1 H0 (s cell.vC) cell.alpha (h v))) ≤
          s v + (1 + 10 * D) :=
        max_le (by linarith) (le_trans (min_le_left _ _) (by linarith))
      linarith
  · simp; positivity

/-- **Lemma 6.1, last sentence.**  "At a fixed point, a change `s' − s` in the common chart changes the
label set by measure `κ_A |s' − s|`, which proves the stated bound": the change of the system-A label set
at any point has measure at most `κ_A (1 + 10 D)`.
Lean: on the concrete label measure `labelMeasure` (Section 3.1, one sign coordinate `σ ∈ {±1}`; the
paper's further sign coordinates do not change these measures), with the label sets
`A_v = labelSet κ_A h s C₀ τ v` (old) and `A'_v = labelSet κ_A h s' C₀ τ v` (new, same height, same chart
variables `C₀, τ`), we prove `μ(A'_v △ A_v) = κ_A |s'(v) − s(v)| ≤ κ_A (1 + 10 D)`.  The change of chart
variables for "a winning height branch" (rebasing) is not modelled. -/
theorem Setup.label_change_le (hset : Setup s cell) (keep : Bool) (C0 : ℝ) (τ : Bool) (v : X) :
    labelMeasure (symmDiff (labelSet c.kappaA h (newField c s h H0 cell keep) C0 τ v)
        (labelSet c.kappaA h s C0 τ v)) =
        ENNReal.ofReal (c.kappaA * |newField c s h H0 cell keep v - s v|) ∧
      labelMeasure (symmDiff (labelSet c.kappaA h (newField c s h H0 cell keep) C0 τ v)
        (labelSet c.kappaA h s C0 τ v)) ≤ ENNReal.ofReal (c.kappaA * (1 + 10 * D)) := by
  have hk := c.kappa_pos.1
  have hraise := hset.raise_bounds (c := c) (h := h) (H0 := H0) keep v
  have heq := labelMeasure_symmDiff_eq_of_height hk.le h h (newField c s h H0 cell keep) s C0 τ
    (v := v) (w := v) rfl
  refine ⟨heq, ?_⟩
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  rw [abs_of_nonneg hraise.1]
  exact mul_le_mul_of_nonneg_left hraise.2 hk.le

/-- **Lemma 6.1, "different cell prescriptions agree at common quotient points".**  "When two cells
have a common quotient point, that point is in the frontier of both cells. Frontier values will
therefore always be left unchanged."  Lean: if `z` is in the frontier of both `cell` and `cell'` (each
with its `Setup`), then `newField` of either cell, with either coin, equals `s z`; so the two
prescriptions agree there. -/
theorem newField_agree_on_common_frontier {cell' : CellData X} (hset : Setup s cell)
    (hset' : Setup s cell') {z : X} (hz : z ∈ cell.Fr) (hz' : z ∈ cell'.Fr) (k k' : Bool) :
    newField c s h H0 cell k z = newField c s h H0 cell' k' z := by
  rw [(hset.frontier_margin (c := c) (h := h) (H0 := H0) hz).2.2.2 k,
    (hset'.frontier_margin (c := c) (h := h) (H0 := H0) hz').2.2.2 k']

/-- **Lemma 6.1, vertical part.**  "The old field and `F_C` have vertical Lipschitz constant at most 1; the
height branch has constant `3/(0.09 a₁)`.  The maximum and minimum in (24) have the maximum of these
constants.  The parameter choice makes its product with `κ_A` strictly less than 1."
Lean: `Vert` is an arbitrary relation ("same column"), assumed to satisfy `d(v,w) ≤ |h v − h w|` (a vertical
path has length `|Δh|`), and `s`, `F_C` are 1-Lipschitz.  Conclusion: along `Vert` the replacement (24)
(as a function on all of `X`) is `L`-Lipschitz in the height with `L = max{1, 3/(0.09 a₁)}`, and
`κ_A · L < 1`.  Not modelled: the "vertical replacement and gluing rule for label sets" that turns this
into nesting / the vertical upper bound (Section 3.2, Task B). -/
theorem Setup.repl_vert_lip (hset : Setup s cell) (Vert : X → X → Prop)
    (hvert : ∀ v w, Vert v w → dist v w ≤ |h v - h w|) :
    (∀ v w, Vert v w →
      |repl c s h H0 cell v - repl c s h H0 cell w| ≤ max 1 (3 / (0.09 * c.a1)) * |h v - h w|) ∧
      c.kappaA * max 1 (3 / (0.09 * c.a1)) < 1 := by
  refine ⟨fun v w hvw => ?_, c.kappaA_mul_maxLip_lt_one⟩
  have hL1 : 1 ≤ max 1 (3 / (0.09 * c.a1)) := le_max_left _ _
  have hL2 : 3 / (0.09 * c.a1) ≤ max 1 (3 / (0.09 * c.a1)) := le_max_right _ _
  have habs : 0 ≤ |h v - h w| := abs_nonneg _
  have hd := hvert v w hvw
  have hs1 : |s v - s w| ≤ max 1 (3 / (0.09 * c.a1)) * |h v - h w| := by
    have := hset.s_lip v w
    rw [one_mul] at this
    nlinarith
  have hF1 : |cell.F v - cell.F w| ≤ max 1 (3 / (0.09 * c.a1)) * |h v - h w| := by
    have := hset.F_lip v w
    rw [one_mul] at this
    nlinarith
  have hP1 : |hProfile c.a1 H0 (s cell.vC) cell.alpha (h v) -
      hProfile c.a1 H0 (s cell.vC) cell.alpha (h w)| ≤ max 1 (3 / (0.09 * c.a1)) * |h v - h w| := by
    have := hProfile_lip c.a1_pos H0 (s cell.vC) cell.alpha (h v) (h w)
    nlinarith
  unfold repl
  refine le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le hs1 ?_)
  exact le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le hF1 hP1)

/-! ### Lemma 6.3 and Corollary 6.4 -/

/-- **Lemma 6.3** (Main raise or a descending path).  "Suppose `w` satisfies the height and radial interior
requirements for its width-`D` cell, and that the cell is available. For every choice of the interpolation
parameters, its kept replacement raises `s(w)` by more than `2E_A`, unless a descending path at `w` exists."
(The last assertion, (26), is `descending_path_bound`.)

Lean: the interior requirements and availability are the hypotheses
* `hw : w ∈ C`;
* `hplat`: `h(w)` lies in the plateau of `p_{h,C}`, i.e. in `[H0 + 0.09 a₁, H0 + a₁ − 0.09 a₁]` (the paper's
  height requirement "avoids the outer tenths of the band" is stronger: `0.1 a₁ ≥ 0.09 a₁`);
* `hpad`: **Lemma 2.12's padding conclusion** `d(w, z) > 0.01 D` for every frontier point `z`
  (the radial interior requirement; hypothesis, not proved);
* `hgeod`: for every frontier point `z` an intrinsic shortest path from `w` to `z` exists (availability:
  "It remains in the old chart band by availability");
* `hset.h23`: **the paper's inequality (23)** (hypothesis);
* the weak diameter bound (Lemma 2.11) and Lipschitz bound (20) inside `Setup`.
"For every choice of the interpolation parameters" is the universal quantification over `F_C`
satisfying (23).  The conclusion is the disjunction "raise `> 2E_A` or a descending path exists", with
`ϵ = Constants.eps`. -/
theorem Setup.main_raise_or_descending (hset : Setup s cell) {w : X} (hw : w ∈ cell.C)
    (hplat : H0 + 0.09 * c.a1 ≤ h w ∧ h w ≤ H0 + c.a1 - 0.09 * c.a1)
    (hpad : ∀ z ∈ cell.Fr, 0.01 * D < dist w z)
    (hgeod : ∀ z ∈ cell.Fr, ∃ γ : ℝ → X, IsShortestPath γ (dist w z) w z) :
    2 * EA < newField c s h H0 cell true w - s w ∨ ∃ γ d₀, DescendingPath s eps w γ d₀ := by
  by_cases hr : 2 * EA < newField c s h H0 cell true w - s w
  · exact Or.inl hr
  right
  have hnf : newField c s h H0 cell true w = repl c s h H0 cell w := by simp [newField, hw]
  rw [hnf] at hr
  replace hr := not_lt.mp hr
  have hsC := abs_le.mp (hset.s_sub_sC hw)
  have hph : hProfile c.a1 H0 (s cell.vC) cell.alpha (h w) = s cell.vC + 2 + cell.alpha :=
    hProfile_plateau c.a1_pos _ _ _ _ hplat.1 hplat.2
  have hpm := plateau_margin
  have hα0 := hset.alpha_nonneg
  have hEA : 0 < EA := fixed_constants_pos.2.2.2.2.2.1
  have hF : cell.F w ≤ s w + 2 * EA := by
    unfold repl at hr
    have h1 : min (cell.F w) (hProfile c.a1 H0 (s cell.vC) cell.alpha (h w)) ≤ s w + 2 * EA := by
      linarith [le_max_right (s w) (min (cell.F w) (hProfile c.a1 H0 (s cell.vC) cell.alpha (h w)))]
    rcases min_le_iff.mp h1 with h2 | h2
    · exact h2
    · exfalso
      rw [hph] at h2
      linarith
  have h27 : pC s zetaA cell.Fr (s cell.vC) w ≤ s w + 7 * EA := by
    have := (hset.h23 w).1
    linarith
  have hconst := seven_EA_add_ten_D_lt_one
  have hne : cell.Fr.Nonempty := by
    by_contra hne
    simp only [pC, hne, ↓reduceIte] at h27
    linarith
  simp only [pC, hne, ↓reduceIte] at h27
  have hinf : frontierInf s zetaA cell.Fr w ≤ s w + 7 * EA := by
    rcases min_le_iff.mp h27 with h2 | h2
    · exfalso; linarith
    · exact h2
  obtain ⟨z, hz, hzeq⟩ := exists_frontierInf_attained (ζ := zetaA) hset.Fr_compact hne hset.s_lip w
  have hzs : s z + (1 - zetaA) * dist w z ≤ s w + 7 * EA := by rw [← hzeq]; exact hinf
  have hd_ge : 1 / 10 ^ 5 ≤ dist w z := by
    have := hpad z hz
    rw [one_hundredth_D] at this
    exact this.le
  have hd_le : dist w z ≤ 10 * D := hset.diam w hw z (hset.Fr_sub hz)
  obtain ⟨γ, hγ⟩ := hgeod z hz
  have hγz : γ (dist w z) = z := hγ.2.1
  have hkey := (zetaA_mul_d0_add_seven_EA_lt_eps dist_nonneg hd_le).2.2
  refine ⟨γ, dist w z, ⟨hd_ge, le_trans hd_le ten_D_lt.1.le, ?_, ?_⟩⟩
  · rw [hγz]; exact hγ
  · rw [hγz]
    nlinarith

open Classical in
/-- The simultaneous replacement of two cells `cx, cy` with coins `kx, ky`: a point of `cx` with kept coin
gets (24) for `cx`, otherwise the `cy` prescription is applied. -/
noncomputable def field2 (c : Choice) (s h : X → ℝ) (H0 : ℝ) (cx cy : CellData X) (kx ky : Bool)
    (v : X) : ℝ :=
  if kx = true ∧ v ∈ cx.C then repl c s h H0 cx v else newField c s h H0 cy ky v

/-- **Corollary 6.4** (Separation supplied by the main test).  "Let `(x, y)` be an eligible pair satisfying
the interior requirements, `1 ≤ d(x, y) ≤ 2`, and `|s(x) − s(y)| ≤ E_A`.  If either endpoint has no
descending path, then, conditional on main-update mode, the independent cell coins give probability at
least `1/4` of system-A symmetric-difference separation at least `κ_A E_A` at this step."

Lean: `x ∈ C_x`, `y ∈ C_y` (their width-`D` cells, with the hypotheses of Lemma 6.3 for each: `hplat`,
`hpad`, `hgeod`, `Setup`) and `1 ≤ d(x,y)` (the upper bound `d ≤ 2` is not needed; eligibility is
encoded in the `Setup`s).  The two cell coins are the two Booleans `k = (kx, ky)`, uniform on `Bool × Bool`;
"probability" is the fraction of the 4 coin outcomes.  The separation is the label measure
`labelMeasure` of the symmetric difference of the new label sets `A'_x △ A'_y` (`labelSet`, one sign
coordinate, arbitrary common chart variables `C₀, τ`: "evaluate both new sets in their common old label
variables"), with the new field `field2` (the two cell replacements with coins `k`).  "Different cells" is
derived from `d(x,y) ≥ 1 > 10 D`.  The conclusion is
`1/4 ≤ #{k | κ_A E_A ≤ μ(A'_x △ A'_y)} / 4`.  Other cells' coins and the other three modes are not
modelled (they do not affect the two points). -/
theorem main_test_separation {c : Choice} {s h : X → ℝ} {H0 : ℝ} {cx cy : CellData X}
    (hx : Setup s cx)
    (hy : Setup s cy) {x y : X} (hxC : x ∈ cx.C) (hyC : y ∈ cy.C) (hdist : 1 ≤ dist x y)
    (hxy : |s x - s y| ≤ EA)
    (hplat_x : H0 + 0.09 * c.a1 ≤ h x ∧ h x ≤ H0 + c.a1 - 0.09 * c.a1)
    (hpad_x : ∀ z ∈ cx.Fr, 0.01 * D < dist x z)
    (hgeod_x : ∀ z ∈ cx.Fr, ∃ γ : ℝ → X, IsShortestPath γ (dist x z) x z)
    (hplat_y : H0 + 0.09 * c.a1 ≤ h y ∧ h y ≤ H0 + c.a1 - 0.09 * c.a1)
    (hpad_y : ∀ z ∈ cy.Fr, 0.01 * D < dist y z)
    (hgeod_y : ∀ z ∈ cy.Fr, ∃ γ : ℝ → X, IsShortestPath γ (dist y z) y z)
    (hnone : (∀ γ d₀, ¬ DescendingPath s eps x γ d₀) ∨ (∀ γ d₀, ¬ DescendingPath s eps y γ d₀))
    (C0 : ℝ) (τ : Bool) :
    (1 : ℝ) / 4 ≤ ((Finset.univ.filter (fun k : Bool × Bool =>
      ENNReal.ofReal (c.kappaA * EA) ≤ labelMeasure (symmDiff
        (labelSet c.kappaA h (field2 c s h H0 cx cy k.1 k.2) C0 τ x)
        (labelSet c.kappaA h (field2 c s h H0 cx cy k.1 k.2) C0 τ y)))).card : ℝ) / 4 := by
  classical
  have hk := c.kappa_pos.1
  have hD := ten_D_lt.2
  have hxcy : x ∉ cy.C := fun hx' => by
    have := hy.diam x hx' y hyC
    linarith
  have hycx : y ∉ cx.C := fun hy' => by
    have := hx.diam y hy' x hxC
    rw [dist_comm] at this
    linarith
  have key : ∃ k : Bool × Bool, ENNReal.ofReal (c.kappaA * EA) ≤ labelMeasure (symmDiff
        (labelSet c.kappaA h (field2 c s h H0 cx cy k.1 k.2) C0 τ x)
        (labelSet c.kappaA h (field2 c s h H0 cx cy k.1 k.2) C0 τ y)) := by
    rcases hnone with hnx | hny
    · have hr := hx.main_raise_or_descending (c := c) (h := h) (H0 := H0) hxC hplat_x hpad_x hgeod_x
      have hr' : 2 * EA < newField c s h H0 cx true x - s x :=
        hr.resolve_right (fun ⟨γ, d, hd⟩ => hnx γ d hd)
      refine ⟨(true, false), le_trans ?_ (labelMeasure_symmDiff_ge hk.le h h _ _ C0 τ x y)⟩
      have e1 : field2 c s h H0 cx cy true false x = newField c s h H0 cx true x := by
        simp [field2, newField, hxC]
      have e2 : field2 c s h H0 cx cy true false y = s y := by
        simp [field2, newField, hycx]
      rw [e1, e2]
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hk.le
      have := (abs_le.mp hxy).1
      exact le_trans (by linarith) (le_abs_self _)
    · have hr := hy.main_raise_or_descending (c := c) (h := h) (H0 := H0) hyC hplat_y hpad_y hgeod_y
      have hr' : 2 * EA < newField c s h H0 cy true y - s y :=
        hr.resolve_right (fun ⟨γ, d, hd⟩ => hny γ d hd)
      refine ⟨(false, true), le_trans ?_ (labelMeasure_symmDiff_ge hk.le h h _ _ C0 τ x y)⟩
      have e1 : field2 c s h H0 cx cy false true x = s x := by
        simp [field2, newField, hxcy]
      have e2 : field2 c s h H0 cx cy false true y = newField c s h H0 cy true y := by
        simp [field2, newField, hyC]
      rw [e1, e2]
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hk.le
      have := (abs_le.mp hxy).2
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self _)
  obtain ⟨k0, hk0⟩ := key
  have hcard : 1 ≤ (Finset.univ.filter (fun k : Bool × Bool =>
      ENNReal.ofReal (c.kappaA * EA) ≤ labelMeasure (symmDiff
        (labelSet c.kappaA h (field2 c s h H0 cx cy k.1 k.2) C0 τ x)
        (labelSet c.kappaA h (field2 c s h H0 cx cy k.1 k.2) C0 τ y)))).card :=
    Finset.card_pos.mpr ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0⟩⟩
  have : (1 : ℝ) ≤ ((Finset.univ.filter (fun k : Bool × Bool =>
      ENNReal.ofReal (c.kappaA * EA) ≤ labelMeasure (symmDiff
        (labelSet c.kappaA h (field2 c s h H0 cx cy k.1 k.2) C0 τ x)
        (labelSet c.kappaA h (field2 c s h H0 cx cy k.1 k.2) C0 τ y)))).card : ℝ) :=
    Nat.one_le_cast.mpr hcard
  linarith

end Cell

/-! ### Lemma 6.5 and formula (29) -/

/-- **Lemma 6.5, first assertion** (Label mass at a separating tip).  "Suppose a retained pair has a
non-neighbor link separating its representatives strictly, with tip `e` at a height in `J₂`, such that
`d(e, x) ≤ 1` or `d(e, y) ≤ 1`.  If `s(e) < s(w) − j` (28) for at least one endpoint `w`, then there is label
mass at least `κ_A j / 4` for which both endpoints are active and `e` is inactive."

Lean: the label mass is `labelMeasure` of the three-membership set
`A_x ∩ A_y ∩ (A_e)ᶜ` (`labelSet`, the sets of Section 3.1); the geometric hypotheses (link, distances,
chart membership) are not needed for this *measure* computation and are omitted; the hypotheses used are
(a) `|s(x) − s(y)| ≤ E_A` ("the other endpoint has `s`-value within `E_A` of `s(w)`", cutoff (19)),
(b) the three heights lie in an interval `[H2, H2 + a₂]` (`J₂`), (c) (28), and (d) all three points are
evaluated with the same chart data `C₀, τ`.  The proof uses `E_A ≤ j/4` and `a₂ ≤ κ_A j/4` of
`Constants`.  The measure is computed exactly: the three-membership set contains
`[T_e, min{T_x, T_y}) × {τ}`. -/
theorem label_mass_at_tip {X : Type*} (c : Choice) (s h : X → ℝ) (C0 : ℝ) (τ : Bool) {x y e w : X}
    (hw : w = x ∨ w = y) (H2 : ℝ) (hx : H2 ≤ h x ∧ h x ≤ H2 + c.a2)
    (hy : H2 ≤ h y ∧ h y ≤ H2 + c.a2) (he : H2 ≤ h e ∧ h e ≤ H2 + c.a2)
    (hxy : |s x - s y| ≤ EA) (hdrop : s e < s w - j) :
    ENNReal.ofReal (c.kappaA * j / 4) ≤ labelMeasure
      (labelSet c.kappaA h s C0 τ x ∩ labelSet c.kappaA h s C0 τ y ∩
        (labelSet c.kappaA h s C0 τ e)ᶜ) := by
  have hk := c.kappa_pos.1
  have hj : 0 < j := fixed_constants_pos.2.2.2.1
  have hsub := c.kappaA_sub_ge
  have hxy':= abs_le.mp hxy
  have hsx : j - EA ≤ s x - s e := by
    rcases hw with rfl | rfl
    · linarith
    · linarith [hxy'.1, hxy'.2]
  have hsy : j - EA ≤ s y - s e := by
    rcases hw with rfl | rfl
    · linarith [hxy'.1, hxy'.2]
    · linarith
  have hTx : c.kappaA * j / 2 ≤ thr c.kappaA h s C0 τ τ x - thr c.kappaA h s C0 τ τ e := by
    rw [thr_same_sign, thr_same_sign]
    nlinarith [hx.1, hx.2, he.1, he.2, mul_le_mul_of_nonneg_left hsx hk.le]
  have hTy : c.kappaA * j / 2 ≤ thr c.kappaA h s C0 τ τ y - thr c.kappaA h s C0 τ τ e := by
    rw [thr_same_sign, thr_same_sign]
    nlinarith [hy.1, hy.2, he.1, he.2, mul_le_mul_of_nonneg_left hsy hk.le]
  set Te := thr c.kappaA h s C0 τ τ e
  set m := min (thr c.kappaA h s C0 τ τ x) (thr c.kappaA h s C0 τ τ y)
  have hm : c.kappaA * j / 2 ≤ m - Te := by
    have := le_min hTx hTy
    rw [min_sub_sub_right] at this
    exact this
  have hsub' : Set.Ico Te m ×ˢ ({τ} : Set Bool) ⊆
      labelSet c.kappaA h s C0 τ x ∩ labelSet c.kappaA h s C0 τ y ∩
        (labelSet c.kappaA h s C0 τ e)ᶜ := by
    rintro ⟨Z, σ⟩ ⟨⟨hZ1, hZ2⟩, hσ⟩
    have hσ' : σ = τ := hσ
    subst hσ'
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact lt_of_lt_of_le hZ2 (min_le_left _ _)
    · exact lt_of_lt_of_le hZ2 (min_le_right _ _)
    · exact not_lt.mpr hZ1
  refine le_trans ?_ (measure_mono hsub')
  unfold labelMeasure
  rw [Measure.prod_prod, signMeasure_singleton, Real.volume_Ico]
  have : ENNReal.ofReal (c.kappaA * j / 4) = ENNReal.ofReal (c.kappaA * j / 2) * (1 / 2) := by
    rw [show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp, ← ENNReal.ofReal_mul (by have := hj; positivity)]
    congr 1; ring
  rw [this]
  gcongr

/-- **Formula (29)** (and the second assertion of Lemma 6.5).  "More generally, suppose subsequent
changes have total unrefined symmetric-difference costs `Δ_x, Δ_y, Δ_e` at the three points.  The final
component-refined separation is at least `2 (κ_A j/4 − Δ_x − Δ_y − Δ_e)_+`."

Lean, on an arbitrary measure space `(Ω, μ)`: `A_x, A_y, A_e` are the label sets at the time of the
certificate and `A'_x, A'_y, A'_e` the final ones; the "unrefined symmetric-difference costs" are
`μ(A'_v △ A_v) ≤ Δ_v` (taken as the cost of the total change, as in the paper); the certificate mass is
`m ≤ μ(A_x ∩ A_y ∩ A_eᶜ)` (with `m = κ_A j/4` from `label_mass_at_tip`); the "component-refined
separation" is `∫⁻ contrib dμ`, where `contrib ω` is the contribution of label `ω` to the refined
pseudometric between `x` and `y` in the final system.  **Lemma 3.2 enters as the hypothesis `hL32`**: in the
final nested system, a label with `x, y` active and the tip `e` inactive contributes at least 2 (this is
where the non-neighbour link strictly separating the representatives is used; here it is part of
`hL32`).  The conclusion `2 (m − Δ_x − Δ_y − Δ_e)_+ ≤ ∫⁻ contrib` is stated with `ENNReal.ofReal`, which is
the positive part.  "No control of the changes in component names is required": indeed none is used. -/
theorem refined_separation_final {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Ax Ay Ae Ax' Ay' Ae' : Set Ω) (m Δx Δy Δe : ℝ) (hΔx : 0 ≤ Δx) (hΔy : 0 ≤ Δy) (hΔe : 0 ≤ Δe)
    (hS0 : ENNReal.ofReal m ≤ μ (Ax ∩ Ay ∩ Aeᶜ))
    (hx : μ (symmDiff Ax' Ax) ≤ ENNReal.ofReal Δx) (hy : μ (symmDiff Ay' Ay) ≤ ENNReal.ofReal Δy)
    (he : μ (symmDiff Ae' Ae) ≤ ENNReal.ofReal Δe)
    (contrib : Ω → ENNReal) (hmeas : Measurable contrib)
    (hL32 : ∀ ω ∈ Ax' ∩ Ay' ∩ Ae'ᶜ, 2 ≤ contrib ω) :
    ENNReal.ofReal (2 * (m - Δx - Δy - Δe)) ≤ ∫⁻ ω, contrib ω ∂μ := by
  set S0 := Ax ∩ Ay ∩ Aeᶜ
  set S1 := Ax' ∩ Ay' ∩ Ae'ᶜ
  have hdiff : S0 \ S1 ⊆ symmDiff Ax' Ax ∪ symmDiff Ay' Ay ∪ symmDiff Ae' Ae := by
    rintro ω ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    by_cases a : ω ∈ Ax'
    · by_cases b : ω ∈ Ay'
      · by_cases c' : ω ∈ Ae'
        · exact Or.inr (Set.mem_symmDiff.mpr (Or.inl ⟨c', h3⟩))
        · exact absurd ⟨⟨a, b⟩, c'⟩ h4
      · exact Or.inl (Or.inr (Set.mem_symmDiff.mpr (Or.inr ⟨h2, b⟩)))
    · exact Or.inl (Or.inl (Set.mem_symmDiff.mpr (Or.inr ⟨h1, a⟩)))
  have h1 : μ S0 ≤ μ S1 + (ENNReal.ofReal Δx + ENNReal.ofReal Δy + ENNReal.ofReal Δe) := by
    calc μ S0 ≤ μ (S0 ∩ S1) + μ (S0 \ S1) := measure_le_inter_add_sdiff μ S0 S1
      _ ≤ μ S1 + (μ (symmDiff Ax' Ax ∪ symmDiff Ay' Ay ∪ symmDiff Ae' Ae)) :=
          add_le_add (measure_mono Set.inter_subset_right) (measure_mono hdiff)
      _ ≤ μ S1 + (μ (symmDiff Ax' Ax) + μ (symmDiff Ay' Ay) + μ (symmDiff Ae' Ae)) := by
          gcongr
          exact le_trans (measure_union_le _ _) (add_le_add_left (measure_union_le _ _) _)
      _ ≤ _ := by gcongr
  have hsum : 0 ≤ Δx + Δy + Δe := by positivity
  have h2 : ENNReal.ofReal (m - (Δx + Δy + Δe)) ≤ μ S1 := by
    rw [ENNReal.ofReal_sub _ hsum]
    rw [tsub_le_iff_right]
    rw [ENNReal.ofReal_add (by positivity) hΔe, ENNReal.ofReal_add hΔx hΔy]
    exact le_trans hS0 h1
  have h3 : ENNReal.ofReal (2 * (m - Δx - Δy - Δe)) = 2 * ENNReal.ofReal (m - (Δx + Δy + Δe)) := by
    rw [ENNReal.ofReal_mul (by norm_num), show (m - Δx - Δy - Δe) = m - (Δx + Δy + Δe) by ring]
    simp
  rw [h3]
  calc 2 * ENNReal.ofReal (m - (Δx + Δy + Δe)) ≤ 2 * μ S1 := by gcongr
    _ ≤ 2 * μ {ω | 2 ≤ contrib ω} := by
        gcongr
        intro ω hω
        exact hL32 ω hω
    _ ≤ ∫⁻ ω, contrib ω ∂μ := mul_meas_ge_le_lintegral₀ hmeas.aemeasurable 2

/-- **Lemma 6.5, second assertion** ("In no-change mode this gives a component-refined separation in system A
of at least `κ_A j / 2` at this step").  This is `refined_separation_final` with `Δ_x = Δ_y = Δ_e = 0`
(no change: `A' = A`) and `m = κ_A j / 4` from `label_mass_at_tip`, on the concrete label measure
`labelMeasure`.  `contrib` and `hL32` are as in `refined_separation_final` (Lemma 3.2 as hypothesis). -/
theorem lemma65 {X : Type*} (c : Choice) (s h : X → ℝ) (C0 : ℝ) (τ : Bool) {x y e w : X}
    (hw : w = x ∨ w = y) (H2 : ℝ) (hx : H2 ≤ h x ∧ h x ≤ H2 + c.a2)
    (hy : H2 ≤ h y ∧ h y ≤ H2 + c.a2) (he : H2 ≤ h e ∧ h e ≤ H2 + c.a2)
    (hxy : |s x - s y| ≤ EA) (hdrop : s e < s w - j)
    (contrib : ℝ × Bool → ENNReal) (hmeas : Measurable contrib)
    (hL32 : ∀ ω ∈ labelSet c.kappaA h s C0 τ x ∩ labelSet c.kappaA h s C0 τ y ∩
        (labelSet c.kappaA h s C0 τ e)ᶜ, 2 ≤ contrib ω) :
    ENNReal.ofReal (c.kappaA * j / 2) ≤ ∫⁻ ω, contrib ω ∂labelMeasure := by
  have h1 := label_mass_at_tip c s h C0 τ hw H2 hx hy he hxy hdrop
  have h2 := refined_separation_final labelMeasure _ _ _ _ _ _ (c.kappaA * j / 4) 0 0 0
    le_rfl le_rfl le_rfl h1 (by simp) (by simp) (by simp) contrib hmeas hL32
  have : 2 * (c.kappaA * j / 4 - 0 - 0 - 0) = c.kappaA * j / 2 := by ring
  rwa [this] at h2

end Update
end PlanarL1

/-! ### Axiom audit

Real output of `#print axioms` (Lean v4.34.1, run with `lake env lean` on a file importing `PlanarL1.Update`),
for every theorem of this file.  Only the three standard axioms occur; no `sorryAx`.

```
-- PlanarL1.Update.Lip.continuous : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.abs_sgn : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.sgn_mul_self : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.descending_path_bound : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.pC_le_const : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.frontierInf_le : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.exists_frontierInf_attained : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.pC_le_frontier : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.pC_lip : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.hProfile_left : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.hProfile_right : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.hProfile_plateau : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.hProfile_lip : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.signMeasure_singleton : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.thr_same_sign : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.key_slice : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.labelMeasure_symmDiff_thresholds : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.labelMeasure_symmDiff_labelSet : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.labelMeasure_symmDiff_ge : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.labelMeasure_symmDiff_eq_of_height : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.Setup.of_thm41 : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.Setup.s_sub_sC : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.Setup.frontier_margin : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.Setup.band_end_margin : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.Setup.raise_bounds : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.Setup.label_change_le : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.newField_agree_on_common_frontier : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.Setup.repl_vert_lip : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.Setup.main_raise_or_descending : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.main_test_separation : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.label_mass_at_tip : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.refined_separation_final : [propext, Classical.choice, Quot.sound]
-- PlanarL1.Update.lemma65 : [propext, Classical.choice, Quot.sound]
```
-/
