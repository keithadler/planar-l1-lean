import Mathlib

/-!
# Section 3.2: exact gluing and component refinement (Lemma 3.2)

Source: OpenAI, *Planar Graph Metrics Embed into L1 with Constant Distortion* (preprint, 23 Sep 2026), Section 3.2,
plus the column-model conventions of Definition 2.1 and Lemma 2.4.  This is a conditional formalisation: nothing from
Section 2 (geometry) or Section 4 (interpolation) is proved here, and no axioms are added.

## What is modelled

* `ColumnModel`: finitely many columns `ι` (a finite linearly ordered type; the circular order of the paper is cut open
  at an arbitrary point, which changes none of the notions used: alternation of four endpoints, strict arcs),
  with a closed bounded set of switch heights `Sw i j` for each pair, noncrossing links and the terminal-switch
  condition of Definition 2.1.
* `SetSystem`: a measurable set `A i H` of labels for every point `(i, H)`, nested increasingly on each column, equal at
  switches, with symmetric-difference measure at most the vertical length.
* Lemma 3.2 (`labelDist_eq_two_of_inactive_tip`, `two_mul_measure_le_refDist`, `symmDist_le_refDist`,
  `refDist_le_of_reach`, `refDist_le_colDist`, ...).
* Exact gluing (`GlueData`, `GlueData.glue`, `GlueData.nested_length`, `GlueData.respects_switch`).

## Not formalised here

See the pull request description.  In particular: Lemma 3.1 / the product label space (Task A) is replaced by the
hypothesis `ChartLabels.law`; the "reference point" subtraction making the refined map a map into a real `L¹` space is
not done (distances are `lintegral`s in `ℝ≥0∞`); recording of new charts, rebasing, system B and the Lipschitz
perturbations that vanish on the boundary are not formalised.
-/

open MeasureTheory Set
open scoped ENNReal symmDiff Classical

noncomputable section

namespace PlanarL1.Refinement

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Four endpoints alternate in the circular order.  For a link `ab` with `a < b` (the circle cut open at the
bottom of the order) and a second link `cd`: `c` lies strictly inside the arc `(a, b)` and `d` strictly outside it.
Paper (Definition 2.1): "The links are noncrossing if no two have four distinct endpoints alternating in the cyclic
order."  Lean: this is that alternation, written for `a < b` with `c` the inside endpoint; the case with `d` inside is
obtained by swapping the roles of `c` and `d` (switch sets are symmetric). -/
def Crosses (a b c d : ι) : Prop := a < b ∧ a < c ∧ c < b ∧ (d < a ∨ b < d)

/-- A column model (paper, Definition 2.1), reduced to the data Lemma 3.2 and the gluing argument use.

Fields (each is a hypothesis, never an axiom):
* `Sw i j`: the closed bounded set `S_ij ⊂ ℝ` of switch heights between columns `i` and `j`; symmetric (`symm`);
  compact (`compact`), as in Definition 2.1.  A link `ij` exists when `Sw i j` is nonempty.
* `noncrossing`: no two links have four distinct endpoints alternating in the circular order (Definition 2.1).
* `terminal`: every link between non-consecutive indices (both open arcs between `a < b` are nonempty) is a switch
  at a single height `He` (the tip), and neither endpoint column has any switch above `He` (Definition 2.1, "terminal
  switch").

Differences from the paper: the cyclic order is given by a `LinearOrder` (the circle cut open); the paper's cyclically
ordered finite index set `V₀` is `ι`.  The quotient space `X`, the height function and the metric `d` are not built
as types: points are pairs `(i, H)` (representatives) and `d` is `colDist` below. -/
structure ColumnModel (ι : Type*) [Fintype ι] [LinearOrder ι] where
  Sw : ι → ι → Set ℝ
  symm : ∀ i j, Sw i j = Sw j i
  compact : ∀ i j, IsCompact (Sw i j)
  noncrossing : ∀ a b c d, (Sw a b).Nonempty → (Sw c d).Nonempty → ¬ Crosses a b c d
  terminal : ∀ a b, a < b → (∃ k, a < k ∧ k < b) → (∃ l, l < a ∨ b < l) → (Sw a b).Nonempty →
    ∃ He, Sw a b = {He} ∧ (∀ k, ∀ s ∈ Sw a k, s ≤ He) ∧ (∀ k, ∀ s ∈ Sw b k, s ≤ He)

/-- A system of label sets on a column model (the hypotheses of Lemma 3.2).

Paper: "Suppose a system of sets is nested increasingly on each column, respects switches, and has
symmetric-difference measure at most vertical length."  Fields:
* `measurable`: every set is measurable (implicit in the paper, where all sets are measurable subsets of `Ω`);
* `nested`: `A i` is monotone in the height (nested increasingly on each column);
* `respects_switch`: `A i H = A j H` whenever `H` is a switch height of the link `ij` (respects switches);
* `vertical_length`: `μ (A i H △ A i H') ≤ |H - H'|` (symmetric-difference measure at most vertical length). -/
structure SetSystem (M : ColumnModel ι) (μ : Measure Ω) where
  A : ι → ℝ → Set Ω
  measurable : ∀ i H, MeasurableSet (A i H)
  nested : ∀ i, Monotone (A i)
  respects_switch : ∀ i j H, H ∈ M.Sw i j → A i H = A j H
  vertical_length : ∀ i H H', μ (A i H ∆ A i H') ≤ ENNReal.ofReal |H - H'|

/-- `Reach M L p q`: there is a path in the column model from the point `p = (i, H)` to `q` of total length `L`:
a finite concatenation of vertical segments (cost `|H - H'|`) and zero-cost switches at heights in `Sw i j`
(paper, Definition 2.1: "Paths consist of finitely many vertical segments and permitted switches; their length is the
sum of the lengths of the vertical segments."). -/
inductive Reach (M : ColumnModel ι) : ℝ≥0∞ → ι × ℝ → ι × ℝ → Prop
  | refl (p : ι × ℝ) : Reach M 0 p p
  | vertical (i : ι) (H H' : ℝ) : Reach M (ENNReal.ofReal |H - H'|) (i, H) (i, H')
  | switch (i j : ι) (H : ℝ) : H ∈ M.Sw i j → Reach M 0 (i, H) (j, H)
  | trans {L L' : ℝ≥0∞} {p q r : ι × ℝ} : Reach M L p q → Reach M L' q r → Reach M (L + L') p r

/-- The column-model distance `d`: the infimum of the lengths of paths (Definition 2.1), as an element of `ℝ≥0∞`.
Only the infimum over `Reach` is used: no bounded-band restriction `d_I` is modelled. -/
def colDist (M : ColumnModel ι) (p q : ι × ℝ) : ℝ≥0∞ := ⨅ (L : ℝ≥0∞) (_ : Reach M L p q), L

namespace SetSystem
variable {M : ColumnModel ι} {μ : Measure Ω} (S : SetSystem M μ)

/-- The unrefined pseudometric of Lemma 3.2: `μ (A_p △ A_q)`, in `ℝ≥0∞` (the paper subtracts a reference vector to
land in a real `L¹` space; here we keep the possibly infinite value, which is always finite on points joined by a
path by `symmDist_le_colDist`). -/
def symmDist (p q : ι × ℝ) : ℝ≥0∞ := μ (S.A p.1 p.2 ∆ S.A q.1 q.2)

/-- For the label `ω`, the link `ij` has a switch at a height active for `ω` (`ω ∈ A i s`, `s ∈ Sw i j`). -/
def switchRel (ω : Ω) (i j : ι) : Prop := ∃ s ∈ M.Sw i j, ω ∈ S.A i s

/-- Paper, Lemma 3.2: "For a label `ω`, join two columns when one of their switches occurs at a height active for
`ω`."  The graph on the columns `ι` whose edges are the links with an active switch. -/
def activeGraph (ω : Ω) : SimpleGraph ι := SimpleGraph.fromRel (S.switchRel ω)

/-- The component of column `i` in `activeGraph ω`, as a subset of `ι` (the paper: "indexed by subsets of the
columns"). -/
def comp (ω : Ω) (i : ι) : Set ι := {k | (S.activeGraph ω).Reachable i k}

/-- Paper, Lemma 3.2: "To an active point assign the unit vector indexed by its component in this finite graph, and to
an inactive point assign zero." -/
def vec (ω : Ω) (p : ι × ℝ) : Set ι → ℝ :=
  fun c => if ω ∈ S.A p.1 p.2 ∧ S.comp ω p.1 = c then 1 else 0

/-- The `ℓ¹` distance of the vectors `vec ω p`, `vec ω q`. -/
def labelDist (ω : Ω) (p q : ι × ℝ) : ℝ := ∑ c : Set ι, |S.vec ω p c - S.vec ω q c|

/-- Paper, Lemma 3.2: "Integrating the `ℓ¹` distances of these vectors gives the refined pseudometric."  Lean: the
integral is a lower Lebesgue integral in `ℝ≥0∞` (no integrability needed); it is a pseudometric on points, see
`refDist_self`, `refDist_comm`, `refDist_triangle`. -/
def refDist (p q : ι × ℝ) : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (S.labelDist ω p q) ∂μ

lemma comp_eq_iff (ω : Ω) (i k : ι) : S.comp ω i = S.comp ω k ↔ (S.activeGraph ω).Reachable i k := by
  constructor
  · intro h
    have : k ∈ S.comp ω k := SimpleGraph.Reachable.refl k
    rw [← h] at this
    exact this
  · intro h
    ext x
    exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩

lemma labelDist_eq (ω : Ω) (p q : ι × ℝ) :
    S.labelDist ω p q =
      if ω ∈ S.A p.1 p.2 then
        (if ω ∈ S.A q.1 q.2 then (if (S.activeGraph ω).Reachable p.1 q.1 then 0 else 2) else 1)
      else (if ω ∈ S.A q.1 q.2 then 1 else 0) := by
  unfold labelDist vec
  by_cases ha : ω ∈ S.A p.1 p.2 <;> by_cases hb : ω ∈ S.A q.1 q.2
  · by_cases hr : (S.activeGraph ω).Reachable p.1 q.1
    · have := (S.comp_eq_iff ω p.1 q.1).2 hr
      simp [ha, hb, hr, this]
    · have hne : S.comp ω p.1 ≠ S.comp ω q.1 := fun h => hr ((S.comp_eq_iff ω p.1 q.1).1 h)
      have key : ∀ c : Set ι, |(if ω ∈ S.A p.1 p.2 ∧ S.comp ω p.1 = c then (1:ℝ) else 0) -
          (if ω ∈ S.A q.1 q.2 ∧ S.comp ω q.1 = c then (1:ℝ) else 0)| =
          (if S.comp ω p.1 = c then 1 else 0) + (if S.comp ω q.1 = c then 1 else 0) := by
        intro c
        by_cases h1 : S.comp ω p.1 = c <;> by_cases h2 : S.comp ω q.1 = c
        · exact absurd (h1.trans h2.symm) hne
        · simp [ha, hb, h1, h2]
        · simp [ha, hb, h1, h2]
        · simp [ha, hb, h1, h2]
      simp only [key, Finset.sum_add_distrib]
      simp [hr, ha, hb]
      norm_num
  · simp [ha, hb, apply_ite abs]
  · simp [ha, hb, apply_ite abs]
  · simp [ha, hb]

lemma switchRel_measurable (i j : ι) : MeasurableSet {ω | S.switchRel ω i j} := by
  by_cases hne : (M.Sw i j).Nonempty
  · have hmax := (M.compact i j).sSup_mem hne
    have : {ω | S.switchRel ω i j} = S.A i (sSup (M.Sw i j)) := by
      ext ω
      constructor
      · rintro ⟨s, hs, hω⟩
        exact S.nested i (le_csSup (M.compact i j).bddAbove hs) hω
      · intro hω
        exact ⟨_, hmax, hω⟩
    rw [this]
    exact S.measurable _ _
  · have : {ω | S.switchRel ω i j} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨s, hs, -⟩
      exact hne ⟨s, hs⟩
    rw [this]
    exact MeasurableSet.empty

lemma adj_measurable (i j : ι) : MeasurableSet {ω | (S.activeGraph ω).Adj i j} := by
  have : {ω | (S.activeGraph ω).Adj i j} =
      if i = j then ∅ else {ω | S.switchRel ω i j} ∪ {ω | S.switchRel ω j i} := by
    ext ω
    by_cases h : i = j <;> simp [activeGraph, SimpleGraph.fromRel_adj, h]
  rw [this]
  split_ifs
  · exact MeasurableSet.empty
  · exact (S.switchRel_measurable i j).union (S.switchRel_measurable j i)

lemma graph_eq_measurable (g : SimpleGraph ι) : MeasurableSet {ω | S.activeGraph ω = g} := by
  have : {ω | S.activeGraph ω = g} = ⋂ i, ⋂ j, {ω | (S.activeGraph ω).Adj i j ↔ g.Adj i j} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_iInter]
    constructor
    · intro h i j; rw [h]
    · intro h; ext i j; exact h i j
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases h : g.Adj i j
  · have : {ω | (S.activeGraph ω).Adj i j ↔ g.Adj i j} = {ω | (S.activeGraph ω).Adj i j} := by
      ext ω; simp [h]
    rw [this]; exact S.adj_measurable i j
  · have : {ω | (S.activeGraph ω).Adj i j ↔ g.Adj i j} = {ω | (S.activeGraph ω).Adj i j}ᶜ := by
      ext ω; simp [h]
    rw [this]; exact (S.adj_measurable i j).compl

lemma reachable_measurable (i k : ι) : MeasurableSet {ω | (S.activeGraph ω).Reachable i k} := by
  have : {ω | (S.activeGraph ω).Reachable i k} =
      ⋃ g : {g : SimpleGraph ι // g.Reachable i k}, {ω | S.activeGraph ω = g.1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h; exact ⟨⟨_, h⟩, rfl⟩
    · rintro ⟨g, hg⟩; rw [hg]; exact g.2
  rw [this]
  have : Finite {g : SimpleGraph ι // g.Reachable i k} := inferInstance
  exact MeasurableSet.iUnion fun g => S.graph_eq_measurable g.1

lemma labelDist_measurable (p q : ι × ℝ) : Measurable fun ω => S.labelDist ω p q := by
  simp_rw [labelDist_eq]
  refine Measurable.ite (S.measurable _ _) (Measurable.ite (S.measurable _ _) ?_ measurable_const)
    (Measurable.ite (S.measurable _ _) measurable_const measurable_const)
  exact Measurable.ite (S.reachable_measurable _ _) measurable_const measurable_const

lemma labelDist_nonneg (ω : Ω) (p q : ι × ℝ) : 0 ≤ S.labelDist ω p q :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma labelDist_self (ω : Ω) (p : ι × ℝ) : S.labelDist ω p p = 0 := by
  simp [labelDist]

lemma labelDist_comm (ω : Ω) (p q : ι × ℝ) : S.labelDist ω p q = S.labelDist ω q p := by
  unfold labelDist
  exact Finset.sum_congr rfl fun c _ => abs_sub_comm _ _

lemma labelDist_triangle (ω : Ω) (p q r : ι × ℝ) :
    S.labelDist ω p r ≤ S.labelDist ω p q + S.labelDist ω q r := by
  unfold labelDist
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun c _ => abs_sub_le _ _ _

lemma refDist_self (p : ι × ℝ) : S.refDist p p = 0 := by
  simp [refDist, labelDist_self]

lemma refDist_comm (p q : ι × ℝ) : S.refDist p q = S.refDist q p := by
  simp [refDist, labelDist_comm S _ p q]

lemma refDist_triangle (p q r : ι × ℝ) : S.refDist p r ≤ S.refDist p q + S.refDist q r := by
  unfold refDist
  have hm : Measurable fun ω => ENNReal.ofReal (S.labelDist ω p q) :=
    ENNReal.measurable_ofReal.comp (S.labelDist_measurable p q)
  rw [← lintegral_add_left hm]
  refine lintegral_mono fun ω => ?_
  rw [← ENNReal.ofReal_add (S.labelDist_nonneg ω p q) (S.labelDist_nonneg ω q r)]
  exact ENNReal.ofReal_le_ofReal (S.labelDist_triangle ω p q r)

lemma symmDist_self (p : ι × ℝ) : S.symmDist p p = 0 := by simp [symmDist]

lemma symmDist_comm (p q : ι × ℝ) : S.symmDist p q = S.symmDist q p := by
  simp [symmDist, symmDiff_comm]

lemma symmDist_triangle (p q r : ι × ℝ) :
    S.symmDist p r ≤ S.symmDist p q + S.symmDist q r :=
  measure_symmDiff_le _ _ _

lemma ofReal_labelDist_vertical (ω : Ω) (i : ι) (H H' : ℝ) :
    ENNReal.ofReal (S.labelDist ω (i, H) (i, H')) = (S.A i H ∆ S.A i H').indicator 1 ω := by
  rw [labelDist_eq]
  by_cases ha : ω ∈ S.A i H <;> by_cases hb : ω ∈ S.A i H' <;>
    simp [ha, hb, Set.indicator, Set.mem_symmDiff]

lemma refDist_vertical (i : ι) (H H' : ℝ) : S.refDist (i, H) (i, H') = S.symmDist (i, H) (i, H') := by
  unfold refDist symmDist
  simp_rw [ofReal_labelDist_vertical]
  exact lintegral_indicator_one ((S.measurable _ _).symmDiff (S.measurable _ _))

lemma refDist_switch (i j : ι) (H : ℝ) (h : H ∈ M.Sw i j) : S.refDist (i, H) (j, H) = 0 := by
  unfold refDist
  have : ∀ ω, S.labelDist ω (i, H) (j, H) = 0 := by
    intro ω
    rw [labelDist_eq]
    have hA := S.respects_switch i j H h
    have hr : ω ∈ S.A i H → (S.activeGraph ω).Reachable i j := by
      intro hω
      by_cases hij : i = j
      · subst hij; exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable
          (by simp only [activeGraph, SimpleGraph.fromRel_adj]; exact ⟨hij, Or.inl ⟨H, h, hω⟩⟩)
    simp only [← hA]
    by_cases hω : ω ∈ S.A i H
    · simp [hω, hr hω]
    · simp [hω]
  simp [this]

/-- **Lemma 3.2, domination.**  Paper: "It dominates the original symmetric-difference pseudometric."
Lean: the same, for all pairs of representatives `p, q`, in `ℝ≥0∞`. -/
lemma symmDist_le_refDist (p q : ι × ℝ) : S.symmDist p q ≤ S.refDist p q := by
  unfold refDist symmDist
  rw [← lintegral_indicator_one ((S.measurable _ _).symmDiff (S.measurable _ _))]
  refine lintegral_mono fun ω => ?_
  rw [labelDist_eq]
  by_cases ha : ω ∈ S.A p.1 p.2 <;> by_cases hb : ω ∈ S.A q.1 q.2 <;>
    simp [ha, hb, Set.indicator, Set.mem_symmDiff]

/-- Paper, Lemma 3.2 (first sentences): the system "defines an L1 pseudometric dominated by `d`": the symmetric-difference
distance is at most the length of every path.  Lean: stated for `Reach`; symmetry and the triangle inequality are
`symmDist_comm`, `symmDist_triangle`. -/
lemma symmDist_le_of_reach {L : ℝ≥0∞} {p q : ι × ℝ} (h : Reach M L p q) : S.symmDist p q ≤ L := by
  induction h with
  | refl p => simp [symmDist_self]
  | vertical i H H' => exact S.vertical_length i H H'
  | switch i j H hs => simp [symmDist, S.respects_switch i j H hs]
  | trans _ _ ih1 ih2 => exact (S.symmDist_triangle _ _ _).trans (add_le_add ih1 ih2)

/-- **Lemma 3.2, same upper bound.**  Paper: "It also admits the following refinement with the same upper bound"
(proof: "At an active switch the two columns belong to the same component; at an inactive switch both vectors are
zero. Integration and any finite path give the upper bound.").  Lean: the refined distance is at most the length of
every path in the column model. -/
lemma refDist_le_of_reach {L : ℝ≥0∞} {p q : ι × ℝ} (h : Reach M L p q) : S.refDist p q ≤ L := by
  induction h with
  | refl p => simp [refDist_self]
  | vertical i H H' => rw [refDist_vertical]; exact S.vertical_length i H H'
  | switch i j H hs => simp [refDist_switch S i j H hs]
  | trans _ _ ih1 ih2 => exact (S.refDist_triangle _ _ _).trans (add_le_add ih1 ih2)


/-- Strictly opposite sides of the link `ab` (`a < b`): one column index strictly inside the arc `(a, b)`, the
other strictly outside it. -/
def StrictlyOpposite (a b i k : ι) : Prop :=
  (a < i ∧ i < b ∧ (k < a ∨ b < k)) ∨ (a < k ∧ k < b ∧ (i < a ∨ b < i))

lemma not_reachable_of_inactive_tip (a b : ι) (hab : a < b) (hin : ∃ k, a < k ∧ k < b)
    (hout : ∃ l, l < a ∨ b < l) (He : ℝ) (hHe : He ∈ M.Sw a b) (ω : Ω) (htip : ω ∉ S.A a He)
    (x y : ι) (hx : a < x ∧ x < b) (hy : y < a ∨ b < y) : ¬ (S.activeGraph ω).Reachable x y := by
  obtain ⟨He', hSw, hA, hB⟩ := M.terminal a b hab hin hout ⟨He, hHe⟩
  have hHe' : He = He' := by rw [hSw] at hHe; exact hHe
  subst hHe'
  have hAb : S.A b He = S.A a He := (S.respects_switch a b He hHe).symm
  have hnoA : ∀ k, ¬ S.switchRel ω a k := by
    rintro k ⟨s, hs, hω⟩
    exact htip (S.nested a (hA k s hs) hω)
  have hnoA' : ∀ k, ¬ S.switchRel ω k a := by
    rintro k ⟨s, hs, hω⟩
    rw [M.symm] at hs
    rw [S.respects_switch k a s (by rwa [M.symm])] at hω
    exact htip (S.nested a (hA k s hs) hω)
  have hnoB : ∀ k, ¬ S.switchRel ω b k := by
    rintro k ⟨s, hs, hω⟩
    exact htip (hAb ▸ S.nested b (hB k s hs) hω)
  have hnoB' : ∀ k, ¬ S.switchRel ω k b := by
    rintro k ⟨s, hs, hω⟩
    rw [M.symm] at hs
    rw [S.respects_switch k b s (by rwa [M.symm])] at hω
    exact htip (hAb ▸ S.nested b (hB k s hs) hω)
  have hlink : (M.Sw a b).Nonempty := ⟨He, hHe⟩
  -- the inner arc is closed under active adjacency
  have hclosed : ∀ u v, (S.activeGraph ω).Adj u v → (a < u ∧ u < b) → (a < v ∧ v < b) := by
    intro u v huv hu
    simp only [activeGraph, SimpleGraph.fromRel_adj] at huv
    obtain ⟨hne, hrel⟩ := huv
    have hSwne : (M.Sw u v).Nonempty := by
      rcases hrel with ⟨s, hs, -⟩ | ⟨s, hs, -⟩
      · exact ⟨s, hs⟩
      · exact ⟨s, by rw [M.symm]; exact hs⟩
    by_contra hv
    have hv' : v = a ∨ v = b ∨ v < a ∨ b < v := by
      rcases lt_trichotomy v a with h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl h
      · rcases lt_trichotomy v b with h' | h' | h'
        · exact absurd ⟨h, h'⟩ hv
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inr h'))
    rcases hv' with rfl | rfl | h | h
    · rcases hrel with h1 | h1
      · exact hnoA' _ h1
      · exact hnoA _ h1
    · rcases hrel with h1 | h1
      · exact hnoB' _ h1
      · exact hnoB _ h1
    · exact M.noncrossing a b u v hlink hSwne ⟨hab, hu.1, hu.2, Or.inl h⟩
    · exact M.noncrossing a b u v hlink hSwne ⟨hab, hu.1, hu.2, Or.inr h⟩
  intro hreach
  obtain ⟨w⟩ := hreach
  have key : ∀ u v (w : (S.activeGraph ω).Walk u v), (a < u ∧ u < b) → (a < v ∧ v < b) := by
    intro u v w
    induction w with
    | nil => exact id
    | cons h _ ih => exact fun hu => ih (hclosed _ _ h hu)
  have := key _ _ w hx
  rcases hy with h | h
  · exact absurd this.1 (not_lt.2 h.le)
  · exact absurd this.2 (not_lt.2 h.le)

/-- **Lemma 3.2, the separation clause, for one label.**  Paper: "If a non-neighbor link has inactive tip and two active
points have representatives strictly on opposite sides of it, their refined distance for that label is 2."

Lean: the link is `ab` (`a < b`, both open arcs nonempty, switch at height `He` with `He ∈ Sw a b`, which by
`terminal` is its unique tip); "inactive tip" is `ω ∉ A a He`; "active" is membership; `p, q` are pairs
`(column, height)`, i.e. representatives, and "strictly opposite" is `StrictlyOpposite`.  The refined distance of the
label is `labelDist`.  Hypotheses used: noncrossing, terminal switch, nesting, switch agreement (all from the
structures); the conclusion is an equality, as in the paper.  Difference: the paper says the points "have
representatives" on opposite sides; here the representatives are the arguments `p, q` themselves (the vectors do not
depend on the representative, by switch agreement). -/
theorem labelDist_eq_two_of_inactive_tip (a b : ι) (hab : a < b) (hin : ∃ k, a < k ∧ k < b)
    (hout : ∃ l, l < a ∨ b < l) (He : ℝ) (hHe : He ∈ M.Sw a b) (ω : Ω) (htip : ω ∉ S.A a He)
    (p q : ι × ℝ) (hp : ω ∈ S.A p.1 p.2) (hq : ω ∈ S.A q.1 q.2) (hopp : StrictlyOpposite a b p.1 q.1) :
    S.labelDist ω p q = 2 := by
  have hnr : ¬ (S.activeGraph ω).Reachable p.1 q.1 := by
    rcases hopp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact S.not_reachable_of_inactive_tip a b hab hin hout He hHe ω htip _ _ ⟨h1, h2⟩ h3
    · intro h
      exact S.not_reachable_of_inactive_tip a b hab hin hout He hHe ω htip _ _ ⟨h1, h2⟩ h3 h.symm
  rw [labelDist_eq]
  simp [hp, hq, hnr]

/-- **Lemma 3.2, separation clause, integrated** (how the paper uses it later, via the certificate of "activity at two
vertices and inactivity at one fixed tip"): the set of labels on which `p`, `q` are active and the tip is inactive
contributes `2` times its measure to the refined distance.  Not stated in this form in Section 3.2; it is the
integral of the previous theorem over that set. -/
theorem two_mul_measure_le_refDist (a b : ι) (hab : a < b) (hin : ∃ k, a < k ∧ k < b)
    (hout : ∃ l, l < a ∨ b < l) (He : ℝ) (hHe : He ∈ M.Sw a b)
    (p q : ι × ℝ) (hopp : StrictlyOpposite a b p.1 q.1) :
    2 * μ ((S.A p.1 p.2 ∩ S.A q.1 q.2) \ S.A a He) ≤ S.refDist p q := by
  have hmeas : MeasurableSet ((S.A p.1 p.2 ∩ S.A q.1 q.2) \ S.A a He) :=
    ((S.measurable _ _).inter (S.measurable _ _)).diff (S.measurable _ _)
  rw [← lintegral_indicator_const hmeas]
  refine lintegral_mono fun ω => ?_
  by_cases hω : ω ∈ (S.A p.1 p.2 ∩ S.A q.1 q.2) \ S.A a He
  · rw [Set.indicator_of_mem hω]
    have := S.labelDist_eq_two_of_inactive_tip a b hab hin hout He hHe ω hω.2 p q hω.1.1 hω.1.2 hopp
    rw [this]
    simp
  · rw [Set.indicator_of_notMem hω]
    exact zero_le

/-- **Lemma 3.2, refined pseudometric dominated by `d`.**  The refined distance is at most the column-model
distance (the infimum of path lengths). -/
theorem refDist_le_colDist (p q : ι × ℝ) : S.refDist p q ≤ colDist M p q :=
  le_iInf₂ fun _ h => S.refDist_le_of_reach h

/-- **Lemma 3.2, first sentence.**  The symmetric-difference pseudometric is dominated by `d`. -/
theorem symmDist_le_colDist (p q : ι × ℝ) : S.symmDist p q ≤ colDist M p q :=
  le_iInf₂ fun _ h => S.symmDist_le_of_reach h


end SetSystem
/-! ### Exact gluing -/

/-- Label data in chart variables (paper, Section 3.1): measurable `Z : Ω → ℝ` and `σ : Ω → {-1, 1}` "whose joint
pushforward measure is Lebesgue measure times a fair sign".  The sign is real valued; the pushforward condition is
replaced by the only consequence used here, `law`: `μ {σ = s, a ≤ Z < b} = (b - a) / 2` for `s = ±1`
(a hypothesis; the product space is Task A, `PlanarL1/Chart.lean`).  A single sign coordinate is used (the paper
uses `{-1,1}^ℕ` and fresh coordinates for rebasing; neither matters for the gluing argument). -/
structure ChartLabels (μ : Measure Ω) where
  Z : Ω → ℝ
  σ : Ω → ℝ
  measurable_Z : Measurable Z
  measurable_σ : Measurable σ
  sign : ∀ ω, σ ω = 1 ∨ σ ω = -1
  law : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ a b : ℝ, a ≤ b →
    μ {ω | σ ω = s ∧ Z ω ∈ Ico a b} = ENNReal.ofReal ((b - a) / 2)

namespace ChartLabels
variable {μ : Measure Ω} (C : ChartLabels μ)

/-- The chart set `{ω | Z ω < H + σ ω * κ * p}` of a point of height `H` carrying field value `p`. -/
def chartSet (κ H p : ℝ) : Set Ω := {ω | C.Z ω < H + C.σ ω * κ * p}

lemma measurable_chartSet (κ H p : ℝ) : MeasurableSet (C.chartSet κ H p) :=
  measurableSet_lt C.measurable_Z
    (measurable_const.add ((C.measurable_σ.mul_const κ).mul_const p))

/-- The piece of the symmetric difference on which the sign is `s`. -/
def piece (u v s : ℝ) : Set Ω := {ω | C.σ ω = s ∧ C.Z ω ∈ Ico (min u v) (max u v)}

lemma realLemma (Z u v : ℝ) :
    ((Z < u ∧ ¬ Z < v) ∨ (Z < v ∧ ¬ Z < u)) ↔ (min u v ≤ Z ∧ Z < max u v) := by
  simp only [min_le_iff, lt_max_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Or.inr (not_lt.1 h2), Or.inl h1⟩
    · exact ⟨Or.inl (not_lt.1 h2), Or.inr h1⟩
  · rintro ⟨h1 | h1, h2 | h2⟩
    · exact absurd h1 (not_le.2 h2)
    · exact Or.inr ⟨h2, not_lt.2 h1⟩
    · exact Or.inl ⟨h2, not_lt.2 h1⟩
    · exact absurd h1 (not_le.2 h2)

lemma chartSet_symmDiff (κ H1 H2 p1 p2 : ℝ) :
    C.chartSet κ H1 p1 ∆ C.chartSet κ H2 p2 =
      C.piece (H1 + 1 * κ * p1) (H2 + 1 * κ * p2) 1 ∪
        C.piece (H1 + (-1) * κ * p1) (H2 + (-1) * κ * p2) (-1) := by
  ext ω
  rcases C.sign ω with hs | hs
  · have h' : ¬ ((1 : ℝ) = -1) := by norm_num
    simp only [chartSet, piece, Set.mem_symmDiff, Set.mem_union, Set.mem_ofPred_eq, hs, h',
      false_and, or_false, true_and, Set.mem_Ico]
    rw [realLemma]
  · have h' : ¬ ((-1 : ℝ) = 1) := by norm_num
    simp only [chartSet, piece, Set.mem_symmDiff, Set.mem_union, Set.mem_ofPred_eq, hs, h',
      false_and, false_or, true_and, Set.mem_Ico]
    rw [realLemma]

lemma measurableSet_piece (u v s : ℝ) : MeasurableSet (C.piece u v s) :=
  (measurableSet_eq_fun C.measurable_σ measurable_const).inter
    (C.measurable_Z measurableSet_Ico)

lemma measure_piece (u v s : ℝ) (hs : s = 1 ∨ s = -1) :
    μ (C.piece u v s) = ENNReal.ofReal (|u - v| / 2) := by
  have := C.law s hs (min u v) (max u v) (min_le_max)
  rw [piece, this, max_sub_min_eq_abs']

lemma measure_chartSet_symmDiff (κ H1 H2 p1 p2 : ℝ) :
    μ (C.chartSet κ H1 p1 ∆ C.chartSet κ H2 p2) =
      ENNReal.ofReal (|(H1 - H2) + κ * (p1 - p2)| / 2) +
        ENNReal.ofReal (|(H1 - H2) - κ * (p1 - p2)| / 2) := by
  rw [chartSet_symmDiff]
  have hdisj : Disjoint (C.piece (H1 + 1 * κ * p1) (H2 + 1 * κ * p2) 1)
      (C.piece (H1 + (-1) * κ * p1) (H2 + (-1) * κ * p2) (-1)) := by
    rw [Set.disjoint_left]
    rintro ω ⟨h1, -⟩ ⟨h2, -⟩
    rw [h1] at h2
    norm_num at h2
  rw [measure_union hdisj (C.measurableSet_piece _ _ _), C.measure_piece _ _ _ (Or.inl rfl),
    C.measure_piece _ _ _ (Or.inr rfl)]
  congr 3 <;> ring_nf

lemma real_aux (a b : ℝ) (h : |b| ≤ |a|) : (|a + b| / 2 + |a - b| / 2) ≤ |a| := by
  rcases abs_le.1 h with ⟨h1, h2⟩
  rcases abs_cases a with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
  rcases abs_cases (a + b) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
  rcases abs_cases (a - b) with ⟨hc, _⟩ | ⟨hc, _⟩ <;> linarith

/-- Inside a chart: the sets of two points on the same column interval, whose field values differ by at most
`L` times the height difference with `κ L ≤ 1`, have symmetric difference at most the vertical length. -/
lemma measure_chartSet_symmDiff_le (κ L H1 H2 p1 p2 : ℝ) (hκ : 0 ≤ κ) (hκL : κ * L ≤ 1)
    (hp : |p1 - p2| ≤ L * |H1 - H2|) :
    μ (C.chartSet κ H1 p1 ∆ C.chartSet κ H2 p2) ≤ ENNReal.ofReal |H1 - H2| := by
  rw [measure_chartSet_symmDiff, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (real_aux _ _ ?_)
  rw [abs_mul, abs_of_nonneg hκ]
  calc κ * |p1 - p2| ≤ κ * (L * |H1 - H2|) := by gcongr
    _ = (κ * L) * |H1 - H2| := by ring
    _ ≤ 1 * |H1 - H2| := by gcongr
    _ = |H1 - H2| := one_mul _

lemma chartSet_mono (κ L H1 H2 p1 p2 : ℝ) (hκ : 0 ≤ κ) (hκL : κ * L ≤ 1) (hH : H1 ≤ H2)
    (hp : |p1 - p2| ≤ L * |H1 - H2|) : C.chartSet κ H1 p1 ⊆ C.chartSet κ H2 p2 := by
  intro ω hω
  simp only [chartSet, Set.mem_ofPred_eq] at hω ⊢
  have hb : |C.σ ω * κ * (p1 - p2)| ≤ H2 - H1 := by
    rw [abs_mul, abs_mul]
    rcases C.sign ω with hs | hs <;> rw [hs] <;> simp only [abs_one, abs_neg, one_mul]
    all_goals
      rw [abs_of_nonneg hκ]
      calc κ * |p1 - p2| ≤ κ * (L * |H1 - H2|) := by gcongr
        _ = (κ * L) * |H1 - H2| := by ring
        _ ≤ 1 * |H1 - H2| := by gcongr
        _ = H2 - H1 := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]; ring
  have := (abs_le.1 hb).2
  have := (abs_le.1 hb).1
  nlinarith

end ChartLabels

/-- The data of one local update, expressed in the old chart variables (paper, Section 3.2: "Every local update is
first expressed in the old chart variables. A clipping replaces the old comparison field by its maximum with a
proposal").

Fields (all are hypotheses):
* `κ, L`: `0 ≤ κ`, `0 ≤ L`, `κ * L < 1` (the paper's `κ Lip_vert < 1`, with `L` a common vertical Lipschitz constant);
* `P`: the old field; `Q`: the proposal (the minimum of finitely many fields is just one function here);
* `D`: the domain of the update, and for each updated point `(i, H) ∈ D` the closed column interval
  `[lo i H, hi i H]` through it (`mem_interval`), which lies inside `D` and is the same interval for all its points
  (`interval_sub`); so `D` splits each column into disjoint closed intervals (possibly infinitely many);
* `old_chart`: on `D` the old sets are the chart sets of `P` ("expressed in the old chart variables");
* `lip_P`, `lip_Q`: on each updated interval `P` and the proposal are vertically `L`-Lipschitz (so also is the max);
* `P_switch`, `Q_switch`: inside `D` both respect switches ("all branches respect switches");
* `boundary`: the proposal lies strictly below the old field on the domain boundary: at interval endpoints and at
  points with a switch leading to a point outside `D`.

Difference from the paper: the paper's `D` is the domain of the update in the quotient space and "boundary" is its
topological boundary; here the boundary is given combinatorially (endpoints of the column intervals and switch exits),
which is what the proof uses. Only `Q ≤ P` is used on the boundary; the strict margin is kept as in the paper. -/
structure GlueData {M : ColumnModel ι} {μ : Measure Ω} (S : SetSystem M μ) (C : ChartLabels μ) where
  κ : ℝ
  L : ℝ
  κ_nonneg : 0 ≤ κ
  L_nonneg : 0 ≤ L
  κL : κ * L < 1
  P : ι → ℝ → ℝ
  Q : ι → ℝ → ℝ
  D : Set (ι × ℝ)
  lo : ι → ℝ → ℝ
  hi : ι → ℝ → ℝ
  old_chart : ∀ i H, (i, H) ∈ D → S.A i H = C.chartSet κ H (P i H)
  mem_interval : ∀ i H, (i, H) ∈ D → lo i H ≤ H ∧ H ≤ hi i H
  interval_sub : ∀ i H, (i, H) ∈ D → ∀ H' ∈ Icc (lo i H) (hi i H),
    (i, H') ∈ D ∧ lo i H' = lo i H ∧ hi i H' = hi i H
  lip_P : ∀ i H, (i, H) ∈ D → ∀ H1 ∈ Icc (lo i H) (hi i H), ∀ H2 ∈ Icc (lo i H) (hi i H),
    |P i H1 - P i H2| ≤ L * |H1 - H2|
  lip_Q : ∀ i H, (i, H) ∈ D → ∀ H1 ∈ Icc (lo i H) (hi i H), ∀ H2 ∈ Icc (lo i H) (hi i H),
    |Q i H1 - Q i H2| ≤ L * |H1 - H2|
  P_switch : ∀ i j H, H ∈ M.Sw i j → (i, H) ∈ D → (j, H) ∈ D → P i H = P j H
  Q_switch : ∀ i j H, H ∈ M.Sw i j → (i, H) ∈ D → (j, H) ∈ D → Q i H = Q j H
  boundary : ∀ i H, (i, H) ∈ D →
    (H = lo i H ∨ H = hi i H ∨ ∃ j, H ∈ M.Sw i j ∧ (j, H) ∉ D) → Q i H < P i H

namespace GlueData
variable {M : ColumnModel ι} {μ : Measure Ω} {S : SetSystem M μ} {C : ChartLabels μ}
  (G : GlueData S C)

/-- The new sets: the chart set of `max P Q` on the domain `D`, the old set elsewhere. -/
def newA (i : ι) (H : ℝ) : Set Ω :=
  if (i, H) ∈ G.D then C.chartSet G.κ H (max (G.P i H) (G.Q i H)) else S.A i H

lemma newA_of_notMem {i : ι} {H : ℝ} (h : (i, H) ∉ G.D) : G.newA i H = S.A i H := by
  simp [newA, h]

lemma newA_of_mem {i : ι} {H : ℝ} (h : (i, H) ∈ G.D) :
    G.newA i H = C.chartSet G.κ H (max (G.P i H) (G.Q i H)) := by
  simp [newA, h]

lemma newA_eq_old_of_lt {i : ι} {H : ℝ} (h : (i, H) ∈ G.D) (hlt : G.Q i H < G.P i H) :
    G.newA i H = S.A i H := by
  rw [G.newA_of_mem h, max_eq_left hlt.le, G.old_chart i H h]

lemma measurable_newA (i : ι) (H : ℝ) : MeasurableSet (G.newA i H) := by
  unfold newA
  split_ifs
  · exact C.measurable_chartSet _ _ _
  · exact S.measurable _ _

/-- Inside one updated interval the new sets are nested and satisfy the vertical-length bound.  This is the paper's
"For points in one updated interval this follows from Lemma 3.1": the Lemma 3.1 content used (the measure of the
symmetric difference of two chart sets) is proved here as `ChartLabels.measure_chartSet_symmDiff`. -/
lemma interval_nested_length {i : ι} {H0 : ℝ} (h0 : (i, H0) ∈ G.D) {H1 H2 : ℝ}
    (h1 : H1 ∈ Icc (G.lo i H0) (G.hi i H0)) (h2 : H2 ∈ Icc (G.lo i H0) (G.hi i H0))
    (hle : H1 ≤ H2) :
    G.newA i H1 ⊆ G.newA i H2 ∧ μ (G.newA i H1 ∆ G.newA i H2) ≤ ENNReal.ofReal |H1 - H2| := by
  have d1 := (G.interval_sub i H0 h0 H1 h1).1
  have d2 := (G.interval_sub i H0 h0 H2 h2).1
  rw [G.newA_of_mem d1, G.newA_of_mem d2]
  have hp : |max (G.P i H1) (G.Q i H1) - max (G.P i H2) (G.Q i H2)| ≤ G.L * |H1 - H2| :=
    (abs_max_sub_max_le_max _ _ _ _).trans
      (max_le (G.lip_P i H0 h0 H1 h1 H2 h2) (G.lip_Q i H0 h0 H1 h1 H2 h2))
  exact ⟨C.chartSet_mono _ G.L _ _ _ _ G.κ_nonneg (G.κL).le hle hp,
    C.measure_chartSet_symmDiff_le _ G.L _ _ _ _ G.κ_nonneg (G.κL).le hp⟩

end GlueData


namespace GlueData
variable {M : ColumnModel ι} {μ : Measure Ω} {S : SetSystem M μ} {C : ChartLabels μ}
  (G : GlueData S C)

/-- Upper endpoint of the updated interval through `(i, H)`, or `H` itself for an unchanged point. -/
def up (i : ι) (H : ℝ) : ℝ := if (i, H) ∈ G.D then G.hi i H else H

/-- Lower endpoint of the updated interval through `(i, H)`, or `H` itself for an unchanged point. -/
def dn (i : ι) (H : ℝ) : ℝ := if (i, H) ∈ G.D then G.lo i H else H

lemma le_up (i : ι) (H : ℝ) : H ≤ G.up i H := by
  unfold up
  split_ifs with h
  · exact (G.mem_interval i H h).2
  · exact le_rfl

lemma dn_le (i : ι) (H : ℝ) : G.dn i H ≤ H := by
  unfold dn
  split_ifs with h
  · exact (G.mem_interval i H h).1
  · exact le_rfl

/-- Comparison of a point with the upper end of its updated interval (step 1 of the three-step argument). -/
lemma up_spec (i : ι) (H : ℝ) :
    G.newA i H ⊆ G.newA i (G.up i H) ∧
    μ (G.newA i H ∆ G.newA i (G.up i H)) ≤ ENNReal.ofReal (G.up i H - H) ∧
    G.newA i (G.up i H) = S.A i (G.up i H) := by
  by_cases h : (i, H) ∈ G.D
  · have hm := G.mem_interval i H h
    have hup : G.up i H = G.hi i H := by simp [up, h]
    have hI : H ∈ Icc (G.lo i H) (G.hi i H) := hm
    have hI' : G.hi i H ∈ Icc (G.lo i H) (G.hi i H) := ⟨hm.1.trans hm.2, le_rfl⟩
    obtain ⟨hsub, hmeas⟩ := G.interval_nested_length h hI hI' hm.2
    obtain ⟨hD', -, hhi'⟩ := G.interval_sub i H h _ hI'
    rw [hup]
    refine ⟨hsub, ?_, ?_⟩
    · rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hm.2)] at hmeas
    · exact G.newA_eq_old_of_lt hD' (G.boundary i _ hD' (Or.inr (Or.inl hhi'.symm)))
  · have hup : G.up i H = H := by simp [up, h]
    rw [hup]
    exact ⟨subset_rfl, by simp, G.newA_of_notMem h⟩

/-- Comparison of a point with the lower end of its updated interval (step 3 of the three-step argument). -/
lemma dn_spec (i : ι) (H : ℝ) :
    G.newA i (G.dn i H) ⊆ G.newA i H ∧
    μ (G.newA i (G.dn i H) ∆ G.newA i H) ≤ ENNReal.ofReal (H - G.dn i H) ∧
    G.newA i (G.dn i H) = S.A i (G.dn i H) := by
  by_cases h : (i, H) ∈ G.D
  · have hm := G.mem_interval i H h
    have hdn : G.dn i H = G.lo i H := by simp [dn, h]
    have hI : H ∈ Icc (G.lo i H) (G.hi i H) := hm
    have hI' : G.lo i H ∈ Icc (G.lo i H) (G.hi i H) := ⟨le_rfl, hm.1.trans hm.2⟩
    obtain ⟨hsub, hmeas⟩ := G.interval_nested_length h hI' hI hm.1
    obtain ⟨hD', hlo', -⟩ := G.interval_sub i H h _ hI'
    rw [hdn]
    refine ⟨hsub, ?_, ?_⟩
    · rwa [abs_of_nonpos (sub_nonpos.2 hm.1), neg_sub] at hmeas
    · exact G.newA_eq_old_of_lt hD' (G.boundary i _ hD' (Or.inl hlo'.symm))
  · have hdn : G.dn i H = H := by simp [dn, h]
    rw [hdn]
    exact ⟨subset_rfl, by simp, G.newA_of_notMem h⟩

/-- Along a column the upper end of one updated interval lies below the lower end of the interval of a
later point. -/
lemma up_le_dn (i : ι) {H1 H2 : ℝ} (hle : H1 ≤ H2) (hsame : ¬ ((i, H1) ∈ G.D ∧ H2 ≤ G.hi i H1)) :
    G.up i H1 ≤ G.dn i H2 := by
  by_cases d1 : (i, H1) ∈ G.D
  · have hgt : G.hi i H1 < H2 := by
      by_contra hc
      exact hsame ⟨d1, not_lt.1 hc⟩
    have hm1 := G.mem_interval i H1 d1
    have hup : G.up i H1 = G.hi i H1 := by simp [up, d1]
    rw [hup]
    by_cases d2 : (i, H2) ∈ G.D
    · have hdn : G.dn i H2 = G.lo i H2 := by simp [dn, d2]
      rw [hdn]
      by_contra hc
      have hlt : G.lo i H2 < G.hi i H1 := not_le.1 hc
      have hm2 := G.mem_interval i H2 d2
      have hmem2 : G.hi i H1 ∈ Icc (G.lo i H2) (G.hi i H2) := ⟨hlt.le, hgt.le.trans hm2.2⟩
      have hmem1 : G.hi i H1 ∈ Icc (G.lo i H1) (G.hi i H1) := ⟨hm1.1.trans hm1.2, le_rfl⟩
      have e2 := (G.interval_sub i H2 d2 _ hmem2).2.2
      have e1 := (G.interval_sub i H1 d1 _ hmem1).2.2
      have : G.hi i H2 = G.hi i H1 := e2.symm.trans e1
      linarith [hm2.2]
    · have hdn : G.dn i H2 = H2 := by simp [dn, d2]
      rw [hdn]
      exact hgt.le
  · have hup : G.up i H1 = H1 := by simp [up, d1]
    rw [hup]
    by_cases d2 : (i, H2) ∈ G.D
    · have hdn : G.dn i H2 = G.lo i H2 := by simp [dn, d2]
      rw [hdn]
      by_contra hc
      have hlt : G.lo i H2 < H1 := not_le.1 hc
      have hm2 := G.mem_interval i H2 d2
      have hmem2 : H1 ∈ Icc (G.lo i H2) (G.hi i H2) := ⟨hlt.le, hle.trans hm2.2⟩
      exact d1 (G.interval_sub i H2 d2 _ hmem2).1
    · have hdn : G.dn i H2 = H2 := by simp [dn, d2]
      rw [hdn]
      exact hle

/-- **Exact gluing, global invariant on one column.**  Paper (Section 3.2): "For points in different updated intervals,
compare the first point with its interval endpoint, then use the old nested sets between the two interval endpoints,
and finally compare with the second point. These three comparisons preserve nesting, and their symmetric-difference
measures sum to the full vertical length. Unchanged points are handled by the same comparison. This argument does not
require a finite number of updated intervals."

Lean: for `H1 ≤ H2` the new sets are nested, and the symmetric difference has measure at most `|H1 - H2|`.  The
three comparisons are `up_spec`, the old system `S` between `up` and `dn`, and `dn_spec`.  Difference: the paper says
the three measures "sum to" the vertical length; Lean proves `≤` (the triangle inequality), which is all the invariant
needs. -/
lemma nested_length (i : ι) {H1 H2 : ℝ} (hle : H1 ≤ H2) :
    G.newA i H1 ⊆ G.newA i H2 ∧ μ (G.newA i H1 ∆ G.newA i H2) ≤ ENNReal.ofReal |H1 - H2| := by
  by_cases hsame : (i, H1) ∈ G.D ∧ H2 ≤ G.hi i H1
  · have hm := G.mem_interval i H1 hsame.1
    exact G.interval_nested_length hsame.1 (H1 := H1) (H2 := H2) hm
      ⟨hm.1.trans hle, hsame.2⟩ hle
  · have hmid := G.up_le_dn i hle hsame
    obtain ⟨s1, m1, e1⟩ := G.up_spec i H1
    obtain ⟨s3, m3, e3⟩ := G.dn_spec i H2
    constructor
    · refine s1.trans ?_
      rw [e1]
      refine (S.nested i hmid).trans ?_
      rw [← e3]
      exact s3
    · have hmid' : μ (G.newA i (G.up i H1) ∆ G.newA i (G.dn i H2)) ≤
          ENNReal.ofReal (G.dn i H2 - G.up i H1) := by
        rw [e1, e3]
        have := S.vertical_length i (G.up i H1) (G.dn i H2)
        rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hmid)] at this
      calc μ (G.newA i H1 ∆ G.newA i H2)
          ≤ μ (G.newA i H1 ∆ G.newA i (G.up i H1)) +
            μ (G.newA i (G.up i H1) ∆ G.newA i H2) := measure_symmDiff_le _ _ _
        _ ≤ μ (G.newA i H1 ∆ G.newA i (G.up i H1)) +
            (μ (G.newA i (G.up i H1) ∆ G.newA i (G.dn i H2)) +
              μ (G.newA i (G.dn i H2) ∆ G.newA i H2)) := by
          gcongr
          exact measure_symmDiff_le _ _ _
        _ ≤ ENNReal.ofReal (G.up i H1 - H1) + (ENNReal.ofReal (G.dn i H2 - G.up i H1) +
              ENNReal.ofReal (H2 - G.dn i H2)) := by gcongr
        _ = ENNReal.ofReal |H1 - H2| := by
          rw [← ENNReal.ofReal_add (sub_nonneg.2 hmid) (sub_nonneg.2 (G.dn_le i H2)),
            ← ENNReal.ofReal_add (sub_nonneg.2 (G.le_up i H1)) (by
              have := G.dn_le i H2
              have := G.le_up i H1
              linarith)]
          congr 1
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
          ring

/-- **Exact gluing, switch agreement.**  Paper: "the clipping equals the old field ... at any switch leading outside
the domain. Inside the domain all branches respect switches ... Exact agreement at the boundary also preserves the
sets at every switching identification."  Lean: `newA i H = newA j H` for every switch `H ∈ Sw i j`, by cases on
whether `(i, H)`, `(j, H)` lie in `D`. -/
lemma respects_switch (i j : ι) (H : ℝ) (hs : H ∈ M.Sw i j) : G.newA i H = G.newA j H := by
  by_cases di : (i, H) ∈ G.D <;> by_cases dj : (j, H) ∈ G.D
  · rw [G.newA_of_mem di, G.newA_of_mem dj, G.P_switch i j H hs di dj, G.Q_switch i j H hs di dj]
  · rw [G.newA_of_notMem dj, G.newA_eq_old_of_lt di
      (G.boundary i H di (Or.inr (Or.inr ⟨j, hs, dj⟩))), S.respects_switch i j H hs]
  · rw [G.newA_of_notMem di, G.newA_eq_old_of_lt dj
      (G.boundary j H dj (Or.inr (Or.inr ⟨i, by rwa [M.symm], di⟩))), S.respects_switch i j H hs]
  · rw [G.newA_of_notMem di, G.newA_of_notMem dj, S.respects_switch i j H hs]

/-- **Exact gluing (Section 3.2).**  Paper: "A clipping replaces the old comparison field by its maximum with a
proposal ... On the boundary of each proposal's domain the proposal lies below the old field, with a strict margin ...
The new sets consequently retain the global upper invariant."

Lean: the glued family is again a `SetSystem` (measurable, nested, respecting switches, vertical-length bound), and
equals the old one off `D` (`newA_of_notMem`) and at all interval endpoints.  Differences: one proposal `Q` with one domain `D` (the maximum of several `L`-Lipschitz proposals over one domain
is again one `Q`; proposals with different domains can be applied one after another, since the result is again a
`SetSystem`, but that iteration is not stated as a theorem); the perturbation-vanishing-on-the-boundary variant at the end of the paper's paragraph is not formalised; the new chart
identifiers and rebasing ("Only after making the update do we record its winning formulas as new charts") are not. -/
def glue : SetSystem M μ where
  A := G.newA
  measurable := G.measurable_newA
  nested := fun i _ _ h => (G.nested_length i h).1
  respects_switch := G.respects_switch
  vertical_length := by
    intro i H H'
    rcases le_total H H' with h | h
    · exact (G.nested_length i h).2
    · rw [symmDiff_comm, abs_sub_comm]
      exact (G.nested_length i h).2

end GlueData


namespace GlueData
variable {M : ColumnModel ι} {μ : Measure Ω} {S : SetSystem M μ} {C : ChartLabels μ}

/-- The glued system has the new sets as its sets. -/
theorem glue_A (G : GlueData S C) : G.glue.A = G.newA := rfl

end GlueData

/-- The hypotheses of `ColumnModel` are satisfiable (sanity check, not part of the paper): any column set with no
switches. -/
example : ColumnModel ι where
  Sw := fun _ _ => ∅
  symm := fun _ _ => rfl
  compact := fun _ _ => isCompact_empty
  noncrossing := fun _ _ _ _ h => absurd h (by simp)
  terminal := fun _ _ _ _ _ h => absurd h (by simp)

/-! ### Axiom check

`#print axioms` for the main theorems (output recorded as comments):
-/

-- 'PlanarL1.Refinement.SetSystem.labelDist_eq_two_of_inactive_tip' depends on axioms: [propext, Classical.choice, Quot.sound]
-- 'PlanarL1.Refinement.SetSystem.two_mul_measure_le_refDist' depends on axioms: [propext, Classical.choice, Quot.sound]
-- 'PlanarL1.Refinement.SetSystem.symmDist_le_refDist' depends on axioms: [propext, Classical.choice, Quot.sound]
-- 'PlanarL1.Refinement.SetSystem.refDist_le_of_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
-- 'PlanarL1.Refinement.SetSystem.symmDist_le_of_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
-- 'PlanarL1.Refinement.SetSystem.refDist_le_colDist' depends on axioms: [propext, Classical.choice, Quot.sound]
-- 'PlanarL1.Refinement.SetSystem.symmDist_le_colDist' depends on axioms: [propext, Classical.choice, Quot.sound]
-- 'PlanarL1.Refinement.SetSystem.refDist_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
-- 'PlanarL1.Refinement.GlueData.nested_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-- 'PlanarL1.Refinement.GlueData.respects_switch' depends on axioms: [propext, Classical.choice, Quot.sound]
-- 'PlanarL1.Refinement.GlueData.glue' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms SetSystem.labelDist_eq_two_of_inactive_tip
#print axioms SetSystem.two_mul_measure_le_refDist
#print axioms SetSystem.symmDist_le_refDist
#print axioms SetSystem.refDist_le_of_reach
#print axioms SetSystem.symmDist_le_of_reach
#print axioms SetSystem.refDist_le_colDist
#print axioms SetSystem.symmDist_le_colDist
#print axioms SetSystem.refDist_triangle
#print axioms GlueData.nested_length
#print axioms GlueData.respects_switch
#print axioms GlueData.glue


end PlanarL1.Refinement
