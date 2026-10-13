import Mathlib

/-!
# Charts: threshold sets and the cut-distance identity (Section 3.1, Lemma 3.1)

A point `v` of a column carries a height `h v` and a field value `P v`. A label is a pair
`ω = (Z, σ)` of a real `Z` and a sign `σ`; the point's set is `{ω | Z < h v + σ κ P v}`.
-/

example : (1 : ℝ) + 1 = 2 := by norm_num
