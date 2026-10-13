# Reader's notes on "Planar Graph Metrics Embed into L1 with Constant Distortion"

OpenAI preprint dated 23 September 2026 (45 pages in the PDF at `github.com/openai/math`, not 90). These notes cover the
introduction (1.3) and Sections 3, 5 and 6.1–6.2, the parts Hung Le's reading log (7–11 Oct) called hard or vague.
They were written by Claude (an AI) for Keith Adler to pass on. **They are a second reader's notes, not a verification.**
Nothing here has been checked by a human expert, and Sections 2, 4, 6.3 and 7–10 are not covered.

## 1. The shape of the argument, in one page

*Goal.* One constant C such that every planar graph metric embeds in L1 with distortion at most C. An L1 embedding is the
same as a weighted family of cuts, so the proof builds a measure on "labels", where each label defines a cut.

*Columns (Section 2, not read in detail).* The planar graph is replaced by vertical columns (height = distance from a root)
with zero-cost switches between them, and the plane embedding gives a circular order in which the switches do not cross.

*Two halves.* The **upper bound** (no pair is stretched by more than C) is built into the structure and survives every
update: along a column the label sets grow with height, and at a switch the sets agree exactly. The **lower bound**
(far pairs are actually separated) comes from random local updates at a decreasing sequence of scales r. The difficulty,
as 1.2 says, is combining separation at different scales without paying for the number of scales.

*Two systems, A and B.* A gets a main update and later a component refinement; B gets a secondary update and an ordered
increment. A pair that A cannot separate is, by the structure of the failure, a pair B can.

## 2. Section 3: what a "chart" is

**The sets.** Labels are ω = (Z, σ), a real Z (Lebesgue) and a fair sign σ. A point v gets the set

    A_v = { ω : Z(ω) < h(v) + σ(ω)·κ·P(v) },     h = height, P = a "field", κ = a small fixed constant.

With P = 0 this is just {Z < h(v)}: sets nest as the height grows, and the cut distance between two points of a column is
their height difference. The field P tilts the threshold up or down depending on the sign.

**Formula (5).** For two points written in the same label variables,

    μ(A_v △ A_w) = max{ |Δh|, κ·|ΔP| }.

Why: for sign +1 the symmetric difference has measure |Δh + κΔP|, for −1 it is |Δh − κΔP|, and the average of the two is
max(|Δh|, κ|ΔP|), because (|a+b| + |a−b|)/2 = max(|a|, |b|). So a field difference acts as extra distance, which is how a
local update can create separation.

**Why the condition κ·Lip_vert(P) < 1.** It makes h + σκP strictly increasing in h on every column, so the sets still nest
and the vertical-length upper bound holds.

**What a chart is.** A region R of the column space together with one field P and one choice of label functions (Z, σ).
Inside a chart (5) applies. Across two different charts the sets are described in different label variables, so (5) cannot
be used; the paper therefore relies on the *global* invariant (nesting plus vertical length) for comparisons across charts,
and on an eligibility condition (3.3) that requires both endpoints' radius-5 balls to lie in one chart in each system.

**Rebasing (Lemma 3.1).** A field that depends only on height, P = ψ(h), can be absorbed. Put φ_σ(H) = H + σκψ(H); a change
of coordinate Z′ = φ_σ⁻¹(Z) gives the same sets with field 0. The new Z′ is still Lebesgue because the ±κψ terms cancel in
the average: (φ₊(b) − φ₊(a) + φ₋(b) − φ₋(a))/2 = b − a. This is why a height-only branch of an update becomes a fresh
"constant chart" and not a new kind of object.

**Ordinary charts.** P = c + η·s, with s the distance within a band to a fixed source o (or s = 0). System A uses only
these; system B later adds a second field type (Section 7).

**Exact gluing (3.2).** An update replaces the old field by max(old, proposal), where every proposal lies *strictly below*
the old field on its domain's boundary. So the new field equals the old one on the boundary and at every switch leaving the
domain; nothing changes there, which is why the upper bound survives any number of updates. Only after the update are the
winning formulas recorded as new charts; unchanged points keep their identifiers.

**Component refinement (Lemma 3.2), system A, once at the end.** For a fixed label, join columns that have an active
switch, and give each active point the unit vector of its component. This pseudometric is at least the old one and has the
same upper bound. If a non-neighbour link has an *inactive tip* and two active points lie strictly on opposite sides of it,
that label contributes 2. Hence a "separation certificate" is just three memberships (x active, y active, tip inactive),
which later updates can only damage by moving the sets by a bounded amount (formula (29)).

**3.3, the three estimates** that Section 9 will use: (1) an update at scale r moves any set by at most M·r; (2) an eligible
pair at distance in [r, 2r) gets separation with probability at least p; (3) a ball of radius ρr already in one chart is split
into different new charts with probability at most C₀(ρ + η₀).

## 3. Section 5: the constants and the step

**The hierarchy** ε ≪ j ≪ g ≪ R ≪ D ≪ 1 (table in 5.1): D is the main radial cell width, R the secondary update radius, g
the grouping width for seeds, j the detectable drop at a separating tip, ε the error in a descending path; a₁, a₂ are broad and
narrow band widths; E_A, E_B the interpolation errors; κ_A, κ_B convert field variation into label mass.

**Order of choice.** Fix R, D, g, j, ε, E_A, E_B numerically (10⁻⁸, 10⁻³, 10⁻¹⁴, 10⁻²⁰, 10⁻²⁴, ε/1000, 10⁻³R). Then pick a₁
small enough for Theorem 4.1 and two geometric lemmas, set κ_A = a₁/10⁶, then a₂ ≤ 10⁻⁶·min{a₁, κ_A·j}, κ_B = a₂/10⁶, then
K = 100 and λ = R/(10¹²K), and finally the scale ratio Q = 2^m. Every choice is only an upper bound on a newly chosen positive
number, so there is no circularity; the values are about existence, not optimisation.

**Scales and schedules.** Dyadic scales cover every nonzero vertex distance. For each residue class of the exponent mod m, one
schedule runs in decreasing order of scale; distances are divided by r for the analysis and the field changes multiplied back
by r.

**One step.** Random shifted tilings of the height line (widths a₁ and a₂), radial cells of widths D and g with independent
shifts, a finite list of eligible pairs, then one of four equally likely modes: no change, main update in A, secondary
clipping in B, ordered increment in B. The order of randomness matters: bands, cells, eligible pairs, groups and admissions
are fixed *before* the fresh interpolation offsets, so conditioning on them leaves the offsets independent. A pair is "interior"
with probability at least 1/4 (the checks in 5.2). The finite-grid convention (mesh η₀) is there to avoid measurability
issues and to make the final mixture a finite sum.

## 4. Section 6: the main update, step by step

**The main replacement on a cell C of width D** (formulas (21)–(24)). Take a base value s_C = s(v_C) and the frontier ∂C. Define

    p_C(v) = min{ s_C + 1,  inf over z in ∂C of [ s(z) + (1 − ζ_A)·d(v, z) ] },

a (1−ζ_A)-Lipschitz "cone" that equals roughly the frontier values near the boundary and is capped at s_C + 1. Smooth it with
Theorem 4.1 to get p̃_C and put F_C = p̃_C − 4E_A. Add a height cap p_{h,C} (a plateau of height s_C + 2 + α_C in the middle of
the band, ramping down to s_C − 1 + α_C at the ends), and replace s by

    s′ = max{ s, min{ F_C, p_{h,C}(h) } }    on C   (if the cell's coin is kept).

In words: raise the field inside the cell as far as the frontier and the height cap allow, never lower it, and leave it
unchanged on the frontier and at the band ends (Lemma 6.1 checks the strict margin there, which is what exact gluing needs).
It moves labels by at most κ_A(1 + 10D).

**Lemma 6.3, the dichotomy.** At a point w that is interior and whose cell is available, either the kept replacement raises
s(w) by more than 2E_A, or there is a *descending path* at w (Definition 6.2): a shortest path of length d₀ in [10⁻⁵, 0.02]
ending at z with s(z) ≤ s(w) − d₀ + ε. The proof is: if the raise is small, the plateau forces F_C(w) to be small, so the
frontier term is the binding one; the minimising frontier point z gives the path, and the Lipschitz bound along it gives (26).
So a failure to rise is always explained by a nearly steepest downhill path to the frontier.

**Corollary 6.4.** If an eligible pair (at distance 1 to 2, equal fields to within E_A) has an endpoint with no descending path,
then in main mode the independent cell coins give probability at least 1/4 of separation at least κ_A·E_A.

**6.2.** What is left are pairs with descending paths at both endpoints. Those separated by a low tip are removed (Lemma 6.5: if
a non-neighbour link separates the representatives and its tip e has s(e) < s(w) − j, there is label mass at least κ_A·j/4
on which both endpoints are active and e is inactive; later changes of total cost Δx, Δy, Δe leave at least
2·(κ_A·j/4 − Δx − Δy − Δe)₊). The endpoints of the remaining pairs are the **seeds**, grouped by band, width-g cell and chart
identifiers in both systems. Section 6.3 (not read here) bounds how many groups meet a narrow-band ball.

## 5. Places where I would want a clarification (not claimed to be errors)

1. **Charts and disconnected regions.** 3.1 says a chart's region may be disconnected, and that its connected pieces do not get
   separate identifiers. Where does the proof use this, and where would splitting by connected piece break the probability
   estimate (3)?
2. **Common label variables.** Formula (5) needs both points in one chart. Is there a short statement of exactly which
   comparisons in Sections 6–9 are made inside one chart and which use only the global invariant? The paper has this
   information spread over 3.1, 3.2 and 3.3.
3. **Why "eligible" uses radius 5.** Radius 5 is claimed to contain every path used in the pair's local tests; a one-line
   accounting of the radii in 6.1 (radius 1 around a cell of diameter below 10D, paths up to 10D, shortest paths of d₀ < 0.02)
   would help.
4. **The interior probability 1/4 (5.2).** The failure budgets (0.21 per height test, 0.081 per radial test) are quoted without
   the computation.
5. **The role of ζ_A, E_A and the shift −4E_A.** The inequality (23) is used to turn a bound on F_C into a bound on p_C, so
   that the "7E_A" in (27) closes against ζ_A·d₀ + 7E_A < ε. A short worked chain of the constants would make 6.3 easier to read.
6. **Section 5 "vaguely".** The scaling description is mostly bookkeeping for the later estimates; it may help to move the
   statement of estimates (1)–(3) from 3.3 to the start of Section 5, or to state what each constant is *for* at the point it
   is chosen.

## 6. Not covered

Section 2 (columns, portals, two-portal property), Section 4 (interpolation by single-source distance functions,
Theorem 4.1), 6.3 onwards (the packing bound, Section 7 ordered fields, Section 8 secondary update, Section 9 assembly with
the schedule, Section 10 consequence for almost-embeddable families), and the bounded-treewidth companion paper.
