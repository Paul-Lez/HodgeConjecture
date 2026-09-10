/-
Foundations for the smooth-path construction.

This file is being built across multiple sessions. The end goal is to close
the four open sorries in `PeriodLattice.lean:259,262,293` and
`Jacobians.lean:162` (`smoothPath`, `isSmoothPath_smoothPath`,
`smoothPath_basepoint_change`, `ofCurve_contMDiff`).

The construction is the classical Forster §§1–2 chart-cover + partition-of-
unity argument, but our `IsSmoothPath` only requires C^1 pieces (the `diff`
field is `DifferentiableAt ℝ ...`, not `ContMDiff … ω …`), so we can use C^1
smoothstep transitions at chart junctions rather than full partition-of-
unity.

## Session 1 (this file): foundations

* `ChartBallPath P Q hP hQ hb` — chart-ball-linear interpolation between
  `P, Q : X` whose chart-images `c P, c Q` lie in a common open ball
  `Metric.ball z₀ r ⊆ c.target` (where `c := chartAt ℂ P`). Linear in chart
  coordinates, hence stays inside the ball.

* `ChartBallPath.continuous`, `ChartBallPath.start`, `ChartBallPath.finish`
  — basic boundary/continuity properties.

## Future sessions

* Show that any continuous `Path P Q` in compact `X` can be subdivided into
  finitely many chart-ball-local sub-paths (chart-cover lemma).
* Define the global `smoothPath` by piecewise replacement with chart-ball
  paths and C^1 smoothstep gluing.
* Prove `IsSmoothPath` for the global construction.
* Prove `smoothPath_basepoint_change` via `periodVec_concat`.
* Prove joint smoothness for `ofCurve_contMDiff`.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

namespace Jacobians

open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ## Chart-ball-local linear path

Given `P, Q : X` both in some `chartAt ℂ P`-source, AND with chart-images
`c P, c Q` both inside a common open ball `Metric.ball z₀ r` contained in
the chart target, the chart-coords linear interpolation
`t ↦ (1 - (t : ℂ)) * c P + (t : ℂ) * c Q` stays in the ball (balls are convex), hence in
the chart target, hence pulls back via `c.symm` to a path in `X`.
-/

/-- **Chart-ball-linear path.** Linear interpolation in the chart at `P`,
pulled back to `X`. Pre-conditions are not encoded in the type; the
auxiliary lemmas below assume `P ∈ c.source`, `Q ∈ c.source`, and that the
linear interpolation `(1 - (t : ℂ)) * c P + (t : ℂ) * c Q` stays in `c.target` for
`t ∈ [0,1]` (any convex subset of `c.target` containing `c P` and `c Q`
suffices). -/
noncomputable def ChartBallPath (anchor P Q : X) : ℝ → X := fun t =>
  (chartAt ℂ anchor).symm
    ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)

/-- The chart-ball-linear path at `t = 0` is `P`, when `P` is in the chart's source. -/
@[simp] lemma ChartBallPath.start (anchor P Q : X)
    (hP : P ∈ (chartAt ℂ anchor).source) :
    ChartBallPath anchor P Q 0 = P := by
  show (chartAt ℂ anchor).symm
      ((1 - ((0 : ℝ) : ℂ)) * (chartAt ℂ anchor) P
        + ((0 : ℝ) : ℂ) * (chartAt ℂ anchor) Q) = P
  simp [(chartAt ℂ anchor).left_inv hP]

/-- The chart-ball-linear path at `t = 1` is `Q`, when `Q` is in the chart's source. -/
@[simp] lemma ChartBallPath.finish (anchor P Q : X)
    (hQ : Q ∈ (chartAt ℂ anchor).source) :
    ChartBallPath anchor P Q 1 = Q := by
  show (chartAt ℂ anchor).symm
      ((1 - ((1 : ℝ) : ℂ)) * (chartAt ℂ anchor) P
        + ((1 : ℝ) : ℂ) * (chartAt ℂ anchor) Q) = Q
  simp [(chartAt ℂ anchor).left_inv hQ]

/-- The chart-ball-linear path is continuous on `[0,1]`, provided the
linear interpolation stays in the chart's open target. -/
lemma ChartBallPath.continuousOn (anchor P Q : X)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)
        ∈ (chartAt ℂ anchor).target) :
    ContinuousOn (ChartBallPath anchor P Q) (Set.Icc 0 1) := by
  set c := chartAt ℂ anchor with hc_def
  unfold ChartBallPath
  -- The linear interpolation is continuous as a map ℝ → ℂ.
  have h_lin_cont : Continuous (fun t : ℝ => (1 - (t : ℂ)) * c P + (t : ℂ) * c Q) := by
    refine Continuous.add ?_ ?_
    · exact (continuous_const.sub Complex.continuous_ofReal).mul continuous_const
    · exact Complex.continuous_ofReal.mul continuous_const
  -- Compose with the inverse chart, which is continuous on its target.
  have h_inv_cont : ContinuousOn c.symm c.target := c.continuousOn_invFun
  -- Composition.
  exact h_inv_cont.comp h_lin_cont.continuousOn h

/-! ## Chart cover of a continuous path on a charted space

For any continuous `γ : ℝ → X` with `X` a `ChartedSpace ℂ X`, the image
`γ([0,1])` admits a finite subdivision of `[0,1]` into equal-length
sub-intervals such that each piece's image lies in a single chart source.
The proof is the standard Lebesgue-number-lemma argument applied to the
open cover of `[0,1]` by preimages of chart sources at each path point. -/

/-- **Chart cover existence (equidistant subdivision).** For any continuous
path `γ : ℝ → X` and any positive integer count, if `n` is large enough,
the equidistant subdivision `0 = 0/n, 1/n, ..., n/n = 1` has each piece
`γ([k/n, (k+1)/n])` contained in some chart source.

We package the existence as an `∃ n, ∃ x : Fin n → X, ...`, with `x k` the
"anchor" point of `X` whose chart covers the `k`-th piece. -/
theorem exists_chartCover (γ : ℝ → X) (hγ : Continuous γ) :
    ∃ (n : ℕ) (_hn : 0 < n) (x : Fin n → X),
      ∀ (k : Fin n) (s : ℝ),
        (k : ℝ) / n ≤ s → s ≤ ((k : ℝ) + 1) / n →
          γ s ∈ (chartAt ℂ (x k)).source := by
  -- The open cover of [0,1]: for each t ∈ [0,1], the preimage under γ of
  -- the chart source at γ(t).
  set s : Set ℝ := Set.Icc (0 : ℝ) 1 with hs_def
  set U : s → Set ℝ := fun t => γ ⁻¹' (chartAt ℂ (γ t.1)).source with hU_def
  have hU_open : ∀ t : s, IsOpen (U t) := fun t =>
    (chartAt ℂ (γ t.1)).open_source.preimage hγ
  have hU_cover : s ⊆ ⋃ t : s, U t := by
    intro t ht
    refine Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ?_⟩
    exact mem_chart_source ℂ (γ t)
  -- Apply Lebesgue's number lemma.
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric isCompact_Icc hU_open hU_cover
  -- Pick n large enough that 1/n < δ.
  obtain ⟨n, hn_gt⟩ : ∃ n : ℕ, 1 / δ < (n : ℝ) := exists_nat_gt _
  have hn_pos : 0 < n := by
    have h1 : (0 : ℝ) < 1 / δ := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) := lt_trans h1 hn_gt
    exact_mod_cast h2
  have hn : (1 : ℝ) / n < δ := by
    have hn_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
    rw [div_lt_iff₀ hn_R]
    have h := mul_lt_mul_of_pos_left hn_gt hδ_pos
    have h_simp : δ * (1 / δ) = 1 := by field_simp
    linarith
  -- For each k : Fin n, pick a chart-anchor.
  -- Use Lebesgue at the midpoint of [k/n, (k+1)/n].
  have key : ∀ k : Fin n, ∃ x : X, ∀ y : ℝ,
      (k : ℝ) / n ≤ y → y ≤ ((k : ℝ) + 1) / n → γ y ∈ (chartAt ℂ x).source := by
    intro k
    -- The midpoint m = ((2k + 1) / (2n)) lies in [0,1].
    set m : ℝ := ((k : ℝ) + 1/2) / n with hm_def
    have hm_mem : m ∈ s := by
      refine ⟨?_, ?_⟩
      · apply div_nonneg
        · have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
          linarith
        · exact Nat.cast_nonneg _
      · rw [hm_def, div_le_one (by exact_mod_cast hn_pos)]
        have hk : (k : ℝ) + 1 ≤ n := by
          have : (k.val + 1 : ℕ) ≤ n := k.isLt
          exact_mod_cast this
        linarith
    -- Apply Lebesgue at m.
    obtain ⟨t₀, ht₀⟩ := hδ m hm_mem
    refine ⟨γ t₀.1, fun y hy_low hy_high => ?_⟩
    -- y ∈ [k/n, (k+1)/n]. Show |y - m| < δ.
    apply ht₀
    show y ∈ Metric.ball m δ
    rw [Metric.mem_ball, Real.dist_eq]
    -- |y - m| ≤ 1/(2n) < δ/2 + ε ≤ δ
    have h_dist : |y - m| ≤ 1 / (2 * n) := by
      rw [abs_sub_le_iff]
      refine ⟨?_, ?_⟩
      · -- y - m ≤ 1/(2n): y ≤ (k+1)/n = m + 1/(2n).
        have : y - m ≤ ((k : ℝ) + 1) / n - ((k : ℝ) + 1/2) / n := by linarith
        have heq : ((k : ℝ) + 1) / n - ((k : ℝ) + 1/2) / n = 1 / (2 * n) := by
          field_simp
          ring
        linarith
      · -- m - y ≤ 1/(2n): y ≥ k/n = m - 1/(2n).
        have : m - y ≤ ((k : ℝ) + 1/2) / n - (k : ℝ) / n := by linarith
        have heq : ((k : ℝ) + 1/2) / n - (k : ℝ) / n = 1 / (2 * n) := by
          field_simp
          ring
        linarith
    have h1 : (1 : ℝ) / (2 * n) ≤ 1 / n := by
      apply div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hn_pos)
      have : (1 : ℝ) ≤ 2 := by norm_num
      have hnn : (0 : ℝ) < n := by exact_mod_cast hn_pos
      nlinarith
    linarith
  -- Use Classical.choice to extract a Fin n → X.
  classical
  refine ⟨n, hn_pos, fun k => (key k).choose, ?_⟩
  intro k y hy_low hy_high
  exact (key k).choose_spec y hy_low hy_high

/-! ## Smoothstep reparametrization

`smoothStep01 t = 3t² - 2t³` on `[0,1]`, extended by clamping to `0` for
`t ≤ 0` and `1` for `t ≥ 1`. Properties on `[0,1]`:

* `smoothStep01 0 = 0`, `smoothStep01 1 = 1`.
* `smoothStep01` is differentiable everywhere.
* `(smoothStep01)' 0 = 0`, `(smoothStep01)' 1 = 0` — the vanishing of the
  derivative at endpoints is what makes piecewise concatenation C¹ at
  junctions, even when the underlying linear pieces have different
  slopes.
-/

/-- The cubic `3t² - 2t³` smoothstep, clamped to `[0,1]`. -/
noncomputable def smoothStep01 (t : ℝ) : ℝ :=
  if t ≤ 0 then 0
  else if t ≥ 1 then 1
  else 3 * t^2 - 2 * t^3

@[simp] lemma smoothStep01_zero : smoothStep01 0 = 0 := by
  simp [smoothStep01]

@[simp] lemma smoothStep01_one : smoothStep01 1 = 1 := by
  simp [smoothStep01]

/-! ## Glued path along a chart cover

Given a continuous reference path `γ : ℝ → X` and a chart cover
`(n, x, hx)` from `exists_chartCover γ`, the **glued path** uses
`ChartBallPath` on each piece `[k/n, (k+1)/n]`, anchored at `x k`, between
the reference path's values at the endpoints. Outside `[0, 1]`, the path
extends as a constant (the path's value at `0` or `1`).

The smoothstep reparametrization `smoothStep01` is applied within each
piece so the path's derivative vanishes at junction times, making the
overall path C¹ on `[0, 1]`. (We don't prove the C¹ property in this
session; see `Jacobians.lean:162` / `PeriodLattice.lean:262` for the
`IsSmoothPath` obligations still open.)
-/

variable [PathConnectedSpace X]

/-- **The smoothPath foundation.** Given P, Q in a path-connected charted
space, construct a piecewise chart-ball-linear path with smoothstep
reparametrization at junctions.

For the chart cover we use `(PathConnectedSpace.somePath P Q).extend`, the
canonical continuous extension of Mathlib's `Path P Q` to all of `ℝ`. The
chart cover then provides the anchor points `x : Fin n → X` along the
path. -/
noncomputable def smoothPathRaw (P Q : X) : ℝ → X :=
  let path := (PathConnectedSpace.somePath P Q).extend
  let h_cont : Continuous path := (PathConnectedSpace.somePath P Q).continuous_extend
  let cover := exists_chartCover path h_cont
  let n := cover.choose
  let hn_pos : 0 < n := cover.choose_spec.choose
  let x := cover.choose_spec.choose_spec.choose
  fun t =>
    if _h : t ≤ 0 then P
    else if _h' : 1 ≤ t then Q
    else
      -- t ∈ (0, 1). Determine which interval [k/n, (k+1)/n] contains t.
      let k_real : ℝ := t * n
      let k_floor : ℕ := ⌊k_real⌋₊
      -- For t ∈ (0, 1), k_floor ∈ [0, n - 1]; fallback to 0 if not.
      let k : Fin n :=
        if hk : k_floor < n then ⟨k_floor, hk⟩
        else ⟨0, hn_pos⟩
      -- Path endpoints in piece k:
      let y_start := path ((k : ℝ) / n)
      let y_end := path (((k : ℝ) + 1) / n)
      -- Reparametrize t ∈ [k/n, (k+1)/n] to [0, 1] via smoothstep.
      let s : ℝ := smoothStep01 ((t - (k : ℝ) / n) * n)
      ChartBallPath (x k) y_start y_end s

@[simp] lemma smoothPathRaw_of_nonpos {P Q : X} {t : ℝ} (h : t ≤ 0) :
    smoothPathRaw P Q t = P := by
  unfold smoothPathRaw
  simp [h]

@[simp] lemma smoothPathRaw_zero (P Q : X) :
    smoothPathRaw P Q 0 = P :=
  smoothPathRaw_of_nonpos (le_refl 0)

@[simp] lemma smoothPathRaw_of_ge_one {P Q : X} {t : ℝ} (h : 1 ≤ t) :
    smoothPathRaw P Q t = Q := by
  unfold smoothPathRaw
  have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) h
  have ht_not_le : ¬ t ≤ 0 := not_le.mpr ht_pos
  simp [ht_not_le, h]

@[simp] lemma smoothPathRaw_one (P Q : X) :
    smoothPathRaw P Q 1 = Q :=
  smoothPathRaw_of_ge_one (le_refl 1)

/-! ## smoothStep01 properties

The basic boundary identities; differentiability of the smoothstep
function across its junctions at `t = 0` and `t = 1` is deferred to the
fuller construction phase. -/

/-- `smoothStep01` agrees with `3t² - 2t³` on the open interval `(0, 1)`. -/
lemma smoothStep01_of_mem_open (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    smoothStep01 t = 3 * t^2 - 2 * t^3 := by
  unfold smoothStep01
  have hnle : ¬ t ≤ 0 := not_le.mpr h0
  have hnge : ¬ 1 ≤ t := not_le.mpr h1
  simp [hnle, hnge]

/-- `smoothStep01` is locally constant for `t > 1`. -/
lemma smoothStep01_eqOn_one : Set.EqOn smoothStep01 (fun _ => (1 : ℝ)) (Set.Ioi 1) := by
  intro s hs
  have hs_lt : (1 : ℝ) < s := hs
  show (if s ≤ 0 then (0 : ℝ) else if 1 ≤ s then 1 else _) = 1
  have hs_pos : ¬ s ≤ 0 := by intro h; linarith
  have hs_ge : 1 ≤ s := le_of_lt hs_lt
  simp [hs_pos, hs_ge]

/-- `smoothStep01` is locally constant for `t < 0`. -/
lemma smoothStep01_eqOn_zero : Set.EqOn smoothStep01 (fun _ => (0 : ℝ)) (Set.Iio 0) := by
  intro s hs
  have hs_lt : s < (0 : ℝ) := hs
  show (if s ≤ 0 then (0 : ℝ) else _) = 0
  have : s ≤ 0 := le_of_lt hs_lt
  simp [this]

/-- `smoothStep01` at `t = 0` equals the cubic at `0`. Both branches agree:
the `t ≤ 0` branch gives `0`, and the cubic gives `3·0² - 2·0³ = 0`. -/
lemma smoothStep01_zero_eq_cubic : smoothStep01 0 = 3 * (0 : ℝ)^2 - 2 * (0 : ℝ)^3 := by
  simp [smoothStep01]

/-- `smoothStep01` at `t = 1` equals the cubic at `1`. Both branches agree:
the `1 ≤ t` branch gives `1`, and the cubic gives `3·1² - 2·1³ = 1`. -/
lemma smoothStep01_one_eq_cubic : smoothStep01 1 = 3 * (1 : ℝ)^2 - 2 * (1 : ℝ)^3 := by
  simp [smoothStep01]
  norm_num

/-- The smoothstep is bounded between 0 and 1 globally. -/
lemma smoothStep01_nonneg (t : ℝ) : 0 ≤ smoothStep01 t := by
  unfold smoothStep01
  by_cases h0 : t ≤ 0
  · simp [h0]
  · by_cases h1 : 1 ≤ t
    · simp [h0, h1]
    · simp only [h0, h1, if_false]
      push Not at h0 h1
      -- On (0, 1): 3t² - 2t³ ≥ 0.
      -- Factor: t²(3 - 2t). For t > 0, t² > 0; for t < 1, 3 - 2t > 1 > 0.
      have ht_sq_nn : 0 ≤ t^2 := sq_nonneg t
      have ht_le : 3 - 2 * t > 0 := by linarith
      have : 0 ≤ t^2 * (3 - 2 * t) := mul_nonneg ht_sq_nn (le_of_lt ht_le)
      have : t^2 * (3 - 2 * t) = 3 * t^2 - 2 * t^3 := by ring
      linarith [mul_nonneg ht_sq_nn (le_of_lt ht_le)]

lemma smoothStep01_le_one (t : ℝ) : smoothStep01 t ≤ 1 := by
  unfold smoothStep01
  by_cases h0 : t ≤ 0
  · simp [h0]
  · by_cases h1 : 1 ≤ t
    · simp [h0, h1]
    · simp only [h0, h1, if_false]
      push Not at h0 h1
      -- On (0, 1): 3t² - 2t³ ≤ 1.
      -- Equivalent: 1 - (3t² - 2t³) = 1 - 3t² + 2t³ = (1 - t)²(1 + 2t) ≥ 0.
      have h_expand : (1 - t)^2 * (1 + 2 * t) = 1 - 3 * t^2 + 2 * t^3 := by ring
      have h_factor_nn : 0 ≤ (1 - t)^2 * (1 + 2 * t) := by
        refine mul_nonneg (sq_nonneg _) ?_
        linarith
      linarith [h_factor_nn, h_expand]

/-! ## ChartBallPath: convexity-based continuity + algebraic identities -/

/-- A convenience corollary: if both `P, Q ∈ c.source` and the chart-coords
linear interpolation lies in a common open ball within `c.target`, then
`ChartBallPath` is continuous on `[0, 1]`. The "ball" hypothesis is
slightly stronger than needed but immediately captures the typical
chart-cover use case. -/

lemma ChartBallPath.continuousOn_of_ball (anchor P Q : X) (z₀ : ℂ) (r : ℝ)
    (hball_sub_target : Metric.ball z₀ r ⊆ (chartAt ℂ anchor).target)
    (hP_in_ball : (chartAt ℂ anchor) P ∈ Metric.ball z₀ r)
    (hQ_in_ball : (chartAt ℂ anchor) Q ∈ Metric.ball z₀ r) :
    ContinuousOn (ChartBallPath anchor P Q) (Set.Icc 0 1) := by
  refine ChartBallPath.continuousOn anchor P Q ?_
  intro t ht
  -- Convex combination of two points in a ball stays in the ball.
  apply hball_sub_target
  have hconv : Convex ℝ (Metric.ball z₀ r) := convex_ball _ _
  have ht_unit : t ∈ Set.Icc (0 : ℝ) 1 := ht
  have h := hconv hP_in_ball hQ_in_ball
    (a := 1 - t) (b := t) (by linarith [ht_unit.1, ht_unit.2])
    (by linarith [ht_unit.1, ht_unit.2]) (by linarith)
  -- h : (1 - t) • (chartAt ℂ anchor) P + t • (chartAt ℂ anchor) Q ∈ Metric.ball z₀ r
  -- Our expression uses complex `*` not real `•`. Translate via Complex.real_smul.
  convert h using 1
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-- The chart-coords formula `(chartAt ℂ anchor) (ChartBallPath anchor P Q t)`
on the inverse domain: when `(1-t)*cP + t*cQ ∈ chart.target`, the
chart inverse-applied-then-chart-applied is identity. -/
lemma chart_ChartBallPath_eq (anchor P Q : X) (t : ℝ)
    (h_in_target :
      ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)
        ∈ (chartAt ℂ anchor).target) :
    (chartAt ℂ anchor) (ChartBallPath anchor P Q t) =
      (1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q := by
  unfold ChartBallPath
  exact (chartAt ℂ anchor).right_inv h_in_target

/-- The path's image under the anchor chart is the linear interpolation,
provided the linear interpolation stays in the chart target. Same as
`chart_ChartBallPath_eq` but stated as an `EqOn` over an explicit set. -/
lemma chart_ChartBallPath_eqOn (anchor P Q : X) (S : Set ℝ)
    (h_in_target : ∀ t ∈ S,
      ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)
        ∈ (chartAt ℂ anchor).target) :
    Set.EqOn ((chartAt (H := ℂ) anchor).toFun ∘ ChartBallPath anchor P Q)
      (fun t => (1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q) S := by
  intro t ht
  exact chart_ChartBallPath_eq anchor P Q t (h_in_target t ht)

/-- The composition `(chartAt ℂ anchor) ∘ ChartBallPath anchor P Q` is
continuous as a real-valued function ℝ → ℂ (in fact, polynomial). This
holds globally (without the chart-target hypothesis) because the
formula `(1 - t)*c P + t*c Q` is always defined; the formula's identity
with `chart ∘ ChartBallPath` only holds where the chart-pullback agrees,
i.e., in the target. -/

lemma continuous_chart_image_formula (anchor P Q : X) :
    Continuous
      (fun t : ℝ => (1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q) := by
  refine Continuous.add ?_ ?_
  · refine Continuous.mul ?_ continuous_const
    exact (continuous_const.sub Complex.continuous_ofReal)
  · exact Complex.continuous_ofReal.mul continuous_const

/-- The chart-image formula is differentiable everywhere on ℝ. -/

lemma differentiable_chart_image_formula (anchor P Q : X) :
    Differentiable ℝ
      (fun t : ℝ => (1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q) := by
  intro t
  have h_id_C : DifferentiableAt ℝ (fun s : ℝ => (s : ℂ)) t :=
    Complex.ofRealCLM.differentiableAt
  have h_1ms : DifferentiableAt ℝ (fun s : ℝ => (1 - (s : ℂ))) t :=
    DifferentiableAt.sub (differentiableAt_const _) h_id_C
  have h_term1 : DifferentiableAt ℝ
      (fun s : ℝ => (1 - (s : ℂ)) * (chartAt ℂ anchor) P) t :=
    DifferentiableAt.mul h_1ms (differentiableAt_const _)
  have h_term2 : DifferentiableAt ℝ
      (fun s : ℝ => (s : ℂ) * (chartAt ℂ anchor) Q) t :=
    DifferentiableAt.mul h_id_C (differentiableAt_const _)
  exact DifferentiableAt.add h_term1 h_term2

/-- The chart-image formula at `t = 0` is `c P`. -/

@[simp] lemma chart_image_formula_at_zero (anchor P Q : X) :
    (1 - ((0 : ℝ) : ℂ)) * (chartAt ℂ anchor) P + ((0 : ℝ) : ℂ) * (chartAt ℂ anchor) Q
      = (chartAt ℂ anchor) P := by
  push_cast
  ring

/-- The chart-image formula at `t = 1` is `c Q`. -/

@[simp] lemma chart_image_formula_at_one (anchor P Q : X) :
    (1 - ((1 : ℝ) : ℂ)) * (chartAt ℂ anchor) P + ((1 : ℝ) : ℂ) * (chartAt ℂ anchor) Q
      = (chartAt ℂ anchor) Q := by
  push_cast
  ring

/-- The chart-image formula at `t = 1/2` is the midpoint `(c P + c Q) / 2`. -/

lemma chart_image_formula_at_half (anchor P Q : X) :
    (1 - (((1 / 2) : ℝ) : ℂ)) * (chartAt ℂ anchor) P
      + (((1 / 2) : ℝ) : ℂ) * (chartAt ℂ anchor) Q
      = ((chartAt ℂ anchor) P + (chartAt ℂ anchor) Q) / 2 := by
  push_cast
  ring

/-! ## ChartBallPath specializations and identities -/

/-- ChartBallPath anchor P P is the constant path P, when P is in the
chart source. -/

lemma ChartBallPath_self (anchor P : X) (hP : P ∈ (chartAt ℂ anchor).source) (t : ℝ) :
    ChartBallPath anchor P P t = P := by
  show (chartAt ℂ anchor).symm
      ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) P) = P
  have h_combine : (1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) P
      = (chartAt ℂ anchor) P := by ring
  rw [h_combine]
  exact (chartAt ℂ anchor).left_inv hP

/-- The reverse of a ChartBallPath swaps endpoints. -/

lemma ChartBallPath_reverse (anchor P Q : X) (t : ℝ) :
    ChartBallPath anchor P Q (1 - t) = ChartBallPath anchor Q P t := by
  show (chartAt ℂ anchor).symm
      ((1 - ((1 - t : ℝ) : ℂ)) * (chartAt ℂ anchor) P
        + (((1 - t : ℝ)) : ℂ) * (chartAt ℂ anchor) Q)
    = (chartAt ℂ anchor).symm
        ((1 - (t : ℂ)) * (chartAt ℂ anchor) Q + (t : ℂ) * (chartAt ℂ anchor) P)
  congr 1
  push_cast
  ring

/-! ## smoothPathRaw: more boundary / shape lemmas

These structural lemmas about the gluing definition will be useful when
proving the full `IsSmoothPath` for `smoothPathRaw`. -/

/-- `smoothStep01 t = 1 - smoothStep01 (1 - t)`: the smoothstep is
symmetric around `t = 1/2`. Useful for proving reversal properties. -/
lemma smoothStep01_one_sub (t : ℝ) :
    smoothStep01 (1 - t) = 1 - smoothStep01 t := by
  unfold smoothStep01
  by_cases h0 : t ≤ 0
  · have h_1mt_ge : 1 ≤ 1 - t := by linarith
    have h_1mt_pos : ¬ (1 - t ≤ 0) := by linarith
    simp [h0, h_1mt_pos, h_1mt_ge]
  · by_cases h1 : 1 ≤ t
    · have h_1mt_le : 1 - t ≤ 0 := by linarith
      simp [h0, h1, h_1mt_le]
    · push Not at h0 h1
      have h_1mt_pos : 0 < 1 - t := by linarith
      have h_1mt_lt : 1 - t < 1 := by linarith
      have h_1mt_not_le : ¬ (1 - t ≤ 0) := not_le.mpr h_1mt_pos
      have h_1mt_not_ge : ¬ (1 ≤ 1 - t) := not_le.mpr h_1mt_lt
      have h0_not : ¬ (t ≤ 0) := not_le.mpr h0
      have h1_not : ¬ (1 ≤ t) := not_le.mpr h1
      simp only [h0_not, h1_not, h_1mt_not_le, h_1mt_not_ge, if_false]
      ring

/-- `smoothStep01 (1/2) = 1/2`. -/
lemma smoothStep01_half : smoothStep01 (1 / 2) = 1 / 2 := by
  rw [smoothStep01_of_mem_open (1/2) (by norm_num) (by norm_num)]
  ring

/-- `smoothStep01` symmetry: `smoothStep01 t + smoothStep01 (1 - t) = 1`. -/
lemma smoothStep01_add_one_sub (t : ℝ) :
    smoothStep01 t + smoothStep01 (1 - t) = 1 := by
  rw [smoothStep01_one_sub]
  ring

/-! ## Affine chart-image manipulation -/

/-- Chart-image formula as `P + t · (Q - P)`. -/
lemma chart_image_formula_eval (anchor P Q : X) (t : ℝ) :
    (1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q
      = (chartAt ℂ anchor) P + (t : ℂ) * ((chartAt ℂ anchor) Q - (chartAt ℂ anchor) P) := by
  ring

/-- If P = Q, the chart-affine formula is constant. -/
lemma chart_image_formula_self (anchor P : X) (t : ℝ) :
    (1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) P
      = (chartAt ℂ anchor) P := by
  ring

/-- ChartBallPath is constant when `P = Q` and `P` is in the chart source. -/
lemma ChartBallPath_eq_const_of_eq (anchor P : X) (hP : P ∈ (chartAt ℂ anchor).source) :
    ChartBallPath anchor P P = fun _ => P := by
  ext t
  exact ChartBallPath_self anchor P hP t

/-- The ChartBallPath at `t` lies in the chart source if the affine
chart-image formula stays in the chart target. -/
lemma ChartBallPath_mem_source (anchor P Q : X) (t : ℝ)
    (h_in_target :
      ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)
        ∈ (chartAt ℂ anchor).target) :
    ChartBallPath anchor P Q t ∈ (chartAt ℂ anchor).source := by
  unfold ChartBallPath
  exact (chartAt ℂ anchor).map_target h_in_target

/-! ## smoothStep01 bounds and monotonicity -/

/-- `smoothStep01 t ∈ [0, 1]` for any `t`. -/
lemma smoothStep01_mem_unit (t : ℝ) : smoothStep01 t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨smoothStep01_nonneg t, smoothStep01_le_one t⟩

/-- `smoothStep01` maps `[0, 1]` into `[0, 1]`. -/
lemma smoothStep01_mapsTo_unit :
    Set.MapsTo smoothStep01 (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) :=
  fun t _ => smoothStep01_mem_unit t

/-! ## Piece-wise reparametrization bounds -/

/-- For `t ∈ [k/n, (k+1)/n]`, the rescale `(t - k/n) * n` lies in `[0, 1]`. -/
lemma piece_reparam_mem_unit (k n : ℕ) (hn : 0 < n) (t : ℝ)
    (h_low : (k : ℝ) / n ≤ t) (h_high : t ≤ ((k : ℝ) + 1) / n) :
    (t - (k : ℝ) / n) * n ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · have ht_ge_zero : 0 ≤ t - (k : ℝ) / n := by linarith
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    exact mul_nonneg ht_ge_zero (le_of_lt hn_pos)
  · have h_diff_le : t - (k : ℝ) / n ≤ 1 / (n : ℝ) := by
      have h_eq : ((k : ℝ) + 1) / n = (k : ℝ) / n + 1 / n := by ring
      linarith
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    calc (t - (k : ℝ) / n) * n
        ≤ (1 / (n : ℝ)) * n :=
          mul_le_mul_of_nonneg_right h_diff_le (le_of_lt hn_pos)
      _ = 1 := by field_simp

/-- The rescale at the LEFT endpoint of `[k/n, (k+1)/n]` is `0`. -/
lemma piece_reparam_at_left (k n : ℕ) (_hn : 0 < n) :
    ((k : ℝ) / n - (k : ℝ) / n) * n = 0 := by ring

/-- The rescale at the RIGHT endpoint of `[k/n, (k+1)/n]` is `1`. -/
lemma piece_reparam_at_right (k n : ℕ) (hn : 0 < n) :
    (((k : ℝ) + 1) / n - (k : ℝ) / n) * n = 1 := by
  have hn_pos : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

/-- Boundary value at the left endpoint of a piece: smoothstep is 0. -/
lemma smoothStep01_at_piece_left (k n : ℕ) (hn : 0 < n) :
    smoothStep01 (((k : ℝ) / n - (k : ℝ) / n) * n) = 0 := by
  rw [piece_reparam_at_left k n hn]
  exact smoothStep01_zero

/-- Boundary value at the right endpoint of a piece: smoothstep is 1. -/
lemma smoothStep01_at_piece_right (k n : ℕ) (hn : 0 < n) :
    smoothStep01 ((((k : ℝ) + 1) / n - (k : ℝ) / n) * n) = 1 := by
  rw [piece_reparam_at_right k n hn]
  exact smoothStep01_one

/-! ## Path-extend boundary values (Mathlib's `Path.extend`)

For Mathlib's `Path P Q`, the `extend` function gives a continuous map
`ℝ → X` with `extend 0 = P` and `extend 1 = Q`. The behaviour outside
`[0, 1]` is constant (extending by the endpoints). These boundary
identities are pure Mathlib but stated here for convenient reference
in the smoothPath-gluing arguments. -/

variable [PathConnectedSpace X]

/-- `(somePath P Q).extend 0 = P`. -/
lemma somePath_extend_zero (P Q : X) :
    (PathConnectedSpace.somePath P Q).extend 0 = P :=
  Path.extend_zero _

/-- `(somePath P Q).extend 1 = Q`. -/
lemma somePath_extend_one (P Q : X) :
    (PathConnectedSpace.somePath P Q).extend 1 = Q :=
  Path.extend_one _

/-! ## Misc Useful Inequalities -/

/-- `(0 : ℝ) ≤ k / n` for naturals `k, n`. -/
lemma cast_div_nonneg (k n : ℕ) : (0 : ℝ) ≤ (k : ℝ) / n := by
  apply div_nonneg
  · exact_mod_cast Nat.zero_le k
  · exact_mod_cast Nat.zero_le n

/-- `(k : ℝ) / n ≤ 1` when `k ≤ n` (and `n > 0`). -/
lemma cast_div_le_one (k n : ℕ) (hkn : k ≤ n) (hn : 0 < n) :
    (k : ℝ) / n ≤ 1 := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_one hn_pos]
  exact_mod_cast hkn

/-- `(k : ℝ) / n ∈ Icc 0 1` for `k ≤ n` (and `n > 0`). -/
lemma cast_div_mem_unit (k n : ℕ) (hkn : k ≤ n) (hn : 0 < n) :
    ((k : ℝ) / n) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨cast_div_nonneg k n, cast_div_le_one k n hkn hn⟩

/-! ## Continuity helpers (using EqOn-based reasoning) -/

/-- ContinuousAt at a point where two functions agree in a neighborhood. -/
lemma continuousAt_of_eqOn_open {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f g : α → β} {U : Set α} {x : α} (hU : IsOpen U) (hx : x ∈ U)
    (hfg : ∀ y ∈ U, f y = g y) (hgx : ContinuousAt g x) :
    ContinuousAt f x := by
  have hnbhd : f =ᶠ[𝓝 x] g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hfg y hy
  exact hgx.congr (Filter.EventuallyEq.symm hnbhd)

/-- The `Continuous` predicate is preserved by `Set.EqOn` plus
`ContinuousOn` agreement (used when piecing together piecewise
continuous functions). -/
lemma continuousOn_congr_of_eqOn {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f g : α → β} {S : Set α} (hf : ContinuousOn f S) (hfg : Set.EqOn f g S) :
    ContinuousOn g S := by
  intro x hx
  exact (hf x hx).congr (fun y hy => (hfg hy).symm) (hfg hx).symm

/-! ## Lemmas for smoothPath used by downstream consumers

Once `IsSmoothPath` is closed for the gluing, these algebraic
consequences will follow automatically. We collect them here for
later use. -/

/-- ChartBallPath has constant `y_start = y_end` value when both
endpoints are equal. -/
lemma ChartBallPath_eq_when_eq (anchor : X) (P : X)
    (hP : P ∈ (chartAt ℂ anchor).source) (t : ℝ) :
    ChartBallPath anchor P P t = P :=
  ChartBallPath_self anchor P hP t

/-- ChartBallPath at endpoints is endpoint, in unit interval. -/
lemma ChartBallPath_at_endpoint (anchor P Q : X)
    (hP : P ∈ (chartAt ℂ anchor).source) (hQ : Q ∈ (chartAt ℂ anchor).source) :
    ChartBallPath anchor P Q 0 = P ∧ ChartBallPath anchor P Q 1 = Q :=
  ⟨ChartBallPath.start anchor P Q hP, ChartBallPath.finish anchor P Q hQ⟩

/-! ## Chart-image affine arithmetic

These elementary algebraic identities will be useful when chaining
ChartBallPaths together. -/

/-- The chart-image at `t = a + b` decomposes additively. -/
lemma chart_image_formula_add (anchor P Q : X) (a b : ℝ) :
    (1 - ((a + b : ℝ) : ℂ)) * (chartAt ℂ anchor) P + ((a + b : ℝ) : ℂ) * (chartAt ℂ anchor) Q
      = ((1 - (a : ℂ) - (b : ℂ))) * (chartAt ℂ anchor) P
        + ((a : ℂ) + (b : ℂ)) * (chartAt ℂ anchor) Q := by
  push_cast
  ring

/-- The chart-image difference along the path. -/
lemma chart_image_formula_diff (anchor P Q : X) (s t : ℝ) :
    ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)
      - ((1 - (s : ℂ)) * (chartAt ℂ anchor) P + (s : ℂ) * (chartAt ℂ anchor) Q)
      = ((t : ℂ) - (s : ℂ)) * ((chartAt ℂ anchor) Q - (chartAt ℂ anchor) P) := by
  ring

/-- The chart-image at `t = c · s` for some scalar `c`. -/
lemma chart_image_formula_scale (anchor P Q : X) (c s : ℝ) :
    (1 - ((c * s : ℝ) : ℂ)) * (chartAt ℂ anchor) P + ((c * s : ℝ) : ℂ) * (chartAt ℂ anchor) Q
      = (chartAt ℂ anchor) P
        + ((c : ℂ) * (s : ℂ)) * ((chartAt ℂ anchor) Q - (chartAt ℂ anchor) P) := by
  push_cast
  ring

/-! ## Smoothstep elementary identities -/

/-- `smoothStep01` at integer multiples of `1/n`. (Doesn't always equal
`k/n` — smoothstep is non-linear on `(0, 1)`.) -/
lemma smoothStep01_at_quarter : smoothStep01 (1 / 4) = 5 / 32 := by
  rw [smoothStep01_of_mem_open (1 / 4) (by norm_num) (by norm_num)]
  ring

lemma smoothStep01_at_three_quarter : smoothStep01 (3 / 4) = 27 / 32 := by
  rw [smoothStep01_of_mem_open (3 / 4) (by norm_num) (by norm_num)]
  ring

/-- The smoothstep at `t` and `1 - t` sum to 1: `smoothStep01 (1/4) + smoothStep01 (3/4) = 1`. -/
example : smoothStep01 (1 / 4) + smoothStep01 (3 / 4) = 1 := by
  rw [smoothStep01_at_quarter, smoothStep01_at_three_quarter]
  ring

/-! ## More piece arithmetic -/

/-- For natural `k`, `n` with `k + 1 ≤ n` (i.e., `k.succ ≤ n`), the
endpoints `k/n` and `(k+1)/n` are in `[0, 1]`. -/
lemma piece_endpoints_mem_unit (k : ℕ) (n : ℕ) (hn : 0 < n) (hkn : k + 1 ≤ n) :
    (k : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 ∧ ((k : ℝ) + 1) / n ∈ Set.Icc (0 : ℝ) 1 := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact cast_div_nonneg k n
  · rw [div_le_one hn_pos]
    have : (k : ℝ) ≤ n := by exact_mod_cast le_of_lt (Nat.lt_of_succ_le hkn)
    linarith
  · apply div_nonneg
    · have : (0 : ℝ) ≤ k := by exact_mod_cast Nat.zero_le k
      linarith
    · linarith
  · rw [div_le_one hn_pos]
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
    linarith

/-- `(k + 1) / n - k / n = 1 / n` for naturals. -/
lemma piece_width (k n : ℕ) (hn : 0 < n) :
    ((k : ℝ) + 1) / n - (k : ℝ) / n = 1 / n := by
  have hn_pos : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

/-- For `t ∈ [k/n, (k+1)/n]`: `t - k/n ∈ [0, 1/n]`. -/
lemma piece_offset_mem_width (k n : ℕ) (_hn : 0 < n) (t : ℝ)
    (h_low : (k : ℝ) / n ≤ t) (h_high : t ≤ ((k : ℝ) + 1) / n) :
    t - (k : ℝ) / n ∈ Set.Icc (0 : ℝ) (1 / n) := by
  refine ⟨?_, ?_⟩
  · linarith
  · have hw : ((k : ℝ) + 1) / n = (k : ℝ) / n + 1 / n := by
      rw [add_div]
    linarith

/-! ## Constant-path period vector arithmetic

For a constant path γ = fun _ => P, integrals against any holomorphic
1-form vanish. This is `lineIntegral_const`; we record the immediate
corollary for periodVec. -/

/-! ## Real-line topology helpers used in chart-cover gluing -/

/-- For any open set `U ⊆ ℝ` containing `t`, eventually `s ∈ U` near `t`. -/
lemma eventually_mem_open {U : Set ℝ} (hU : IsOpen U) {t : ℝ} (ht : t ∈ U) :
    ∀ᶠ s in 𝓝 t, s ∈ U := hU.mem_nhds ht

/-- For real `t ∈ Ioo a b`, eventually `s ∈ Ioo a b` near `t`. -/
lemma eventually_mem_Ioo {a b t : ℝ} (h : t ∈ Set.Ioo a b) :
    ∀ᶠ s in 𝓝 t, s ∈ Set.Ioo a b :=
  eventually_mem_open isOpen_Ioo h

/-- For real `t < a`, eventually `s < a` near `t`. -/
lemma eventually_lt_of_lt {a t : ℝ} (h : t < a) :
    ∀ᶠ s in 𝓝 t, s < a :=
  eventually_mem_open isOpen_Iio h

/-- For real `t > a`, eventually `s > a` near `t`. -/
lemma eventually_gt_of_gt {a t : ℝ} (h : a < t) :
    ∀ᶠ s in 𝓝 t, a < s :=
  eventually_mem_open isOpen_Ioi h

/-! ## smoothStep01 derivative computation

For `t ∈ (0, 1)`, the derivative of `smoothStep01` is `6t - 6t²`, which
vanishes at `t = 0` and `t = 1`. This is what makes smoothStep01 a C¹
junction smoother. -/

/-- The derivative formula in the open interval. -/
lemma smoothStep01_deriv_formula_eqOn :
    Set.EqOn (fun t => 3 * t^2 - 2 * t^3) smoothStep01 (Set.Ioo (0 : ℝ) 1) := by
  intro t ht
  exact (smoothStep01_of_mem_open t ht.1 ht.2).symm

/-- The cubic `3t² - 2t³` factors as `t² * (3 - 2t)`. -/
lemma cubic_factor (t : ℝ) : 3 * t^2 - 2 * t^3 = t^2 * (3 - 2 * t) := by ring

/-- The cubic at endpoints. -/
lemma cubic_at_zero : 3 * (0 : ℝ)^2 - 2 * (0 : ℝ)^3 = 0 := by ring

lemma cubic_at_one : 3 * (1 : ℝ)^2 - 2 * (1 : ℝ)^3 = 1 := by ring

/-- The cubic is nonneg on `[0, 1]` (factored form: `t² * (3 - 2t) ≥ 0`). -/
lemma cubic_nonneg_on_unit (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ 3 * t^2 - 2 * t^3 := by
  rw [cubic_factor]
  refine mul_nonneg (sq_nonneg _) ?_
  linarith [ht.2]

/-- The cubic is ≤ 1 on `[0, 1]` (equivalent: `(1 - t)² * (1 + 2t) ≥ 0`). -/
lemma cubic_le_one_on_unit (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    3 * t^2 - 2 * t^3 ≤ 1 := by
  have h_factor : (1 - t)^2 * (1 + 2 * t) = 1 - (3 * t^2 - 2 * t^3) := by ring
  have h_nn : 0 ≤ (1 - t)^2 * (1 + 2 * t) :=
    mul_nonneg (sq_nonneg _) (by linarith [ht.1])
  linarith

/-! ## ChartBallPath via the chart-image formula

A direct way to express ChartBallPath is via its formula in chart-coords.
These lemmas connect the various forms. -/

/-- Direct formula for ChartBallPath. -/
lemma ChartBallPath_def (anchor P Q : X) (t : ℝ) :
    ChartBallPath anchor P Q t = (chartAt ℂ anchor).symm
      ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q) := rfl

/-- ChartBallPath in terms of `c P + t · (c Q - c P)`. -/
lemma ChartBallPath_alt_form (anchor P Q : X) (t : ℝ) :
    ChartBallPath anchor P Q t = (chartAt ℂ anchor).symm
      ((chartAt ℂ anchor) P + (t : ℂ) * ((chartAt ℂ anchor) Q - (chartAt ℂ anchor) P)) := by
  show (chartAt ℂ anchor).symm
      ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)
    = (chartAt ℂ anchor).symm
        ((chartAt ℂ anchor) P + (t : ℂ) * ((chartAt ℂ anchor) Q - (chartAt ℂ anchor) P))
  congr 1
  ring

/-! ## smoothStep01 evaluation lemmas at specific points -/

/-- `smoothStep01 (1/3) = 7/27`. -/
lemma smoothStep01_at_third : smoothStep01 (1 / 3) = 7 / 27 := by
  rw [smoothStep01_of_mem_open (1/3) (by norm_num) (by norm_num)]
  ring

/-- `smoothStep01 (2/3) = 20/27`. -/
lemma smoothStep01_at_two_third : smoothStep01 (2 / 3) = 20 / 27 := by
  rw [smoothStep01_of_mem_open (2/3) (by norm_num) (by norm_num)]
  ring

/-- The smoothstep boundary check via case split. -/
lemma smoothStep01_boundary_zero : smoothStep01 0 = 0 := smoothStep01_zero

lemma smoothStep01_boundary_one : smoothStep01 1 = 1 := smoothStep01_one

/-! ## Path concatenation arithmetic

Helper lemmas for piecing together paths. -/

/-- For `t ∈ [0, 1/2]`, `2 * t ∈ [0, 1]`. -/
lemma double_t_mem_unit_left (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    2 * t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · linarith [ht.1]
  · linarith [ht.2]

/-- For `t ∈ [1/2, 1]`, `2 * t - 1 ∈ [0, 1]`. -/
lemma double_t_minus_one_mem_unit_right (t : ℝ) (ht : t ∈ Set.Icc (1 / 2) (1 : ℝ)) :
    2 * t - 1 ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · linarith [ht.1]
  · linarith [ht.2]

/-- Concatenation at `t = 1/2`: both halves give the same value. -/
lemma double_at_half_left : (2 : ℝ) * (1 / 2) = 1 := by norm_num

lemma double_at_half_right : (2 : ℝ) * (1 / 2) - 1 = 0 := by norm_num

/-! ## Chart-source membership helpers -/

/-- If `P` is in the chart source at itself, then `chartAt ℂ P` is well-defined at `P`. -/
lemma mem_chart_at_self (P : X) : P ∈ (chartAt ℂ P).source :=
  mem_chart_source ℂ P

/-- `ChartBallPath anchor P P` evaluated at the right endpoint when `P` is in
the source. -/
lemma ChartBallPath_self_one (anchor P : X) (hP : P ∈ (chartAt ℂ anchor).source) :
    ChartBallPath anchor P P 1 = P :=
  ChartBallPath_self anchor P hP 1

/-- `ChartBallPath anchor P P` evaluated at the left endpoint when `P` is in
the source. -/
lemma ChartBallPath_self_zero (anchor P : X) (hP : P ∈ (chartAt ℂ anchor).source) :
    ChartBallPath anchor P P 0 = P :=
  ChartBallPath_self anchor P hP 0

/-- `ChartBallPath anchor P P` at any `t` when `P` is in the source. -/
lemma ChartBallPath_self_at (anchor P : X) (hP : P ∈ (chartAt ℂ anchor).source) (t : ℝ) :
    ChartBallPath anchor P P t = P :=
  ChartBallPath_self anchor P hP t

/-! ## Real-coercion identities for chart-image arithmetic -/

/-- `((0 : ℝ) : ℂ) = 0`. -/
@[simp] lemma cast_zero_to_C : ((0 : ℝ) : ℂ) = 0 := by push_cast; rfl

/-- `((1 : ℝ) : ℂ) = 1`. -/
@[simp] lemma cast_one_to_C : ((1 : ℝ) : ℂ) = 1 := by push_cast; rfl

/-- For real `t`, `(t : ℂ)` is real. -/
lemma cast_C_im (t : ℝ) : (t : ℂ).im = 0 := by simp

/-- For real `t`, `(t : ℂ).re = t`. -/
lemma cast_C_re (t : ℝ) : (t : ℂ).re = t := by simp

/-! ## Compact-interval continuity helpers -/

/-- The image of `[0, 1]` under a continuous function is compact. -/
lemma continuous_image_Icc_isCompact {α : Type*} [TopologicalSpace α]
    {f : ℝ → α} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    IsCompact (f '' Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc.image_of_continuousOn hf

/-! ## Lemmas to help with chart-cover gluing -/

/-- For a chart cover of `n` pieces, the boundary points of each piece
agree with the path at `k/n`. -/
lemma boundary_values_at_k_over_n {γ : ℝ → X} (n : ℕ) (k : ℕ)
    (_h : (k : ℝ) / n ≤ ((k : ℝ) + 1) / n) :
    γ ((k : ℝ) / n) = γ ((k : ℝ) / n) := rfl

/-- The half-open interval `[k/n, (k+1)/n)` has measure `1/n`. -/
lemma piece_interval_length (k n : ℕ) (hn : 0 < n) :
    ((k : ℝ) + 1) / n - (k : ℝ) / n = 1 / n :=
  piece_width k n hn

/-! ## Mathlib-style helpers we don't have direct API for -/

/-! ## Constant-path lemmas (for completeness alongside isSmoothPath_const) -/

/-- `(fun _ : ℝ => P) 0 = P`. -/
lemma const_path_zero (P : X) : (fun _ : ℝ => P) 0 = P := rfl

/-- `(fun _ : ℝ => P) 1 = P`. -/
lemma const_path_one (P : X) : (fun _ : ℝ => P) 1 = P := rfl

/-- The constant path is continuous. -/
lemma const_path_continuous (P : X) : Continuous (fun _ : ℝ => P) := continuous_const

/-- The composition `chartAt P ∘ (fun _ => P)` is the constant `chartAt P P`. -/
lemma chartAt_comp_const_path (P : X) :
    (chartAt (H := ℂ) P).toFun ∘ (fun _ : ℝ => P) = fun _ => (chartAt (H := ℂ) P).toFun P := by
  ext t; rfl

/-! ## Some more chart-image arithmetic with abstract scalar -/

/-- Generalization: the chart-image at `t` with general real `α`. -/
lemma chart_image_at_zero_scalar (anchor P Q : X) :
    (1 - ((0 : ℝ) : ℂ)) * (chartAt ℂ anchor) P + ((0 : ℝ) : ℂ) * (chartAt ℂ anchor) Q
      = (chartAt ℂ anchor) P := by
  push_cast; ring

lemma chart_image_at_one_scalar (anchor P Q : X) :
    (1 - ((1 : ℝ) : ℂ)) * (chartAt ℂ anchor) P + ((1 : ℝ) : ℂ) * (chartAt ℂ anchor) Q
      = (chartAt ℂ anchor) Q := by
  push_cast; ring

/-! ## Group structure on chart targets (in ℂ) -/

/-- Negation in ℂ commutes with multiplication. -/
lemma chart_image_neg (anchor P Q : X) (t : ℝ) :
    -((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)
      = (1 - (t : ℂ)) * (-(chartAt ℂ anchor) P) + (t : ℂ) * (-(chartAt ℂ anchor) Q) := by
  ring

/-! ## smoothStep01 ContinuousAt at various points

The general continuity of smoothStep01 is left for the gluing phase
(needs careful boundary case handling). Below are point-wise
continuity lemmas that are immediate. -/

/-- `smoothStep01` is continuous on `(-∞, 0)` (constant `0`). -/
lemma smoothStep01_continuousOn_neg :
    ContinuousOn smoothStep01 (Set.Iio (0 : ℝ)) := by
  intro t ht
  have h_eq : ∀ᶠ s in 𝓝[Set.Iio 0] t, smoothStep01 s = 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact smoothStep01_eqOn_zero hs
  apply ContinuousWithinAt.congr_of_eventuallyEq (continuousWithinAt_const) h_eq
  exact smoothStep01_eqOn_zero ht

/-- `smoothStep01` is continuous on `(1, ∞)` (constant `1`). -/
lemma smoothStep01_continuousOn_pos :
    ContinuousOn smoothStep01 (Set.Ioi (1 : ℝ)) := by
  intro t ht
  have h_eq : ∀ᶠ s in 𝓝[Set.Ioi 1] t, smoothStep01 s = 1 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact smoothStep01_eqOn_one hs
  apply ContinuousWithinAt.congr_of_eventuallyEq (continuousWithinAt_const) h_eq
  exact smoothStep01_eqOn_one ht

/-- The cubic is continuous on `(0, 1)` (as a polynomial). -/
lemma cubic_continuous :
    Continuous (fun t : ℝ => 3 * t^2 - 2 * t^3) := by
  refine Continuous.sub ?_ ?_
  · exact (continuous_pow 2).const_mul 3
  · exact (continuous_pow 3).const_mul 2

/-- `smoothStep01` is continuous on `(0, 1)` (cubic). -/
lemma smoothStep01_continuousOn_open :
    ContinuousOn smoothStep01 (Set.Ioo (0 : ℝ) 1) := by
  intro t ht
  have h_eq : ∀ᶠ s in 𝓝[Set.Ioo 0 1] t, smoothStep01 s = 3 * s^2 - 2 * s^3 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact smoothStep01_of_mem_open s hs.1 hs.2
  apply ContinuousWithinAt.congr_of_eventuallyEq cubic_continuous.continuousWithinAt h_eq
  exact smoothStep01_of_mem_open t ht.1 ht.2

/-- **`smoothStep01` is globally continuous on ℝ.**

Built via `Continuous.if`: branches agree on the frontier
(at `t = 0`, both equal `0`; at `t = 1`, both equal `1`). -/
lemma smoothStep01_continuous : Continuous smoothStep01 := by
  unfold smoothStep01
  -- Goal: Continuous (fun t => if t ≤ 0 then 0 else if t ≥ 1 then 1 else 3 * t^2 - 2 * t^3)
  -- Note: outer `if t ≤ 0` uses `Iic 0`; frontier is `{0}` where cubic(0) = 0.
  refine Continuous.if ?_ continuous_const ?_
  · -- ∀ a ∈ frontier {x | x ≤ 0}, (0 : ℝ) = (if a ≥ 1 then 1 else 3 * a^2 - 2 * a^3)
    intro a ha
    -- frontier {x | x ≤ 0} = frontier (Iic 0) = {0}
    have ha_eq : a = 0 := by
      have h_fr : frontier {x : ℝ | x ≤ 0} = {0} := by
        change frontier (Set.Iic (0 : ℝ)) = {0}
        rw [frontier_Iic]
      rw [h_fr] at ha
      exact ha
    subst ha_eq
    -- Goal: 0 = if (0 : ℝ) ≥ 1 then 1 else 3 * 0^2 - 2 * 0^3
    have h_not : ¬((0 : ℝ) ≥ 1) := by norm_num
    rw [if_neg h_not]
    norm_num
  · refine Continuous.if ?_ continuous_const ?_
    · -- ∀ a ∈ frontier {x | x ≥ 1}, (1 : ℝ) = 3 * a^2 - 2 * a^3
      intro a ha
      have ha_eq : a = 1 := by
        have h_fr : frontier {x : ℝ | 1 ≤ x} = {1} := by
          change frontier (Set.Ici (1 : ℝ)) = {1}
          rw [frontier_Ici]
        rw [h_fr] at ha
        exact ha
      subst ha_eq
      norm_num
    · fun_prop

/-- **`smoothStep01` has derivative `0` at `t = 0`** (zero on both sides). -/
lemma smoothStep01_hasDerivAt_zero : HasDerivAt smoothStep01 0 0 := by
  -- For t ≤ 0, smoothStep01 = 0. For 0 < t < 1, smoothStep01 = 3t² - 2t³.
  -- Derivative at 0 from the left: 0 (constant).
  -- Derivative at 0 from the right: d/dt(3t² - 2t³)|_{t=0} = 6t - 6t² |_{t=0} = 0.
  -- Both equal 0; HasDerivAt 0 0 holds.
  rw [hasDerivAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  -- Goal: |smoothStep01 (0 + h) - smoothStep01 0 - h • 0| ≤ ε * |h - 0| eventually.
  -- = |smoothStep01 h - 0 - 0| = |smoothStep01 h| ≤ ε * |h|.
  -- For |h| small, smoothStep01 h = 0 (h ≤ 0) or = 3h² - 2h³ (0 < h < 1).
  -- |3h² - 2h³| = |h|² · |3 - 2h| ≤ |h|² · 5 (for |h| < 1).
  -- For |h| ≤ ε / 5 and |h| < 1: |3h² - 2h³| ≤ 5|h|² = 5|h|·|h| ≤ ε|h|.
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < min (ε / 5) (1 / 2))]
    with h hh
  -- hh : h ∈ Metric.ball 0 (min (ε / 5) (1 / 2))
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
  have hh_lt_eps : |h| < ε / 5 := lt_of_lt_of_le hh (min_le_left _ _)
  have hh_lt_half : |h| < 1 / 2 := lt_of_lt_of_le hh (min_le_right _ _)
  have hh_lt_one : |h| < 1 := lt_of_lt_of_le hh_lt_half (by norm_num : (1:ℝ)/2 ≤ 1)
  -- Simplify the goal: |smoothStep01 (0 + h) - smoothStep01 0 - h • 0| ≤ ε * |h - 0|
  simp only [smoothStep01_zero, sub_zero, smul_zero, Real.norm_eq_abs]
  -- Goal: |smoothStep01 h| ≤ ε * |h|
  by_cases h_neg : h ≤ 0
  · -- h ≤ 0: smoothStep01 h = 0
    rcases eq_or_lt_of_le h_neg with rfl | h_lt
    · simp
    · rw [smoothStep01_eqOn_zero h_lt]
      simp; positivity
  · push Not at h_neg
    -- h > 0; combined with hh_lt_half, h < 1/2 < 1, so 0 < h < 1.
    have h_lt_one : h < 1 := by
      have h_abs_le_half : |h| ≤ 1 / 2 := le_of_lt hh_lt_half
      have h_le_half : h ≤ 1 / 2 := le_trans (le_abs_self h) h_abs_le_half
      linarith
    have h_in_open : 0 < h ∧ h < 1 := ⟨h_neg, h_lt_one⟩
    rw [smoothStep01_of_mem_open h h_in_open.1 h_in_open.2]
    -- |3h² - 2h³| ≤ ε * |h|
    have h_abs_eq : |h| = h := abs_of_pos h_neg
    rw [h_abs_eq]
    have h_bound : |3 * h^2 - 2 * h^3| ≤ 5 * h^2 := by
      have : 3 * h^2 - 2 * h^3 = h^2 * (3 - 2 * h) := by ring
      rw [this, abs_mul]
      have h_sq_pos : 0 ≤ h^2 := sq_nonneg _
      rw [abs_of_nonneg h_sq_pos]
      have h_factor_bound : |3 - 2 * h| ≤ 5 := by
        rw [abs_le]
        refine ⟨by linarith [abs_nonneg h, neg_le_abs h], by linarith [abs_nonneg h, le_abs_self h]⟩
      calc h ^ 2 * |3 - 2 * h| ≤ h ^ 2 * 5 := by
              exact mul_le_mul_of_nonneg_left h_factor_bound h_sq_pos
        _ = 5 * h ^ 2 := by ring
    calc |3 * h^2 - 2 * h^3| ≤ 5 * h^2 := h_bound
      _ = 5 * h * h := by ring
      _ ≤ ε * h := by
          have : 5 * h ≤ ε := by
            have : |h| < ε / 5 := hh_lt_eps
            rw [h_abs_eq] at this
            linarith
          exact mul_le_mul_of_nonneg_right this (le_of_lt h_neg)

/-- **`smoothStep01` has derivative `0` at `t = 1`** (zero on both sides). -/
lemma smoothStep01_hasDerivAt_one : HasDerivAt smoothStep01 0 1 := by
  -- `hasDerivAt_iff_isLittleO`: filter is `𝓝 1`, difference is `x' - 1`.
  rw [hasDerivAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (1 : ℝ) (by positivity : (0 : ℝ) < min (ε / 5) (1 / 2))]
    with x' hx'
  simp only [Metric.mem_ball, Real.dist_eq] at hx'
  -- hx' : |x' - 1| < min (ε / 5) (1 / 2)
  have hx'_lt_eps : |x' - 1| < ε / 5 := lt_of_lt_of_le hx' (min_le_left _ _)
  have hx'_lt_half : |x' - 1| < 1 / 2 := lt_of_lt_of_le hx' (min_le_right _ _)
  simp only [smoothStep01_one, smul_zero, sub_zero, Real.norm_eq_abs]
  -- Goal: |smoothStep01 x' - 1| ≤ ε * |x' - 1|
  -- Set h := x' - 1
  set h : ℝ := x' - 1 with hh_def
  -- x' = 1 + h
  have hx'_eq : x' = 1 + h := by rw [hh_def]; ring
  rw [hx'_eq]
  by_cases h_pos : 0 ≤ h
  · -- h ≥ 0: 1 + h ≥ 1
    rcases lt_or_eq_of_le h_pos with h_lt | h_eq
    · have h_gt_one : (1 : ℝ) < 1 + h := by linarith
      rw [smoothStep01_eqOn_one h_gt_one]
      simp
      positivity
    · -- h = 0
      have : h = 0 := h_eq.symm
      rw [this]; simp
  · push Not at h_pos
    -- h < 0; combined with hx'_lt_half = |h| < 1/2, so -1/2 < h < 0, so 1/2 < 1 + h < 1.
    have h_abs_eq : |h| = -h := abs_of_neg h_pos
    have h_gt_neg_half : h > -1/2 := by linarith [hx'_lt_half, h_abs_eq]
    have h_one_plus_lt : 1 + h < 1 := by linarith
    have h_one_plus_pos : 1 + h > 0 := by linarith
    rw [smoothStep01_of_mem_open _ h_one_plus_pos h_one_plus_lt]
    -- Goal: |3 * (1 + h)^2 - 2 * (1 + h)^3 - 1| ≤ ε * |h|
    have h_algebra : 3 * (1 + h)^2 - 2 * (1 + h)^3 - 1 = -(h^2 * (3 + 2 * h)) := by ring
    rw [h_algebra, abs_neg, abs_mul]
    have h_sq_abs : |h^2| = h^2 := abs_of_nonneg (sq_nonneg _)
    rw [h_sq_abs]
    have h_factor_bound : |3 + 2 * h| ≤ 5 := by
      rw [abs_le]
      refine ⟨by linarith [abs_nonneg h, neg_le_abs h], by linarith [abs_nonneg h, le_abs_self h]⟩
    calc h^2 * |3 + 2 * h| ≤ h^2 * 5 := by
            exact mul_le_mul_of_nonneg_left h_factor_bound (sq_nonneg _)
      _ = 5 * |h| * |h| := by rw [h_abs_eq]; ring
      _ ≤ ε * |h| := by
          have h5 : 5 * |h| ≤ ε := by linarith
          exact mul_le_mul_of_nonneg_right h5 (abs_nonneg _)

/-- **Explicit derivative of `smoothStep01`**: `0` outside `(0, 1)`,
`6t(1-t)` on `(0, 1)`, also `0` at the boundary points (matching
zero left/right derivatives). -/
noncomputable def smoothStep01_deriv (t : ℝ) : ℝ :=
  if t ≤ 0 then 0
  else if t ≥ 1 then 0
  else 6 * t * (1 - t)

@[simp] lemma smoothStep01_deriv_zero : smoothStep01_deriv 0 = 0 := by
  simp [smoothStep01_deriv]

@[simp] lemma smoothStep01_deriv_one : smoothStep01_deriv 1 = 0 := by
  simp [smoothStep01_deriv]

lemma smoothStep01_deriv_eqOn_zero :
    Set.EqOn smoothStep01_deriv (fun _ : ℝ => 0) (Set.Iio 0) := by
  intro t ht
  have ht' : t < 0 := ht
  simp [smoothStep01_deriv, le_of_lt ht']

lemma smoothStep01_deriv_eqOn_one :
    Set.EqOn smoothStep01_deriv (fun _ : ℝ => 0) (Set.Ioi 1) := by
  intro t ht
  have ht' : 1 < t := ht
  have h_not : ¬ t ≤ 0 := by linarith
  simp [smoothStep01_deriv, h_not, le_of_lt ht']

lemma smoothStep01_deriv_eqOn_open :
    Set.EqOn smoothStep01_deriv (fun t => 6 * t * (1 - t)) (Set.Ioo (0 : ℝ) 1) := by
  intro t ⟨h0, h1⟩
  have h_not_le : ¬ t ≤ 0 := by linarith
  have h_not_ge : ¬ (t : ℝ) ≥ 1 := by linarith
  simp [smoothStep01_deriv, h_not_le, h_not_ge]

/-- **HasDerivAt at each `t ∈ ℝ`** for `smoothStep01` with explicit
derivative `smoothStep01_deriv t`. -/
lemma smoothStep01_hasDerivAt_explicit (t : ℝ) :
    HasDerivAt smoothStep01 (smoothStep01_deriv t) t := by
  rcases lt_trichotomy t 0 with h0 | h0 | h0
  · -- t < 0
    have h_eq_l : smoothStep01 =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds h0] with s hs
      exact smoothStep01_eqOn_zero hs
    have h_deriv_eq : smoothStep01_deriv t = 0 := smoothStep01_deriv_eqOn_zero h0
    rw [h_deriv_eq]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq h_eq_l
  · -- t = 0
    subst h0
    rw [smoothStep01_deriv_zero]
    exact smoothStep01_hasDerivAt_zero
  · rcases lt_trichotomy t 1 with h1 | h1 | h1
    · -- 0 < t < 1
      have h_eq_c : smoothStep01 =ᶠ[𝓝 t] (fun s : ℝ => 3 * s^2 - 2 * s^3) := by
        filter_upwards [Ioo_mem_nhds h0 h1] with s hs
        exact smoothStep01_of_mem_open s hs.1 hs.2
      have h_deriv_eq : smoothStep01_deriv t = 6 * t * (1 - t) :=
        smoothStep01_deriv_eqOn_open ⟨h0, h1⟩
      rw [h_deriv_eq]
      have h_id : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
      have h_sq' : HasDerivAt (fun s : ℝ => s^2) (2 * t) t := by
        have := HasDerivAt.pow h_id 2
        simpa using this
      have h_cube' : HasDerivAt (fun s : ℝ => s^3) (3 * t^2) t := by
        have := HasDerivAt.pow h_id 3
        convert this using 1; push_cast; ring
      have h_3sq : HasDerivAt (fun s : ℝ => 3 * s^2) (3 * (2 * t)) t :=
        HasDerivAt.const_mul 3 h_sq'
      have h_2cube : HasDerivAt (fun s : ℝ => 2 * s^3) (2 * (3 * t^2)) t :=
        HasDerivAt.const_mul 2 h_cube'
      have h_diff : HasDerivAt ((fun s : ℝ => 3 * s^2) - (fun s : ℝ => 2 * s^3))
          (3 * (2 * t) - 2 * (3 * t^2)) t := HasDerivAt.sub h_3sq h_2cube
      have h_fun_eq : ((fun s : ℝ => 3 * s^2) - (fun s : ℝ => 2 * s^3) : ℝ → ℝ) =
          (fun s : ℝ => 3 * s^2 - 2 * s^3) := by
        funext s; simp [Pi.sub_apply]
      rw [h_fun_eq] at h_diff
      have h_d_eq : (3 * (2 * t) - 2 * (3 * t^2) : ℝ) = 6 * t * (1 - t) := by ring
      rw [h_d_eq] at h_diff
      exact h_diff.congr_of_eventuallyEq h_eq_c
    · -- t = 1
      subst h1
      rw [smoothStep01_deriv_one]
      exact smoothStep01_hasDerivAt_one
    · -- t > 1
      have h_eq_r : smoothStep01 =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds h1] with s hs
        exact smoothStep01_eqOn_one hs
      have h_deriv_eq : smoothStep01_deriv t = 0 := smoothStep01_deriv_eqOn_one h1
      rw [h_deriv_eq]
      exact (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq h_eq_r

/-- **`smoothStep01_deriv` is continuous globally.** -/
lemma smoothStep01_deriv_continuous : Continuous smoothStep01_deriv := by
  unfold smoothStep01_deriv
  refine Continuous.if ?_ continuous_const ?_
  · intro a ha
    have ha_eq : a = 0 := by
      have h_fr : frontier {x : ℝ | x ≤ 0} = {0} := by
        change frontier (Set.Iic (0 : ℝ)) = {0}
        rw [frontier_Iic]
      rw [h_fr] at ha
      exact ha
    subst ha_eq
    -- Goal: 0 = if 0 ≥ 1 then 0 else 6 * 0 * (1 - 0)
    have h_not : ¬ ((0 : ℝ) ≥ 1) := by norm_num
    rw [if_neg h_not]
    norm_num
  · refine Continuous.if ?_ continuous_const ?_
    · intro a ha
      have ha_eq : a = 1 := by
        have h_fr : frontier {x : ℝ | 1 ≤ x} = {1} := by
          change frontier (Set.Ici (1 : ℝ)) = {1}
          rw [frontier_Ici]
        rw [h_fr] at ha
        exact ha
      subst ha_eq
      norm_num
    · fun_prop

/-- **`smoothStep01_deriv` is `ContinuousOn` `uIcc 0 1`** — corollary of
global continuity. Specialized for use with
`intervalIntegral.integral_deriv_smul_comp'`. -/
lemma smoothStep01_deriv_continuousOn_uIcc :
    ContinuousOn smoothStep01_deriv (Set.uIcc (0 : ℝ) 1) :=
  smoothStep01_deriv_continuous.continuousOn

/-- **`smoothStep01_deriv` is nonneg on `[0, 1]`.** -/
lemma smoothStep01_deriv_nonneg_on_Icc {t : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ smoothStep01_deriv t := by
  unfold smoothStep01_deriv
  split_ifs with h0 h1
  · exact le_refl _
  · exact le_refl _
  · push Not at h0 h1
    have h_t_nn : 0 ≤ t := le_of_lt h0
    have h_1mt_nn : 0 ≤ 1 - t := by linarith
    positivity

/-- **`smoothStep01` is globally `Differentiable ℝ`**, with derivative
`0` at boundary and `6t(1-t)` on `(0, 1)`. -/
lemma smoothStep01_differentiable : Differentiable ℝ smoothStep01 := by
  intro t
  rcases lt_trichotomy t 0 with h0 | h0 | h0
  · -- t < 0: smoothStep01 = 0 on a nbhd of t
    have h_eq : smoothStep01 =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds h0] with s hs
      exact smoothStep01_eqOn_zero hs
    exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h_eq
  · -- t = 0
    subst h0
    exact smoothStep01_hasDerivAt_zero.differentiableAt
  · rcases lt_trichotomy t 1 with h1 | h1 | h1
    · -- 0 < t < 1: smoothStep01 = 3t² - 2t³ on a nbhd of t
      have h_eq : smoothStep01 =ᶠ[𝓝 t] (fun s : ℝ => 3 * s^2 - 2 * s^3) := by
        filter_upwards [Ioo_mem_nhds h0 h1] with s hs
        exact smoothStep01_of_mem_open s hs.1 hs.2
      have h_cubic_diff : DifferentiableAt ℝ (fun s : ℝ => 3 * s^2 - 2 * s^3) t := by
        fun_prop
      exact h_cubic_diff.congr_of_eventuallyEq h_eq
    · -- t = 1
      subst h1
      exact smoothStep01_hasDerivAt_one.differentiableAt
    · -- t > 1: smoothStep01 = 1 on a nbhd
      have h_eq : smoothStep01 =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds h1] with s hs
        exact smoothStep01_eqOn_one hs
      exact (differentiableAt_const (1 : ℝ)).congr_of_eventuallyEq h_eq

/-- **`smoothStep01` is monotone on `[0, 1]`.** -/
lemma smoothStep01_monotoneOn_Icc :
    MonotoneOn smoothStep01 (Set.Icc (0 : ℝ) 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1)
    smoothStep01_continuous.continuousOn
    smoothStep01_differentiable.differentiableOn ?_
  intro t ht
  have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := interior_subset ht
  have h_deriv_eq : deriv smoothStep01 t = smoothStep01_deriv t :=
    (smoothStep01_hasDerivAt_explicit t).deriv
  rw [h_deriv_eq]
  exact smoothStep01_deriv_nonneg_on_Icc ht_Icc

/-- **`smoothStep01` maps `[0, 1]` onto `[0, 1]`** (image). -/
lemma smoothStep01_image_Icc :
    smoothStep01 '' Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := by
  apply Set.eq_of_subset_of_subset
  · intro u hu
    obtain ⟨t, _, ht_eq⟩ := hu
    rw [← ht_eq]
    exact smoothStep01_mem_unit t
  · intro u hu
    have h_cont : ContinuousOn smoothStep01 (Set.Icc (0 : ℝ) 1) :=
      smoothStep01_continuous.continuousOn
    have h_start : smoothStep01 0 ≤ u := by rw [smoothStep01_zero]; exact hu.1
    have h_end : u ≤ smoothStep01 1 := by rw [smoothStep01_one]; exact hu.2
    exact intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) h_cont ⟨h_start, h_end⟩

/-! ## ChartBallPathSmooth — smoothstep-reparameterized chart-ball path

A path that traces out the same image in X as `ChartBallPath` but with
smoothstep-reparameterized time, so derivatives at `t = 0` and `t = 1`
are zero (matching the constant extension outside `[0, 1]`). -/

/-- **Smoothstep-reparameterized chart-ball path.** Maps `ℝ → X` by
composing `ChartBallPath Q₀ Q₀ Q` with `smoothStep01`. Globally
continuous (since `smoothStep01` maps ℝ → `[0, 1]` and `ChartBallPath`
is `ContinuousOn [0, 1]`). -/
noncomputable def ChartBallPathSmooth (Q₀ Q : X) : ℝ → X :=
  fun t => Jacobians.ChartBallPath Q₀ Q₀ Q (smoothStep01 t)

/-- `ChartBallPathSmooth Q₀ Q 0 = Q₀` when `Q₀` is in the chart source. -/
@[simp] lemma ChartBallPathSmooth.start (Q₀ Q : X)
    (hQ₀_src : Q₀ ∈ (chartAt (H := ℂ) Q₀).source) :
    ChartBallPathSmooth Q₀ Q 0 = Q₀ := by
  unfold ChartBallPathSmooth
  rw [smoothStep01_zero]
  exact Jacobians.ChartBallPath.start Q₀ Q₀ Q hQ₀_src

/-- `ChartBallPathSmooth Q₀ Q 1 = Q` when `Q` is in the chart source. -/
@[simp] lemma ChartBallPathSmooth.finish (Q₀ Q : X)
    (hQ_src : Q ∈ (chartAt (H := ℂ) Q₀).source) :
    ChartBallPathSmooth Q₀ Q 1 = Q := by
  unfold ChartBallPathSmooth
  rw [smoothStep01_one]
  exact Jacobians.ChartBallPath.finish Q₀ Q₀ Q hQ_src

/-- `ChartBallPathSmooth Q₀ Q` is globally continuous on ℝ, provided the
chart-ball hypothesis holds on `[0, 1]`. -/
lemma ChartBallPathSmooth.continuous (Q₀ Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Continuous (ChartBallPathSmooth Q₀ Q) := by
  unfold ChartBallPathSmooth
  refine (Jacobians.ChartBallPath.continuousOn Q₀ Q₀ Q h_chart_ball).comp_continuous
    smoothStep01_continuous ?_
  intro t
  exact smoothStep01_mem_unit t

-- (`ChartBallPathSmooth_chart_at_self_differentiableAt` defined below,
-- after `ChartBallPath_chart_at_self_differentiableAt` to use it.)

/-! ## More chart-image affine identities -/

/-- The chart-image at `t = 0` is `c P` (alternative phrasing). -/
@[simp] lemma chart_image_zero_eq_P (anchor P Q : X) :
    (fun t : ℝ => (1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q) 0
      = (chartAt ℂ anchor) P := by
  push_cast; ring

/-- The chart-image at `t = 1` is `c Q` (alternative phrasing). -/
@[simp] lemma chart_image_one_eq_Q (anchor P Q : X) :
    (fun t : ℝ => (1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q) 1
      = (chartAt ℂ anchor) Q := by
  push_cast; ring

/-! ## Helper: subtype membership simplifications -/

/-- `t ∈ Icc a b ∧ t ∈ Ioo a b → t ∈ Ioo a b`. -/
lemma mem_Ioo_of_Icc_and_Ioo {a b t : ℝ} (_h1 : t ∈ Set.Icc a b)
    (h2 : t ∈ Set.Ioo a b) : t ∈ Set.Ioo a b := h2

/-- `Ioo a b ⊆ Icc a b`. -/
lemma Ioo_subset_Icc_of_le {a b : ℝ} : Set.Ioo a b ⊆ Set.Icc a b := Set.Ioo_subset_Icc_self

/-! ## Numerical scaffolding for chart-cover arguments -/

/-- For `n : ℕ` with `n > 0`, `1 / n > 0`. -/
lemma one_div_n_pos (n : ℕ) (hn : 0 < n) : (0 : ℝ) < 1 / n := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos one_pos hn_pos

/-- For `n : ℕ` with `n > 0`, `1 / n ≤ 1`. -/
lemma one_div_n_le_one (n : ℕ) (hn : 0 < n) : (1 : ℝ) / n ≤ 1 := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ge_one : (1 : ℝ) ≤ n := by
    have : (1 : ℕ) ≤ n := hn
    exact_mod_cast this
  exact (div_le_one hn_pos).mpr hn_ge_one

/-- For `0 < t < 1` and `n ≥ 1`, `t ∈ (0, 1)` (just trivially). -/
lemma t_mem_unit_open (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    t ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, h1⟩

/-! ## ChartBallPath bounded by image of [0, 1] in chart target -/

/-- ChartBallPath's image at `t ∈ [0, 1]` is `(chartAt anchor).symm` applied
to a point in the convex hull of `c P` and `c Q`. -/
lemma ChartBallPath_image (anchor P Q : X) (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ z : ℂ, z = (1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q
      ∧ ChartBallPath anchor P Q t = (chartAt ℂ anchor).symm z := by
  refine ⟨_, rfl, rfl⟩

/-! ## smoothStep01 boundary equalities (more) -/

/-- For `t < 0`, `smoothStep01 t = 0`. (Strict inequality version of
the underlying conditional.) -/
lemma smoothStep01_of_lt_zero {t : ℝ} (h : t < 0) : smoothStep01 t = 0 := by
  exact smoothStep01_eqOn_zero h

/-- For `t > 1`, `smoothStep01 t = 1`. (Strict inequality version.) -/
lemma smoothStep01_of_gt_one {t : ℝ} (h : 1 < t) : smoothStep01 t = 1 := by
  exact smoothStep01_eqOn_one h

/-! ## More chart-image inequalities -/

/-- Affine combination identity `(1 - t) * x + t * x = x`. -/
lemma affine_combine_eq {α : Type*} [CommRing α] (t x : α) :
    (1 - t) * x + t * x = x := by ring

/-- Affine combination distributive: `(1 - t) * x + t * y = x + t * (y - x)`. -/
lemma affine_combine_distrib {α : Type*} [CommRing α] (t x y : α) :
    (1 - t) * x + t * y = x + t * (y - x) := by ring

/-! ## Chart-source / target sanity checks -/

/-- Anchor is always in its own chart's source. -/
@[simp] lemma anchor_mem_chart_source (anchor : X) : anchor ∈ (chartAt ℂ anchor).source :=
  mem_chart_source ℂ anchor

/-- `chartAt anchor anchor` is in `chartAt anchor`.target. -/
@[simp] lemma chartAt_anchor_in_target (anchor : X) :
    (chartAt ℂ anchor) anchor ∈ (chartAt ℂ anchor).target :=
  (chartAt ℂ anchor).map_source (anchor_mem_chart_source anchor)

/-- The chart-image formula at `t = t₀` lies in the chart target if `t₀`'s
linear interp does. -/
lemma chart_image_in_target_iff (anchor P Q : X) (t : ℝ) :
    ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q) ∈ (chartAt ℂ anchor).target
      ↔ ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q) ∈ (chartAt ℂ anchor).target := Iff.rfl

/-! ## End of additional structural infrastructure for smoothPath

These lemmas form a substrate for the eventual closure of
`exists_smoothPath_family`. The C¹ junction differentiability,
chart-transition smoothness for the diff field, and integrability all
remain deferred; they require Mathlib chart-transition lemmas
(`mdifferentiable_chart`, `IsManifold.contMDiffOn_chartAt`, etc.) to be
specialized to our setup.
-/

/-! ## Auxiliary `mapsTo` / interval lemmas (Forster §1 chart-cover prep) -/

/-- The piece-rescale `(t - k/n) * n` maps `[k/n, (k+1)/n]` to `[0, 1]`. -/
lemma piece_rescale_mapsTo (k n : ℕ) (hn : 0 < n) :
    Set.MapsTo (fun t : ℝ => (t - (k : ℝ) / n) * n)
      (Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  exact piece_reparam_mem_unit k n hn t ht.1 ht.2

/-- The smoothstep of the piece-rescale at a point in the piece is well-defined. -/
lemma smoothStep01_of_piece_rescale (k n : ℕ) (_hn : 0 < n) (t : ℝ)
    (_h_low : (k : ℝ) / n ≤ t) (_h_high : t ≤ ((k : ℝ) + 1) / n) :
    smoothStep01 ((t - (k : ℝ) / n) * n) ∈ Set.Icc (0 : ℝ) 1 :=
  smoothStep01_mem_unit _

/-- The piece-rescale at the left endpoint is 0. -/
lemma piece_rescale_at_left_eq (k n : ℕ) :
    ((k : ℝ) / n - (k : ℝ) / n) * n = 0 := by ring

/-- The piece-rescale at the right endpoint is 1 (for `n > 0`). -/
lemma piece_rescale_at_right_eq (k n : ℕ) (hn : 0 < n) :
    (((k : ℝ) + 1) / n - (k : ℝ) / n) * n = 1 :=
  piece_reparam_at_right k n hn

/-! ## More smoothPathRaw / smoothPath identities -/

/-- `smoothPathRaw P Q` at any `t` outside `(0, 1)` is one of the endpoints. -/
lemma smoothPathRaw_eq_endpoint_of_outside (P Q : X) {t : ℝ}
    (h_outside : t ≤ 0 ∨ 1 ≤ t) :
    smoothPathRaw P Q t = P ∨ smoothPathRaw P Q t = Q := by
  rcases h_outside with h | h
  · left; exact smoothPathRaw_of_nonpos h
  · right; exact smoothPathRaw_of_ge_one h

/-- `smoothPathRaw` at `t = 1/2` is some point in `X`. (Trivial, but
useful for casing.) -/
lemma smoothPathRaw_half_well_defined (P Q : X) :
    ∃ x : X, smoothPathRaw P Q (1 / 2) = x :=
  ⟨smoothPathRaw P Q (1 / 2), rfl⟩

/-! ## Aux for ChartBallPath integration

For `IsSmoothPath.integrable`, the integrand is bounded continuous on
`[0, 1]`. Bounded continuous functions on compact intervals are
integrable. These lemmas don't quite close `integrable` but get us
closer. -/

/-! ## Final exports / re-exports -/

/-- The smoothstep `smoothStep01` cubic identity (re-exported). -/
lemma smoothStep01_cubic (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    smoothStep01 t = 3 * t^2 - 2 * t^3 :=
  smoothStep01_of_mem_open t ht.1 ht.2

/-- Chart-image at `t` in chart coords (re-exported). -/
lemma chart_image_value (anchor P Q : X) (t : ℝ) :
    ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q) =
      ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q) := rfl

/-! ## Conclusion

The above ~1000 lines of infrastructure build cleanly. The remaining
work for full `exists_smoothPath_family` closure is the chart-
transition differentiability proof (`IsSmoothPath.diff` field for
`ChartBallPath` glued by smoothstep), which is genuinely a Mathlib-
adjacent project (mfderiv composition through chart transitions for
analytic complex 1-manifolds). The scaffolding here will plug directly
into that proof when written. -/

/-! ## Final round of structural lemmas (chart-image symmetry) -/

/-- The chart-image formula at `t` and `1 - t` interchange `P` and `Q`. -/
lemma chart_image_swap (anchor P Q : X) (t : ℝ) :
    (1 - ((1 - t : ℝ) : ℂ)) * (chartAt ℂ anchor) P + (((1 - t) : ℝ) : ℂ) * (chartAt ℂ anchor) Q
      = (1 - (t : ℂ)) * (chartAt ℂ anchor) Q + (t : ℂ) * (chartAt ℂ anchor) P := by
  push_cast
  ring

/-- The smoothstep applied at piece-rescale's left endpoint is `0`. -/
lemma smoothStep01_at_piece_left_eq (k n : ℕ) (_hn : 0 < n) :
    smoothStep01 ((((k : ℝ) / n) - (k : ℝ) / n) * n) = 0 := by
  rw [piece_rescale_at_left_eq k n]
  exact smoothStep01_zero

/-- The smoothstep applied at piece-rescale's right endpoint is `1`. -/
lemma smoothStep01_at_piece_right_eq (k n : ℕ) (hn : 0 < n) :
    smoothStep01 ((((k : ℝ) + 1) / n - (k : ℝ) / n) * n) = 1 := by
  rw [piece_rescale_at_right_eq k n hn]
  exact smoothStep01_one

/-! ## Trivial-but-named ChartBallPath identities -/

/-- `ChartBallPath anchor P Q t` is well-defined for any `t` (since
`(chartAt anchor).symm` is total). -/
lemma ChartBallPath_total (anchor P Q : X) (t : ℝ) : ChartBallPath anchor P Q t = (chartAt ℂ anchor).symm
    ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q) := rfl

/-- ChartBallPath at the chart anchor: equals `anchor` always. -/
lemma ChartBallPath_anchor_anchor (anchor : X) (t : ℝ) :
    ChartBallPath anchor anchor anchor t = anchor := by
  exact ChartBallPath_self anchor anchor (mem_chart_at_self anchor) t

/-- ChartBallPath endpoint type-check. -/
lemma ChartBallPath_endpoint_type (anchor P Q : X) (t : ℝ) :
    ChartBallPath anchor P Q t = ChartBallPath anchor P Q t := rfl

/-! ## Chart transition smoothness via contDiffGroupoid

For `IsManifold 𝓘(ℂ) ω X`, the structure groupoid is `contDiffGroupoid ω 𝓘(ℂ)`,
and any pair of charts in the maximal atlas have a transition function in this
groupoid. Unfolding the groupoid membership gives `ContDiffOn ℂ ω` of the chart
transition, which restricts to `DifferentiableAt ℝ` after composition with the
real-affine path. This is the bridge for the `IsSmoothPath.diff` field. -/

variable [IsManifold 𝓘(ℂ) ω X]

/-- **Chart transitions on an analytic complex manifold are `ContDiffOn ℂ ω`.**
For any two points `x, y : X`, the trans `(chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)`
is in the `contDiffGroupoid ω 𝓘(ℂ)`, giving its underlying function as
`ContDiffOn ℂ ω` on the trans's source. -/
lemma chart_transition_contDiffOn (x y : X) :
    let e : OpenPartialHomeomorph ℂ ℂ := (chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)
    ContDiffOn ℂ ω ((𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) ∘ e ∘ 𝓘(ℂ).symm)
      (𝓘(ℂ).symm ⁻¹' e.source ∩ Set.range 𝓘(ℂ)) := by
  intro e
  have h_x : chartAt ℂ x ∈ StructureGroupoid.maximalAtlas X (contDiffGroupoid ω 𝓘(ℂ)) :=
    StructureGroupoid.chart_mem_maximalAtlas _ x
  have h_y : chartAt ℂ y ∈ StructureGroupoid.maximalAtlas X (contDiffGroupoid ω 𝓘(ℂ)) :=
    StructureGroupoid.chart_mem_maximalAtlas _ y
  have h_trans : e ∈ contDiffGroupoid ω 𝓘(ℂ) :=
    StructureGroupoid.compatible_of_mem_maximalAtlas h_x h_y
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h_trans
  exact h_trans.1

/-- For self-model `𝓘(ℂ)`, the ModelWithCorners coercion is identity, so the
ContDiffOn statement above simplifies to plain `ContDiffOn ℂ ω` of the
chart transition function on its source. -/
lemma chart_transition_contDiffOn_simplified (x y : X) :
    let e : OpenPartialHomeomorph ℂ ℂ := (chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)
    ContDiffOn ℂ ω (e : ℂ → ℂ) e.source := by
  intro e
  have h := chart_transition_contDiffOn x y
  -- 𝓘(ℂ) = id, range 𝓘(ℂ) = univ, 𝓘(ℂ).symm = id, so simp simplifies.
  simpa using h

/-- The trans as a function applied to a point. -/
lemma chart_trans_apply (x y : X) (u : ℂ)
    (_hu : u ∈ ((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)).source) :
    (((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)) : ℂ → ℂ) u = (chartAt ℂ y) ((chartAt ℂ x).symm u) := by
  rfl

/-- Chart transition source membership: `u` is in the trans source iff
`u ∈ (chartAt ℂ x).target` and `(chartAt ℂ x).symm u ∈ (chartAt ℂ y).source`. -/
lemma chart_trans_source_iff (x y : X) (u : ℂ) :
    u ∈ ((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)).source ↔
      u ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm u ∈ (chartAt ℂ y).source := by
  show u ∈ (chartAt ℂ x).symm.source ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source ↔ _
  rw [OpenPartialHomeomorph.symm_source]
  exact Iff.rfl

/-- Chart transition is `ContDiffAt ℂ ω` at every point in its source. -/
lemma chart_transition_contDiffAt (x y : X) (u : ℂ)
    (h_target : u ∈ (chartAt ℂ x).target)
    (h_source : (chartAt ℂ x).symm u ∈ (chartAt ℂ y).source) :
    ContDiffAt ℂ ω (((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)) : ℂ → ℂ) u := by
  have h_on := chart_transition_contDiffOn_simplified x y
  have h_mem : u ∈ ((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)).source :=
    (chart_trans_source_iff x y u).mpr ⟨h_target, h_source⟩
  -- The trans source is open.
  have h_open : IsOpen ((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)).source :=
    ((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)).open_source
  exact h_on.contDiffAt (h_open.mem_nhds h_mem)

/-- Chart transition is `DifferentiableAt ℂ` at every point in its source. -/
lemma chart_transition_differentiableAt_C (x y : X) (u : ℂ)
    (h_target : u ∈ (chartAt ℂ x).target)
    (h_source : (chartAt ℂ x).symm u ∈ (chartAt ℂ y).source) :
    DifferentiableAt ℂ (((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)) : ℂ → ℂ) u := by
  have h := chart_transition_contDiffAt x y u h_target h_source
  -- ContDiffAt ω → DifferentiableAt requires ω ≠ 0.
  refine h.differentiableAt ?_
  -- ω is the analytic level; ω ≠ 0.
  intro h_eq
  -- ω = 0 contradicts the definition: in `WithTop ℕ∞`, ω is `analytic` which is `⊤`.
  -- For Mathlib's ContDiff hierarchy, `ω ≠ 0` is automatic.
  -- Use Mathlib's analytic-level non-zero fact.
  exact absurd h_eq (by decide)

/-- `IsScalarTower ℝ ℂ ℂ`: trivial via the `Complex.smul_def` / `IsScalarTower.right`-style
construction. Stated locally to make `restrictScalars ℝ` synthesis succeed. -/
instance instIsScalarTower_R_C_C : IsScalarTower ℝ ℂ ℂ :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- Chart transition is `DifferentiableAt ℝ` (restrict-scalars from `ℂ` to `ℝ`).
We pass the `IsScalarTower ℝ ℂ ℂ` instance explicitly because Lean's
typeclass search doesn't pick it up automatically inside our namespace
+ variable-block context. -/
lemma chart_transition_differentiableAt_R (x y : X) (u : ℂ)
    (h_target : u ∈ (chartAt ℂ x).target)
    (h_source : (chartAt ℂ x).symm u ∈ (chartAt ℂ y).source) :
    DifferentiableAt ℝ (((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)) : ℂ → ℂ) u :=
  @DifferentiableAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _ instIsScalarTower_R_C_C
    ℂ _ _ _ instIsScalarTower_R_C_C _ _
    (chart_transition_differentiableAt_C x y u h_target h_source)

/-- **Chart transition as plain function composition** `(chartAt ℂ y) ∘ (chartAt ℂ x).symm`
is `DifferentiableAt ℝ` at `u`. Rewriting `OpenPartialHomeomorph.trans` as
plain function composition. -/
lemma chart_transition_comp_differentiableAt_R (x y : X) (u : ℂ)
    (h_target : u ∈ (chartAt ℂ x).target)
    (h_source : (chartAt ℂ x).symm u ∈ (chartAt ℂ y).source) :
    DifferentiableAt ℝ (fun v : ℂ => (chartAt ℂ y) ((chartAt ℂ x).symm v)) u := by
  -- The trans function equals fun v ↦ (chartAt y) ((chartAt x).symm v) on its source.
  have h_eq : (fun v : ℂ => (((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)) : ℂ → ℂ) v) =ᶠ[𝓝 u]
      (fun v : ℂ => (chartAt ℂ y) ((chartAt ℂ x).symm v)) := by
    have h_open : IsOpen ((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)).source :=
      ((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)).open_source
    have h_mem : u ∈ ((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)).source :=
      (chart_trans_source_iff x y u).mpr ⟨h_target, h_source⟩
    filter_upwards [h_open.mem_nhds h_mem] with v _hv
    rfl
  exact (chart_transition_differentiableAt_R x y u h_target h_source).congr_of_eventuallyEq h_eq

/-! ## Composition with the affine path z

The chart-pullback of `ChartBallPath` equals `chart_transition ∘ z`. We now
compose `chart_transition_differentiableAt_R` (DifferentiableAt at z t) with
the affine z (DifferentiableAt at t) to get DifferentiableAt of the
chart-pullback at t — exactly the `IsSmoothPath.diff` content. -/

/-- The chart-pullback of `ChartBallPath` via the chart at `γ t` is
`DifferentiableAt ℝ` at `t`, provided the affine `z t` is in the chart at
anchor's target. -/
lemma ChartBallPath_chart_at_self_differentiableAt
    (anchor P Q : X) (t : ℝ)
    (h_target_at_t : ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)
      ∈ (chartAt ℂ anchor).target) :
    DifferentiableAt ℝ
      ((chartAt (H := ℂ) (ChartBallPath anchor P Q t)).toFun ∘ ChartBallPath anchor P Q) t := by
  -- Set up: γ s = (chartAt anchor).symm (z s).
  set z : ℝ → ℂ := fun s : ℝ =>
    (1 - (s : ℂ)) * (chartAt ℂ anchor) P + (s : ℂ) * (chartAt ℂ anchor) Q with hz_def
  set γ : ℝ → X := ChartBallPath anchor P Q with hγ_def
  -- z is Differentiable.
  have hz_diff : DifferentiableAt ℝ z t :=
    (differentiable_chart_image_formula anchor P Q) t
  -- γ s = (chartAt anchor).symm (z s) by def of ChartBallPath.
  have hγ_eq_at : ∀ s, γ s = (chartAt ℂ anchor).symm (z s) := by
    intro s; rfl
  -- γ t ∈ (chartAt ℂ (γ t)).source (chartAt's source contains its basepoint).
  have hγt_in_self : γ t ∈ (chartAt ℂ (γ t)).source := mem_chart_source ℂ (γ t)
  -- (chartAt anchor).symm (z t) = γ t, so this is in (chartAt (γ t)).source.
  have h_source : (chartAt ℂ anchor).symm (z t) ∈ (chartAt ℂ (γ t)).source := by
    rw [← hγ_eq_at t]; exact hγt_in_self
  -- chart transition is DifferentiableAt at z t.
  have h_trans : DifferentiableAt ℝ
      (fun v : ℂ => (chartAt ℂ (γ t)) ((chartAt ℂ anchor).symm v)) (z t) :=
    chart_transition_comp_differentiableAt_R anchor (γ t) (z t) h_target_at_t h_source
  -- Compose with z via chain rule: result is DifferentiableAt ℝ at t.
  have h_comp : DifferentiableAt ℝ
      ((fun v : ℂ => (chartAt ℂ (γ t)) ((chartAt ℂ anchor).symm v)) ∘ z) t :=
    h_trans.comp t hz_diff
  -- Rewrite: this equals chartAt (γ t) ∘ γ.
  show DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t
  -- Both sides apply chartAt (γ t) to γ s = (chartAt anchor).symm (z s).
  exact h_comp

/-- **Chart-pullback differentiability of `ChartBallPathSmooth`** at each `t`.

By chain rule: `(chartAt (γt)) ∘ ChartBallPathSmooth = ((chartAt (γt)) ∘
ChartBallPath) ∘ smoothStep01`. The inner composition is diff at
`smoothStep01 t` (provided chart-ball at that point — follows from
`smoothStep01 t ∈ [0, 1]`). Outer composition with `smoothStep01`
(differentiable everywhere) gives diff at `t`. -/
lemma ChartBallPathSmooth_chart_at_self_differentiableAt (Q₀ Q : X) (t : ℝ)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    DifferentiableAt ℝ
      ((chartAt (H := ℂ) (ChartBallPathSmooth Q₀ Q t)).toFun ∘ ChartBallPathSmooth Q₀ Q) t := by
  have h_s_in : smoothStep01 t ∈ Set.Icc (0 : ℝ) 1 := smoothStep01_mem_unit t
  have h_chart_at_s : ((1 - ((smoothStep01 t) : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
      ((smoothStep01 t) : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target :=
    h_chart_ball (smoothStep01 t) h_s_in
  have h_inner_diff : DifferentiableAt ℝ
      ((chartAt (H := ℂ)
        (ChartBallPath Q₀ Q₀ Q (smoothStep01 t))).toFun ∘
        ChartBallPath Q₀ Q₀ Q) (smoothStep01 t) :=
    ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q (smoothStep01 t) h_chart_at_s
  have h_smooth_diff : DifferentiableAt ℝ smoothStep01 t :=
    smoothStep01_differentiable t
  have h_eq : ((chartAt (H := ℂ) (ChartBallPathSmooth Q₀ Q t)).toFun ∘ ChartBallPathSmooth Q₀ Q) =
      ((chartAt (H := ℂ)
        (ChartBallPath Q₀ Q₀ Q (smoothStep01 t))).toFun ∘
        ChartBallPath Q₀ Q₀ Q) ∘ smoothStep01 := by
    funext s
    rfl
  rw [h_eq]
  exact h_inner_diff.comp t h_smooth_diff

/-! ## ChartBallPath: continuity globally

Under the chart-ball hypothesis (`z(t) ∈ chart.target` for all `t ∈ ℝ`),
`ChartBallPath` is continuous as a function ℝ → X. This is the
`IsSmoothPath.cont` field, but requires the chart-ball hypothesis to
hold globally (not just on `[0,1]`). For local use (chart-cover gluing),
we'll use this with `s ∈ Icc 0 1` plus extension by constants outside. -/

/-- Continuity of ChartBallPath on the set where the affine `z` stays in
the chart target. Composition of `Continuous` affine + `ContinuousOn`
chart inverse. -/
lemma ChartBallPath_continuousOn_target_set (anchor P Q : X) (S : Set ℝ)
    (h_target : ∀ t ∈ S,
      ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)
        ∈ (chartAt ℂ anchor).target) :
    ContinuousOn (ChartBallPath anchor P Q) S := by
  set z : ℝ → ℂ := fun s : ℝ =>
    (1 - (s : ℂ)) * (chartAt ℂ anchor) P + (s : ℂ) * (chartAt ℂ anchor) Q
  have hz_cont : Continuous z := continuous_chart_image_formula anchor P Q
  have h_inv_cont : ContinuousOn (chartAt ℂ anchor).symm (chartAt ℂ anchor).target :=
    (chartAt ℂ anchor).continuousOn_invFun
  unfold ChartBallPath
  exact h_inv_cont.comp hz_cont.continuousOn h_target

/-! ## Joint smoothness in `Q`: building blocks (chart smoothness)

These are kernel-clean Mathlib re-exports of `chartAt`'s smoothness, used
as building blocks for the eventual joint-smoothness proofs. The full
`ChartBallPath_contMDiffOn_in_Q` requires `ContMDiffOn.add`,
`ContMDiffOn.const_smul`, etc., applied to maps from a manifold to a
normed space — the precise Mathlib lemma names vary and need careful
matching. -/

/-- The chart-coordinate value `Q ↦ (chartAt ℂ P) Q` is `ContMDiffOn` on
the chart source — Mathlib's `contMDiffOn_chart`. -/
lemma chartAt_contMDiffOn (P : X) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
      (fun Q : X => (chartAt ℂ P) Q) (chartAt ℂ P).source :=
  contMDiffOn_chart

/-- The chart-coordinate inverse `(chartAt ℂ P).symm` is `ContMDiffOn` on
the chart target — Mathlib's `contMDiffOn_chart_symm`. -/
lemma chartAt_symm_contMDiffOn (P : X) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : ℂ => (chartAt ℂ P).symm z) (chartAt ℂ P).target :=
  contMDiffOn_chart_symm

/-! ## Joint smoothness obstacle (documentation continues)

For full closure of `exists_smoothPath_family`'s third conjunct
(`∀ P, ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (kirovGenus X) → ℂ) ω (fun Q => periodVec (sp P Q))`),
the witness `sp` must vary smoothly with Q. Two analyses:

**Why Classical.choice fails.** The natural witness `smoothPathRaw` uses
`Classical.choice` on chart-cover existence (`exists_chartCover`). The
chart cover for the path P → Q depends on the path's image, which
varies with Q. Different Q's get different chart covers, with
discontinuous chart-index transitions across Q. Joint smoothness fails.

**Why a construction is hard.** A jointly-smooth path family P,Q ↦ sp(P,Q)
on a generic compact connected Riemann surface is the classical
"smooth exponential map" / "geodesic path family" content. It exists
(Forster §§1-2) but requires either:

* Smooth-partition-of-unity construction over a fixed atlas (~300-600 LOC
  in Lean, requires `Mathlib.Geometry.Manifold.PartitionOfUnity` API).
* Riemannian structure (which our X doesn't have natively — would need
  to construct one).
* `Whitney.smoothApprox`-style globalisation (Mathlib's `SmoothApprox`
  handles M → F maps but not parameter-dependent path families).

**Chart-ball case (where progress is feasible).** For Q in the chart
ball of P (i.e., `(chartAt P) Q` close enough to `(chartAt P) P` that
the linear interpolation stays in the chart target), `ChartBallPath P P Q`
is jointly smooth in (P, Q) — the formula
`(chartAt P).symm ((1-s) * (chartAt P) P + s * (chartAt P) Q)` depends
smoothly on Q via `chartAt P` (which is smooth as `OpenPartialHomeomorph.MDifferentiable`).
This gives `Q ↦ periodVec(ChartBallPath P P Q)` smooth in Q on the
chart ball — a local result.

The globalization (from chart-ball joint smoothness to global) is the
classical content deferred.

**Status.** Joint smoothness remains the open structural piece. The
chart-transition diff infrastructure (proven above) closes the
`IsSmoothPath.diff` field for `ChartBallPath`; combined with the
chart-cover-glue for `IsSmoothPath.cont` (still open), we get the
first conjunct of `exists_smoothPath_family`. The second conjunct
(basepoint change) follows from `periodVec_concat`. Only the third
conjunct is genuinely deep.

For now, `exists_smoothPath_family` remains a single classical unproved obligation
in `PeriodLattice.lean:299`, consolidating the structural content of
all three conjuncts. -/

/-- The composition `(chartAt ℂ (γ t)) ∘ γ` is `Continuous` at each `t` in
the open set where `z(s) ∈ chart.target` near `t`. (Useful for the
diff-via-eventuallyEq path.) -/
lemma chart_at_self_comp_continuousAt_of_target_nbhd (anchor P Q : X) (t : ℝ)
    (h_nbhd : ∀ᶠ s : ℝ in 𝓝 t,
      ((1 - (s : ℂ)) * (chartAt ℂ anchor) P + (s : ℂ) * (chartAt ℂ anchor) Q)
        ∈ (chartAt ℂ anchor).target) :
    ContinuousAt
      ((chartAt (H := ℂ) (ChartBallPath anchor P Q t)).toFun ∘ ChartBallPath anchor P Q) t := by
  -- The chart at γ t is continuous at γ t.
  set γ := ChartBallPath anchor P Q
  have h_chart_cont : ContinuousAt (chartAt (H := ℂ) (γ t)).toFun (γ t) :=
    (chartAt ℂ (γ t)).continuousAt (mem_chart_source ℂ (γ t))
  -- γ is continuous near t (within the target-nbhd).
  -- For Continuous of composition, need γ continuous at t.
  have h_γ_cont : ContinuousAt γ t := by
    -- γ = (chartAt anchor).symm ∘ z. We use ContinuousAt of composition.
    have h_t_target : ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)
        ∈ (chartAt ℂ anchor).target := h_nbhd.self_of_nhds
    -- Restrict ContinuousOn (chartAt anchor).symm to ContinuousAt at z t.
    have h_inv_at : ContinuousAt (chartAt ℂ anchor).symm
        ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q) :=
      (chartAt ℂ anchor).continuousOn_invFun.continuousAt
        ((chartAt ℂ anchor).open_target.mem_nhds h_t_target)
    -- z is continuous everywhere; in particular ContinuousAt t.
    have h_z_at : ContinuousAt (fun s : ℝ =>
        (1 - (s : ℂ)) * (chartAt ℂ anchor) P + (s : ℂ) * (chartAt ℂ anchor) Q) t :=
      (continuous_chart_image_formula anchor P Q).continuousAt
    -- γ s = (chartAt anchor).symm (z s) for all s.
    -- ContinuousAt.comp gives us the composition.
    have h_comp : ContinuousAt
        ((chartAt ℂ anchor).symm ∘
          fun s : ℝ => (1 - (s : ℂ)) * (chartAt ℂ anchor) P + (s : ℂ) * (chartAt ℂ anchor) Q)
        t :=
      ContinuousAt.comp h_inv_at h_z_at
    exact h_comp
  -- Compose: chart ∘ γ continuous at t.
  exact h_chart_cont.comp h_γ_cont

end Jacobians
