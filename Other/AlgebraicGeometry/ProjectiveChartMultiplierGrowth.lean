/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveHomogeneousRatioEvaluation

/-!
# Polynomial growth of the chart multipliers

For `b ≤ a`, the chart multipliers of a morphism `𝒪(−a)^an ⟶ 𝒪(−b)^an` on `ℙᴺ` satisfy
`hᵢ · (Xⱼ/Xᵢ)ᵇ = (Xⱼ/Xᵢ)ᵃ · hⱼ` on chart overlaps, and by `chartRatioEvaluation` the transition
unit is the `j`-th homogeneous coordinate of `insertNth i 1 z`.  Choosing `j` with
`|wⱼ| = max_l |w_l| ≥ 1` for `w = insertNth i 1 z` puts the point in the `j`-th chart with chart
coordinates in the closed unit polydisc, where the (continuous) multiplier `hⱼ` is bounded by
compactness.  This gives `‖fᵢ z‖ ≤ C (1 + ‖z‖)^{a−b}`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint Other.ProjectiveChart

/-! ### Values of sections of the holomorphic structure sheaf -/

variable {N : ℕ}

theorem holSectionFun_mul {V : Opens (TopCat.of (ComplexPoint (projectiveSpaceOver N)))}
    (u v : (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op V)) (x : V) :
    holSectionFun (u * v) x = holSectionFun u x * holSectionFun v x := rfl

theorem holSectionFun_holRingRes
    {V W : Opens (TopCat.of (ComplexPoint (projectiveSpaceOver N)))} (h : W ≤ V)
    (u : (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op V)) (x : W) :
    holSectionFun (ComplexPoint.holRingRes h u) x = holSectionFun u ⟨x.1, h x.2⟩ := rfl

theorem holSectionFun_analyticFunction (U : (projectiveSpaceOver N).left.Opens)
    (r : Γ((projectiveSpaceOver N).left, U))
    (x : ComplexPoint.analyticOpen (projectiveSpaceOver N) U) :
    holSectionFun (ComplexPoint.analyticFunction (projectiveSpaceOver N) N U r) x =
      Point.evaluate U r x.1 := rfl

theorem continuous_holSectionFun
    {V : Opens (TopCat.of (ComplexPoint (projectiveSpaceOver N)))}
    (u : (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op V)) :
    Continuous (holSectionFun u) :=
  (id (α := C^ω⟮𝓘(ℂ, Fin N → ℂ), (V : Opens (ComplexPoint (projectiveSpaceOver N))); ℂ⟯)
    u).contMDiff.continuous

/-! ### The chart expression of a multiplier -/

variable (N) in
/-- The chart expression of a section of `𝒪^an` on the `i`-th homogeneous chart. -/
def chartFun (i : Fin (N + 1))
    (u : (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op (chartOpen N i))) :
    (Fin N → ℂ) → ℂ :=
  fun z => holSectionFun u (chartPointIn N i z)

theorem continuous_chartFun (i : Fin (N + 1))
    (u : (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op (chartOpen N i))) :
    Continuous (chartFun N i u) :=
  (continuous_holSectionFun u).comp (contMDiff_chartPointIn N i).continuous

/-! ### Chart points in two charts -/

theorem chartPointIn_mem_inf (i j : Fin (N + 1)) (z : Fin N → ℂ)
    (hz : (i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j ≠ 0) :
    ((chartPointIn N i z : ComplexPoint (projectiveSpaceOver N))) ∈
      chartOpen N i ⊓ chartOpen N j :=
  ⟨chartPoint_mem_overOpen_self N i z, chartPoint_mem_overOpen_of_ne_zero N i j z hz⟩

set_option backward.isDefEq.respectTransparency false in
theorem holSectionFun_analyticSpaceRatio (n : ℕ) (i j : Fin (N + 1)) (z : Fin N → ℂ)
    (hz : (i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j ≠ 0) :
    holSectionFun (analyticSpaceRatio N n i j)
        ⟨(chartPointIn N i z : ComplexPoint (projectiveSpaceOver N)),
          chartPointIn_mem_inf i j z hz⟩ =
      ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ n :=
  chartRatioEvaluation N n i j z hz

set_option backward.isDefEq.respectTransparency false in
theorem chartPointIn_chartRatio_eq (i j : Fin (N + 1)) (z : Fin N → ℂ)
    (hz : (i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j ≠ 0) :
    (⟨(chartPointIn N i z : ComplexPoint (projectiveSpaceOver N)),
        (inf_le_right : chartOpen N i ⊓ chartOpen N j ≤ chartOpen N j)
          (chartPointIn_mem_inf i j z hz)⟩ : chartOpen N j) =
      chartPointIn N j (chartRatio j (i.insertNth (1 : ℂ) z)) := by
  apply Subtype.ext
  rw [coe_chartPointIn, coe_chartPointIn,
    chartPoint_chartRatio (insertNth_one_ne_zero i z) hz]
  rfl

/-! ### The growth bound -/

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Polynomial growth of the chart multipliers.** -/
theorem chartMultiplierGrowth (N a b : ℕ) : Other.ProjectiveChart.ChartMultiplierGrowth N a b := by
  classical
  intro hba φ i h hh
  have hex : ∀ j : Fin (N + 1), ∃ u, φ.val.app (op (chartOpen N j)) (anChartFrame N a j) =
      u • anChartFrame N b j := fun j => (existsUnique_canonicalChartMultiplier N a b j φ).exists
  choose u hu using hex
  have hbd : ∀ j : Fin (N + 1), ∃ M : ℝ, ∀ y : Fin N → ℂ, ‖y‖ ≤ 1 → ‖chartFun N j (u j) y‖ ≤ M := by
    intro j
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Fin N → ℂ) 1).exists_bound_of_continuousOn
      (continuous_chartFun (N := N) j (u j)).continuousOn
    exact ⟨M, fun y hy => hM y (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)⟩
  choose M hM using hbd
  refine ⟨Finset.univ.sup' Finset.univ_nonempty M, ?_⟩
  intro z
  obtain ⟨j, hj⟩ := Finite.exists_max (fun l => ‖(i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) l‖)
  have hwi : (i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) i = 1 := Fin.insertNth_apply_same _ _ _
  have hj1 : (1 : ℝ) ≤ ‖(i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j‖ := by
    have hi := hj i
    rw [hwi] at hi
    simpa using hi
  have hwj : (i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hj1
    linarith
  have hco := canonicalChartMultiplier_transition N a b i j φ hh (hu j)
  have hpt : holSectionFun h (chartPointIn N i z) *
        ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ b =
      ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ a *
        chartFun N j (u j) (chartRatio j (i.insertNth (1 : ℂ) z)) := by
    have hval := congrArg (fun t : (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj
        (op (chartOpen N i ⊓ chartOpen N j)) =>
      holSectionFun t ⟨(chartPointIn N i z : ComplexPoint (projectiveSpaceOver N)),
        chartPointIn_mem_inf i j z hwj⟩) hco
    rw [holSectionFun_mul, holSectionFun_mul, holSectionFun_holRingRes,
      holSectionFun_holRingRes, holSectionFun_analyticSpaceRatio (N := N) b i j z hwj,
      holSectionFun_analyticSpaceRatio (N := N) a i j z hwj,
      chartPointIn_chartRatio_eq i j z hwj] at hval
    exact hval
  have hne : ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ b ≠ 0 := pow_ne_zero _ hwj
  have hpow : ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ a =
      ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ (a - b) *
        ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ b := by
    rw [← pow_add]
    congr 1
    omega
  have hA : holSectionFun h (chartPointIn N i z) =
      ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ (a - b) *
        chartFun N j (u j) (chartRatio j (i.insertNth (1 : ℂ) z)) := by
    apply mul_right_cancel₀ hne
    rw [hpt, hpow]
    ring
  rw [hA, norm_mul, norm_pow]
  have hratio : ‖chartRatio j (i.insertNth (1 : ℂ) z)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => ?_
    show ‖(i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) (j.succAbove l) /
      (i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j‖ ≤ 1
    rw [norm_div, div_le_one (by linarith)]
    exact hj (j.succAbove l)
  have hle : ‖(i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j‖ ≤ 1 + ‖z‖ := by
    rcases eq_or_ne j i with rfl | hji
    · rw [hwi, norm_one]
      linarith [norm_nonneg z]
    · obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hji
      rw [Fin.insertNth_apply_succAbove]
      linarith [norm_le_pi_norm z m, norm_nonneg z]
  have hMj : ‖chartFun N j (u j) (chartRatio j (i.insertNth (1 : ℂ) z))‖ ≤
      Finset.univ.sup' Finset.univ_nonempty M :=
    le_trans (hM j _ hratio) (Finset.le_sup' M (Finset.mem_univ j))
  calc ‖(i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j‖ ^ (a - b) *
        ‖chartFun N j (u j) (chartRatio j (i.insertNth (1 : ℂ) z))‖
      ≤ (1 + ‖z‖) ^ (a - b) * Finset.univ.sup' Finset.univ_nonempty M := by
        refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hle _) hMj (norm_nonneg _) ?_
        positivity
    _ = Finset.univ.sup' Finset.univ_nonempty M * (1 + ‖z‖) ^ (a - b) := mul_comm _ _

end AlgebraicGeometry.ComplexProjectiveSpace
