/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveChartLocality

/-!
# Vanishing of morphisms of twists in negative degree

For `0 < N` and `a < b` there is no nonzero morphism `𝒪(−a)^an ⟶ 𝒪(−b)^an` on `ℙᴺ`.

The cocycle `hᵢ ρᵇ = ρᵃ hⱼ` with `ρ` the `j`-th homogeneous coordinate (`chartRatioEvaluation`)
gives, after choosing `j` with `|wⱼ|` maximal, the *decay* estimate

```
‖fᵢ z‖ · max(1, ‖z‖)^{b−a} ≤ C,
```

where `C` bounds the multipliers on the closed unit polydiscs of the `N + 1` charts.  In
particular `fᵢ` is bounded, hence (by the `H⁰` comparison in degree `0`) constant; and then the
decay estimate with `‖z‖ → ∞` forces the constant to be `0`.  Locality on the charts turns this
into `φ = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint Other.ProjectiveChart

set_option maxHeartbeats 1000000 in
/-- **The decay estimate.**  For `a ≤ b`, the chart expression of a chart multiplier decays like
`max(1, ‖z‖)^{-(b−a)}`. -/
theorem chartMultiplier_decay {N a b : ℕ} (hab : a ≤ b)
    (φ : analyticTwist N a ⟶ analyticTwist N b)
    (u : ∀ j : Fin (N + 1), (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj
      (op (chartOpen N j)))
    (hu : ∀ j, φ.val.app (op (chartOpen N j)) (anChartFrame N a j) = u j • anChartFrame N b j)
    (M : Fin (N + 1) → ℝ)
    (hM : ∀ j (y : Fin N → ℂ), ‖y‖ ≤ 1 → ‖chartFun N j (u j) y‖ ≤ M j)
    (i : Fin (N + 1)) (z : Fin N → ℂ) :
    ‖chartFun N i (u i) z‖ * (max 1 ‖z‖) ^ (b - a) ≤
      Finset.univ.sup' Finset.univ_nonempty M := by
  classical
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
  have hco := canonicalChartMultiplier_transition N a b i j φ (hu i) (hu j)
  have hpt : chartFun N i (u i) z *
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
  have hne : ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ a ≠ 0 := pow_ne_zero _ hwj
  have hpow : ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ b =
      ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ (b - a) *
        ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ a := by
    rw [← pow_add]
    congr 1
    omega
  have hA : chartFun N i (u i) z *
        ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ (b - a) =
      chartFun N j (u j) (chartRatio j (i.insertNth (1 : ℂ) z)) := by
    apply mul_right_cancel₀ hne
    rw [mul_assoc, ← hpow, hpt]
    ring
  have hratio : ‖chartRatio j (i.insertNth (1 : ℂ) z)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => ?_
    show ‖(i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) (j.succAbove l) /
      (i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j‖ ≤ 1
    rw [norm_div, div_le_one (by linarith)]
    exact hj (j.succAbove l)
  have hge : max 1 ‖z‖ ≤ ‖(i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j‖ := by
    refine max_le hj1 ?_
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun l => ?_
    have hl := hj (i.succAbove l)
    rwa [Fin.insertNth_apply_succAbove] at hl
  calc ‖chartFun N i (u i) z‖ * (max 1 ‖z‖) ^ (b - a)
      ≤ ‖chartFun N i (u i) z‖ *
        ‖(i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j‖ ^ (b - a) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hge _
    _ = ‖chartFun N j (u j) (chartRatio j (i.insertNth (1 : ℂ) z))‖ := by
        rw [← norm_pow, ← norm_mul, hA]
    _ ≤ Finset.univ.sup' Finset.univ_nonempty M :=
        le_trans (hM j _ hratio) (Finset.le_sup' M (Finset.mem_univ j))

/-- The chart expression of a section of `𝒪^an` is entire. -/
theorem analyticOnNhd_chartFun {N : ℕ} (i : Fin (N + 1))
    (v : (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op (chartOpen N i))) :
    AnalyticOnNhd ℂ (chartFun N i v) Set.univ :=
  analyticOnNhd_comp_chartPointIn N i
    (id (α := C^ω⟮𝓘(ℂ, Fin N → ℂ), (chartOpen N i :
      Opens (ComplexPoint (projectiveSpaceOver N))); ℂ⟯) v).contMDiff

set_option maxHeartbeats 1000000 in
/-- **Vanishing in negative degree.**  For `0 < N` and `a < b` every morphism
`𝒪(−a)^an ⟶ 𝒪(−b)^an` on `ℙᴺ` is zero. -/
theorem twistRankOneVanishesNeg_of_pos {N : ℕ} (hN : 0 < N) (a b : ℕ) (hab : a < b)
    (φ : analyticTwist N a ⟶ analyticTwist N b) : φ = 0 := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hex : ∀ j : Fin (N + 1), ∃ v,
      φ.val.app (op (chartOpen N j)) (anChartFrame N a j) = v • anChartFrame N b j :=
    fun j => (existsUnique_canonicalChartMultiplier N a b j φ).exists
  choose u hu using hex
  have hbd : ∀ j : Fin (N + 1), ∃ M : ℝ, ∀ y : Fin N → ℂ, ‖y‖ ≤ 1 → ‖chartFun N j (u j) y‖ ≤ M := by
    intro j
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Fin N → ℂ) 1).exists_bound_of_continuousOn
      (continuous_chartFun (N := N) j (u j)).continuousOn
    exact ⟨M, fun y hy => hM y (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)⟩
  choose M hM using hbd
  have hdecay := chartMultiplier_decay hab.le φ u hu M hM
  refine hom_eq_zero_of_anChartFrame φ fun i => ?_
  -- the chart expression is bounded
  have hbound : ∀ z : Fin N → ℂ,
      ‖chartFun N i (u i) z‖ ≤ (Finset.univ.sup' Finset.univ_nonempty M) * (1 + ‖z‖) ^ 0 := by
    intro z
    have h1 := hdecay i z
    have h2 : (1 : ℝ) ≤ (max 1 ‖z‖) ^ (b - a) := one_le_pow₀ (le_max_left _ _)
    have h3 : (0 : ℝ) ≤ ‖chartFun N i (u i) z‖ := norm_nonneg _
    simp only [pow_zero, mul_one]
    nlinarith
  -- hence constant
  obtain ⟨Q, ⟨hQhom, hQeval⟩, -⟩ :=
    existsUnique_isHomogeneous_of_growth (m := 0) i (analyticOnNhd_chartFun i (u i)) hbound
  obtain ⟨c, hc⟩ : ∃ c : ℂ, deh ℂ i Q = MvPolynomial.C c :=
    ⟨MvPolynomial.coeff 0 (deh ℂ i Q),
      (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := deh ℂ i Q)).mp
        (Nat.le_zero.mp (totalDegree_deh_le ℂ i hQhom))⟩
  have hconst : ∀ z : Fin N → ℂ, chartFun N i (u i) z = c := by
    intro z
    rw [← hQeval z, hc, MvPolynomial.eval_C]
  -- the constant vanishes
  have hzero : c = 0 := by
    by_contra hcne
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
    set C : ℝ := Finset.univ.sup' Finset.univ_nonempty M with hCdef
    set R : ℝ := max 1 ((C + 1) / ‖c‖) with hRdef
    have hR1 : (1 : ℝ) ≤ R := le_max_left _ _
    have hkey := hdecay i (fun _ : Fin N => (R : ℂ))
    rw [hconst] at hkey
    have hznorm : ‖(fun _ : Fin N => (R : ℂ))‖ = R := by
      rw [pi_norm_const]
      simp [abs_of_nonneg (le_trans zero_le_one hR1)]
    rw [hznorm, max_eq_right hR1] at hkey
    have hRk : R ≤ R ^ (b - a) := by
      calc R = R ^ 1 := (pow_one R).symm
        _ ≤ R ^ (b - a) := pow_le_pow_right₀ hR1 (by omega)
    have h1 : ‖c‖ * R ≤ C := le_trans (by nlinarith [norm_nonneg c]) hkey
    have h2 : (C + 1) / ‖c‖ ≤ R := le_max_right _ _
    have h3 : C + 1 ≤ ‖c‖ * R := by
      rw [div_le_iff₀ hcpos] at h2
      linarith [h2]
    linarith
  have hu0 : u i = 0 := by
    refine holSection_ext i fun z => ?_
    rw [hconst z, hzero]
    rfl
  rw [hu i, hu0, zero_smul]

/-- **The negative-degree obligation for `0 < N`.** -/
theorem twistRankOneAlgebraizesNeg_of_pos {N : ℕ} (hN : 0 < N) :
    Other.ProjectiveChart.TwistRankOneAlgebraizesNeg N :=
  Other.ProjectiveChart.twistRankOneAlgebraizesNeg_of_vanishing N
    fun a b hab φ => twistRankOneVanishesNeg_of_pos hN a b hab φ

end AlgebraicGeometry.ComplexProjectiveSpace
