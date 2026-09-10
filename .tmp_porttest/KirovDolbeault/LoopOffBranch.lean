import KirovDolbeault.SmoothPathCore
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Chart-local FTC for the line integral, and the off-branch-loop foundations

This module builds the **chart-local Fundamental Theorem of Calculus** for the
manifold `lineIntegral`, the genuine analytic nugget needed to discharge
`exists_loop_off_branchLocus` (obligation #6) via the *local-detour* route (Forster
§10.5, but with NO global manifold Stokes):

* `chartFrame_cancel_general` — for **any** path `γ` staying in a single chart
  source around `Q₀`, the `lineIntegral` integrand `ωᵢ(γ t)(γ'(t))` equals the
  chart-coordinate integrand
  `chartFormCoeff Q₀ i (chartₖ(γ t)) · (chartₖ ∘ γ)'(t)`.
  (The `ChartBallPath`-specific `chartFrame_cancel` in `SmoothPathCore` is the
  special case `γ = ChartBallPath`.)

* `lineIntegral_eq_primitive_diff_in_ballChart` — **chart-local FTC**: if `γ`
  stays in a *ball*-chart (target `Metric.ball c r`, hence simply connected) and
  is C¹ in chart coordinates, then
  `lineIntegral ωᵢ γ = F (chart γ(1)) − F (chart γ(0))`
  where `F` is a holomorphic **primitive** of the (holomorphic) coefficient
  `chartFormCoeff Q₀ i` on the ball (Mathlib's
  `DifferentiableOn.isExactOn_ball`, Morera). The line integral therefore depends
  only on the chart-coordinate endpoints.

* `lineIntegral_eq_of_chart_ball_endpoints` — the immediate corollary: two
  C¹ paths with **equal endpoints** inside one ball-chart have **equal**
  `lineIntegral`. (This reinstates, with the correct `ball` hypothesis, the
  `lineIntegral_eq_of_chart_local` lemma that was removed from
  `Jacobians/LineIntegral.lean` as unprovable in full generality.)

These are the local primitives for period-preservation: replacing a sub-arc of a
loop by a detour with the same endpoints inside one ball-chart does not change the
contribution to any period, because both contributions equal the same
primitive-difference. The remaining work (global subdivision, detour-off-`B`
surgery, C¹ gluing, telescoping the primitive-differences across chart overlaps)
is the assembly of `exists_loop_off_branchLocus` itself.

## References
Forster §10.5; Mathlib `Mathlib/Analysis/Complex/HasPrimitives.lean` (Morera).
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Complex Set MeasureTheory Filter

namespace Jacobians.OfCurveSkeleton

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **General chart-frame cancellation.** For any path `γ` that stays in the chart
source of `Q₀` on a neighbourhood of `t`, and is chart-pullback-differentiable at
`t`, the `lineIntegral` integrand of the `i`-th period basis form factors through
the chart `e := chartAt ℂ Q₀`:

```
ωᵢ(γ t)(pathSpeed γ t) = chartFormCoeff Q₀ i (e (γ t)) · (fderiv ℝ (e ∘ γ) t 1).
```

This is `OfCurveSkeleton.chartFrame_cancel` generalised from `ChartBallPath` to an
arbitrary path: the proof is the same chart-transition + ℂ-linearity computation,
with the `ChartBallPath`-specific `chart_ChartBallPath_eq` step replaced by the
local equality `e ∘ γ` (the chart coordinate) directly. -/
lemma chartFrame_cancel_general (Q₀ : X) (γ : ℝ → X) (i : Fin (kirovGenus X)) (t : ℝ)
    (h_source_nbhd : ∀ᶠ s : ℝ in nhds t, γ s ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t) :
    (periodBasisForm X i).toFun (γ t) (pathSpeed γ t) =
      chartFormCoeff (X := X) Q₀ i ((chartAt (H := ℂ) Q₀) (γ t))
        * (fderiv ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t 1) := by
  set e := chartAt (H := ℂ) Q₀ with he
  set w : ℂ := e (γ t) with hw
  have hγt_source : γ t ∈ e.source := h_source_nbhd.self_of_nhds
  have hγt_self_source : γ t ∈ (chartAt (H := ℂ) (γ t)).source := mem_chart_source ℂ (γ t)
  -- The chart transition `h_trans := (chartAt γt) ∘ e.symm`, holomorphic at `w`.
  set h_trans : ℂ → ℂ := fun v => (chartAt (H := ℂ) (γ t)) (e.symm v) with hh_trans
  have h_trans_diff_C : DifferentiableAt ℂ h_trans w := by
    have h_src : e.symm w ∈ (chartAt (H := ℂ) (γ t)).source := by
      rw [show e.symm w = γ t from e.left_inv hγt_source]; exact hγt_self_source
    have h_wtarget : w ∈ e.target := e.map_source hγt_source
    have h_dC := Jacobians.chart_transition_differentiableAt_C (X := X) Q₀ (γ t) w h_wtarget h_src
    have h_eq_comp : (fun v : ℂ =>
        (((e.symm ≫ₕ (chartAt (H := ℂ) (γ t))) : ℂ → ℂ)) v) =ᶠ[nhds w] h_trans := by
      have h_open : IsOpen (e.symm ≫ₕ (chartAt (H := ℂ) (γ t))).source :=
        (e.symm ≫ₕ (chartAt (H := ℂ) (γ t))).open_source
      have h_mem : w ∈ (e.symm ≫ₕ (chartAt (H := ℂ) (γ t))).source :=
        (Jacobians.chart_trans_source_iff (X := X) Q₀ (γ t) w).mpr ⟨h_wtarget, h_src⟩
      filter_upwards [h_open.mem_nhds h_mem] with v _; rfl
    exact h_dC.congr_of_eventuallyEq h_eq_comp
  have h_trans_diff_R : DifferentiableAt ℝ h_trans w :=
    @DifferentiableAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _ Jacobians.instIsScalarTower_R_C_C
      ℂ _ _ _ Jacobians.instIsScalarTower_R_C_C _ _ h_trans_diff_C
  -- `(chartAt γt) ∘ γ =ᶠ h_trans ∘ (e ∘ γ)` near `t`.
  have h_local_eq : (chartAt (H := ℂ) (γ t)).toFun ∘ γ =ᶠ[nhds t]
      h_trans ∘ (e.toFun ∘ γ) := by
    filter_upwards [h_source_nbhd] with s hs
    show (chartAt (H := ℂ) (γ t)) (γ s) = h_trans (e (γ s))
    rw [hh_trans]; simp only; rw [e.left_inv hs]
  have h_pathSpeed : pathSpeed γ t = fderiv ℝ (h_trans ∘ (e.toFun ∘ γ)) t 1 := by
    show fderiv ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t 1 = _
    rw [Filter.EventuallyEq.fderiv_eq h_local_eq]
  have h_chain : fderiv ℝ (h_trans ∘ (e.toFun ∘ γ)) t =
      (fderiv ℝ h_trans w).comp (fderiv ℝ (e.toFun ∘ γ) t) :=
    fderiv_comp t h_trans_diff_R hγ_diff
  set D : ℂ := fderiv ℝ (e.toFun ∘ γ) t 1 with hD
  have h_pathSpeed_eq : pathSpeed γ t = (fderiv ℝ h_trans w) D := by
    rw [h_pathSpeed, h_chain, ContinuousLinearMap.comp_apply]
  have h_trans_fderiv_RC : fderiv ℝ h_trans w = (fderiv ℂ h_trans w).restrictScalars ℝ := by
    have hFD_C : HasFDerivAt h_trans (fderiv ℂ h_trans w) w := h_trans_diff_C.hasFDerivAt
    have hFD_R : HasFDerivAt h_trans ((fderiv ℂ h_trans w).restrictScalars ℝ) w := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hFD_C ⊢
      simp only [ContinuousLinearMap.coe_restrictScalars']; exact hFD_C
    exact hFD_R.fderiv
  have h_pathSpeed_C : pathSpeed γ t = (fderiv ℂ h_trans w) D := by
    rw [h_pathSpeed_eq, h_trans_fderiv_RC, ContinuousLinearMap.coe_restrictScalars']
  have h_fderiv_apply : (fderiv ℂ h_trans w) D = D * (fderiv ℂ h_trans w) 1 := by
    have := (fderiv ℂ h_trans w).map_smul D (1 : ℂ)
    rw [smul_eq_mul, mul_one] at this; rw [this, smul_eq_mul]
  have h_pathSpeed_final : pathSpeed γ t = D * (fderiv ℂ h_trans w) 1 := by
    rw [h_pathSpeed_C, h_fderiv_apply]
  have h_chartFormCoeff : chartFormCoeff (X := X) Q₀ i w =
      (periodBasisForm X i).toFun (γ t) ((fderiv ℂ h_trans w) 1) := by
    unfold chartFormCoeff
    show Jacobians.Montel.localRep (periodBasisForm X i) Q₀ (e.symm w) = _
    rw [show e.symm w = γ t from e.left_inv hγt_source]
    show (periodBasisForm X i).toFun (γ t)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ (γ t) 1) = _
    rw [trivAt_symmL_one_eq_fderiv_C Q₀ (γ t) hγt_source]
    congr 1
  rw [h_chartFormCoeff, h_pathSpeed_final]
  have h_lin : ((periodBasisForm X i).toFun (γ t)) (D * (fderiv ℂ h_trans w) 1) =
        D * ((periodBasisForm X i).toFun (γ t)) ((fderiv ℂ h_trans w) 1) := by
    have := (periodBasisForm X i).toFun (γ t) |>.map_smul D ((fderiv ℂ h_trans w) 1)
    simp only [smul_eq_mul] at this; exact this
  rw [h_lin]; ring

/-- **Chart-local Fundamental Theorem of Calculus for `lineIntegral`.**

If a path `γ` stays in a **ball**-chart around `Q₀` (chart target
`Metric.ball c r`, so the chart-coordinate region is simply connected) and is
C¹ in chart coordinates on `[0,1]`, then the line integral of the `i`-th period
basis form along `γ` equals the **primitive-difference**

```
lineIntegral ωᵢ γ = F (e (γ 1)) − F (e (γ 0)),    e := chartAt ℂ Q₀,
```

where `F` is a holomorphic primitive of the (holomorphic) chart coefficient
`chartFormCoeff Q₀ i` on the ball, produced by Morera's theorem
(`DifferentiableOn.isExactOn_ball`). In particular the value depends on `γ` only
through its chart-coordinate endpoints `e (γ 0)`, `e (γ 1)`.

`hint` (interval-integrability of the line-integral integrand) is what a
`IsClosedSmoothLoop`/`IsSmoothPath` already supplies via
`intervalIntegrable_form_pathSpeed_of_velContinuous`. -/
lemma lineIntegral_eq_primitive_diff_in_ballChart
    (Q₀ : X) (γ : ℝ → X) (i : Fin (kirovGenus X)) (c : ℂ) (r : ℝ)
    (htgt : (chartAt (H := ℂ) Q₀).target = Metric.ball c r)
    (hγ_in : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t)
    (hint : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)) volume 0 1) :
    ∃ F : ℂ → ℂ,
      (∀ w ∈ Metric.ball c r, HasDerivAt F (chartFormCoeff (X := X) Q₀ i w) w) ∧
      lineIntegral (periodBasisForm X i) γ =
        F ((chartAt (H := ℂ) Q₀) (γ 1)) - F ((chartAt (H := ℂ) Q₀) (γ 0)) := by
  set e := chartAt (H := ℂ) Q₀ with he
  -- `chartFormCoeff Q₀ i` is holomorphic on the (ball) chart target ⟹ has a primitive `F`.
  have hcoeff_diffOn : DifferentiableOn ℂ (chartFormCoeff (X := X) Q₀ i) (Metric.ball c r) := by
    rw [← htgt]; exact chartFormCoeff_differentiableOn Q₀ i
  obtain ⟨F, hF⟩ := hcoeff_diffOn.isExactOn_ball
  refine ⟨F, hF, ?_⟩
  set g : ℝ → ℂ := e.toFun ∘ γ with hg
  have hg_ball : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ Metric.ball c r := by
    intro t ht; rw [hg]; show e (γ t) ∈ Metric.ball c r
    rw [← htgt]; exact e.map_source (hγ_in t ht)
  have huIcc_sub : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le (by norm_num)
  -- `F ∘ g` has derivative `coeff(g t) · g'(t)` by the chain rule.
  have hFg_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (F ∘ g) (chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1)) t := by
    intro t ht
    rw [huIcc_sub] at ht
    have hg_deriv : HasDerivAt g (fderiv ℝ g t 1) t := (hγ_diff t (huIcc_sub ▸ ht)).hasDerivAt
    have hF_at : HasDerivAt F (chartFormCoeff (X := X) Q₀ i (g t)) (g t) := hF (g t) (hg_ball t ht)
    have := hF_at.comp t hg_deriv
    convert this using 1
  unfold lineIntegral
  -- The line-integral integrand equals `coeff(g t) · g'(t)` on `[0,1]`.
  have hintegrand : Set.EqOn
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
      (fun t => chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1))
      (Set.uIcc 0 1) := by
    intro t ht
    rw [huIcc_sub] at ht
    have h_src_nbhd : ∀ᶠ s : ℝ in nhds t, γ s ∈ e.source :=
      (e.open_source.preimage hγ_cont).mem_nhds (hγ_in t ht)
    exact chartFrame_cancel_general Q₀ γ i t h_src_nbhd (hγ_diff t (huIcc_sub ▸ ht))
  rw [intervalIntegral.integral_congr hintegrand,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hFg_deriv
      (hint.congr (fun t ht => hintegrand (Set.uIoc_subset_uIcc ht)))]
  rfl

/-- **Chart-local path-independence of `lineIntegral`** (the corrected form of the
lemma removed from `Jacobians/LineIntegral.lean`). Two C¹ paths `γ₁, γ₂` that both
stay inside one **ball**-chart around `Q₀` and share endpoints
(`e (γ₁ 0) = e (γ₂ 0)` and `e (γ₁ 1) = e (γ₂ 1)`, with `e := chartAt ℂ Q₀`) have
**equal** line integrals of each period basis form. Proof: both equal the same
primitive-difference (`lineIntegral_eq_primitive_diff_in_ballChart`).

This is the local period-preservation primitive: a sub-arc and a same-endpoints
detour inside a ball-chart contribute equally to every period. -/
lemma lineIntegral_eq_of_chart_ball_endpoints
    (Q₀ : X) (γ₁ γ₂ : ℝ → X) (i : Fin (kirovGenus X)) (c : ℂ) (r : ℝ)
    (htgt : (chartAt (H := ℂ) Q₀).target = Metric.ball c r)
    (hγ₁_in : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₁ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ₂_in : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₂ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ₁_cont : Continuous γ₁) (hγ₂_cont : Continuous γ₂)
    (hγ₁_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ₁) t)
    (hγ₂_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ₂) t)
    (hint₁ : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ₁ t) (pathSpeed γ₁ t)) volume 0 1)
    (hint₂ : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ₂ t) (pathSpeed γ₂ t)) volume 0 1)
    (h0 : (chartAt (H := ℂ) Q₀) (γ₁ 0) = (chartAt (H := ℂ) Q₀) (γ₂ 0))
    (h1 : (chartAt (H := ℂ) Q₀) (γ₁ 1) = (chartAt (H := ℂ) Q₀) (γ₂ 1)) :
    lineIntegral (periodBasisForm X i) γ₁ = lineIntegral (periodBasisForm X i) γ₂ := by
  obtain ⟨F₁, hF₁, he₁⟩ :=
    lineIntegral_eq_primitive_diff_in_ballChart Q₀ γ₁ i c r htgt hγ₁_in hγ₁_cont hγ₁_diff hint₁
  obtain ⟨F₂, hF₂, he₂⟩ :=
    lineIntegral_eq_primitive_diff_in_ballChart Q₀ γ₂ i c r htgt hγ₂_in hγ₂_cont hγ₂_diff hint₂
  -- `F₁ − F₂` has zero derivative on the (open, preconnected) ball, hence is constant there;
  -- so the endpoint-differences `F₁ p1 − F₁ p0` and `F₂ p1 − F₂ p0` agree.
  set D : ℂ → ℂ := fun z => F₁ z - F₂ z with hD
  have hD_diff : DifferentiableOn ℂ D (Metric.ball c r) := fun w hw =>
    ((hF₁ w hw).sub (hF₂ w hw)).differentiableAt.differentiableWithinAt
  have hD_deriv0 : Set.EqOn (deriv D) 0 (Metric.ball c r) := by
    intro w hw
    have : HasDerivAt D 0 w := by simpa using (hF₁ w hw).sub (hF₂ w hw)
    simp [this.deriv]
  have hp0 : (chartAt (H := ℂ) Q₀) (γ₁ 0) ∈ Metric.ball c r := by
    rw [← htgt]; exact (chartAt (H := ℂ) Q₀).map_source (hγ₁_in 0 ⟨le_rfl, zero_le_one⟩)
  have hp1 : (chartAt (H := ℂ) Q₀) (γ₁ 1) ∈ Metric.ball c r := by
    rw [← htgt]; exact (chartAt (H := ℂ) Q₀).map_source (hγ₁_in 1 ⟨zero_le_one, le_rfl⟩)
  have hDeq : D ((chartAt (H := ℂ) Q₀) (γ₁ 1)) = D ((chartAt (H := ℂ) Q₀) (γ₁ 0)) :=
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
      hD_diff hD_deriv0 hp1 hp0
  rw [he₁, he₂, ← h0, ← h1]
  -- Goal: `F₁ p1 − F₁ p0 = F₂ p1 − F₂ p0`, which is `D p1 = D p0` rearranged.
  have hthis := hDeq
  simp only [hD] at hthis
  linear_combination hthis

/-! ## Sub-ball generalization (usable with `chart_restrict_to_ball`)

The two lemmas above require the chart `chartAt Q₀` to have its **entire** target equal
to a ball — which generic charts do not. The downstream subdivision machinery
(`Path.exists_ball_chart_subdivision`, built on `chart_restrict_to_ball`) instead gives a
ball `Metric.ball c r ⊆ (chartAt Q₀).target` that is a *sub-region* of the chart target,
together with the guarantee that the path stays in the restricted (smaller) source. The
following generalizations replace the `target = ball` hypothesis by `ball ⊆ target` plus an
explicit "chart-images land in the ball" hypothesis. The proofs are identical: the ball is
still the simply-connected region carrying Morera's primitive (`isExactOn_ball`); the only
change is `chartFormCoeff` is now holomorphic on the ball by `DifferentiableOn.mono` from
the full target, and chart-image confinement is supplied rather than derived from
`map_source`. -/

/-- **Chart-local FTC on a sub-ball of the chart target.** Generalizes
`lineIntegral_eq_primitive_diff_in_ballChart`: the ball `Metric.ball c r` need only be a
subset of `(chartAt Q₀).target`, with the path's chart-images supplied to lie in the ball
(`hg_ball`). The conclusion is the same primitive-difference. -/
lemma lineIntegral_eq_primitive_diff_in_subball
    (Q₀ : X) (γ : ℝ → X) (i : Fin (kirovGenus X)) (c : ℂ) (r : ℝ)
    (hsub : Metric.ball c r ⊆ (chartAt (H := ℂ) Q₀).target)
    (hg_ball : ∀ t ∈ Set.Icc (0 : ℝ) 1, (chartAt (H := ℂ) Q₀) (γ t) ∈ Metric.ball c r)
    (hγ_in : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t)
    (hint : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)) volume 0 1) :
    ∃ F : ℂ → ℂ,
      (∀ w ∈ Metric.ball c r, HasDerivAt F (chartFormCoeff (X := X) Q₀ i w) w) ∧
      lineIntegral (periodBasisForm X i) γ =
        F ((chartAt (H := ℂ) Q₀) (γ 1)) - F ((chartAt (H := ℂ) Q₀) (γ 0)) := by
  set e := chartAt (H := ℂ) Q₀ with he
  -- `chartFormCoeff Q₀ i` is holomorphic on the (sub-)ball ⟹ has a primitive `F`.
  have hcoeff_diffOn : DifferentiableOn ℂ (chartFormCoeff (X := X) Q₀ i) (Metric.ball c r) :=
    (chartFormCoeff_differentiableOn Q₀ i).mono hsub
  obtain ⟨F, hF⟩ := hcoeff_diffOn.isExactOn_ball
  refine ⟨F, hF, ?_⟩
  set g : ℝ → ℂ := e.toFun ∘ γ with hg
  have hg_ball' : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ Metric.ball c r := hg_ball
  have huIcc_sub : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le (by norm_num)
  -- `F ∘ g` has derivative `coeff(g t) · g'(t)` by the chain rule.
  have hFg_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (F ∘ g) (chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1)) t := by
    intro t ht
    rw [huIcc_sub] at ht
    have hg_deriv : HasDerivAt g (fderiv ℝ g t 1) t := (hγ_diff t (huIcc_sub ▸ ht)).hasDerivAt
    have hF_at : HasDerivAt F (chartFormCoeff (X := X) Q₀ i (g t)) (g t) := hF (g t) (hg_ball' t ht)
    have := hF_at.comp t hg_deriv
    convert this using 1
  unfold lineIntegral
  -- The line-integral integrand equals `coeff(g t) · g'(t)` on `[0,1]`.
  have hintegrand : Set.EqOn
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
      (fun t => chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1))
      (Set.uIcc 0 1) := by
    intro t ht
    rw [huIcc_sub] at ht
    have h_src_nbhd : ∀ᶠ s : ℝ in nhds t, γ s ∈ e.source :=
      (e.open_source.preimage hγ_cont).mem_nhds (hγ_in t ht)
    exact chartFrame_cancel_general Q₀ γ i t h_src_nbhd (hγ_diff t (huIcc_sub ▸ ht))
  rw [intervalIntegral.integral_congr hintegrand,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hFg_deriv
      (hint.congr (fun t ht => hintegrand (Set.uIoc_subset_uIcc ht)))]
  rfl

/-- **Chart-local path-independence on a sub-ball of the chart target.** Generalizes
`lineIntegral_eq_of_chart_ball_endpoints`: two C¹ paths `γ₁, γ₂` whose chart-images lie in a
common ball `Metric.ball c r ⊆ (chartAt Q₀).target` and share chart-coordinate endpoints have
equal line integrals. This is the form directly usable from the subdivision machinery, where
the relevant ball is the `chart_restrict_to_ball` ball sitting inside the chart target. -/
lemma lineIntegral_eq_of_chart_subball_endpoints
    (Q₀ : X) (γ₁ γ₂ : ℝ → X) (i : Fin (kirovGenus X)) (c : ℂ) (r : ℝ)
    (hsub : Metric.ball c r ⊆ (chartAt (H := ℂ) Q₀).target)
    (hg₁_ball : ∀ t ∈ Set.Icc (0 : ℝ) 1, (chartAt (H := ℂ) Q₀) (γ₁ t) ∈ Metric.ball c r)
    (hg₂_ball : ∀ t ∈ Set.Icc (0 : ℝ) 1, (chartAt (H := ℂ) Q₀) (γ₂ t) ∈ Metric.ball c r)
    (hγ₁_in : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₁ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ₂_in : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₂ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ₁_cont : Continuous γ₁) (hγ₂_cont : Continuous γ₂)
    (hγ₁_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ₁) t)
    (hγ₂_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ₂) t)
    (hint₁ : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ₁ t) (pathSpeed γ₁ t)) volume 0 1)
    (hint₂ : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ₂ t) (pathSpeed γ₂ t)) volume 0 1)
    (h0 : (chartAt (H := ℂ) Q₀) (γ₁ 0) = (chartAt (H := ℂ) Q₀) (γ₂ 0))
    (h1 : (chartAt (H := ℂ) Q₀) (γ₁ 1) = (chartAt (H := ℂ) Q₀) (γ₂ 1)) :
    lineIntegral (periodBasisForm X i) γ₁ = lineIntegral (periodBasisForm X i) γ₂ := by
  obtain ⟨F₁, hF₁, he₁⟩ :=
    lineIntegral_eq_primitive_diff_in_subball Q₀ γ₁ i c r hsub hg₁_ball hγ₁_in hγ₁_cont hγ₁_diff hint₁
  obtain ⟨F₂, hF₂, he₂⟩ :=
    lineIntegral_eq_primitive_diff_in_subball Q₀ γ₂ i c r hsub hg₂_ball hγ₂_in hγ₂_cont hγ₂_diff hint₂
  set D : ℂ → ℂ := fun z => F₁ z - F₂ z with hD
  have hD_diff : DifferentiableOn ℂ D (Metric.ball c r) := fun w hw =>
    ((hF₁ w hw).sub (hF₂ w hw)).differentiableAt.differentiableWithinAt
  have hD_deriv0 : Set.EqOn (deriv D) 0 (Metric.ball c r) := by
    intro w hw
    have : HasDerivAt D 0 w := by simpa using (hF₁ w hw).sub (hF₂ w hw)
    simp [this.deriv]
  have hp0 : (chartAt (H := ℂ) Q₀) (γ₁ 0) ∈ Metric.ball c r := hg₁_ball 0 ⟨le_rfl, zero_le_one⟩
  have hp1 : (chartAt (H := ℂ) Q₀) (γ₁ 1) ∈ Metric.ball c r := hg₁_ball 1 ⟨zero_le_one, le_rfl⟩
  have hDeq : D ((chartAt (H := ℂ) Q₀) (γ₁ 1)) = D ((chartAt (H := ℂ) Q₀) (γ₁ 0)) :=
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
      hD_diff hD_deriv0 hp1 hp0
  rw [he₁, he₂, ← h0, ← h1]
  have hthis := hDeq
  simp only [hD] at hthis
  linear_combination hthis

/-! ## Sub-interval primitive-difference (telescoping primitive)

The lemmas above integrate over the *full* interval `[0,1]` (i.e. over `lineIntegral`). For the
global off-branch assembly we instead need the **partial** line integral over a sub-interval
`[a,b] ⊆ [0,1]` of a loop: when the sub-arc `γ([a,b])` lies in a sub-ball of one chart, the
partial integral `∫ t in a..b, ωᵢ(γ t)(γ'(t))` equals the primitive-difference
`F(chart γ(b)) − F(chart γ(a))`, hence depends on `γ` only through its chart-coordinate values at
`a` and `b`. This is the "splice" primitive: replacing a sub-arc of a loop by a same-chart-endpoints
detour over the SAME parameter sub-interval leaves the partial integral — and therefore (by
additivity over the subdivision) the whole `periodVec` — unchanged, with NO reparametrization. -/

/-- **Sub-interval primitive-difference.** The partial line-integral integrand of `ωᵢ` over a
sub-interval `[a,b]` of a path `γ` whose sub-arc lies in a sub-ball `Metric.ball c r ⊆ chart
target`, integrates to `F(chart γ b) − F(chart γ a)` for the Morera primitive `F`. Hence the
partial integral depends only on the chart-coordinate endpoints `chart γ a`, `chart γ b`. -/
lemma intervalIntegral_form_pathSpeed_eq_primitive_diff_in_subball
    (Q₀ : X) (γ : ℝ → X) (i : Fin (kirovGenus X)) (c : ℂ) (r : ℝ) (a b : ℝ)
    (hsub : Metric.ball c r ⊆ (chartAt (H := ℂ) Q₀).target)
    (hg_ball : ∀ t ∈ Set.uIcc a b, (chartAt (H := ℂ) Q₀) (γ t) ∈ Metric.ball c r)
    (hγ_in : ∀ t ∈ Set.uIcc a b, γ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t)
    (hint : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)) volume a b) :
    ∃ F : ℂ → ℂ,
      (∀ w ∈ Metric.ball c r, HasDerivAt F (chartFormCoeff (X := X) Q₀ i w) w) ∧
      (∫ t in a..b, (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)) =
        F ((chartAt (H := ℂ) Q₀) (γ b)) - F ((chartAt (H := ℂ) Q₀) (γ a)) := by
  set e := chartAt (H := ℂ) Q₀ with he
  have hcoeff_diffOn : DifferentiableOn ℂ (chartFormCoeff (X := X) Q₀ i) (Metric.ball c r) :=
    (chartFormCoeff_differentiableOn Q₀ i).mono hsub
  obtain ⟨F, hF⟩ := hcoeff_diffOn.isExactOn_ball
  refine ⟨F, hF, ?_⟩
  set g : ℝ → ℂ := e.toFun ∘ γ with hg
  have hg_ball' : ∀ t ∈ Set.uIcc a b, g t ∈ Metric.ball c r := hg_ball
  -- `F ∘ g` has derivative `coeff(g t) · g'(t)` by the chain rule on `uIcc a b`.
  have hFg_deriv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (F ∘ g) (chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1)) t := by
    intro t ht
    have hg_deriv : HasDerivAt g (fderiv ℝ g t 1) t := (hγ_diff t ht).hasDerivAt
    have hF_at : HasDerivAt F (chartFormCoeff (X := X) Q₀ i (g t)) (g t) := hF (g t) (hg_ball' t ht)
    have := hF_at.comp t hg_deriv
    convert this using 1
  -- The line-integral integrand equals `coeff(g t) · g'(t)` on `uIcc a b`.
  have hintegrand : Set.EqOn
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
      (fun t => chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1))
      (Set.uIcc a b) := by
    intro t ht
    have h_src_nbhd : ∀ᶠ s : ℝ in nhds t, γ s ∈ e.source :=
      (e.open_source.preimage hγ_cont).mem_nhds (hγ_in t ht)
    exact chartFrame_cancel_general Q₀ γ i t h_src_nbhd (hγ_diff t ht)
  rw [intervalIntegral.integral_congr hintegrand,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hFg_deriv
      (hint.congr (fun t ht => hintegrand (Set.uIoc_subset_uIcc ht)))]
  rfl

/-- **Sub-interval primitive-difference, with a GIVEN primitive `F`.** Identical to
`intervalIntegral_form_pathSpeed_eq_primitive_diff_in_subball`, but `F` (a primitive of
`chartFormCoeff Q₀ i` on the ball) is *supplied as input* rather than produced existentially.
This is what lets a *single* ball-`k` primitive `F` be reused across several confined paths
(the original loop, the detour, and the connecting paths) so that their primitive-differences
telescope — the line integral over each confined path is `F(chart endpoint) − F(chart start)`
with the SAME `F`. -/
lemma intervalIntegral_form_pathSpeed_eq_primitive_diff_of_primitive
    (Q₀ : X) (γ : ℝ → X) (i : Fin (kirovGenus X)) (c : ℂ) (r : ℝ) (a b : ℝ)
    (F : ℂ → ℂ) (hF : ∀ w ∈ Metric.ball c r, HasDerivAt F (chartFormCoeff (X := X) Q₀ i w) w)
    (hg_ball : ∀ t ∈ Set.uIcc a b, (chartAt (H := ℂ) Q₀) (γ t) ∈ Metric.ball c r)
    (hγ_in : ∀ t ∈ Set.uIcc a b, γ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t)
    (hint : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)) volume a b) :
    (∫ t in a..b, (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)) =
      F ((chartAt (H := ℂ) Q₀) (γ b)) - F ((chartAt (H := ℂ) Q₀) (γ a)) := by
  set e := chartAt (H := ℂ) Q₀ with he
  set g : ℝ → ℂ := e.toFun ∘ γ with hg
  have hg_ball' : ∀ t ∈ Set.uIcc a b, g t ∈ Metric.ball c r := hg_ball
  have hFg_deriv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (F ∘ g) (chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1)) t := by
    intro t ht
    have hg_deriv : HasDerivAt g (fderiv ℝ g t 1) t := (hγ_diff t ht).hasDerivAt
    have hF_at : HasDerivAt F (chartFormCoeff (X := X) Q₀ i (g t)) (g t) := hF (g t) (hg_ball' t ht)
    have := hF_at.comp t hg_deriv
    convert this using 1
  have hintegrand : Set.EqOn
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
      (fun t => chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1))
      (Set.uIcc a b) := by
    intro t ht
    have h_src_nbhd : ∀ᶠ s : ℝ in nhds t, γ s ∈ e.source :=
      (e.open_source.preimage hγ_cont).mem_nhds (hγ_in t ht)
    exact chartFrame_cancel_general Q₀ γ i t h_src_nbhd (hγ_diff t ht)
  rw [intervalIntegral.integral_congr hintegrand,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hFg_deriv
      (hint.congr (fun t ht => hintegrand (Set.uIoc_subset_uIcc ht)))]
  rfl

/-- **Sub-interval splice.** Two paths `γ₁, γ₂` whose sub-arcs over `[a,b]` lie in a common
sub-ball and share chart-coordinate endpoints (`chart γ₁ a = chart γ₂ a`, `chart γ₁ b = chart γ₂ b`)
have equal partial line integrals over `[a,b]`. This is the telescoping step: it lets a bad sub-arc
be replaced by a same-chart-endpoints detour over the SAME `[a,b]` without changing the integral. -/
lemma intervalIntegral_form_pathSpeed_eq_of_subball_endpoints
    (Q₀ : X) (γ₁ γ₂ : ℝ → X) (i : Fin (kirovGenus X)) (c : ℂ) (r : ℝ) (a b : ℝ)
    (hsub : Metric.ball c r ⊆ (chartAt (H := ℂ) Q₀).target)
    (hg₁_ball : ∀ t ∈ Set.uIcc a b, (chartAt (H := ℂ) Q₀) (γ₁ t) ∈ Metric.ball c r)
    (hg₂_ball : ∀ t ∈ Set.uIcc a b, (chartAt (H := ℂ) Q₀) (γ₂ t) ∈ Metric.ball c r)
    (hγ₁_in : ∀ t ∈ Set.uIcc a b, γ₁ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ₂_in : ∀ t ∈ Set.uIcc a b, γ₂ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ₁_cont : Continuous γ₁) (hγ₂_cont : Continuous γ₂)
    (hγ₁_diff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ₁) t)
    (hγ₂_diff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ₂) t)
    (hint₁ : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ₁ t) (pathSpeed γ₁ t)) volume a b)
    (hint₂ : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ₂ t) (pathSpeed γ₂ t)) volume a b)
    (h0 : (chartAt (H := ℂ) Q₀) (γ₁ a) = (chartAt (H := ℂ) Q₀) (γ₂ a))
    (h1 : (chartAt (H := ℂ) Q₀) (γ₁ b) = (chartAt (H := ℂ) Q₀) (γ₂ b)) :
    (∫ t in a..b, (periodBasisForm X i).toFun (γ₁ t) (pathSpeed γ₁ t)) =
      (∫ t in a..b, (periodBasisForm X i).toFun (γ₂ t) (pathSpeed γ₂ t)) := by
  obtain ⟨F₁, hF₁, he₁⟩ :=
    intervalIntegral_form_pathSpeed_eq_primitive_diff_in_subball Q₀ γ₁ i c r a b hsub hg₁_ball
      hγ₁_in hγ₁_cont hγ₁_diff hint₁
  obtain ⟨F₂, hF₂, he₂⟩ :=
    intervalIntegral_form_pathSpeed_eq_primitive_diff_in_subball Q₀ γ₂ i c r a b hsub hg₂_ball
      hγ₂_in hγ₂_cont hγ₂_diff hint₂
  set D : ℂ → ℂ := fun z => F₁ z - F₂ z with hD
  have hD_diff : DifferentiableOn ℂ D (Metric.ball c r) := fun w hw =>
    ((hF₁ w hw).sub (hF₂ w hw)).differentiableAt.differentiableWithinAt
  have hD_deriv0 : Set.EqOn (deriv D) 0 (Metric.ball c r) := by
    intro w hw
    have : HasDerivAt D 0 w := by simpa using (hF₁ w hw).sub (hF₂ w hw)
    simp [this.deriv]
  have hp0 : (chartAt (H := ℂ) Q₀) (γ₁ a) ∈ Metric.ball c r := hg₁_ball a Set.left_mem_uIcc
  have hp1 : (chartAt (H := ℂ) Q₀) (γ₁ b) ∈ Metric.ball c r := hg₁_ball b Set.right_mem_uIcc
  have hDeq : D ((chartAt (H := ℂ) Q₀) (γ₁ b)) = D ((chartAt (H := ℂ) Q₀) (γ₁ a)) :=
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
      hD_diff hD_deriv0 hp1 hp0
  rw [he₁, he₂, ← h0, ← h1]
  have hthis := hDeq
  simp only [hD] at hthis
  linear_combination hthis

/-! ## §off-branch surgery — foundational pieces (Layer A)

The remaining geometric construction for `exists_loop_off_branchLocus` is assembled here as
reusable sub-lemmas, then wired together in `Jacobians/TracePullback.lean`.

### A1. Flat seam velocities of `ChartBallPathSmooth`

Every detour piece is a `ChartBallPathSmooth` (a `ChartBallPath` reparametrized by `smoothStep01`).
Because `smoothStep01` has vanishing derivative at `0` and `1`, the pathSpeed of any such piece
vanishes at its own endpoints. This is exactly the `pathSpeed γ 1 = 0` / `pathSpeed γ 0 = 0`
hypothesis that `IsSmoothPath.concat` needs at each seam, so n-fold concatenation of these pieces is
automatically C¹ with NO velocity-matching. -/

/-- **Seam velocity of `ChartBallPathSmooth` vanishes at `t = 0`.** Via the smoothStep chain rule
(`pathSpeed_smoothStep01_comp_eq`) and `smoothStep01_deriv 0 = 0`. The chart-pullback
differentiability of the underlying `ChartBallPath` at `smoothStep01 0 = 0` is supplied by
`ChartBallPath_chart_at_self_differentiableAt`. -/
lemma pathSpeed_ChartBallPathSmooth_zero (Q₀ Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.pathSpeed (Jacobians.ChartBallPathSmooth Q₀ Q) 0 = 0 := by
  have hdiff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (Jacobians.ChartBallPath Q₀ Q₀ Q (Jacobians.smoothStep01 0))).toFun ∘
        Jacobians.ChartBallPath Q₀ Q₀ Q) (Jacobians.smoothStep01 0) :=
    Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q (Jacobians.smoothStep01 0)
      (h_chart_ball _ (Jacobians.smoothStep01_mem_unit 0))
  have h := pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath Q₀ Q₀ Q) 0 hdiff
  show Jacobians.pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q ∘ Jacobians.smoothStep01) 0 = 0
  rw [h, Jacobians.smoothStep01_deriv_zero]; simp

/-- **Seam velocity of `ChartBallPathSmooth` vanishes at `t = 1`.** Same as the `t = 0` case, with
`smoothStep01 1 = 1` and `smoothStep01_deriv 1 = 0`. -/
lemma pathSpeed_ChartBallPathSmooth_one (Q₀ Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.pathSpeed (Jacobians.ChartBallPathSmooth Q₀ Q) 1 = 0 := by
  have hdiff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (Jacobians.ChartBallPath Q₀ Q₀ Q (Jacobians.smoothStep01 1))).toFun ∘
        Jacobians.ChartBallPath Q₀ Q₀ Q) (Jacobians.smoothStep01 1) :=
    Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q (Jacobians.smoothStep01 1)
      (h_chart_ball _ (Jacobians.smoothStep01_mem_unit 1))
  have h := pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath Q₀ Q₀ Q) 1 hdiff
  show Jacobians.pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q ∘ Jacobians.smoothStep01) 1 = 0
  rw [h, Jacobians.smoothStep01_deriv_one]; simp

/-! ### A2. Planar two-segment dodge in ℂ

The geometric heart of the off-branch detour: given a finite set `B ⊆ ℂ` (the chart-coordinate
image of the branch locus), an open ball `Metric.ball c r`, and two points `p, q` in the ball off
`B`, there is a relay point `m` in the ball such that both segments `[p,m]` and `[m,q]` stay in the
ball and avoid `B`. This is the convex/ball-confined analogue of Mathlib's
`Set.Countable.isPathConnected_compl_of_one_lt_rank` (whose proof is the same two-segment dodge),
specialized so the relay stays inside a prescribed ball. The detour `p → m → q` is then pulled back
through the chart and reparametrized (smoothStep) to give a flat-ended off-branch chart path. -/

/-- A neighborhood of `0` in the relay parameter keeps `c + t·y` inside the ball. -/
private lemma eventually_relay_mem_ball (c : ℂ) (r : ℝ) (hr : 0 < r) (y : ℂ) :
    ∀ᶠ t : ℝ in nhds 0, c + (t : ℂ) * y ∈ Metric.ball c r := by
  have hcont : Continuous (fun t : ℝ => c + (t : ℂ) * y) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have h0 : Filter.Tendsto (fun t : ℝ => c + (t : ℂ) * y) (nhds 0) (nhds c) := by
    simpa using hcont.tendsto 0
  exact h0.eventually_mem (Metric.ball_mem_nhds c hr)

/-- **Two-segment planar dodge, ball-confined.** For a finite `B ⊆ ℂ`, an open ball and two points
`p, q` of the ball off `B`, a relay `m` in the ball exists with `[p,m]` and `[m,q]` inside the ball
and disjoint from `B`.

The argument is the ball-confined version of Mathlib's
`Set.Countable.isPathConnected_compl_of_one_lt_rank`: writing `p = cm - x`, `q = cm + x` with `cm`
the midpoint, pick a relay direction `y` linearly independent from `x`; the pencils of segments from
`p` (resp. `q`) to `cm + t·y` are pairwise disjoint off their common vertex, so only countably many
`t` let a segment meet the (countable) `B`. The midpoint `cm` lies in the convex ball, so a whole
neighborhood of `t = 0` keeps `cm + t·y` in the ball; intersecting with the cofinite good set (dense
complement) yields a valid `t`. -/
lemma exists_relay_dodge_finite (B : Set ℂ) (hB : B.Finite) (c : ℂ) (r : ℝ)
    (p q : ℂ) (hp : p ∈ Metric.ball c r) (hq : q ∈ Metric.ball c r)
    (hpB : p ∉ B) (hqB : q ∉ B) :
    ∃ m ∈ Metric.ball c r,
      segment ℝ p m ⊆ Metric.ball c r ∧ segment ℝ m q ⊆ Metric.ball c r ∧
      Disjoint (segment ℝ p m) B ∧ Disjoint (segment ℝ m q) B := by
  classical
  have hBc : B.Countable := hB.countable
  have hr : 0 < r := Metric.pos_of_mem_ball hp
  -- Midpoint / half-difference decomposition: p = cm - x, q = cm + x.
  set cm : ℂ := (2 : ℝ)⁻¹ • (p + q) with hcm
  set x : ℂ := (2 : ℝ)⁻¹ • (q - p) with hx
  have Ip : cm - x = p := by simp only [hcm, hx]; module
  have Iq : cm + x = q := by simp only [hcm, hx]; module
  have hcm_ball : cm ∈ Metric.ball c r := by
    have hmid : cm ∈ segment ℝ p q :=
      ⟨(2:ℝ)⁻¹, (2:ℝ)⁻¹, by norm_num, by norm_num, by norm_num, by rw [hcm]; module⟩
    exact (convex_ball c r).segment_subset hp hq hmid
  -- Relay direction `y` linearly independent from `x`; if `x = 0` then `p = q`, handle separately.
  rcases eq_or_ne x 0 with hx0 | hxne
  · -- p = q: relay m = p works with degenerate segments.
    have hpq : p = q := by rw [← Ip, ← Iq, hx0]; ring
    refine ⟨p, hp, ?_, ?_, ?_, ?_⟩
    · rw [show segment ℝ p p = {p} from segment_same ℝ p]; exact Set.singleton_subset_iff.2 hp
    · rw [← hpq, show segment ℝ p p = {p} from segment_same ℝ p]
      exact Set.singleton_subset_iff.2 hp
    · rw [show segment ℝ p p = {p} from segment_same ℝ p]; exact Set.disjoint_singleton_left.2 hpB
    · rw [← hpq, show segment ℝ p p = {p} from segment_same ℝ p]
      exact Set.disjoint_singleton_left.2 hpB
  · obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
      exists_linearIndependent_pair_of_one_lt_rank
        (by rw [Complex.rank_real_complex]; exact_mod_cast one_lt_two) hxne
    -- bad-t for the q-vertex (q = cm + x) and p-vertex (p = cm - x).
    have A : Set.Countable {t : ℝ | (segment ℝ q (cm + t • y) ∩ B).Nonempty} := by
      apply countable_setOf_nonempty_of_disjoint _ (fun t => Set.inter_subset_right) hBc
      intro t t' htt'
      apply Set.disjoint_iff_inter_eq_empty.2
      have N : {cm + x} ∩ B = ∅ := by
        rw [Set.singleton_inter_eq_empty]; rw [Iq]; exact hqB
      have hseg : ∀ s : ℝ, segment ℝ q (cm + s • y) = segment ℝ (cm + x) (cm + s • y) := by
        intro s; rw [Iq]
      simp only [hseg t, hseg t']
      rw [Set.inter_assoc, Set.inter_comm B, Set.inter_assoc, Set.inter_self,
        ← Set.inter_assoc, ← Set.subset_empty_iff, ← N]
      apply Set.inter_subset_inter_left
      exact Eq.subset (segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm cm)
    have Bc : Set.Countable {t : ℝ | (segment ℝ p (cm + t • y) ∩ B).Nonempty} := by
      apply countable_setOf_nonempty_of_disjoint _ (fun t => Set.inter_subset_right) hBc
      intro t t' htt'
      apply Set.disjoint_iff_inter_eq_empty.2
      have N : {cm - x} ∩ B = ∅ := by
        rw [Set.singleton_inter_eq_empty]; rw [Ip]; exact hpB
      have hseg : ∀ s : ℝ, segment ℝ p (cm + s • y) = segment ℝ (cm + -x) (cm + s • y) := by
        intro s; rw [show cm + -x = p by rw [← Ip]; ring]
      simp only [hseg t, hseg t']
      rw [Set.inter_assoc, Set.inter_comm B, Set.inter_assoc, Set.inter_self,
        ← Set.inter_assoc, ← Set.subset_empty_iff, ← N]
      apply Set.inter_subset_inter_left
      rw [show cm - x = cm + -x by ring]
      refine Eq.subset (segment_inter_eq_endpoint_of_linearIndependent_of_ne ?_ htt'.symm cm)
      have := hy.units_smul ![(-1 : ℝˣ), 1]
      simpa [← List.ofFn_inj, Matrix.cons_val_zero, Matrix.cons_val_one] using this
    -- good relay parameters: cofinite (off both bad sets) ∩ keeps cm+t•y in the ball.
    have hgood : Set.Nonempty (({t : ℝ | (segment ℝ q (cm + t • y) ∩ B).Nonempty} ∪
        {t : ℝ | (segment ℝ p (cm + t • y) ∩ B).Nonempty})ᶜ ∩
        {t : ℝ | cm + t • y ∈ Metric.ball c r}) := by
      have hUnhds : {t : ℝ | cm + t • y ∈ Metric.ball c r} ∈ nhds (0 : ℝ) := by
        have hcont : Continuous (fun t : ℝ => cm + t • y) := by
          have : (fun t : ℝ => cm + t • y) = fun t : ℝ => cm + (t : ℂ) * y := by
            funext t; rw [Complex.real_smul]
          rw [this]
          exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        have h0 : Filter.Tendsto (fun t : ℝ => cm + t • y) (nhds 0) (nhds cm) := by
          simpa using hcont.tendsto 0
        exact h0.eventually_mem (Metric.isOpen_ball.mem_nhds hcm_ball)
      have hdense : Dense (({t : ℝ | (segment ℝ q (cm + t • y) ∩ B).Nonempty} ∪
          {t : ℝ | (segment ℝ p (cm + t • y) ∩ B).Nonempty})ᶜ) :=
        Set.Countable.dense_compl ℝ (A.union Bc)
      exact hdense.inter_nhds_nonempty hUnhds
    obtain ⟨t, ht_good, ht_ball⟩ := hgood
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or,
      Set.not_nonempty_iff_eq_empty] at ht_good
    refine ⟨cm + t • y, ht_ball, ?_, ?_, ?_, ?_⟩
    · exact (convex_ball c r).segment_subset hp ht_ball
    · exact (convex_ball c r).segment_subset ht_ball hq
    · rw [Set.disjoint_iff_inter_eq_empty]; exact ht_good.2
    · rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
      rw [show segment ℝ (cm + t • y) q = segment ℝ q (cm + t • y) from segment_symm _ _ _]
      rw [Set.inter_comm B]; exact ht_good.1

/-! ### A3. General-anchor flat-ended chart path

`ChartBallPathSmooth` (in `SmoothPath.lean`) is anchored at its own start point. For the off-branch
detour we need a flat-ended chart path between two arbitrary points `P, Q` measured in a *third*
anchor's chart `chartAt w` (the common cover anchor of the piece), so that all pieces of `δ'` over
one sub-interval share the chart frame the splice lemma needs. We build it as `ChartBallPath w P Q ∘
smoothStep01` and prove `IsSmoothPath P Q` for it. Every building block already exists for a general
anchor (the `_self` in `ChartBallPath_chart_at_self_differentiableAt` refers to the *moving* frame
`chartAt (γ t)`, not the anchor), so this is the self-anchored `isSmoothPath_ChartBallPathSmooth`
argument with `chartAt w P`, `chartAt w Q` in place of `chartAt Q₀ Q₀`, `chartAt Q₀ Q`. -/

/-- Flat-ended chart-linear path `P → Q` in the chart at anchor `w` (smoothStep-reparametrized so
both endpoint velocities vanish). -/
noncomputable def ChartBallPathSmooth3 (w P Q : X) : ℝ → X :=
  fun t => Jacobians.ChartBallPath w P Q (Jacobians.smoothStep01 t)

/-- `ChartBallPathSmooth3 w P Q 0 = P` when `P` is in the anchor chart's source. -/
@[simp] lemma ChartBallPathSmooth3_zero (w P Q : X) (hP : P ∈ (chartAt (H := ℂ) w).source) :
    ChartBallPathSmooth3 w P Q 0 = P := by
  unfold ChartBallPathSmooth3
  rw [Jacobians.smoothStep01_zero]; exact Jacobians.ChartBallPath.start w P Q hP

/-- `ChartBallPathSmooth3 w P Q 1 = Q` when `Q` is in the anchor chart's source. -/
@[simp] lemma ChartBallPathSmooth3_one (w P Q : X) (hQ : Q ∈ (chartAt (H := ℂ) w).source) :
    ChartBallPathSmooth3 w P Q 1 = Q := by
  unfold ChartBallPathSmooth3
  rw [Jacobians.smoothStep01_one]; exact Jacobians.ChartBallPath.finish w P Q hQ

/-- The chart-`w` pullback of `ChartBallPathSmooth3 w P Q` is the affine interpolation
reparametrized by `smoothStep01` — used to read off the chart-coordinate endpoints for the splice. -/
lemma chart_ChartBallPathSmooth3_eq (w P Q : X) (t : ℝ)
    (h_in_target : ((1 - (Jacobians.smoothStep01 t : ℂ)) * (chartAt (H := ℂ) w) P +
      (Jacobians.smoothStep01 t : ℂ) * (chartAt (H := ℂ) w) Q) ∈ (chartAt (H := ℂ) w).target) :
    (chartAt (H := ℂ) w) (ChartBallPathSmooth3 w P Q t) =
      (1 - (Jacobians.smoothStep01 t : ℂ)) * (chartAt (H := ℂ) w) P +
        (Jacobians.smoothStep01 t : ℂ) * (chartAt (H := ℂ) w) Q := by
  unfold ChartBallPathSmooth3
  exact Jacobians.chart_ChartBallPath_eq w P Q (Jacobians.smoothStep01 t) h_in_target

/-- `ChartBallPathSmooth3 w P Q` stays in the anchor chart source on `[0,1]` under the chart-ball
hypothesis. -/
lemma ChartBallPathSmooth3_mem_source (w P Q : X) (t : ℝ)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    ChartBallPathSmooth3 w P Q t ∈ (chartAt (H := ℂ) w).source := by
  unfold ChartBallPathSmooth3
  exact Jacobians.ChartBallPath_mem_source w P Q (Jacobians.smoothStep01 t)
    (h_chart_ball _ (Jacobians.smoothStep01_mem_unit t))

/-- Continuity of `ChartBallPathSmooth3 w P Q` under the chart-ball hypothesis on `[0,1]`. -/
lemma ChartBallPathSmooth3_continuous (w P Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    Continuous (ChartBallPathSmooth3 w P Q) := by
  unfold ChartBallPathSmooth3
  refine (Jacobians.ChartBallPath_continuousOn_target_set w P Q (Set.Icc 0 1) ?_).comp_continuous
    Jacobians.smoothStep01_continuous (fun t => Jacobians.smoothStep01_mem_unit t)
  intro s hs; exact h_chart_ball s hs

/-- Moving-frame chart-pullback differentiability of `ChartBallPathSmooth3` (the `IsSmoothPath.diff`
field). Chain rule on `(general-anchor ChartBallPath chart-pullback) ∘ smoothStep01`. -/
lemma ChartBallPathSmooth3_chart_at_differentiableAt (w P Q : X) (t : ℝ)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    DifferentiableAt ℝ
      ((chartAt (H := ℂ) (ChartBallPathSmooth3 w P Q t)).toFun ∘ ChartBallPathSmooth3 w P Q) t := by
  have h_at : ((1 - (Jacobians.smoothStep01 t : ℂ)) * (chartAt (H := ℂ) w) P +
      (Jacobians.smoothStep01 t : ℂ) * (chartAt (H := ℂ) w) Q) ∈ (chartAt (H := ℂ) w).target :=
    h_chart_ball _ (Jacobians.smoothStep01_mem_unit t)
  have h_inner : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (Jacobians.ChartBallPath w P Q (Jacobians.smoothStep01 t))).toFun ∘
        Jacobians.ChartBallPath w P Q) (Jacobians.smoothStep01 t) :=
    Jacobians.ChartBallPath_chart_at_self_differentiableAt w P Q (Jacobians.smoothStep01 t) h_at
  have h_eq : ((chartAt (H := ℂ) (ChartBallPathSmooth3 w P Q t)).toFun ∘ ChartBallPathSmooth3 w P Q) =
      ((chartAt (H := ℂ) (Jacobians.ChartBallPath w P Q (Jacobians.smoothStep01 t))).toFun ∘
        Jacobians.ChartBallPath w P Q) ∘ Jacobians.smoothStep01 := by
    funext s; rfl
  rw [h_eq]
  exact h_inner.comp t (Jacobians.smoothStep01_differentiable t)

/-- Velocity-section continuity of `ChartBallPathSmooth3` (the `IsSmoothPath.velCont` field). The
path is `(chartAt w).symm ∘ β` with `β` the smoothStep-reparametrized affine chart-coord curve;
push the model-space velocity continuity through the holomorphic chart inverse via
`velCont_compOn`. -/
lemma ChartBallPathSmooth3_velCont (w P Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    ContinuousOn (fun s : ℝ =>
        Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
          (ChartBallPathSmooth3 w P Q s) (Jacobians.pathSpeed (ChartBallPathSmooth3 w P Q) s))
      (Set.Icc 0 1) := by
  set z₀ : ℂ := (chartAt (H := ℂ) w) P with hz₀
  set z : ℂ := (chartAt (H := ℂ) w) Q with hz
  set β : ℝ → ℂ := fun t : ℝ =>
    (1 - (Jacobians.smoothStep01 t : ℂ)) * z₀ + (Jacobians.smoothStep01 t : ℂ) * z with hβ
  have hβcont : Continuous β := by
    refine Continuous.add ?_ ?_
    · exact (continuous_const.sub
        (Complex.continuous_ofReal.comp Jacobians.smoothStep01_continuous)).mul continuous_const
    · exact (Complex.continuous_ofReal.comp Jacobians.smoothStep01_continuous).mul continuous_const
  have hβderiv_eq : deriv β = fun t : ℝ => (Jacobians.smoothStep01_deriv t : ℂ) * (z - z₀) := by
    funext t
    have hσ : HasDerivAt (fun s : ℝ => (Jacobians.smoothStep01 s : ℂ))
        (Jacobians.smoothStep01_deriv t : ℂ) t :=
      (Jacobians.smoothStep01_hasDerivAt_explicit t).ofReal_comp
    have hβhd : HasDerivAt β ((Jacobians.smoothStep01_deriv t : ℂ) * (z - z₀)) t := by
      have h1 : HasDerivAt (fun s : ℝ => (1 - (Jacobians.smoothStep01 s : ℂ)) * z₀)
          (-(Jacobians.smoothStep01_deriv t : ℂ) * z₀) t := by
        simpa using (hσ.const_sub 1).mul_const z₀
      have h2 : HasDerivAt (fun s : ℝ => (Jacobians.smoothStep01 s : ℂ) * z)
          ((Jacobians.smoothStep01_deriv t : ℂ) * z) t := hσ.mul_const z
      have hsum := h1.add h2
      convert hsum using 1; ring
    exact hβhd.deriv
  have hβ' : Continuous (deriv β) := by
    rw [hβderiv_eq]
    exact (Complex.continuous_ofReal.comp Jacobians.smoothStep01_deriv_continuous).mul
      continuous_const
  have hβvel := velCont_modelPath β hβcont hβ'
  have hVo : IsOpen (chartAt (H := ℂ) w).target := (chartAt (H := ℂ) w).open_target
  have hg : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (fun v : ℂ => (chartAt (H := ℂ) w).symm v)
      (chartAt (H := ℂ) w).target := Jacobians.chartAt_symm_contMDiffOn w
  have hβV : ∀ s ∈ Set.Icc (0 : ℝ) 1, β s ∈ (chartAt (H := ℂ) w).target := by
    intro s hs; exact h_chart_ball (Jacobians.smoothStep01 s) (Jacobians.smoothStep01_mem_unit s)
  have hβdiff : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (β s)).toFun ∘ β) s := by
    intro s _
    have hd : DifferentiableAt ℝ β s :=
      ((differentiableAt_const _).sub
        (Complex.ofRealCLM.differentiableAt.comp s (Jacobians.smoothStep01_differentiable s))
          |>.mul (differentiableAt_const _)).add
        ((Complex.ofRealCLM.differentiableAt.comp s (Jacobians.smoothStep01_differentiable s))
          |>.mul (differentiableAt_const _))
    exact hd
  have hcompOn := velCont_compOn (fun v : ℂ => (chartAt (H := ℂ) w).symm v) hg hVo β hβV
    hβcont hβdiff hβvel
  exact hcompOn

/-- **`IsSmoothPath` for the general-anchor flat-ended chart path.** Assembled from the fields
above; this is the per-piece building block of the off-branch detour. -/
lemma isSmoothPath_ChartBallPathSmooth3 (w P Q : X)
    (hP : P ∈ (chartAt (H := ℂ) w).source) (hQ : Q ∈ (chartAt (H := ℂ) w).source)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    Jacobians.IsSmoothPath P Q (ChartBallPathSmooth3 w P Q) :=
  ⟨ChartBallPathSmooth3_zero w P Q hP, ChartBallPathSmooth3_one w P Q hQ,
    ChartBallPathSmooth3_continuous w P Q h_chart_ball,
    fun t _ => ChartBallPathSmooth3_chart_at_differentiableAt w P Q t h_chart_ball,
    ChartBallPathSmooth3_velCont w P Q h_chart_ball⟩

/-- Endpoint velocities of `ChartBallPathSmooth3` vanish (smoothStep chain rule, as in A1). -/
lemma pathSpeed_ChartBallPathSmooth3_zero (w P Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    Jacobians.pathSpeed (ChartBallPathSmooth3 w P Q) 0 = 0 := by
  have hdiff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (Jacobians.ChartBallPath w P Q (Jacobians.smoothStep01 0))).toFun ∘
        Jacobians.ChartBallPath w P Q) (Jacobians.smoothStep01 0) :=
    Jacobians.ChartBallPath_chart_at_self_differentiableAt w P Q (Jacobians.smoothStep01 0)
      (h_chart_ball _ (Jacobians.smoothStep01_mem_unit 0))
  have h := pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath w P Q) 0 hdiff
  show Jacobians.pathSpeed (Jacobians.ChartBallPath w P Q ∘ Jacobians.smoothStep01) 0 = 0
  rw [h, Jacobians.smoothStep01_deriv_zero]; simp

lemma pathSpeed_ChartBallPathSmooth3_one (w P Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    Jacobians.pathSpeed (ChartBallPathSmooth3 w P Q) 1 = 0 := by
  have hdiff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (Jacobians.ChartBallPath w P Q (Jacobians.smoothStep01 1))).toFun ∘
        Jacobians.ChartBallPath w P Q) (Jacobians.smoothStep01 1) :=
    Jacobians.ChartBallPath_chart_at_self_differentiableAt w P Q (Jacobians.smoothStep01 1)
      (h_chart_ball _ (Jacobians.smoothStep01_mem_unit 1))
  have h := pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath w P Q) 1 hdiff
  show Jacobians.pathSpeed (Jacobians.ChartBallPath w P Q ∘ Jacobians.smoothStep01) 1 = 0
  rw [h, Jacobians.smoothStep01_deriv_one]; simp

/-! ### A4. Balanced binary glue of `2^d` flat-ended pieces

The off-branch loop `δ'` is assembled from per-sub-interval detours by a **balanced binary
concatenation** of `2^d` pieces. Because `Jacobians.concat` always splits the parameter at `1/2`,
balanced (rather than right-linear) nesting makes the `k`-th piece occupy *exactly* the uniform
dyadic sub-interval `[k/2^d, (k+1)/2^d]`, and the split points align with the dyadic breakpoints —
so the whole construction reuses the proven `concat` suite with **no** variable-split-point or affine
reparametrization machinery.

`balancedGlue g d` glues `g 0, …, g (2^d - 1)`. Every piece is flat-ended (zero endpoint velocity),
so each `concat` junction is C¹ for free (`IsSmoothPath.concat`). The fundamental
`balancedGlue_apply_of_mem` reads off the value on the `k`-th dyadic interval as `g k` affinely
reparametrized by `t ↦ 2^d · t − k`. -/

/-- Balanced binary concatenation of `2^d` paths `g 0, …, g (2^d-1)` (split always at the midpoint,
so pieces land on uniform dyadic sub-intervals). -/
noncomputable def balancedGlue (g : ℕ → ℝ → X) : ℕ → ℝ → X
  | 0 => g 0
  | (d+1) => Jacobians.concat (balancedGlue g d) (balancedGlue (fun k => g (2^d + k)) d)

@[simp] lemma balancedGlue_zero (g : ℕ → ℝ → X) : balancedGlue g 0 = g 0 := rfl

lemma balancedGlue_succ (g : ℕ → ℝ → X) (d : ℕ) :
    balancedGlue g (d+1) =
      Jacobians.concat (balancedGlue g d) (balancedGlue (fun k => g (2^d + k)) d) := rfl

/-- **Value of the balanced glue on the `k`-th dyadic sub-interval.** For `k < 2^d` and
`t ∈ [k/2^d, (k+1)/2^d]`, the glue equals `g k` reparametrized affinely by `t ↦ 2^d·t − k`.
The chaining hypothesis `hchain` (consecutive pieces share their shared node value) handles the
junctions, which `concat` resolves by its left branch. -/
lemma balancedGlue_apply_of_mem (g : ℕ → ℝ → X) (hchain : ∀ j, g j 1 = g (j+1) 0)
    (d : ℕ) (k : ℕ) (hk : k < 2^d) (t : ℝ)
    (ht0 : (k : ℝ) / 2^d ≤ t) (ht1 : t ≤ ((k : ℝ) + 1) / 2^d) :
    balancedGlue g d t = g k ((2:ℝ)^d * t - k) := by
  induction d generalizing g k t with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [balancedGlue_zero, pow_zero, Nat.cast_zero, one_mul, sub_zero]
  | succ d ih =>
    have h2d : (0:ℝ) < 2^d := by positivity
    rw [balancedGlue_succ]
    rcases lt_or_ge k (2^d) with hklt | hkge
    · -- left half: k < 2^d, so t ≤ 1/2.
      have hk1 : ((k:ℝ) + 1) ≤ 2^d := by exact_mod_cast hklt
      have ht0' : (k:ℝ) / 2^d ≤ 2 * t := by
        have h := ht0; rw [pow_succ, div_le_iff₀ (by positivity)] at h
        rw [div_le_iff₀ h2d]; nlinarith
      have ht1' : 2 * t ≤ ((k:ℝ) + 1) / 2^d := by
        have h := ht1; rw [pow_succ, le_div_iff₀ (by positivity)] at h
        rw [le_div_iff₀ h2d]; nlinarith
      have ht_le_half : t ≤ 1/2 := by
        have : 2 * t ≤ ((k:ℝ)+1) / 2^d := ht1'
        rw [le_div_iff₀ h2d] at this; nlinarith
      rw [Jacobians.concat_apply_left _ _ ht_le_half, ih g hchain k hklt (2*t) ht0' ht1']
      rw [pow_succ]; ring_nf
    · -- right half: 2^d ≤ k < 2^(d+1).
      have hk2 : k < 2^d + 2^d := by have := hk; rw [pow_succ] at this; omega
      set k' := k - 2^d with hk'_def
      have hkk' : k = 2^d + k' := by omega
      have hk'lt : k' < 2^d := by omega
      have hk_cast : (k:ℝ) = 2^d + k' := by rw [hkk']; push_cast; ring
      have ht_ge_half : (1:ℝ)/2 ≤ t := by
        have h := ht0; rw [pow_succ, div_le_iff₀ (by positivity)] at h
        have hkge' : (2:ℝ)^d ≤ k := by exact_mod_cast hkge
        nlinarith
      rcases eq_or_lt_of_le ht_ge_half with hhalf | hgt
      · -- t = 1/2: must be the left node k = 2^d, k' = 0; resolved by chaining.
        have ht_le : t ≤ 1/2 := le_of_eq hhalf.symm
        rw [Jacobians.concat_apply_left _ _ ht_le]
        have hk_eq : k = 2^d := by
          have hlo : (k:ℝ) / 2^(d+1) ≤ 1/2 := by linarith
          rw [pow_succ, div_le_iff₀ (by positivity)] at hlo
          have : (k:ℝ) ≤ 2^d := by nlinarith
          have hkle : k ≤ 2^d := by exact_mod_cast this
          omega
        have h2t1 : 2 * t = 1 := by rw [← hhalf]; ring
        rw [h2t1]
        have h1le : 1 ≤ 2^d := Nat.one_le_two_pow
        have hcastsub : ((2^d : ℕ) - 1 : ℕ) = (2^d : ℝ) - 1 := by
          push_cast [Nat.cast_sub h1le]; ring
        have hidx : (2^d : ℕ) - 1 < 2^d := by omega
        have hlast : (2:ℝ)^d * 1 - (((2^d : ℕ) - 1 : ℕ) : ℝ) = 1 := by rw [hcastsub]; ring
        rw [ih g hchain ((2^d : ℕ) - 1) hidx 1
              (by rw [hcastsub, div_le_one h2d]; linarith)
              (by rw [hcastsub, le_div_iff₀ h2d]; nlinarith), hlast]
        have hrhs_arg : (2:ℝ)^(d+1) * t - k = 0 := by
          rw [← hhalf, hk_eq]; push_cast [pow_succ]; ring
        rw [hrhs_arg, hk_eq]
        have hchain_last := hchain ((2^d : ℕ) - 1)
        rwa [Nat.sub_add_cancel h1le] at hchain_last
      · -- t > 1/2: right branch.
        rw [Jacobians.concat_apply_right _ _ (not_le.mpr hgt)]
        have ht0' : (k':ℝ) / 2^d ≤ 2 * t - 1 := by
          have h := ht0; rw [pow_succ, div_le_iff₀ (by positivity)] at h
          rw [hk_cast] at h; rw [div_le_iff₀ h2d]; nlinarith
        have ht1' : 2 * t - 1 ≤ ((k':ℝ) + 1) / 2^d := by
          have h := ht1; rw [pow_succ, le_div_iff₀ (by positivity)] at h
          rw [hk_cast] at h; rw [le_div_iff₀ h2d]; nlinarith
        rw [ih (fun j => g (2^d + j)) (fun j => hchain (2^d + j)) k' hk'lt (2*t-1) ht0' ht1']
        congr 1
        · rw [hkk']
        · rw [hk_cast, pow_succ]; ring

/-- **`balancedGlue` is a flat-ended smooth path with vanishing endpoint velocities.** The
`n`-piece (dyadic) generalization of `IsSmoothPath.concat`: every piece `g k` (`k < 2^d`) is a
flat-ended smooth path (zero endpoint velocity), consecutive pieces chain (`g k 1 = g (k+1) 0`), so
each `concat` seam is `C¹` for free. Carried alongside the `IsSmoothPath` are the two endpoint
velocities of the glue itself (`= pathSpeed (g 0) 0 = 0` and `= pathSpeed (g (2^d-1)) 1 = 0`),
needed as the junction hypotheses of the next `concat` in the induction. -/
lemma isSmoothPath_balancedGlue (g : ℕ → ℝ → X)
    (hchain : ∀ j, g j 1 = g (j+1) 0) (d : ℕ)
    (hpiece : ∀ k, k < 2^d → Jacobians.IsSmoothPath (g k 0) (g k 1) (g k))
    (hv0 : ∀ k, k < 2^d → Jacobians.pathSpeed (g k) 0 = 0)
    (hv1 : ∀ k, k < 2^d → Jacobians.pathSpeed (g k) 1 = 0) :
    Jacobians.IsSmoothPath (g 0 0) (g (2^d - 1) 1) (balancedGlue g d) ∧
      Jacobians.pathSpeed (balancedGlue g d) 0 = 0 ∧
      Jacobians.pathSpeed (balancedGlue g d) 1 = 0 := by
  induction d generalizing g with
  | zero =>
    have h2 : (2:ℕ)^0 = 1 := pow_zero 2
    have hk0 : (0:ℕ) < 2^0 := by simp
    have hidx : (2:ℕ)^0 - 1 = 0 := by simp
    rw [balancedGlue_zero, hidx]
    exact ⟨hpiece 0 hk0, hv0 0 hk0, hv1 0 hk0⟩
  | succ d ih =>
    have h2d_pos : (0:ℕ) < 2^d := pow_pos (by norm_num) d
    -- left and right half-glues with their hypotheses.
    have hpieceL : ∀ k, k < 2^d → Jacobians.IsSmoothPath (g k 0) (g k 1) (g k) :=
      fun k hk => hpiece k (by have := pow_succ 2 d; omega)
    have hv0L : ∀ k, k < 2^d → Jacobians.pathSpeed (g k) 0 = 0 :=
      fun k hk => hv0 k (by have := pow_succ 2 d; omega)
    have hv1L : ∀ k, k < 2^d → Jacobians.pathSpeed (g k) 1 = 0 :=
      fun k hk => hv1 k (by have := pow_succ 2 d; omega)
    set gR : ℕ → ℝ → X := fun k => g (2^d + k) with hgR
    have hchainR : ∀ j, gR j 1 = gR (j+1) 0 := fun j => by
      simp only [hgR]; rw [show 2^d + (j+1) = (2^d + j) + 1 from by ring]; exact hchain (2^d + j)
    have hpieceR : ∀ k, k < 2^d → Jacobians.IsSmoothPath (gR k 0) (gR k 1) (gR k) :=
      fun k hk => hpiece (2^d + k) (by have := pow_succ 2 d; omega)
    have hv0R : ∀ k, k < 2^d → Jacobians.pathSpeed (gR k) 0 = 0 :=
      fun k hk => hv0 (2^d + k) (by have := pow_succ 2 d; omega)
    have hv1R : ∀ k, k < 2^d → Jacobians.pathSpeed (gR k) 1 = 0 :=
      fun k hk => hv1 (2^d + k) (by have := pow_succ 2 d; omega)
    obtain ⟨hspL, hL0, hL1⟩ := ih g hchain hpieceL hv0L hv1L
    obtain ⟨hspR, hR0, hR1⟩ := ih gR hchainR hpieceR hv0R hv1R
    -- the junction value matches: g (2^d - 1) 1 = gR 0 0 = g (2^d) 0.
    have hmid : g (2^d - 1) 1 = gR 0 0 := by
      simp only [hgR, Nat.add_zero]
      have := hchain (2^d - 1)
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))] at this
    -- right half retargeted so its start point is the left half's finish.
    have hspR' : Jacobians.IsSmoothPath (g (2^d - 1) 1) (gR (2^d - 1) 1) (balancedGlue gR d) := by
      rw [hmid]; exact hspR
    -- concat is a smooth path from `g 0 0` to `gR (2^d-1) 1`.
    have hconcat : Jacobians.IsSmoothPath (g 0 0) (gR (2^d - 1) 1)
        (Jacobians.concat (balancedGlue g d) (balancedGlue gR d)) :=
      hspL.concat hspR' hL1 hR0
    have hidx_succ : (2:ℕ)^(d+1) - 1 = 2^d + (2^d - 1) := by
      have : (2:ℕ)^(d+1) = 2^d + 2^d := by rw [pow_succ]; ring
      omega
    have hfinish_eq : gR (2^d - 1) 1 = g (2^(d+1) - 1) 1 := by
      simp only [hgR]; rw [hidx_succ]
    rw [balancedGlue_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hfinish_eq]; exact hconcat
    · -- endpoint velocity at 0: pathSpeed (concat L R) 0 = 2 * pathSpeed L 0 = 0.
      have hdL0 : DifferentiableAt ℝ
          ((chartAt (H := ℂ) (balancedGlue g d (2 * 0))).toFun ∘ balancedGlue g d) (2 * 0) := by
        rw [show (2:ℝ) * 0 = 0 from by norm_num]
        exact hspL.diff 0 (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_refl _, zero_le_one⟩)
      rw [Jacobians.pathSpeed_concat_left _ _ 0 (by norm_num) hdL0,
        show (2:ℝ) * 0 = 0 from by norm_num, hL0, mul_zero]
    · -- endpoint velocity at 1: pathSpeed (concat L R) 1 = 2 * pathSpeed R 1 = 0.
      have hdR1 : DifferentiableAt ℝ
          ((chartAt (H := ℂ) (balancedGlue gR d (2 * 1 - 1))).toFun ∘ balancedGlue gR d) (2 * 1 - 1) := by
        rw [show (2:ℝ) * 1 - 1 = 1 from by norm_num]
        exact hspR.diff 1 (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩)
      rw [Jacobians.pathSpeed_concat_right _ _ 1 (by norm_num) hdR1,
        show (2:ℝ) * 1 - 1 = 1 from by norm_num, hR1, mul_zero]

/-! ### A4'. Uniform `n`-piece glue

For the off-branch surgery the detour pieces must occupy the **uniform** sub-intervals `[k/n,(k+1)/n]`
handed by `exists_subBallChartCover`, so the dyadic `balancedGlue` is not directly usable.
`uniformGlue g n` glues the `n` flat-ended pieces `g 0, …, g (n-1)` at the uniform breakpoints `k/n`,
reading off the value on the `k`-th piece as `g k` affinely reparametrized by `t ↦ n·t − k`.

`uIdx n t = min ⌊n·t⌋₊-clamped (n-1)` is the piece index; the glue is the closed form
`g (uIdx n t) (n·t − uIdx n t)`. Every piece is flat-ended (zero endpoint velocity) and consecutive
pieces chain (`g k 1 = g (k+1) 0`), so each seam `t = k/n` is `C¹` for free — the same
`HasDerivWithinAt … 0` union argument as `IsSmoothPath.concat`, with split point `k/n` and scale `n`.
-/

/-- **Moving-chart to fixed-anchor differentiability transfer.** If `γ` is continuous, `γ t` lies in
the source of a fixed anchor chart `chartAt Q₀`, and `γ` is chart-pullback-differentiable at `t` in
its own moving chart `chartAt (γ t)`, then it is also chart-pullback-differentiable in the fixed
anchor chart. (Composition with the smooth chart-transition `chartAt Q₀ ∘ (chartAt (γ t)).symm`.) -/
lemma differentiableAt_chart_anchor_of_self (Q₀ : X) (γ : ℝ → X) (t : ℝ)
    (hγcont : Continuous γ)
    (hmem : γ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hdiff : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) :
    DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t := by
  set e := chartAt (H := ℂ) (γ t) with he
  set e0 := chartAt (H := ℂ) Q₀ with he0
  have hmem_e : γ t ∈ e.source := mem_chart_source ℂ (γ t)
  have hopen : IsOpen (e.source ∩ e0.source) := e.open_source.inter e0.open_source
  have ht_mem : γ t ∈ e.source ∩ e0.source := ⟨hmem_e, hmem⟩
  have hpre : (γ ⁻¹' (e.source ∩ e0.source)) ∈ nhds t :=
    hγcont.continuousAt.preimage_mem_nhds (hopen.mem_nhds ht_mem)
  have heq : ((chartAt (H := ℂ) Q₀).toFun ∘ γ) =ᶠ[nhds t]
      ((fun v : ℂ => e0 (e.symm v)) ∘ (e.toFun ∘ γ)) := by
    filter_upwards [hpre] with s hs
    show e0 (γ s) = e0 (e.symm (e (γ s)))
    rw [e.left_inv hs.1]
  rw [heq.differentiableAt_iff]
  have htrans : DifferentiableAt ℝ (fun v : ℂ => e0 (e.symm v)) ((e.toFun ∘ γ) t) := by
    have h_target : (e.toFun ∘ γ) t ∈ e.target := e.map_source hmem_e
    have h_source : e.symm ((e.toFun ∘ γ) t) ∈ e0.source := by
      show e.symm (e (γ t)) ∈ e0.source; rw [e.left_inv hmem_e]; exact hmem
    exact chart_transition_comp_differentiableAt_R (γ t) Q₀ ((e.toFun ∘ γ) t) h_target h_source
  exact htrans.comp t hdiff

/-- Piece index of `t` among `n` uniform sub-intervals of `[0,1]`, clamped to `[0, n-1]`. -/
noncomputable def uIdx (n : ℕ) (t : ℝ) : ℕ := min (⌊(n:ℝ) * t⌋.toNat) (n - 1)

/-- **Uniform `n`-piece glue** of `g 0, …, g (n-1)`: on `[k/n,(k+1)/n]` it is `g k (n·t − k)`. -/
noncomputable def uniformGlue (g : ℕ → ℝ → X) (n : ℕ) : ℝ → X :=
  fun t => g (uIdx n t) ((n:ℝ) * t - uIdx n t)

/-- **Piece index on the half-open `k`-th sub-interval.** For `k < n` and `t ∈ [k/n, (k+1)/n)`,
`uIdx n t = k`. -/
lemma uIdx_eq (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) (t : ℝ)
    (h0 : (k:ℝ)/n ≤ t) (h1 : t < ((k:ℝ)+1)/n) : uIdx n t = k := by
  unfold uIdx
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hb0 : (k:ℝ) ≤ n * t := by rw [div_le_iff₀ hnpos] at h0; linarith
  have hb1 : (n:ℝ) * t < k + 1 := by rw [lt_div_iff₀ hnpos] at h1; linarith
  have hfloor : ⌊(n:ℝ)*t⌋ = (k:ℤ) := by
    rw [Int.floor_eq_iff]; exact ⟨by push_cast; linarith, by push_cast; linarith⟩
  rw [hfloor]; simp only [Int.toNat_natCast]; omega

/-- **Piece index at the right endpoint `t = 1`.** `uIdx n 1 = n - 1`. -/
lemma uIdx_one (n : ℕ) (hn : 0 < n) : uIdx n 1 = n - 1 := by
  unfold uIdx
  rw [mul_one, Int.floor_natCast]
  simp only [Int.toNat_natCast]; omega

/-- **Piece index left of the loop** (`t ≤ 0`): `uIdx n t = 0`. -/
lemma uIdx_zero_of_nonpos (n : ℕ) (t : ℝ) (ht : t ≤ 0) : uIdx n t = 0 := by
  unfold uIdx
  have hnt : (n:ℝ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
  have : ⌊(n:ℝ)*t⌋ ≤ 0 := Int.floor_nonpos hnt
  omega

/-- **Piece index right of the loop** (`t ≥ 1`): `uIdx n t = n - 1`. -/
lemma uIdx_last_of_ge_one (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 1 ≤ t) : uIdx n t = n - 1 := by
  unfold uIdx
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hnt : (n:ℝ) ≤ n * t := by nlinarith
  have : (n:ℤ) ≤ ⌊(n:ℝ)*t⌋ := by rw [Int.le_floor]; push_cast; linarith
  have h2 : (n:ℕ) ≤ ⌊(n:ℝ)*t⌋.toNat := by omega
  omega

/-- **Value of the uniform glue on the closed `k`-th sub-interval** (for `k < n`, with the right
endpoint resolved by chaining `g k 1 = g (k+1) 0`). -/
lemma uniformGlue_apply_of_mem (g : ℕ → ℝ → X) (hchain : ∀ j, g j 1 = g (j+1) 0)
    (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) (t : ℝ)
    (h0 : (k:ℝ)/n ≤ t) (h1 : t ≤ ((k:ℝ)+1)/n) :
    uniformGlue g n t = g k ((n:ℝ) * t - k) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  rcases eq_or_lt_of_le h1 with htop | hlt
  · -- t = (k+1)/n : the right node; resolved by chaining (handle last piece too).
    have hnt : (n:ℝ) * t = k + 1 := by rw [htop]; field_simp
    rcases eq_or_lt_of_le (show k + 1 ≤ n from hk) with hlast | hnext
    · -- k+1 = n : last node t = 1, uIdx = n-1 = k.
      have hncast : (n:ℝ) = (k:ℝ) + 1 := by rw [← hlast]; push_cast; ring
      have ht1 : t = 1 := by rw [htop, hncast]; field_simp
      rw [ht1] at hnt ⊢
      unfold uniformGlue
      rw [uIdx_one n hn, hnt]
      have : n - 1 = k := by omega
      rw [this]
    · -- k+1 < n : node lies in piece (k+1) too; uIdx = k+1, value = g (k+1) 0 = g k 1.
      have hidx : uIdx n t = k + 1 := by
        apply uIdx_eq n hn (k+1) hnext
        · rw [htop]; push_cast; rfl
        · rw [htop]; rw [div_lt_div_iff_of_pos_right hnpos]; push_cast; linarith
      unfold uniformGlue
      rw [hidx, hnt]
      rw [show (k:ℝ) + 1 - ((k+1 : ℕ):ℝ) = 0 from by push_cast; ring]
      rw [show (k:ℝ) + 1 - (k:ℝ) = 1 from by ring]
      exact (hchain k).symm
  · -- t ∈ [k/n, (k+1)/n) : uIdx = k.
    unfold uniformGlue
    rw [uIdx_eq n hn k hk t h0 hlt]

/-- **General affine-reparametrization pathSpeed.** `pathSpeed (s ↦ γ (a·s+b)) t = a · pathSpeed γ
(a·t+b)`, given the chart-pullback of `γ` is differentiable at `a·t+b`. The general-`(a,b)` analogue
of `pathSpeed_concat_left/right` (`a=2`), used at uniform-glue seams (`a=n`). -/
lemma pathSpeed_affine_comp (γ : ℝ → X) (a b t : ℝ)
    (hdiff : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ (a*t+b))).toFun ∘ γ) (a*t+b)) :
    Jacobians.pathSpeed (fun s => γ (a*s+b)) t = (a:ℂ) * Jacobians.pathSpeed γ (a*t+b) := by
  unfold Jacobians.pathSpeed
  show fderiv ℝ ((chartAt (H := ℂ) (γ (a*t+b))).toFun ∘ (fun s => γ (a*s+b))) t (1:ℝ)
      = (a:ℂ) * fderiv ℝ ((chartAt (H := ℂ) (γ (a*t+b))).toFun ∘ γ) (a*t+b) (1:ℝ)
  set ψ : ℝ → ℂ := (chartAt (H := ℂ) (γ (a*t+b))).toFun ∘ γ with hψ
  have hcomp : (chartAt (H := ℂ) (γ (a*t+b))).toFun ∘ (fun s => γ (a*s+b))
      = ψ ∘ (fun s : ℝ => a*s+b) := by funext s; rfl
  rw [hcomp]
  have haff : DifferentiableAt ℝ (fun s : ℝ => a*s+b) t :=
    ((differentiableAt_const a).mul differentiableAt_id).add (differentiableAt_const b)
  rw [fderiv_comp t hdiff haff]
  have hfa : fderiv ℝ (fun s : ℝ => a*s+b) t (1:ℝ) = a := by
    rw [fderiv_add_const, fderiv_const_mul differentiableAt_id]; simp
  show (fderiv ℝ ψ (a*t+b)) (fderiv ℝ (fun s : ℝ => a*s+b) t 1) = _
  rw [hfa]
  calc (fderiv ℝ ψ (a*t+b)) a
      = (fderiv ℝ ψ (a*t+b)) ((a:ℝ) • (1:ℝ)) := by rw [smul_eq_mul, mul_one]
    _ = (a:ℝ) • (fderiv ℝ ψ (a*t+b)) 1 := (fderiv ℝ ψ (a*t+b)).map_smul a 1
    _ = (a:ℂ) * (fderiv ℝ ψ (a*t+b)) 1 := by rw [Complex.real_smul]

/-- `uniformGlue g n` agrees with the affine reparametrization `s ↦ g k (n·s − k)` of piece `k` on
the closed `k`-th sub-interval `[k/n,(k+1)/n]`. -/
lemma uniformGlue_eqOn_piece (g : ℕ → ℝ → X) (hchain : ∀ j, g j 1 = g (j+1) 0)
    (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) :
    Set.EqOn (uniformGlue g n) (fun s => g k ((n:ℝ) * s - k))
      (Set.Icc ((k:ℝ)/n) (((k:ℝ)+1)/n)) :=
  fun s hs => uniformGlue_apply_of_mem g hchain n hn k hk s hs.1 hs.2

/-- On the open `k`-th sub-interval, the glue locally equals the affine reparam of piece `k`. -/
lemma uniformGlue_eventuallyEq_piece (g : ℕ → ℝ → X) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n)
    (t : ℝ) (ht : t ∈ Set.Ioo ((k:ℝ)/n) (((k:ℝ)+1)/n)) :
    uniformGlue g n =ᶠ[nhds t] (fun s => g k ((n:ℝ)*s - k)) := by
  have hmem : Set.Ioo ((k:ℝ)/n) (((k:ℝ)+1)/n) ∈ nhds t := isOpen_Ioo.mem_nhds ht
  filter_upwards [hmem] with s hs
  obtain ⟨hs1, hs2⟩ := hs
  unfold uniformGlue
  rw [uIdx_eq n hn k hk s (le_of_lt hs1) hs2]

/-- **Seam `C¹`-junction of the uniform glue.** At an interior breakpoint `t₀ = j/n` (`0 < j < n`)
the glue's chart-pullback has derivative `0`: both adjacent pieces are flat-ended, so each one-sided
`HasDerivWithinAt` is `0`, and the two `Icc` halves union to a neighborhood. -/
lemma uniformGlue_seam (g : ℕ → ℝ → X) (hchain : ∀ j, g j 1 = g (j+1) 0) (n : ℕ) (hn : 0 < n)
    (hpiece : ∀ k, k < n → Jacobians.IsSmoothPath (g k 0) (g k 1) (g k))
    (hv0 : ∀ k, k < n → Jacobians.pathSpeed (g k) 0 = 0)
    (hv1 : ∀ k, k < n → Jacobians.pathSpeed (g k) 1 = 0)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n - 1) (t₀ : ℝ) (ht₀ : (n:ℝ) * t₀ = j) :
    HasDerivAt ((chartAt (H := ℂ) (uniformGlue g n t₀)).toFun ∘ uniformGlue g n) 0 t₀ := by
  classical
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hjlt : j < n := by omega
  have hj1lt : j - 1 < n := by omega
  have ht₀eq : t₀ = (j:ℝ)/n := by field_simp at ht₀ ⊢; linarith
  have hval : uniformGlue g n t₀ = g j 0 := by
    have := uniformGlue_apply_of_mem g hchain n hn j hjlt t₀
      (by rw [ht₀eq]) (by rw [ht₀eq, div_le_div_iff_of_pos_right hnpos]; linarith)
    rwa [ht₀, show (j:ℝ) - j = 0 from by ring] at this
  have hchainj : g (j-1) 1 = g j 0 := by
    have := hchain (j-1); rwa [Nat.sub_add_cancel hj1] at this
  rw [hval]
  set c : X := g j 0 with hc
  set f : ℝ → ℂ := (chartAt (H := ℂ) c).toFun ∘ uniformGlue g n with hf
  set gL : ℝ → ℂ := (chartAt (H := ℂ) c).toFun ∘ (fun s => g (j-1) ((n:ℝ)*s-(j-1:ℕ))) with hgLdef
  set gR : ℝ → ℂ := (chartAt (H := ℂ) c).toFun ∘ (fun s => g j ((n:ℝ)*s-(j:ℕ))) with hgRdef
  have hgL_HDA : HasDerivAt gL 0 t₀ := by
    have harg : (n:ℝ)*t₀ - (j-1:ℕ) = 1 := by rw [ht₀, Nat.cast_sub hj1]; push_cast; ring
    have hg_HDA : HasDerivAt ((chartAt (H := ℂ) c).toFun ∘ g (j-1)) 0 1 := by
      have hd : DifferentiableAt ℝ ((chartAt (H := ℂ) (g (j-1) 1)).toFun ∘ g (j-1)) 1 :=
        (hpiece (j-1) hj1lt).diff 1 (by rw [Set.uIcc_of_le (by norm_num:(0:ℝ)≤1)]; exact ⟨zero_le_one,le_refl _⟩)
      have hdz : deriv ((chartAt (H := ℂ) (g (j-1) 1)).toFun ∘ g (j-1)) 1 = 0 := hv1 (j-1) hj1lt
      have : HasDerivAt ((chartAt (H := ℂ) (g (j-1) 1)).toFun ∘ g (j-1)) 0 1 := by
        rw [← hdz]; exact hd.hasDerivAt
      rwa [hchainj] at this
    have haff_HDA : HasDerivAt (fun s:ℝ => (n:ℝ)*s - (j-1:ℕ)) (n:ℝ) t₀ := by
      simpa using ((hasDerivAt_id t₀).const_mul (n:ℝ)).sub_const ((j-1:ℕ):ℝ)
    have := hg_HDA.scomp_of_eq t₀ haff_HDA harg.symm; simpa [hgLdef] using this
  have hgR_HDA : HasDerivAt gR 0 t₀ := by
    have harg : (n:ℝ)*t₀ - (j:ℕ) = 0 := by rw [ht₀]; ring
    have hg_HDA : HasDerivAt ((chartAt (H := ℂ) c).toFun ∘ g j) 0 0 := by
      have hd : DifferentiableAt ℝ ((chartAt (H := ℂ) (g j 0)).toFun ∘ g j) 0 :=
        (hpiece j hjlt).diff 0 (by rw [Set.uIcc_of_le (by norm_num:(0:ℝ)≤1)]; exact ⟨le_refl _,zero_le_one⟩)
      have hdz : deriv ((chartAt (H := ℂ) (g j 0)).toFun ∘ g j) 0 = 0 := hv0 j hjlt
      rw [← hdz]; exact hd.hasDerivAt
    have haff_HDA : HasDerivAt (fun s:ℝ => (n:ℝ)*s - (j:ℕ)) (n:ℝ) t₀ := by
      simpa using ((hasDerivAt_id t₀).const_mul (n:ℝ)).sub_const ((j:ℕ):ℝ)
    have := hg_HDA.scomp_of_eq t₀ haff_HDA harg.symm; simpa [hgRdef] using this
  have hlo : ((j-1:ℕ):ℝ)/n ≤ t₀ := by
    rw [ht₀eq, div_le_div_iff_of_pos_right hnpos, Nat.cast_sub hj1]; push_cast; linarith
  have hhi : t₀ ≤ (((j:ℝ))+1)/n := by
    rw [ht₀eq, div_le_div_iff_of_pos_right hnpos]; linarith
  have heqL : Set.EqOn f gL (Set.Icc (((j-1:ℕ):ℝ)/n) t₀) := by
    intro s hs
    simp only [hf, hgLdef, Function.comp_apply]; congr 1
    have hcast : ((j-1:ℕ):ℝ) + 1 = (j:ℝ) := by rw [Nat.cast_sub hj1]; push_cast; ring
    apply uniformGlue_apply_of_mem g hchain n hn (j-1) hj1lt s hs.1
    rw [hcast]; rw [ht₀eq] at hs; exact hs.2
  have heqR : Set.EqOn f gR (Set.Icc t₀ ((((j:ℝ))+1)/n)) := by
    intro s hs
    simp only [hf, hgRdef, Function.comp_apply]; congr 1
    apply uniformGlue_apply_of_mem g hchain n hn j hjlt s _ hs.2
    rw [ht₀eq] at hs; exact hs.1
  have hL_WDA : HasDerivWithinAt f 0 (Set.Icc (((j-1:ℕ):ℝ)/n) t₀) t₀ :=
    (hgL_HDA.hasDerivWithinAt).congr (fun s hs => heqL hs) (heqL (Set.right_mem_Icc.mpr hlo))
  have hR_WDA : HasDerivWithinAt f 0 (Set.Icc t₀ ((((j:ℝ))+1)/n)) t₀ :=
    (hgR_HDA.hasDerivWithinAt).congr (fun s hs => heqR hs) (heqR (Set.left_mem_Icc.mpr hhi))
  have hunion : HasDerivWithinAt f 0
      (Set.Icc (((j-1:ℕ):ℝ)/n) t₀ ∪ Set.Icc t₀ ((((j:ℝ))+1)/n)) t₀ := hL_WDA.union hR_WDA
  have hnbhd : Set.Icc (((j-1:ℕ):ℝ)/n) t₀ ∪ Set.Icc t₀ ((((j:ℝ))+1)/n) ∈ nhds t₀ := by
    rw [Set.Icc_union_Icc_eq_Icc hlo hhi]
    apply Icc_mem_nhds
    · rw [ht₀eq, div_lt_div_iff_of_pos_right hnpos, Nat.cast_sub hj1]; push_cast; linarith
    · rw [ht₀eq, div_lt_div_iff_of_pos_right hnpos]; linarith
  exact hunion.hasDerivAt hnbhd

/-- `pathSpeed` is local: it agrees on functions equal near the point. -/
lemma pathSpeed_congr_nhds (γ γ' : ℝ → X) (t : ℝ) (h : γ =ᶠ[nhds t] γ') :
    Jacobians.pathSpeed γ t = Jacobians.pathSpeed γ' t := by
  unfold Jacobians.pathSpeed
  rw [h.eq_of_nhds]; congr 1; exact Filter.EventuallyEq.fderiv_eq (h.fun_comp _)

/-- Near `t = 0` the glue equals the affine reparam of piece `0` (clamped index). -/
lemma uniformGlue_eventuallyEq_zero (g : ℕ → ℝ → X) (n : ℕ) (hn : 0 < n) :
    uniformGlue g n =ᶠ[nhds 0] (fun s => g 0 ((n:ℝ)*s - (0:ℕ))) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hmem : Iio ((1:ℝ)/n) ∈ nhds (0:ℝ) := isOpen_Iio.mem_nhds (by simp only [mem_Iio]; positivity)
  filter_upwards [hmem] with s hs
  simp only [Nat.cast_zero, sub_zero]
  rcases le_or_gt s 0 with h | h
  · unfold uniformGlue; rw [uIdx_zero_of_nonpos n s h]; norm_num
  · unfold uniformGlue
    rw [uIdx_eq n hn 0 hn s (by rw [Nat.cast_zero, zero_div]; exact le_of_lt h) (by simpa using hs)]
    norm_num

/-- Near `t = 1` the glue equals the affine reparam of the last piece (clamped index). -/
lemma uniformGlue_eventuallyEq_one (g : ℕ → ℝ → X) (n : ℕ) (hn : 0 < n) :
    uniformGlue g n =ᶠ[nhds 1] (fun s => g (n-1) ((n:ℝ)*s - (n-1:ℕ))) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hmem : Ioi (((n-1:ℕ):ℝ)/n) ∈ nhds (1:ℝ) := by
    apply isOpen_Ioi.mem_nhds
    simp only [mem_Ioi]
    rw [div_lt_one hnpos, Nat.cast_sub hn]; push_cast; linarith
  filter_upwards [hmem] with s hs
  rcases le_or_gt 1 s with h | h
  · unfold uniformGlue; rw [uIdx_last_of_ge_one n hn s h]
  · unfold uniformGlue
    rw [uIdx_eq n hn (n-1) (by omega) s (le_of_lt hs)
        (by rw [show ((n-1:ℕ):ℝ)+1 = (n:ℝ) from by rw [Nat.cast_sub hn]; push_cast; ring,
              div_self (ne_of_gt hnpos)]; exact h)]

/-- The affine reparam of piece `k` has pathSpeed `n · (pathSpeed of piece k at the rescaled arg)`. -/
lemma piece_pathSpeed_eq (g : ℕ → ℝ → X) (n : ℕ) (_hn : 0 < n)
    (hpiece : ∀ k, k < n → Jacobians.IsSmoothPath (g k 0) (g k 1) (g k))
    (k : ℕ) (hk : k < n) (s : ℝ) (hsmem : (n:ℝ)*s - k ∈ Icc (0:ℝ) 1) :
    Jacobians.pathSpeed (fun u => g k ((n:ℝ)*u - k)) s
      = (n:ℂ) * Jacobians.pathSpeed (g k) ((n:ℝ)*s - k) := by
  have hform : (fun u => g k ((n:ℝ)*u - k)) = (fun u => g k ((n:ℝ)*u + (-(k:ℝ)))) := by
    funext u; ring_nf
  rw [hform]
  have hdiff : DifferentiableAt ℝ ((chartAt (H := ℂ) (g k ((n:ℝ)*s + (-(k:ℝ))))).toFun ∘ g k)
      ((n:ℝ)*s + (-(k:ℝ))) := by
    have : (n:ℝ)*s + (-(k:ℝ)) = (n:ℝ)*s - k := by ring
    rw [this]
    exact (hpiece k hk).diff ((n:ℝ)*s-k) (by rw [Set.uIcc_of_le (by norm_num:(0:ℝ)≤1)]; exact hsmem)
  rw [pathSpeed_affine_comp (g k) (n:ℝ) (-(k:ℝ)) s hdiff]
  congr 2

/-- **The glue's pathSpeed equals the affine-reparam piece's pathSpeed on the closed `k`-th piece.**
On the open interior via locality; at the two endpoints both vanish (flat-ended seams / boundaries). -/
lemma uniformGlue_pathSpeed_eqOn_piece (g : ℕ → ℝ → X) (hchain : ∀ j, g j 1 = g (j+1) 0)
    (n : ℕ) (hn : 0 < n)
    (hpiece : ∀ k, k < n → Jacobians.IsSmoothPath (g k 0) (g k 1) (g k))
    (hv0 : ∀ k, k < n → Jacobians.pathSpeed (g k) 0 = 0)
    (hv1 : ∀ k, k < n → Jacobians.pathSpeed (g k) 1 = 0)
    (k : ℕ) (hk : k < n) :
    ∀ s ∈ Icc ((k:ℝ)/n) (((k:ℝ)+1)/n),
      Jacobians.pathSpeed (uniformGlue g n) s
        = Jacobians.pathSpeed (fun u => g k ((n:ℝ)*u - k)) s := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  intro s hs
  have harg_mem : (n:ℝ)*s - k ∈ Icc (0:ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have := hs.1; rw [div_le_iff₀ hnpos] at this; linarith
    · have := hs.2; rw [le_div_iff₀ hnpos] at this; linarith
  rcases eq_or_lt_of_le hs.1 with hesL | hgt
  · have hns : (n:ℝ)*s = k := by rw [← hesL]; field_simp
    have hargL : (n:ℝ)*s - k = 0 := by rw [hns]; ring
    have hrhs : Jacobians.pathSpeed (fun u => g k ((n:ℝ)*u - k)) s = 0 := by
      rw [piece_pathSpeed_eq g n hn hpiece k hk s harg_mem, hargL, hv0 k hk, mul_zero]
    rw [hrhs]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hs0 : s = 0 := by simpa using hesL.symm
      subst hs0
      rw [pathSpeed_congr_nhds _ _ 0 (uniformGlue_eventuallyEq_zero g n hn)]
      rw [piece_pathSpeed_eq g n hn hpiece 0 hk 0 (by simp)]
      simp [hv0 0 hk]
    · have hseam := uniformGlue_seam g hchain n hn hpiece hv0 hv1 k hkpos (by omega) s hns
      show fderiv ℝ ((chartAt (H := ℂ) (uniformGlue g n s)).toFun ∘ uniformGlue g n) s (1:ℝ) = 0
      rw [fderiv_apply_one_eq_deriv]; exact hseam.deriv
  · rcases eq_or_lt_of_le hs.2 with hesR | hlt2
    · have hns : (n:ℝ)*s = k + 1 := by rw [hesR]; field_simp
      have hargR : (n:ℝ)*s - k = 1 := by rw [hns]; ring
      have hrhs : Jacobians.pathSpeed (fun u => g k ((n:ℝ)*u - k)) s = 0 := by
        rw [piece_pathSpeed_eq g n hn hpiece k hk s harg_mem, hargR, hv1 k hk, mul_zero]
      rw [hrhs]
      rcases lt_or_ge (k+1) n with hknext | hklast
      · have hseam := uniformGlue_seam g hchain n hn hpiece hv0 hv1 (k+1) (by omega) (by omega) s
          (by rw [hns]; push_cast; ring)
        show fderiv ℝ ((chartAt (H := ℂ) (uniformGlue g n s)).toFun ∘ uniformGlue g n) s (1:ℝ) = 0
        rw [fderiv_apply_one_eq_deriv]; exact hseam.deriv
      · have hkn : k + 1 = n := by omega
        have hncast : (n:ℝ) = (k:ℝ) + 1 := by rw [← hkn]; push_cast; ring
        have hs1 : s = 1 := by rw [hesR, hncast]; field_simp
        subst hs1
        rw [pathSpeed_congr_nhds _ _ 1 (uniformGlue_eventuallyEq_one g n hn)]
        have hk' : n - 1 < n := by omega
        rw [piece_pathSpeed_eq g n hn hpiece (n-1) hk' 1 ?_]
        · have hcast : (n:ℝ)*1 - (n-1:ℕ) = 1 := by rw [Nat.cast_sub hn]; push_cast; ring
          rw [hcast, hv1 (n-1) hk', mul_zero]
        · rw [show (n:ℝ)*1 - (n-1:ℕ) = 1 from by rw [Nat.cast_sub hn]; push_cast; ring]
          exact ⟨zero_le_one, le_refl _⟩
    · rw [pathSpeed_congr_nhds _ _ s (uniformGlue_eventuallyEq_piece g n hn k hk s ⟨hgt, hlt2⟩)]

/-! ### A4''. Smoothness of the uniform glue -/

/-- **The uniform glue is a flat-ended smooth path.** Given each piece `g k` (`k < n`) is an
`IsSmoothPath (g k 0) (g k 1)` with vanishing endpoint velocities, and consecutive pieces chain,
`uniformGlue g n` is an `IsSmoothPath (g 0 0) (g (n-1) 1)`: continuity and velocity-continuity glue
over the closed uniform cover via the affine-reparam machinery; chart-pullback differentiability is
the per-point chain rule on open pieces, and the `HasDerivWithinAt … 0` union at each seam (every
piece flat-ended ⇒ both one-sided seam derivatives vanish). -/
lemma isSmoothPath_uniformGlue (g : ℕ → ℝ → X)
    (hchain : ∀ j, g j 1 = g (j+1) 0) (n : ℕ) (hn : 0 < n)
    (hpiece : ∀ k, k < n → Jacobians.IsSmoothPath (g k 0) (g k 1) (g k))
    (hv0 : ∀ k, k < n → Jacobians.pathSpeed (g k) 0 = 0)
    (hv1 : ∀ k, k < n → Jacobians.pathSpeed (g k) 1 = 0) :
    Jacobians.IsSmoothPath (g 0 0) (g (n-1) 1) (uniformGlue g n) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  -- chart-pullback differentiability of each piece's affine reparam, anywhere its arg lands in [0,1].
  have hpiece_diff : ∀ k, k < n → ∀ u : ℝ, u ∈ Set.Icc (0:ℝ) 1 →
      DifferentiableAt ℝ ((chartAt (H := ℂ) (g k u)).toFun ∘ g k) u :=
    fun k hk u hu => (hpiece k hk).diff u (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hu)
  -- value at 0 and 1.
  have hval0 : uniformGlue g n 0 = g 0 0 := by
    have := uniformGlue_apply_of_mem g hchain n hn 0 hn 0
      (by rw [Nat.cast_zero, zero_div])
      (by rw [Nat.cast_zero, zero_add]; positivity)
    rwa [Nat.cast_zero, mul_zero, sub_zero] at this
  have hval1 : uniformGlue g n 1 = g (n-1) 1 := by
    have hk : n - 1 < n := by omega
    have hcast : ((n:ℝ) - 1) = ((n-1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hn]; push_cast; ring
    have h0 : ((n-1 : ℕ):ℝ)/n ≤ 1 := by rw [div_le_one hnpos]; rw [← hcast]; linarith
    have h1 : (1:ℝ) ≤ (((n-1:ℕ):ℝ)+1)/n := by
      rw [le_div_iff₀ hnpos, ← hcast]; ring_nf; linarith
    have := uniformGlue_apply_of_mem g hchain n hn (n-1) hk 1 h0 h1
    rwa [mul_one, ← hcast, sub_sub_cancel] at this
  -- per-piece affine reparam (continuous) and its agreement with the glue on each closed piece.
  have hcont_piece : ∀ k, k < n → Continuous (fun s : ℝ => g k ((n:ℝ)*s - k)) := fun k hk =>
    (hpiece k hk).cont.comp ((continuous_const.mul continuous_id).sub continuous_const)
  have hpieceOn : ∀ k, k < n →
      ContinuousOn (uniformGlue g n) (Set.Icc ((k:ℝ)/n) (((k:ℝ)+1)/n)) := fun k hk =>
    (hcont_piece k hk).continuousOn.congr (fun s hs => (uniformGlue_eqOn_piece g hchain n hn k hk hs))
  -- continuity on `[0,1]` by unioning the `n` closed pieces.
  have hOn01 : ContinuousOn (uniformGlue g n) (Set.Icc 0 1) := by
    have key : ∀ m, m ≤ n → ContinuousOn (uniformGlue g n) (Set.Icc 0 ((m:ℝ)/n)) := by
      intro m hm
      induction m with
      | zero => rw [Nat.cast_zero, zero_div, Set.Icc_self]; exact continuousOn_singleton _ _
      | succ j ih =>
        have hjn : j < n := by omega
        have hsplit : Set.Icc (0:ℝ) ((j+1:ℕ)/n) =
            Set.Icc 0 ((j:ℝ)/n) ∪ Set.Icc ((j:ℝ)/n) (((j:ℝ)+1)/n) := by
          rw [Set.Icc_union_Icc_eq_Icc (by positivity)
            (by rw [div_le_div_iff_of_pos_right hnpos]; linarith)]
          congr 1; push_cast; ring
        rw [hsplit]
        exact (ih (by omega)).union_of_isClosed (hpieceOn j hjn) isClosed_Icc isClosed_Icc
    have := key n (le_refl n)
    rwa [div_self (ne_of_gt hnpos)] at this
  refine ⟨hval0, hval1, ?_, ?_, ?_⟩
  · -- continuity: glue `[0,1]` with the two clamped tails `Iic 0` and `Ici 1`.
    have hOnLeft : ContinuousOn (uniformGlue g n) (Set.Iic 0) :=
      ((hcont_piece 0 hn).continuousOn).congr (fun s hs => by
        show uniformGlue g n s = g 0 ((n:ℝ)*s - (0:ℕ))
        unfold uniformGlue; rw [uIdx_zero_of_nonpos n s hs])
    have hOnRight : ContinuousOn (uniformGlue g n) (Set.Ici 1) := by
      have hk : n - 1 < n := by omega
      exact ((hcont_piece (n-1) hk).continuousOn).congr (fun s hs => by
        show uniformGlue g n s = g (n-1) ((n:ℝ)*s - (n-1:ℕ))
        unfold uniformGlue; rw [uIdx_last_of_ge_one n hn s hs])
    have hAll : ContinuousOn (uniformGlue g n) ((Set.Iic 0 ∪ Set.Icc 0 1) ∪ Set.Ici 1) :=
      (hOnLeft.union_of_isClosed hOn01 isClosed_Iic isClosed_Icc).union_of_isClosed
        hOnRight (isClosed_Iic.union isClosed_Icc) isClosed_Ici
    have huniv : (Set.Iic (0:ℝ) ∪ Set.Icc 0 1) ∪ Set.Ici 1 = Set.univ := by
      ext x; simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc, Set.mem_Ici, Set.mem_univ, iff_true]
      rcases le_or_gt x 0 with h | h
      · exact Or.inl (Or.inl h)
      · rcases le_or_gt x 1 with h2 | h2
        · exact Or.inl (Or.inr ⟨le_of_lt h, h2⟩)
        · exact Or.inr (le_of_lt h2)
    rw [huniv] at hAll; rwa [continuousOn_univ] at hAll
  · -- chart-pullback differentiability at each t ∈ [0,1]: interior chain rule + seam union.
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hfromEv : ∀ (k : ℕ), k < n → (n:ℝ)*t - k ∈ Set.Icc (0:ℝ) 1 →
        uniformGlue g n =ᶠ[nhds t] (fun s => g k ((n:ℝ)*s - k)) →
        DifferentiableAt ℝ ((chartAt (H := ℂ) (uniformGlue g n t)).toFun ∘ uniformGlue g n) t := by
      intro k hk harg hev
      have hpt : uniformGlue g n t = g k ((n:ℝ)*t - k) := hev.eq_of_nhds
      have hev2 : ((chartAt (H := ℂ) (uniformGlue g n t)).toFun ∘ uniformGlue g n)
          =ᶠ[nhds t]
          ((chartAt (H := ℂ) (g k ((n:ℝ)*t - k))).toFun ∘ (fun s => g k ((n:ℝ)*s - k))) := by
        rw [hpt]; exact hev.fun_comp _
      rw [hev2.differentiableAt_iff]
      have hcomp : ((chartAt (H := ℂ) (g k ((n:ℝ)*t - k))).toFun ∘ (fun s => g k ((n:ℝ)*s - k)))
          = ((chartAt (H := ℂ) (g k ((n:ℝ)*t - k))).toFun ∘ g k) ∘ (fun s:ℝ => (n:ℝ)*s - k) := by
        funext s; rfl
      rw [hcomp]
      have haff : DifferentiableAt ℝ (fun s:ℝ => (n:ℝ)*s - (k:ℝ)) t :=
        ((differentiableAt_const _).mul differentiableAt_id).sub (differentiableAt_const _)
      have hgd : DifferentiableAt ℝ ((chartAt (H := ℂ) (g k ((n:ℝ)*t - k))).toFun ∘ g k)
          ((fun s:ℝ => (n:ℝ)*s - (k:ℝ)) t) :=
        (hpiece k hk).diff ((n:ℝ)*t - k) (by rw [Set.uIcc_of_le (by norm_num:(0:ℝ)≤1)]; exact harg)
      exact hgd.comp t haff
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0pos
    · refine hfromEv 0 hn ?_ ?_
      · rw [← ht0]; simp
      · rw [← ht0]; simpa using uniformGlue_eventuallyEq_zero g n hn
    · rcases eq_or_lt_of_le ht.2 with ht1 | ht1lt
      · refine hfromEv (n-1) (by omega) ?_ ?_
        · rw [ht1, show (n:ℝ)*1 - (n-1:ℕ) = 1 from by rw [Nat.cast_sub hn]; push_cast; ring]
          exact ⟨zero_le_one, le_refl _⟩
        · rw [ht1]; exact uniformGlue_eventuallyEq_one g n hn
      · have hnt0 : (0:ℝ) < n * t := by positivity
        have hntn : (n:ℝ) * t < n := by nlinarith
        set k : ℕ := ⌊(n:ℝ)*t⌋.toNat with hkdef
        have hfl_nonneg : 0 ≤ ⌊(n:ℝ)*t⌋ := Int.floor_nonneg.mpr (le_of_lt hnt0)
        have hcastk : ((k:ℕ):ℝ) = (⌊(n:ℝ)*t⌋ : ℝ) := by
          rw [hkdef]; exact_mod_cast Int.toNat_of_nonneg hfl_nonneg
        have hk_le : (k:ℝ) ≤ n * t := by rw [hcastk]; exact Int.floor_le _
        have hk_lt : (n:ℝ)*t < k + 1 := by rw [hcastk]; exact Int.lt_floor_add_one _
        have hkn : k < n := by
          by_contra h; push Not at h
          have : (n:ℝ) ≤ k := by exact_mod_cast h
          linarith
        have hhi : t < ((k:ℝ)+1)/n := by rw [lt_div_iff₀ hnpos]; linarith
        rcases eq_or_lt_of_le hk_le with hseam | hint
        · have hkpos : 0 < k := by
            by_contra h; push Not at h
            have hk0 : k = 0 := by omega
            rw [hk0] at hseam; simp only [Nat.cast_zero] at hseam
            have ht0' : t = 0 := by
              rcases mul_eq_zero.mp hseam.symm with hc | hc
              · exact absurd hc (ne_of_gt hnpos)
              · exact hc
            linarith
          exact (uniformGlue_seam g hchain n hn hpiece hv0 hv1 k hkpos (by omega) t
            hseam.symm).differentiableAt
        · refine hfromEv k hkn ?_ (uniformGlue_eventuallyEq_piece g n hn k hkn t ⟨?_, hhi⟩)
          · exact ⟨by linarith, by linarith⟩
          · rw [div_lt_iff₀ hnpos]; linarith
  · -- velocity-section continuity: union over the closed uniform pieces.
    have hpieceVC : ∀ k, k < n →
        ContinuousOn (fun s : ℝ =>
          Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
            (uniformGlue g n s) (Jacobians.pathSpeed (uniformGlue g n) s))
          (Set.Icc ((k:ℝ)/n) (((k:ℝ)+1)/n)) := by
      intro k hk
      have hmaps : Set.MapsTo (fun s : ℝ => (n:ℝ) * s + (-(k:ℝ)))
          (Set.Icc ((k:ℝ)/n) (((k:ℝ)+1)/n)) (Set.Icc 0 1) := by
        intro s hs
        simp only [Set.mem_Icc]
        refine ⟨?_, ?_⟩
        · have := hs.1; rw [div_le_iff₀ hnpos] at this; linarith
        · have := hs.2; rw [le_div_iff₀ hnpos] at this; linarith
      have haff := Jacobians.velCont_affineReparam (g k) (n:ℝ) (-(k:ℝ)) hmaps (hpiece k hk).velCont
      apply haff.congr
      intro s hs
      have hval : uniformGlue g n s = g k ((n:ℝ)*s - k) :=
        uniformGlue_apply_of_mem g hchain n hn k hk s hs.1 hs.2
      have hsp : Jacobians.pathSpeed (uniformGlue g n) s
          = (n:ℂ) * Jacobians.pathSpeed (g k) ((n:ℝ)*s - k) := by
        rw [uniformGlue_pathSpeed_eqOn_piece g hchain n hn hpiece hv0 hv1 k hk s hs]
        have harg : (n:ℝ)*s - k ∈ Set.Icc (0:ℝ) 1 := by
          refine ⟨?_, ?_⟩
          · have := hs.1; rw [div_le_iff₀ hnpos] at this; linarith
          · have := hs.2; rw [le_div_iff₀ hnpos] at this; linarith
        exact piece_pathSpeed_eq g n hn hpiece k hk s harg
      show Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (uniformGlue g n s)
          (Jacobians.pathSpeed (uniformGlue g n) s) = _
      simp only []
      rw [hval, hsp, show ((n:ℝ)*s + (-(k:ℝ))) = (n:ℝ)*s - k from by ring, smul_eq_mul]
      norm_cast
    have key : ∀ m, m ≤ n →
        ContinuousOn (fun s : ℝ =>
          Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
            (uniformGlue g n s) (Jacobians.pathSpeed (uniformGlue g n) s)) (Set.Icc 0 ((m:ℝ)/n)) := by
      intro m hm
      induction m with
      | zero => rw [Nat.cast_zero, zero_div, Set.Icc_self]; exact continuousOn_singleton _ _
      | succ j ih =>
        have hjn : j < n := by omega
        have hsplit : Set.Icc (0:ℝ) ((j+1:ℕ)/n) =
            Set.Icc 0 ((j:ℝ)/n) ∪ Set.Icc ((j:ℝ)/n) (((j:ℝ)+1)/n) := by
          rw [Set.Icc_union_Icc_eq_Icc (by positivity)
            (by rw [div_le_div_iff_of_pos_right hnpos]; linarith)]
          congr 1; push_cast; ring
        rw [hsplit]
        exact (ih (by omega)).union_of_isClosed (hpieceVC j hjn) isClosed_Icc isClosed_Icc
    have := key n (le_refl n)
    rwa [div_self (ne_of_gt hnpos)] at this

/-! ### A5. Sub-ball chart cover (subdivision infrastructure)

`exists_chartCover` (in `Jacobians/SmoothPath.lean`) delivers, for a continuous `γ`, a uniform
partition of `[0,1]` into `n` pieces with a chart anchor `x k` per piece such that `γ` stays in
`(chartAt ℂ (x k)).source` over the `k`-th piece. The off-branch splice lemma
`intervalIntegral_form_pathSpeed_eq_of_subball_endpoints` needs strictly more: a *ball*
`Metric.ball (c k) (r k)` lying inside the chart **target**, with the chart-image of `γ` over the
piece confined to that ball (so the holomorphic primitive on the ball applies). `exists_subBallChartCover`
upgrades the cover to carry exactly that ball data. The construction is the same single Lebesgue-number
argument as `exists_chartCover`, but each cover element also pins the chart-image into a target sub-ball. -/

/-- **Sub-ball chart cover.** For a continuous `γ : ℝ → X`, there is a uniform partition into `n`
pieces with, per piece `k`, a chart anchor `x k`, a center `c k` and radius `r k > 0` such that
`Metric.ball (c k) (r k) ⊆ (chartAt ℂ (x k)).target`, and for every `s` in the `k`-th piece
`[k/n, (k+1)/n]` the point `γ s` lies in `(chartAt ℂ (x k)).source` with chart-image
`chartAt ℂ (x k) (γ s) ∈ Metric.ball (c k) (r k)`. This supplies the sub-ball confinement consumed by
`intervalIntegral_form_pathSpeed_eq_of_subball_endpoints`. -/
theorem exists_subBallChartCover (γ : ℝ → X) (hγ : Continuous γ) :
    ∃ (n : ℕ) (_hn : 0 < n) (x : Fin n → X) (c : Fin n → ℂ) (r : Fin n → ℝ),
      (∀ k, 0 < r k) ∧
      ∀ (k : Fin n) (s : ℝ),
        (k : ℝ) / n ≤ s → s ≤ ((k : ℝ) + 1) / n →
          Metric.ball (c k) (r k) ⊆ (chartAt (H := ℂ) (x k)).target ∧
          γ s ∈ (chartAt (H := ℂ) (x k)).source ∧
          (chartAt (H := ℂ) (x k)) (γ s) ∈ Metric.ball (c k) (r k) := by
  classical
  set S : Set ℝ := Set.Icc (0 : ℝ) 1 with hS_def
  -- Per base time `t`, a positive radius `ρ t` whose ball around the chart-image of `γ t` sits
  -- inside the chart target.
  have hrad : ∀ t : S, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball ((chartAt (H := ℂ) (γ t.1)) (γ t.1)) ρ ⊆ (chartAt (H := ℂ) (γ t.1)).target := by
    intro t
    have hmem : (chartAt (H := ℂ) (γ t.1)) (γ t.1) ∈ (chartAt (H := ℂ) (γ t.1)).target :=
      mem_chart_target ℂ (γ t.1)
    have hnhds : (chartAt (H := ℂ) (γ t.1)).target ∈
        nhds ((chartAt (H := ℂ) (γ t.1)) (γ t.1)) :=
      (chartAt (H := ℂ) (γ t.1)).open_target.mem_nhds hmem
    obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.mem_nhds_iff.mp hnhds
    exact ⟨ρ, hρ_pos, hρ_sub⟩
  set ρ : S → ℝ := fun t => (hrad t).choose with hρ_def
  have hρ_pos : ∀ t : S, 0 < ρ t := fun t => (hrad t).choose_spec.1
  have hρ_sub : ∀ t : S, Metric.ball ((chartAt (H := ℂ) (γ t.1)) (γ t.1)) (ρ t) ⊆
      (chartAt (H := ℂ) (γ t.1)).target := fun t => (hrad t).choose_spec.2
  -- The open cover: `U t` is the set of times whose `γ`-image stays in the chart source of `γ t`
  -- AND lands in the sub-ball around the chart-image of `γ t`.
  set U : S → Set ℝ := fun t =>
    γ ⁻¹' ((chartAt (H := ℂ) (γ t.1)).source ∩
      (chartAt (H := ℂ) (γ t.1)) ⁻¹'
        Metric.ball ((chartAt (H := ℂ) (γ t.1)) (γ t.1)) (ρ t)) with hU_def
  have hU_open : ∀ t : S, IsOpen (U t) := by
    intro t
    have hVopen : IsOpen ((chartAt (H := ℂ) (γ t.1)).source ∩
        (chartAt (H := ℂ) (γ t.1)) ⁻¹'
          Metric.ball ((chartAt (H := ℂ) (γ t.1)) (γ t.1)) (ρ t)) :=
      (chartAt (H := ℂ) (γ t.1)).continuousOn.isOpen_inter_preimage
        (chartAt (H := ℂ) (γ t.1)).open_source Metric.isOpen_ball
    exact hVopen.preimage hγ
  have hU_cover : S ⊆ ⋃ t : S, U t := by
    intro t ht
    refine Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ?_⟩
    simp only [hU_def, Set.mem_preimage, Set.mem_inter_iff]
    exact ⟨mem_chart_source ℂ (γ t), Metric.mem_ball_self (hρ_pos ⟨t, ht⟩)⟩
  -- Lebesgue number for the cover of the compact `[0,1]`.
  obtain ⟨lebδ, hlebδ_pos, hlebδ⟩ :=
    lebesgue_number_lemma_of_metric (isCompact_Icc (a := (0:ℝ)) (b := 1)) hU_open hU_cover
  obtain ⟨n, hn_gt⟩ : ∃ n : ℕ, 1 / lebδ < (n : ℝ) := exists_nat_gt _
  have hn_pos : 0 < n := by
    have h1 : (0 : ℝ) < 1 / lebδ := by positivity
    exact_mod_cast lt_trans h1 hn_gt
  have hn : (1 : ℝ) / n < lebδ := by
    have hn_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
    rw [div_lt_iff₀ hn_R]
    have h := mul_lt_mul_of_pos_left hn_gt hlebδ_pos
    have h_simp : lebδ * (1 / lebδ) = 1 := by field_simp
    linarith
  -- Per `k`, anchor at the piece midpoint via the Lebesgue ball.
  have key : ∀ k : Fin n, ∃ (xk : X) (ck : ℂ) (rk : ℝ), 0 < rk ∧
      ∀ y : ℝ, (k : ℝ) / n ≤ y → y ≤ ((k : ℝ) + 1) / n →
        Metric.ball ck rk ⊆ (chartAt (H := ℂ) xk).target ∧
        γ y ∈ (chartAt (H := ℂ) xk).source ∧
        (chartAt (H := ℂ) xk) (γ y) ∈ Metric.ball ck rk := by
    intro k
    set m : ℝ := ((k : ℝ) + 1/2) / n with hm_def
    have hm_mem : m ∈ S := by
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
    obtain ⟨t₀, ht₀⟩ := hlebδ m hm_mem
    refine ⟨γ t₀.1, (chartAt (H := ℂ) (γ t₀.1)) (γ t₀.1), ρ t₀, hρ_pos t₀, ?_⟩
    intro y hy_low hy_high
    -- `y` lies in the Lebesgue ball about `m`, hence in `U t₀`.
    have hy_ball : y ∈ Metric.ball m lebδ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have h_dist : |y - m| ≤ 1 / (2 * n) := by
        rw [abs_sub_le_iff]
        refine ⟨?_, ?_⟩
        · have : y - m ≤ ((k : ℝ) + 1) / n - ((k : ℝ) + 1/2) / n := by linarith
          have heq : ((k : ℝ) + 1) / n - ((k : ℝ) + 1/2) / n = 1 / (2 * n) := by
            field_simp; ring
          linarith
        · have : m - y ≤ ((k : ℝ) + 1/2) / n - (k : ℝ) / n := by linarith
          have heq : ((k : ℝ) + 1/2) / n - (k : ℝ) / n = 1 / (2 * n) := by
            field_simp; ring
          linarith
      have h1 : (1 : ℝ) / (2 * n) ≤ 1 / n := by
        apply div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hn_pos)
        have hnn : (0 : ℝ) < n := by exact_mod_cast hn_pos
        nlinarith
      linarith
    have hyU : y ∈ U t₀ := ht₀ hy_ball
    simp only [hU_def, Set.mem_preimage, Set.mem_inter_iff] at hyU
    exact ⟨hρ_sub t₀, hyU.1, hyU.2⟩
  refine ⟨n, hn_pos, fun k => (key k).choose,
    fun k => (key k).choose_spec.choose,
    fun k => (key k).choose_spec.choose_spec.choose,
    fun k => (key k).choose_spec.choose_spec.choose_spec.1, ?_⟩
  intro k s hs_low hs_high
  exact (key k).choose_spec.choose_spec.choose_spec.2 s hs_low hs_high

end Jacobians.OfCurveSkeleton

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Period-vector telescoping over a partition.** If `δ, δ'` are closed smooth loops and there
is a partition `0 = s₀ ≤ s₁ ≤ ⋯ ≤ sₙ = 1` of `[0,1]` (with each sub-interval inside `[0,1]`) such
that the *partial* line integrals of every period basis form agree piece-by-piece
(`∫_{sₖ}^{sₖ₊₁} ωᵢ(δ') = ∫_{sₖ}^{sₖ₊₁} ωᵢ(δ)`), then `periodVec δ' = periodVec δ`.

This is the analytic core of period-preservation for the off-branch surgery, fully discharged:
`periodVec` is the integral over `[0,1]`, which splits as the sum of the partial integrals over the
subdivision (`intervalIntegral.sum_integral_adjacent_intervals`, with per-piece integrability
inherited from `IsClosedSmoothLoop.integrable` via `IntervalIntegrable.mono_set`); the hypothesis
makes the two sums equal term-by-term. The remaining (geometric) work for
`exists_loop_off_branchLocus` is to *produce* a `δ'` avoiding `branchLocus f` whose per-piece partial
integrals match `δ`'s — for pieces where `δ'` is left equal to `δ` this is trivial, and for replaced
pieces it is exactly `OfCurveSkeleton.intervalIntegral_form_pathSpeed_eq_of_subball_endpoints` (the
detour and the original sub-arc share chart-coordinate endpoints inside one sub-ball). -/
theorem periodVec_eq_of_partition_integral_eq (δ δ' : ℝ → X)
    (hδ : IsClosedSmoothLoop δ) (hδ' : IsClosedSmoothLoop δ')
    (s : ℕ → ℝ) (n : ℕ) (hs0 : s 0 = 0) (hsn : s n = 1)
    (hs_sub : ∀ k, k < n → Set.uIcc (s k) (s (k+1)) ⊆ Set.Icc (0:ℝ) 1)
    (hpiece : ∀ (i : Fin (kirovGenus X)) (k : ℕ), k < n →
      (∫ t in (s k)..(s (k+1)), (periodBasisForm X i).toFun (δ' t) (pathSpeed δ' t)) =
      (∫ t in (s k)..(s (k+1)), (periodBasisForm X i).toFun (δ t) (pathSpeed δ t))) :
    periodVec δ' = periodVec δ := by
  funext i
  show lineIntegral (periodBasisForm X i) δ' = lineIntegral (periodBasisForm X i) δ
  unfold lineIntegral
  have hint_δ : ∀ k, k < n → IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (δ t) (pathSpeed δ t)) volume (s k) (s (k+1)) :=
    fun k hk => (hδ.integrable i).mono_set (by
      rw [Set.uIcc_of_le (zero_le_one)]; exact hs_sub k hk)
  have hint_δ' : ∀ k, k < n → IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (δ' t) (pathSpeed δ' t)) volume (s k) (s (k+1)) :=
    fun k hk => (hδ'.integrable i).mono_set (by
      rw [Set.uIcc_of_le (zero_le_one)]; exact hs_sub k hk)
  have htel_δ := intervalIntegral.sum_integral_adjacent_intervals (a := s) (n := n)
    (f := fun t => (periodBasisForm X i).toFun (δ t) (pathSpeed δ t)) hint_δ
  have htel_δ' := intervalIntegral.sum_integral_adjacent_intervals (a := s) (n := n)
    (f := fun t => (periodBasisForm X i).toFun (δ' t) (pathSpeed δ' t)) hint_δ'
  rw [hs0, hsn] at htel_δ htel_δ'
  rw [← htel_δ, ← htel_δ']
  exact Finset.sum_congr rfl (fun k hk => hpiece i k (Finset.mem_range.mp hk))

/-- **Period-vector telescoping with a per-piece correction term.** Generalizes
`periodVec_eq_of_partition_integral_eq`: instead of demanding the partial line integrals agree
piece-by-piece, we allow a *correction* `corr i : ℕ → ℂ` so that on piece `k`
`∫δ' = ∫δ + corr (k+1) − corr k`. If the correction is **periodic** (`corr i n = corr i 0`) the
correction terms telescope to `corr i n − corr i 0 = 0`, so `periodVec δ' = periodVec δ`.

This is the analytic core of period-preservation for the off-branch surgery once the breakpoints are
*perturbed* (so the per-piece integrals no longer match exactly): `corr i k` is the intrinsic line
integral of the period form along the short connecting path from `δ(k/n)` to the perturbed off-branch
breakpoint `p k`. Because that connector lies in the overlap of the two adjacent sub-balls, the same
`corr i k` value serves both piece `k−1` (its right end) and piece `k` (its left end), and periodicity
`corr i n = corr i 0` holds because breakpoint `n` *is* breakpoint `0` (`δ 1 = δ 0`, `p n = p 0`). -/
theorem periodVec_eq_of_partition_integral_telescope (δ δ' : ℝ → X)
    (hδ : IsClosedSmoothLoop δ) (hδ' : IsClosedSmoothLoop δ')
    (s : ℕ → ℝ) (n : ℕ) (hs0 : s 0 = 0) (hsn : s n = 1)
    (hs_sub : ∀ k, k < n → Set.uIcc (s k) (s (k+1)) ⊆ Set.Icc (0:ℝ) 1)
    (corr : Fin (kirovGenus X) → ℕ → ℂ) (hcorr_per : ∀ i, corr i n = corr i 0)
    (hpiece : ∀ (i : Fin (kirovGenus X)) (k : ℕ), k < n →
      (∫ t in (s k)..(s (k+1)), (periodBasisForm X i).toFun (δ' t) (pathSpeed δ' t)) =
      (∫ t in (s k)..(s (k+1)), (periodBasisForm X i).toFun (δ t) (pathSpeed δ t))
        + corr i (k+1) - corr i k) :
    periodVec δ' = periodVec δ := by
  funext i
  show lineIntegral (periodBasisForm X i) δ' = lineIntegral (periodBasisForm X i) δ
  unfold lineIntegral
  have hint_δ : ∀ k, k < n → IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (δ t) (pathSpeed δ t)) volume (s k) (s (k+1)) :=
    fun k hk => (hδ.integrable i).mono_set (by
      rw [Set.uIcc_of_le (zero_le_one)]; exact hs_sub k hk)
  have hint_δ' : ∀ k, k < n → IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (δ' t) (pathSpeed δ' t)) volume (s k) (s (k+1)) :=
    fun k hk => (hδ'.integrable i).mono_set (by
      rw [Set.uIcc_of_le (zero_le_one)]; exact hs_sub k hk)
  have htel_δ := intervalIntegral.sum_integral_adjacent_intervals (a := s) (n := n)
    (f := fun t => (periodBasisForm X i).toFun (δ t) (pathSpeed δ t)) hint_δ
  have htel_δ' := intervalIntegral.sum_integral_adjacent_intervals (a := s) (n := n)
    (f := fun t => (periodBasisForm X i).toFun (δ' t) (pathSpeed δ' t)) hint_δ'
  rw [hs0, hsn] at htel_δ htel_δ'
  rw [← htel_δ, ← htel_δ']
  -- Sum of the per-piece corrections telescopes to `corr i n − corr i 0 = 0`.
  have hsum : ∑ k ∈ Finset.range n,
      (∫ t in (s k)..(s (k+1)), (periodBasisForm X i).toFun (δ' t) (pathSpeed δ' t)) =
      ∑ k ∈ Finset.range n,
        ((∫ t in (s k)..(s (k+1)), (periodBasisForm X i).toFun (δ t) (pathSpeed δ t))
          + (corr i (k+1) - corr i k)) :=
    Finset.sum_congr rfl (fun k hk => by
      rw [hpiece i k (Finset.mem_range.mp hk)]; ring)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_range_sub (corr i) n, hcorr_per i, sub_self,
    add_zero]

end Jacobians
