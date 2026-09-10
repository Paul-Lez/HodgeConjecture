/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.SlitLogIntegral

/-!
# E4 (b)-brick: chart-segment periods of holomorphic 1-forms

The bridge between the planar atom's segment integral and the chain period: inside one
chart ball both the line integral of `α` along a path piece and the straight-segment
integral of the chart coefficient are endpoint differences of a single holomorphic
primitive (Morera on the ball, `DifferentiableOn.isExactOn_ball`), hence equal.

Main declarations:

* `segPeriod α Q₀ za zb` — the chart-segment value
  `(zb − za)·∫₀¹ coeffAt α Q₀ (za + s(zb − za)) ds` (the right-hand side of the planar
  atom `integral_slitLog_dbar_mul`, divided by `π`).
* `form_chartFrame_cancel` — chart-frame cancellation for an **arbitrary** holomorphic
  1-form: `α(γ t)(pathSpeed γ t) = coeffAt α Q₀ (e(γ t)) · (e∘γ)'(t)` (the
  `chartFrame_cancel_general` computation of `LoopOffBranch.lean`, generalized from the
  period basis forms).
* `differentiableAt_chart_comp_transfer` — chart-pullback differentiability transfers
  from the path's own chart to any chart whose source contains the local image
  (holomorphic transition + chain rule).
* `intervalIntegral_form_eq_primitive_diff` / `segPeriod_eq_primitive_diff` — both
  integrals as primitive endpoint differences.
* `intervalIntegral_form_eq_segPeriod` — **the (b)-brick**: a path piece in a chart ball
  contributes exactly its chart-segment value.
* `segPeriod_swap` — orientation antisymmetry `segPeriod α Q₀ zb za = −segPeriod α Q₀ za zb`
  (the sign bookkeeping for negative chain coefficients).

Reference: Forster §20.5; Miranda Ch. VIII §4 (chart-local period computations).
-/

open Complex Filter MeasureTheory Metric Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Chart-frame cancellation for an arbitrary form -/

/-- **Chart-frame cancellation for an arbitrary holomorphic 1-form.**  For any path `γ`
staying in the chart source of `Q₀` near `t` and chart-pullback-differentiable at `t`,
the `lineIntegral` integrand of `α` factors through the chart `e := chartAt ℂ Q₀`:

  `α(γ t)(pathSpeed γ t) = coeffAt α Q₀ (e (γ t)) · (fderiv ℝ (e ∘ γ) t 1)`.

This is `chartFrame_cancel_general` (`LoopOffBranch.lean`) with the period basis form
replaced by an arbitrary `α`; the proof is the same chart-transition + ℂ-linearity
computation. -/
lemma form_chartFrame_cancel (α : HolomorphicOneForms X) (Q₀ : X) (γ : ℝ → X) (t : ℝ)
    (h_source_nbhd : ∀ᶠ s : ℝ in 𝓝 t, γ s ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t) :
    α.toFun (γ t) (pathSpeed γ t) =
      coeffAt α Q₀ ((chartAt (H := ℂ) Q₀) (γ t))
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
        (((e.symm ≫ₕ (chartAt (H := ℂ) (γ t))) : ℂ → ℂ)) v) =ᶠ[𝓝 w] h_trans := by
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
  have h_local_eq : (chartAt (H := ℂ) (γ t)).toFun ∘ γ =ᶠ[𝓝 t]
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
  have h_coeffAt : coeffAt α Q₀ w = α.toFun (γ t) ((fderiv ℂ h_trans w) 1) := by
    show Jacobians.Montel.localRep α Q₀ (e.symm w) = _
    rw [show e.symm w = γ t from e.left_inv hγt_source]
    show α.toFun (γ t)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ (γ t) 1) = _
    rw [Jacobians.OfCurveSkeleton.trivAt_symmL_one_eq_fderiv_C Q₀ (γ t) hγt_source]
    congr 1
  rw [h_coeffAt, h_pathSpeed_final]
  have h_lin : (α.toFun (γ t)) (D * (fderiv ℂ h_trans w) 1) =
        D * (α.toFun (γ t)) ((fderiv ℂ h_trans w) 1) := by
    have := α.toFun (γ t) |>.map_smul D ((fderiv ℂ h_trans w) 1)
    simp only [smul_eq_mul] at this; exact this
  rw [h_lin]; ring

/-! ## Chart-pullback differentiability transfer -/

omit [T2Space X] [CompactSpace X] [Nonempty X] in
/-- Chart-pullback differentiability transfers from the path's own chart to any chart
whose source contains the path near `t` (holomorphic chart transition + chain rule). -/
lemma differentiableAt_chart_comp_transfer (Q₀ : X) {γ : ℝ → X} {t : ℝ}
    (h_source_nbhd : ∀ᶠ s : ℝ in 𝓝 t, γ s ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ_cont : Continuous γ)
    (hd : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) :
    DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t := by
  set e := chartAt (H := ℂ) Q₀ with he
  set e' := chartAt (H := ℂ) (γ t) with he'
  have hγt_source : γ t ∈ e.source := h_source_nbhd.self_of_nhds
  have hγt_self : γ t ∈ e'.source := mem_chart_source ℂ (γ t)
  set w' : ℂ := e' (γ t) with hw'
  set h_trans : ℂ → ℂ := fun v => e (e'.symm v) with hh_trans
  have h_wt : w' ∈ e'.target := e'.map_source hγt_self
  have h_src : e'.symm w' ∈ e.source := by
    rw [show e'.symm w' = γ t from e'.left_inv hγt_self]; exact hγt_source
  have h_trans_diff_C : DifferentiableAt ℂ h_trans w' := by
    have h_dC := Jacobians.chart_transition_differentiableAt_C (X := X) (γ t) Q₀ w' h_wt h_src
    have h_eq_comp : (fun v : ℂ => (((e'.symm ≫ₕ e) : ℂ → ℂ)) v) =ᶠ[𝓝 w'] h_trans := by
      have h_open : IsOpen (e'.symm ≫ₕ e).source := (e'.symm ≫ₕ e).open_source
      have h_mem : w' ∈ (e'.symm ≫ₕ e).source :=
        (Jacobians.chart_trans_source_iff (X := X) (γ t) Q₀ w').mpr ⟨h_wt, h_src⟩
      filter_upwards [h_open.mem_nhds h_mem] with v _; rfl
    exact h_dC.congr_of_eventuallyEq h_eq_comp
  have h_trans_diff_R : DifferentiableAt ℝ h_trans w' :=
    @DifferentiableAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _ Jacobians.instIsScalarTower_R_C_C
      ℂ _ _ _ Jacobians.instIsScalarTower_R_C_C _ _ h_trans_diff_C
  have h_local : (e.toFun ∘ γ) =ᶠ[𝓝 t] h_trans ∘ (e'.toFun ∘ γ) := by
    have h_nbhd' : ∀ᶠ s in 𝓝 t, γ s ∈ e'.source :=
      hγ_cont.continuousAt.preimage_mem_nhds (e'.open_source.mem_nhds hγt_self)
    filter_upwards [h_nbhd'] with s hs
    show e (γ s) = e (e'.symm (e' (γ s)))
    rw [e'.left_inv hs]
  have hcomp : DifferentiableAt ℝ (h_trans ∘ (e'.toFun ∘ γ)) t :=
    h_trans_diff_R.comp t hd
  exact hcomp.congr_of_eventuallyEq h_local

/-! ## The chart-segment value -/

/-- **The chart-segment value** of a holomorphic 1-form between two chart coordinates:
the straight-segment integral `(zb − za)·∫₀¹ coeffAt α Q₀ (za + s(zb − za)) ds` of the
chart coefficient.  This is the right-hand side of the planar atom
`integral_slitLog_dbar_mul` (divided by `π`), and by `intervalIntegral_form_eq_segPeriod`
it is the line integral of `α` along any chart-ball path piece with these endpoints. -/
def segPeriod (α : HolomorphicOneForms X) (Q₀ : X) (za zb : ℂ) : ℂ :=
  (zb - za) * ∫ s in (0 : ℝ)..1, coeffAt α Q₀ (za + s • (zb - za))

omit [Nonempty X] in
/-- Orientation antisymmetry of the chart-segment value (substitution `s ↦ 1 − s`). -/
theorem segPeriod_swap (α : HolomorphicOneForms X) (Q₀ : X) (za zb : ℂ) :
    segPeriod α Q₀ zb za = -segPeriod α Q₀ za zb := by
  rw [segPeriod, segPeriod]
  have hpt : ∀ s : ℝ, zb + s • (za - zb) = za + (1 - s) • (zb - za) := by
    intro s
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hsub : (∫ s in (0 : ℝ)..1, coeffAt α Q₀ (zb + s • (za - zb)))
      = ∫ s in (0 : ℝ)..1, coeffAt α Q₀ (za + s • (zb - za)) := by
    calc (∫ s in (0 : ℝ)..1, coeffAt α Q₀ (zb + s • (za - zb)))
        = ∫ s in (0 : ℝ)..1, coeffAt α Q₀ (za + (1 - s) • (zb - za)) := by
          refine intervalIntegral.integral_congr fun s _ => ?_
          rw [hpt]
      _ = ∫ s in (1 - 1 : ℝ)..(1 - 0 : ℝ), coeffAt α Q₀ (za + s • (zb - za)) := by
          rw [intervalIntegral.integral_comp_sub_left
            (fun u => coeffAt α Q₀ (za + u • (zb - za))) 1]
      _ = ∫ s in (0 : ℝ)..1, coeffAt α Q₀ (za + s • (zb - za)) := by norm_num
  rw [hsub]
  ring

/-! ## Primitive endpoint differences -/

/-- **Path-piece FTC for an arbitrary holomorphic 1-form**: if the chart image of the
piece `γ|[s₀,s₁]` lies in a ball carrying a primitive `F` of the chart coefficient, the
line-integral piece is the primitive endpoint difference. -/
lemma intervalIntegral_form_eq_primitive_diff
    (α : HolomorphicOneForms X) (Q₀ : X) {γ : ℝ → X} {s₀ s₁ : ℝ} (hle : s₀ ≤ s₁)
    {c : ℂ} {r : ℝ}
    {F : ℂ → ℂ} (hF : ∀ w ∈ Metric.ball c r, HasDerivAt F (coeffAt α Q₀ w) w)
    (hγ_in : ∀ t ∈ Set.Icc s₀ s₁, γ t ∈ (chartAt (H := ℂ) Q₀).source)
    (himg : ∀ t ∈ Set.Icc s₀ s₁, (chartAt (H := ℂ) Q₀) (γ t) ∈ Metric.ball c r)
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc s₀ s₁,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t)
    (hint : IntervalIntegrable (fun t => α.toFun (γ t) (pathSpeed γ t)) volume s₀ s₁) :
    ∫ t in s₀..s₁, α.toFun (γ t) (pathSpeed γ t)
      = F ((chartAt (H := ℂ) Q₀) (γ s₁)) - F ((chartAt (H := ℂ) Q₀) (γ s₀)) := by
  set e := chartAt (H := ℂ) Q₀ with he
  set g : ℝ → ℂ := e.toFun ∘ γ with hg
  have huIcc : Set.uIcc s₀ s₁ = Set.Icc s₀ s₁ := Set.uIcc_of_le hle
  have hFg_deriv : ∀ t ∈ Set.uIcc s₀ s₁,
      HasDerivAt (F ∘ g) (coeffAt α Q₀ (g t) * (fderiv ℝ g t 1)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc s₀ s₁ := huIcc ▸ ht
    have hg_deriv : HasDerivAt g (fderiv ℝ g t 1) t := (hγ_diff t ht).hasDerivAt
    have hF_at : HasDerivAt F (coeffAt α Q₀ (g t)) (g t) := hF (g t) (himg t ht')
    have := hF_at.comp t hg_deriv
    convert this using 1
  have hintegrand : Set.EqOn
      (fun t => α.toFun (γ t) (pathSpeed γ t))
      (fun t => coeffAt α Q₀ (g t) * (fderiv ℝ g t 1)) (Set.uIcc s₀ s₁) := by
    intro t ht
    have ht' : t ∈ Set.Icc s₀ s₁ := huIcc ▸ ht
    have h_src_nbhd : ∀ᶠ s : ℝ in 𝓝 t, γ s ∈ e.source :=
      (e.open_source.preimage hγ_cont).mem_nhds (hγ_in t ht')
    exact form_chartFrame_cancel α Q₀ γ t h_src_nbhd (hγ_diff t ht)
  rw [intervalIntegral.integral_congr hintegrand,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hFg_deriv
      (hint.congr (fun t ht => hintegrand (Set.uIoc_subset_uIcc ht)))]
  rfl

/-- **Segment FTC**: the chart-segment value between two points of a primitive-carrying
ball is the primitive endpoint difference. -/
lemma segPeriod_eq_primitive_diff
    (α : HolomorphicOneForms X) (Q₀ : X) {za zb c : ℂ} {r : ℝ}
    (hsub : Metric.ball c r ⊆ (chartAt (H := ℂ) Q₀).target)
    {F : ℂ → ℂ} (hF : ∀ w ∈ Metric.ball c r, HasDerivAt F (coeffAt α Q₀ w) w)
    (hza : za ∈ Metric.ball c r) (hzb : zb ∈ Metric.ball c r) :
    segPeriod α Q₀ za zb = F zb - F za := by
  set ℓ : ℝ → ℂ := fun s => za + s • (zb - za) with hℓdef
  have hℓball : ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → ℓ s ∈ Metric.ball c r := fun {s} hs =>
    (convex_ball c r).segment_subset hza hzb (segParam_mem_segment hs)
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (F ∘ ℓ) (coeffAt α Q₀ (ℓ s) * (zb - za)) s := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hℓd : HasDerivAt ℓ (zb - za) s := by
      show HasDerivAt (fun u : ℝ => za + u • (zb - za)) (zb - za) s
      simpa using ((hasDerivAt_id s).smul_const (zb - za)).const_add za
    have hFat : HasDerivAt F (coeffAt α Q₀ (ℓ s)) (ℓ s) := hF _ (hℓball hs)
    have := hFat.comp s hℓd
    convert this using 1
  have hint : IntervalIntegrable (fun s => coeffAt α Q₀ (ℓ s) * (zb - za)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine ContinuousOn.mul ?_ continuousOn_const
    intro s hs
    have han : AnalyticAt ℂ (coeffAt α Q₀) (ℓ s) := coeffAt_analyticAt α Q₀ (hsub (hℓball hs))
    have hℓcont : Continuous ℓ := by fun_prop
    exact (han.continuousAt.comp hℓcont.continuousAt).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h1 : ℓ 1 = zb := by
    show za + (1 : ℝ) • (zb - za) = zb
    rw [one_smul]
    ring
  have h0 : ℓ 0 = za := by
    show za + (0 : ℝ) • (zb - za) = za
    rw [zero_smul, add_zero]
  calc segPeriod α Q₀ za zb
      = ∫ s in (0 : ℝ)..1, coeffAt α Q₀ (ℓ s) * (zb - za) := by
        rw [segPeriod, intervalIntegral.integral_mul_const]
        ring
    _ = F (ℓ 1) - F (ℓ 0) := hFTC
    _ = F zb - F za := by rw [h1, h0]

/-! ## The (b)-brick -/

/-- **The (b)-brick**: a path piece whose chart image stays in a ball inside the chart
target contributes exactly its chart-segment value — the line integral of `α` over
`[s₀, s₁]` equals `segPeriod` between the chart endpoints.  Both sides are endpoint
differences of one Morera primitive of the chart coefficient on the ball. -/
theorem intervalIntegral_form_eq_segPeriod
    (α : HolomorphicOneForms X) (Q₀ : X) {γ : ℝ → X} {s₀ s₁ : ℝ} (hle : s₀ ≤ s₁)
    {c : ℂ} {r : ℝ} (hsub : Metric.ball c r ⊆ (chartAt (H := ℂ) Q₀).target)
    (hγ_in : ∀ t ∈ Set.Icc s₀ s₁, γ t ∈ (chartAt (H := ℂ) Q₀).source)
    (himg : ∀ t ∈ Set.Icc s₀ s₁, (chartAt (H := ℂ) Q₀) (γ t) ∈ Metric.ball c r)
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc s₀ s₁,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t)
    (hint : IntervalIntegrable (fun t => α.toFun (γ t) (pathSpeed γ t)) volume s₀ s₁) :
    ∫ t in s₀..s₁, α.toFun (γ t) (pathSpeed γ t)
      = segPeriod α Q₀ ((chartAt (H := ℂ) Q₀) (γ s₀)) ((chartAt (H := ℂ) Q₀) (γ s₁)) := by
  have hcoeff_diffOn : DifferentiableOn ℂ (coeffAt α Q₀) (Metric.ball c r) := fun w hw =>
    (coeffAt_analyticAt α Q₀ (hsub hw)).differentiableAt.differentiableWithinAt
  obtain ⟨F, hF⟩ := hcoeff_diffOn.isExactOn_ball
  have hs₀ : s₀ ∈ Set.Icc s₀ s₁ := ⟨le_rfl, hle⟩
  have hs₁ : s₁ ∈ Set.Icc s₀ s₁ := ⟨hle, le_rfl⟩
  rw [intervalIntegral_form_eq_primitive_diff α Q₀ hle hF hγ_in himg hγ_cont hγ_diff hint,
    segPeriod_eq_primitive_diff α Q₀ hsub hF (himg s₀ hs₀) (himg s₁ hs₁)]

end Jacobians.Dolbeault

end
