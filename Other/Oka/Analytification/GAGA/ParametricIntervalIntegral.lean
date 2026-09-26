/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytic.ParametricCircleIntegral

/-!
# Holomorphy of parametric interval integrals

Let `E` be a finite-dimensional complex normed space, `U ⊆ E` open and `G : E → ℝ → ℂ` jointly
continuous on `U × [a, b]` and holomorphic in the first variable. Then `x ↦ ∫ t in a..b, G x t`
is holomorphic on `U`. The proof is the one of `analyticAt_circleIntegral`: on a small polydisc
`G · t` is its own Cauchy integral, and Fubini exchanges the torus and the interval integral.

## Main results

- `torusIntegral_intervalIntegral_swap`: Fubini for a torus and an interval integral.
- `analyticAt_intervalIntegral`: the polydisc version, at the origin of `ℂ^m`.
- `analyticAt_of_differentiableOn_of_finiteDimensional`: a holomorphic function on an open
  subset of a finite-dimensional complex normed space is analytic.
- `complexChart E`, `exists_complexChart_polydisc_subset`, `analyticAt_of_complexChart`: a
  linear chart `ℂ^k ≃ E` and its use to reduce analyticity statements to polydiscs in `ℂ^k`.
- `differentiableOn_intervalIntegral`: holomorphy of parametric interval integrals with
  parameters in a finite-dimensional complex normed space.
-/

@[expose] public section

open Complex MeasureTheory
open scoped Topology Interval

/-- Fubini: a torus integral and an interval integral of a jointly continuous function
commute. -/
theorem torusIntegral_intervalIntegral_swap {m : ℕ} (c : Fin m → ℂ) (R : Fin m → ℝ)
    {a b : ℝ} (hab : a ≤ b) (H : (Fin m → ℂ) → ℝ → ℂ)
    (hH : Continuous fun p : (Fin m → ℝ) × ℝ ↦ H (torusMap c R p.1) p.2) :
    (∯ ξ in T(c, R), ∫ t in a..b, H ξ t) = ∫ t in a..b, ∯ ξ in T(c, R), H ξ t := by
  set A : (Fin m → ℝ) → ℝ → ℂ := fun φ t ↦
      (∏ i, (R i : ℂ) * Complex.exp (φ i * Complex.I) * Complex.I) * H (torusMap c R φ) t
    with hA
  have hcontA : Continuous (Function.uncurry A) := by
    have h1 : Continuous fun p : (Fin m → ℝ) × ℝ ↦
        (∏ i, (R i : ℂ) * Complex.exp (p.1 i * Complex.I) * Complex.I) := by
      apply continuous_finsetProd
      intro i _
      fun_prop
    exact h1.mul hH
  have hint : Integrable (Function.uncurry A)
      ((volume.restrict (Set.Icc (0 : Fin m → ℝ) fun _ ↦ 2 * Real.pi)).prod
        (volume.restrict (Set.Ioc a b))) := by
    rw [Measure.prod_restrict]
    refine IntegrableOn.mono_set ?_
      (Set.prod_mono (subset_refl _) Set.Ioc_subset_Icc_self)
    exact hcontA.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  simp only [torusIntegral, intervalIntegral.integral_of_le hab, smul_eq_mul]
  have hL : ∀ φ : Fin m → ℝ,
      (∏ i, (R i : ℂ) * Complex.exp (φ i * Complex.I) * Complex.I) *
          (∫ t in Set.Ioc a b, H (torusMap c R φ) t)
        = ∫ t in Set.Ioc a b, A φ t := by
    intro φ
    rw [← integral_const_mul]
  simp_rw [hL]
  exact integral_integral_swap hint

/-- An interval integral of a family that is holomorphic in the parameter on a closed polydisc,
and jointly continuous, is analytic at the centre of the polydisc. -/
theorem analyticAt_intervalIntegral {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (hab : a ≤ b)
    {G : (Fin m → ℂ) → ℝ → ℂ}
    (hdiff : ∀ t : ℝ, DifferentiableOn ℂ (fun x ↦ G x t)
      (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ))
    (hcont : Continuous fun p : (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
      G (p.1 : Fin m → ℂ) p.2) :
    AnalyticAt ℂ (fun x ↦ ∫ t in a..b, G x t) 0 := by
  have htm : Continuous fun φ : Fin m → ℝ ↦ torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) φ := by
    unfold torusMap; fun_prop
  have hnorm : ∀ (φ : Fin m → ℝ) (i), ‖torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) φ i‖ = ρ := by
    intro φ i
    simp [torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ]
  have hmem : ∀ φ : Fin m → ℝ,
      torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) φ ∈
        (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ) := by
    intro φ
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    simp only [Metric.mem_closedBall, Complex.dist_eq, sub_zero, hnorm, le_refl]
  have hGtc : Continuous fun p : (Fin m → ℝ) × ℝ ↦
      G (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) p.1) p.2 :=
    hcont.comp (((htm.comp continuous_fst).subtype_mk fun p ↦ hmem p.1).prodMk continuous_snd)
  have hcontI : ContinuousOn (fun x ↦ ∫ t in a..b, G x t)
      (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ) := by
    rw [continuousOn_iff_continuous_restrict]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (x : Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ) (t : ℝ) ↦
        G (x : Fin m → ℂ) t) hcont a b
  refine analyticAt_of_cauchyRepr hρ hcontI ?_
  intro y hy
  have hyne : ∀ (φ : Fin m → ℝ) (i), torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) φ i - y i ≠ 0 := by
    intro φ i h
    have h1 : ‖y i‖ < ρ := hy i
    rw [sub_eq_zero] at h
    rw [← h, hnorm] at h1
    exact lt_irrefl _ h1
  have hHcont : Continuous fun p : (Fin m → ℝ) × ℝ ↦
      (∏ i, (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) p.1 i - y i)⁻¹) *
        G (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) p.1) p.2 := by
    refine Continuous.mul ?_ hGtc
    apply continuous_finsetProd
    intro i _
    exact (((continuous_apply i).comp (htm.comp continuous_fst)).sub continuous_const).inv₀
      (fun p ↦ hyne p.1 i)
  have hfib : ∀ t : ℝ,
      G y t = (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
        ∯ ξ in T((0 : Fin m → ℂ), fun _ ↦ ρ), (∏ i, (ξ i - y i)⁻¹) • G ξ t := by
    intro t
    refine cauchy_torus_formula (fun x ↦ G x t) 0 (fun _ ↦ ρ) (fun _ ↦ hρ) (hdiff t) y
      (fun i ↦ ?_)
    simp only [Metric.mem_ball, Pi.zero_apply, dist_zero_right]
    exact hy i
  have h1 : (∫ t in a..b, G y t)
      = ∫ t in a..b, (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
          ∯ ξ in T((0 : Fin m → ℂ), fun _ ↦ ρ), (∏ i, (ξ i - y i)⁻¹) • G ξ t :=
    intervalIntegral.integral_congr fun t _ ↦ hfib t
  rw [h1, intervalIntegral.integral_smul]
  congr 1
  simp only [smul_eq_mul]
  rw [← torusIntegral_intervalIntegral_swap (0 : Fin m → ℂ) (fun _ ↦ ρ) hab
    (fun ξ t ↦ (∏ i, (ξ i - y i)⁻¹) * G ξ t) hHcont]
  simp_rw [intervalIntegral.integral_const_mul]

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A chart `ℂ^k ≃ E` of a finite-dimensional complex normed space. -/
noncomputable def complexChart (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] : (Fin (Module.finrank ℂ E) → ℂ) ≃L[ℂ] E :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- Around a point `x₀` of an open set `U ⊆ E`, the image of a small closed polydisc under the
affine chart `y ↦ x₀ + complexChart E y` lies in `U`. -/
lemma exists_complexChart_polydisc_subset {U : Set E} (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ ρ > 0, ∀ y ∈ Set.univ.pi fun _ : Fin (Module.finrank ℂ E) ↦ Metric.closedBall (0 : ℂ) ρ,
      x₀ + complexChart E y ∈ U := by
  have hφ : Continuous fun y : Fin (Module.finrank ℂ E) → ℂ ↦ x₀ + complexChart E y := by
    fun_prop
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hU.preimage hφ) 0 (by simpa using hx₀)
  refine ⟨δ / 2, by linarith, fun y hy ↦ hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i ↦ ?_)
    (by linarith : δ / 2 < δ)
  simpa using hy i (Set.mem_univ i)

/-- Analyticity at `x₀` follows from analyticity at `0` in the affine chart
`y ↦ x₀ + complexChart E y`. -/
lemma analyticAt_of_complexChart {f : E → ℂ} {x₀ : E}
    (h : AnalyticAt ℂ (fun y ↦ f (x₀ + complexChart E y)) 0) : AnalyticAt ℂ f x₀ := by
  have hlin : AnalyticAt ℂ (fun x : E ↦ (complexChart E).symm (x - x₀)) x₀ :=
    ((complexChart E).symm.toContinuousLinearMap.analyticAt _).comp
      (analyticAt_id.sub analyticAt_const)
  have := h.comp_of_eq hlin (by simp)
  convert this using 1
  funext x
  simp

/-- A holomorphic function on an open subset of a finite-dimensional complex normed space is
analytic. -/
theorem analyticAt_of_differentiableOn_of_finiteDimensional {U : Set E} (hU : IsOpen U)
    {f : E → ℂ} (hf : DifferentiableOn ℂ f U) {x₀ : E} (hx₀ : x₀ ∈ U) : AnalyticAt ℂ f x₀ := by
  refine analyticAt_of_complexChart ?_
  have hφ : Continuous fun y : Fin (Module.finrank ℂ E) → ℂ ↦ x₀ + complexChart E y := by
    fun_prop
  refine analyticAt_of_differentiableOn (hU.preimage hφ) ?_ (by simpa using hx₀)
  exact hf.comp (by fun_prop : Differentiable ℂ _).differentiableOn fun y hy ↦ hy

/-- **Holomorphy of parametric interval integrals.** If `G : E → ℝ → ℂ` is jointly continuous
on `U × [a, b]` and holomorphic on `U` in the first variable, then `x ↦ ∫ t in a..b, G x t` is
holomorphic on `U`. -/
theorem differentiableOn_intervalIntegral {U : Set E} (hU : IsOpen U) {a b : ℝ}
    {G : E → ℝ → ℂ} (hdiff : ∀ t ∈ [[a, b]], DifferentiableOn ℂ (fun x ↦ G x t) U)
    (hcont : ContinuousOn (fun p : E × ℝ ↦ G p.1 p.2) (U ×ˢ [[a, b]])) :
    DifferentiableOn ℂ (fun x ↦ ∫ t in a..b, G x t) U := by
  wlog hab : a ≤ b generalizing a b
  · have h := this (a := b) (b := a) (by rwa [Set.uIcc_comm]) (by rwa [Set.uIcc_comm])
      (le_of_not_ge hab)
    simp_rw [intervalIntegral.integral_symm b a]
    exact h.neg
  rw [Set.uIcc_of_le hab] at hdiff hcont
  intro x₀ hx₀
  refine (analyticAt_of_complexChart ?_).differentiableAt.differentiableWithinAt
  obtain ⟨ρ, hρ, hsub⟩ := exists_complexChart_polydisc_subset hU hx₀
  set G' : (Fin (Module.finrank ℂ E) → ℂ) → ℝ → ℂ :=
    fun y t ↦ G (x₀ + complexChart E y) (Set.projIcc a b hab t) with hG'
  have hmemI : ∀ t, (Set.projIcc a b hab t : ℝ) ∈ Set.Icc a b := fun t ↦
    (Set.projIcc a b hab t).2
  have hdiff' : ∀ t : ℝ, DifferentiableOn ℂ (fun y ↦ G' y t)
      (Set.univ.pi fun _ : Fin (Module.finrank ℂ E) ↦ Metric.closedBall (0 : ℂ) ρ) :=
    fun t ↦ (hdiff _ (hmemI t)).comp (by fun_prop : Differentiable ℂ _).differentiableOn
      fun y hy ↦ hsub y hy
  have hcont' : Continuous fun p : (Set.univ.pi fun _ : Fin (Module.finrank ℂ E) ↦
      Metric.closedBall (0 : ℂ) ρ) × ℝ ↦ G' (p.1 : Fin (Module.finrank ℂ E) → ℂ) p.2 := by
    refine hcont.comp_continuous (f := fun p : (Set.univ.pi fun _ : Fin (Module.finrank ℂ E) ↦
      Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
        (x₀ + complexChart E (p.1 : Fin (Module.finrank ℂ E) → ℂ), (Set.projIcc a b hab p.2 : ℝ)))
      (by fun_prop) fun p ↦ ⟨hsub _ p.1.2, hmemI _⟩
  have hA := analyticAt_intervalIntegral hρ hab hdiff' hcont'
  refine hA.congr (Filter.Eventually.of_forall fun y ↦ ?_)
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [Set.uIcc_of_le hab] at ht
  simp [hG', Set.projIcc_of_mem hab ht]

end FiniteDimensional

end
