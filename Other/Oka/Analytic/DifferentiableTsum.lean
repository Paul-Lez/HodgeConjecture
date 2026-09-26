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
# Series of holomorphic functions of several variables

The Weierstrass theorem for series in several complex variables: a series of holomorphic
functions on an open set `U ⊆ ℂᵐ` which is dominated, near every point of `U`, by a summable
sequence of constants has a holomorphic sum.

The proof passes through the Cauchy integral formula on a polydisc: each term satisfies it
(`cauchy_torus_formula`), the domination allows term-by-term integration over the distinguished
boundary, so the sum satisfies it as well, and a continuous function satisfying the Cauchy
formula is analytic (`analyticAt_of_cauchyRepr`).

## Main results

- `hasSum_torusIntegral_of_dominated`: term-by-term integration over a torus of a series
  dominated by a summable sequence.
- `differentiableOn_tsum_of_locally_summable`: the Weierstrass theorem for series.
-/

@[expose] public section

open Complex Metric Set MeasureTheory
open scoped Topology

/-- Term-by-term integration over a torus of a series dominated by a summable sequence. -/
theorem hasSum_torusIntegral_of_dominated {ι : Type*} [Countable ι] {m : ℕ}
    {F : ι → (Fin m → ℂ) → ℂ} {G : (Fin m → ℂ) → ℂ} {c : Fin m → ℂ} {R : Fin m → ℝ}
    (hF : ∀ i, Continuous fun θ ↦ F i (torusMap c R θ)) {u : ι → ℝ} (hu : Summable u)
    (hle : ∀ i θ, ‖F i (torusMap c R θ)‖ ≤ u i)
    (hG : ∀ θ, HasSum (fun i ↦ F i (torusMap c R θ)) (G (torusMap c R θ))) :
    HasSum (fun i ↦ ∯ z in T(c, R), F i z) (∯ z in T(c, R), G z) := by
  have hJ : Continuous fun θ : Fin m → ℝ ↦
      (∏ i, (R i : ℂ) * Complex.exp (θ i * Complex.I) * Complex.I) := by
    apply continuous_finsetProd
    intro i _
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Fin m → ℝ)) (b := fun _ ↦ 2 * Real.pi))
    |>.exists_bound_of_continuousOn hJ.continuousOn
  simp only [torusIntegral]
  refine hasSum_integral_of_dominated_convergence (fun i _ ↦ C * u i)
    (fun i ↦ (hJ.smul (hF i)).aestronglyMeasurable) (fun i ↦ ?_) ?_ ?_ ?_
  · refine (ae_restrict_iff' measurableSet_Icc).2 (.of_forall fun θ hθ ↦ ?_)
    rw [norm_smul]
    exact mul_le_mul (hC θ hθ) (hle i θ) (norm_nonneg _) ((norm_nonneg _).trans (hC θ hθ))
  · exact .of_forall fun θ ↦ hu.mul_left C
  · exact (continuousOn_const.integrableOn_compact isCompact_Icc)
  · exact .of_forall fun θ ↦ (hG θ).const_smul _

/-- **Weierstrass theorem** for series of holomorphic functions of several variables: if each
term is holomorphic on the open set `U` and near every point of `U` the terms are dominated by a
summable sequence, then the sum is holomorphic on `U`. -/
theorem differentiableOn_tsum_of_locally_summable {ι : Type*} [Countable ι] {m : ℕ}
    {F : ι → (Fin m → ℂ) → ℂ} {U : Set (Fin m → ℂ)} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hb : ∀ x ∈ U, ∃ u : ι → ℝ, Summable u ∧ ∃ V ∈ 𝓝 x, ∀ i, ∀ y ∈ V, ‖F i y‖ ≤ u i) :
    DifferentiableOn ℂ (fun y ↦ ∑' i, F i y) U := by
  intro x₀ hx₀
  obtain ⟨u, hu, V, hV, hle⟩ := hb x₀ hx₀
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (hU.mem_nhds hx₀) hV)
  set ρ := ε / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  set P : Set (Fin m → ℂ) := Set.univ.pi fun _ ↦ closedBall (0 : ℂ) ρ
  have hPsub : ∀ y ∈ P, x₀ + y ∈ U ∩ V := by
    intro y hy
    apply hεsub
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    have : y ∈ closedBall (0 : Fin m → ℂ) ρ := by rwa [closedBall_pi _ hρ.le]
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hshift : Differentiable ℂ fun y : Fin m → ℂ ↦ x₀ + y := by fun_prop
  have hFd : ∀ i, DifferentiableOn ℂ (fun y ↦ F i (x₀ + y)) P := fun i ↦
    (hF i).comp hshift.differentiableOn fun y hy ↦ (hPsub y hy).1
  set g : (Fin m → ℂ) → ℂ := fun y ↦ ∑' i, F i (x₀ + y) with hg
  have hsum : ∀ y ∈ P, HasSum (fun i ↦ F i (x₀ + y)) (g y) := fun y hy ↦
    (Summable.of_norm_bounded hu fun i ↦ hle i _ (hPsub y hy).2).hasSum
  have htm : ∀ θ, torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ ∈ P := by
    intro θ
    simp only [P, Set.mem_pi, Set.mem_univ, true_implies, mem_closedBall, dist_zero_right]
    intro i
    simp [torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ]
  have htmc : Continuous fun θ : Fin m → ℝ ↦ torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ := by
    unfold torusMap; fun_prop
  have hanalytic : AnalyticAt ℂ g 0 := by
    refine analyticAt_of_cauchyRepr hρ
      (continuousOn_tsum (fun i ↦ (hFd i).continuousOn) hu fun i y hy ↦ hle i _ (hPsub y hy).2)
      fun y hy ↦ ?_
    have hyne : ∀ θ i, torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i - y i ≠ 0 := by
      intro θ i h
      rw [sub_eq_zero] at h
      have h1 : ‖y i‖ < ρ := hy i
      rw [← h] at h1
      simp [torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ] at h1
    have hK : Continuous fun θ ↦
        ∏ i, (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i - y i)⁻¹ := by
      apply continuous_finsetProd
      intro i _
      exact (((continuous_apply i).comp htmc).sub continuous_const).inv₀ fun θ ↦ hyne θ i
    have hnorm : ∀ θ i, ‖torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i‖ = ρ := by
      intro θ i
      simp [torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ]
    have hC0 : 0 ≤ ∏ i, (ρ - ‖y i‖)⁻¹ :=
      Finset.prod_nonneg fun i _ ↦ inv_nonneg.2 (sub_nonneg.2 (hy i).le)
    have hC' : ∀ θ, ‖∏ i, (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i - y i)⁻¹‖ ≤
        ∏ i, (ρ - ‖y i‖)⁻¹ := by
      intro θ
      rw [norm_prod]
      refine Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) fun i _ ↦ ?_
      rw [norm_inv]
      have h2 := norm_sub_norm_le (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i) (y i)
      rw [hnorm] at h2
      exact inv_anti₀ (sub_pos.2 (hy i)) h2
    have key := hasSum_torusIntegral_of_dominated (c := 0) (R := fun _ ↦ ρ)
      (F := fun i ζ ↦ (∏ j, (ζ j - y j)⁻¹) * F i (x₀ + ζ))
      (G := fun ζ ↦ (∏ j, (ζ j - y j)⁻¹) * g ζ)
      (fun i ↦ hK.mul (((hFd i).continuousOn.comp_continuous htmc htm)))
      (hu.mul_left (∏ i, (ρ - ‖y i‖)⁻¹)) (fun i θ ↦ ?_) fun θ ↦ (hsum _ (htm θ)).mul_left _
    · have hrepr : ∀ i, (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
          (∯ ζ in T((0 : Fin m → ℂ), fun _ ↦ ρ), (∏ j, (ζ j - y j)⁻¹) * F i (x₀ + ζ)) =
            F i (x₀ + y) := fun i ↦ by
        rw [cauchy_torus_formula (fun ζ ↦ F i (x₀ + ζ)) 0 (fun _ ↦ ρ) (fun _ ↦ hρ) (hFd i) y
          fun j ↦ by simpa using hy j]
        simp only [smul_eq_mul]
      have h2 := key.const_smul ((2 * ↑Real.pi * Complex.I)⁻¹ ^ m)
      simp only [hrepr] at h2
      exact h2.unique (hsum y fun j _ ↦ by simpa using (hy j).le)
    · rw [norm_mul]
      exact mul_le_mul (hC' θ) (hle i _ (hPsub _ (htm θ)).2) (norm_nonneg _) hC0
  have := analyticAt_of_shift (f := fun y ↦ ∑' i, F i y) (x₀ := x₀) hanalytic
  exact this.differentiableAt.differentiableWithinAt

end
