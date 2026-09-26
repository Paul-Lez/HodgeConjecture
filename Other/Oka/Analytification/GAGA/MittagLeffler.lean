/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ParametricIntervalIntegral

/-!
# Weierstrass' theorem and the Mittag-Leffler argument in several variables

Let `E` be a finite-dimensional complex normed space.

## Main results

- `differentiableOn_of_tendstoLocallyUniformlyOn`: **Weierstrass' theorem**: a locally uniform
  limit of holomorphic functions on an open subset of `E` is holomorphic. The limit satisfies
  the Cauchy integral formula on small polydiscs, hence is analytic (`analyticAt_of_cauchyRepr`).
- `differentiableOn_tsum_of_summable_norm_le`: a series of holomorphic functions dominated by a
  summable sequence has a holomorphic sum.
- `exists_mittagLeffler`: **Mittag-Leffler**: let `U₀ ⊆ U₁ ⊆ ⋯` be open with union `X`, such
  that every function holomorphic on `U_{k+1}` can be approximated uniformly on `U_k` by
  functions holomorphic on `X`. Then for all `g_k` holomorphic on `U_k` there are `f_k`
  holomorphic on `U_k` with `g_k = f_k - f_{k+1}` on `U_k`; i.e. `lim¹_k 𝒪(U_k) = 0`.
-/

@[expose] public section

open Complex Filter Metric Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Weierstrass' theorem** in several variables: a locally uniform limit of holomorphic
functions on an open subset of a finite-dimensional space is holomorphic. -/
theorem differentiableOn_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set E} (hU : IsOpen U) {F : ι → E → ℂ} {G : E → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hFG : TendstoLocallyUniformlyOn F G l U) :
    DifferentiableOn ℂ G U := by
  intro x₀ hx₀
  refine (analyticAt_of_complexChart ?_).differentiableAt.differentiableWithinAt
  obtain ⟨ρ, hρ, hsub⟩ := exists_complexChart_polydisc_subset hU hx₀
  set m := Module.finrank ℂ E
  set Pd : Set (Fin m → ℂ) := Set.univ.pi fun _ ↦ closedBall (0 : ℂ) ρ with hPd
  set φ : (Fin m → ℂ) → E := fun y ↦ x₀ + complexChart E y with hφ
  have hφc : Continuous φ := by fun_prop
  have hPdc : IsCompact Pd := isCompact_univ_pi fun _ ↦ isCompact_closedBall _ _
  have hunif : TendstoUniformlyOn F G l (φ '' Pd) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hFG _
      (by rintro _ ⟨y, hy, rfl⟩; exact hsub y hy) (hPdc.image hφc)
  have hunif' : TendstoUniformlyOn (fun n y ↦ F n (φ y)) (fun y ↦ G (φ y)) l Pd :=
    (hunif.comp φ).mono fun y hy ↦ ⟨y, hy, rfl⟩
  have hFn : ∀ n, DifferentiableOn ℂ (fun y ↦ F n (φ y)) Pd := fun n ↦
    (hF n).comp (by fun_prop : Differentiable ℂ φ).differentiableOn fun y hy ↦ hsub y hy
  have hcont : ContinuousOn (fun y ↦ G (φ y)) Pd :=
    hunif'.continuousOn (Frequently.of_forall fun n ↦ (hFn n).continuousOn)
  refine analyticAt_of_cauchyRepr hρ hcont fun y hy ↦ ?_
  have htm : ∀ θ, torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ ∈ Pd := by
    intro θ
    simp only [Pd, Set.mem_pi, Set.mem_univ, true_implies, mem_closedBall, dist_zero_right]
    intro i
    simp [torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ]
  have htmc : Continuous fun θ : Fin m → ℝ ↦ torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ := by
    unfold torusMap; fun_prop
  have hnorm : ∀ θ i, ‖torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i‖ = ρ := by
    intro θ i
    simp [torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ]
  have hyne : ∀ θ i, torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i - y i ≠ 0 := by
    intro θ i h
    rw [sub_eq_zero] at h
    have h1 : ‖y i‖ < ρ := hy i
    rw [← h, hnorm] at h1
    exact lt_irrefl _ h1
  have hK : Continuous fun θ ↦ ∏ i, (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i - y i)⁻¹ := by
    apply continuous_finsetProd
    intro i _
    exact (((continuous_apply i).comp htmc).sub continuous_const).inv₀ fun θ ↦ hyne θ i
  set Cy : ℝ := ∏ i, (ρ - ‖y i‖)⁻¹ with hCy
  have hC0 : 0 ≤ Cy := Finset.prod_nonneg fun i _ ↦ inv_nonneg.2 (sub_nonneg.2 (hy i).le)
  have hKle : ∀ θ, ‖∏ i, (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i - y i)⁻¹‖ ≤ Cy := by
    intro θ
    rw [norm_prod]
    refine Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) fun i _ ↦ ?_
    rw [norm_inv]
    have h2 := norm_sub_norm_le (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i) (y i)
    rw [hnorm] at h2
    exact inv_anti₀ (sub_pos.2 (hy i)) h2
  have hint : ∀ g : (Fin m → ℂ) → ℂ, ContinuousOn g Pd →
      TorusIntegrable (fun ξ ↦ (∏ i, (ξ i - y i)⁻¹) * g ξ) 0 fun _ ↦ ρ := fun g hg ↦
    (hK.mul (hg.comp_continuous htmc htm)).continuousOn.integrableOn_compact isCompact_Icc
  set c : ℂ := (2 * ↑Real.pi * Complex.I)⁻¹ ^ m
  have hT : Tendsto (fun n ↦ c • ∯ ξ in T((0 : Fin m → ℂ), fun _ ↦ ρ),
      (∏ i, (ξ i - y i)⁻¹) * F n (φ ξ)) l
      (𝓝 (c • ∯ ξ in T((0 : Fin m → ℂ), fun _ ↦ ρ), (∏ i, (ξ i - y i)⁻¹) * G (φ ξ))) := by
    refine Tendsto.const_smul ?_ c
    rw [Metric.tendsto_nhds]
    intro ε hε
    set B : ℝ := ((2 * Real.pi) ^ m * ∏ _i : Fin m, |ρ|) * Cy
    have hB : 0 ≤ B := by positivity
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif' (ε / (B + 1)) (by positivity)]
      with n hn
    rw [dist_eq_norm, ← torusIntegral_sub (hint _ (hFn n).continuousOn) (hint _ hcont)]
    calc _ ≤ ((2 * Real.pi) ^ m * ∏ _i : Fin m, |ρ|) * (Cy * (ε / (B + 1))) := by
          refine norm_torusIntegral_le_of_norm_le_const fun θ ↦ ?_
          rw [← mul_sub, norm_mul]
          refine mul_le_mul (hKle θ) ?_ (norm_nonneg _) hC0
          rw [← dist_eq_norm, dist_comm]
          exact (hn _ (htm θ)).le
      _ = B * (ε / (B + 1)) := by ring
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  have hrepr : ∀ n, F n (φ y) = c • ∯ ξ in T((0 : Fin m → ℂ), fun _ ↦ ρ),
      (∏ i, (ξ i - y i)⁻¹) * F n (φ ξ) := by
    intro n
    rw [cauchy_torus_formula (fun ξ ↦ F n (φ ξ)) 0 (fun _ ↦ ρ) (fun _ ↦ hρ) (hFn n) y
      fun i ↦ by simpa using hy i]
    simp only [smul_eq_mul]
    rfl
  have hy' : y ∈ Pd := fun i _ ↦ by simpa using (hy i).le
  have h2 : Tendsto (fun n ↦ F n (φ y)) l
      (𝓝 (c • ∯ ξ in T((0 : Fin m → ℂ), fun _ ↦ ρ), (∏ i, (ξ i - y i)⁻¹) * G (φ ξ))) := by
    rw [show (fun n ↦ F n (φ y)) = _ from funext hrepr]
    exact hT
  exact (tendsto_nhds_unique (hunif'.tendsto_at hy') h2).symm

/-- A series of holomorphic functions on an open subset of a finite-dimensional space, dominated
by a summable sequence, has a holomorphic sum. -/
theorem differentiableOn_tsum_of_summable_norm_le {U : Set E} (hU : IsOpen U)
    {F : ℕ → E → ℂ} (hF : ∀ n, DifferentiableOn ℂ (F n) U) {u : ℕ → ℝ} (hu : Summable u)
    (hle : ∀ n, ∀ z ∈ U, ‖F n z‖ ≤ u n) :
    DifferentiableOn ℂ (fun z ↦ ∑' n, F n z) U :=
  differentiableOn_of_tendstoLocallyUniformlyOn hU
    (fun _ ↦ DifferentiableOn.fun_sum fun n _ ↦ hF n)
    (tendstoUniformlyOn_tsum_nat hu fun n z hz ↦ hle n z hz).tendstoLocallyUniformlyOn

/-- **Mittag-Leffler.** Let `U₀ ⊆ U₁ ⊆ ⋯` be open, such that every function holomorphic on
`U_{k+1}` is a uniform limit on `U_k` of functions holomorphic on `⋃ U_j`. Then for all
`g_k` holomorphic on `U_k` there are `f_k` holomorphic on `U_k` with `g_k = f_k - f_{k+1}` on
`U_k`. In other words `lim¹_k 𝒪(U_k) = 0`. -/
theorem exists_mittagLeffler {U : ℕ → Set E} (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (happrox : ∀ k (g : E → ℂ), DifferentiableOn ℂ g (U (k + 1)) → ∀ ε > 0,
      ∃ h : E → ℂ, DifferentiableOn ℂ h (⋃ j, U j) ∧ ∀ z ∈ U k, ‖g z - h z‖ ≤ ε)
    (g : ℕ → E → ℂ) (hg : ∀ k, DifferentiableOn ℂ (g k) (U k)) :
    ∃ f : ℕ → E → ℂ, (∀ k, DifferentiableOn ℂ (f k) (U k)) ∧
      ∀ k, ∀ z ∈ U k, g k z = f k z - f (k + 1) z := by
  choose h hh hle using fun j ↦ happrox j (g (j + 1)) (hg (j + 1)) ((1 / 2) ^ j) (by positivity)
  set d : ℕ → E → ℂ := fun j z ↦ g (j + 1) z - h j z with hd
  have hdiff : ∀ j k, k ≤ j + 1 → DifferentiableOn ℂ (d j) (U k) := fun j k hk ↦
    ((hg (j + 1)).mono (hmono hk)).sub ((hh j).mono (subset_iUnion U k))
  have hbound : ∀ k j, ∀ z ∈ U k, ‖d (j + k) z‖ ≤ (1 / 2) ^ j := fun k j z hz ↦
    (hle (j + k) z (hmono (Nat.le_add_left k j) hz)).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right j k))
  have hsum : ∀ k, ∀ z ∈ U k, Summable fun j ↦ d (j + k) z := fun k z hz ↦
    Summable.of_norm_bounded (summable_geometric_two) fun j ↦ by
      simpa [one_div] using hbound k j z hz
  refine ⟨fun k z ↦ g k z + ∑' j, d (j + k) z - ∑ j ∈ Finset.range k, h j z, fun k ↦ ?_,
    fun k z hz ↦ ?_⟩
  · refine ((hg k).add ?_).sub ?_
    · exact differentiableOn_tsum_of_summable_norm_le (hU k)
        (fun j ↦ hdiff (j + k) k (by omega)) summable_geometric_two
        fun j z hz ↦ by simpa [one_div] using hbound k j z hz
    · exact DifferentiableOn.fun_sum fun j _ ↦ (hh j).mono (subset_iUnion U k)
  · dsimp only
    rw [(hsum k z hz).tsum_eq_zero_add, Finset.sum_range_succ]
    simp only [zero_add, hd]
    have : ∀ j, j + 1 + k = j + (k + 1) := fun j ↦ by omega
    simp_rw [this]
    ring

end
