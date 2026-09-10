/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.LocalKFoldMultiplicityFullyUnconditional
import KirovDolbeault.Discharge.Manifold.LocalMultiplicityInvariance
import KirovDolbeault.Discharge.Manifold.AnalyticLocalFactorization
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros

set_option autoImplicit true


/-! # Bridge: critical set ↔ chart-pullback derivative zero (ZZ99)

This file supplies bridge lemmas linking ZZ97's *topological* critical-set
definition

```
criticalSet f := { x | ¬ ∃ U ∈ 𝓝 x, Set.InjOn (f̃) U }
```

to the *analytic* "chart-pullback derivative vanishes" condition consumed
downstream.

## Pieces delivered

* **`deriv_ne_zero_of_analyticOrderAt_eq_one`** — order-`1` ⇒ deriv ≠ `0`.
  From the factorization `g(z) - w₀ = (z - x₀) · u(z)` with `u(x₀) ≠ 0`
  (ZZ90), the product rule gives `deriv g x₀ = u(x₀) ≠ 0`.

* **`notInjOn_of_deriv_zero_of_analyticOrderAt`** — the headline planar
  consequence: for analytic `g : ℂ → ℂ` at `x₀` with `g x₀ = w₀` and the
  analytic order of `g - w₀` at `x₀` equal to some `k ≥ 2`, then `g` is
  not injective on any neighbourhood of `x₀`. Proof: extract the
  `KthRootSubstitution`-style data via the local factorization (ZZ90)
  and the `k`-th root branch (ZZ87); use the inverse function theorem
  applied to `v(z) := (z - x₀) · r(z)` (which has nonvanishing
  derivative) to pull two distinct `k`-th roots of unity back to two
  distinct preimages of any small target value.

* **`injOn_nhds_of_deriv_ne_zero`** — the immediate forward direction:
  `deriv g x₀ ≠ 0` ⇒ `g` is locally injective. Routes through the
  inverse function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`).

* **`notInjOn_iff_deriv_zero_of_analytic_of_order`** — combined planar
  iff. We state the iff under the explicit hypothesis that the analytic
  order of `g - g x₀` at `x₀` equals some `k ≥ 1`; this avoids the
  identity-theorem branching for "g locally constant at its value"
  (which is folded into `analyticOrderAt = ⊤` in the unhypothesised
  formulation).

* **`criticalSet_iff_chart_pullback_deriv_zero`** — manifold-side
  translation, packaged as a bridge taking a `ChartBridgePackage` that
  records the chart pullback, its analyticity at the chart image, and
  its order data.

No gaps, no `axiom`. No signature changes outside this new file.
-/

@[expose] public section

noncomputable section

open scoped Topology
open Set Filter Metric

namespace Jacobians.Discharge
namespace Manifold

/-! ## Step 1. `analyticOrderAt = 1` ⇒ `deriv ≠ 0` -/

/-- **From `analyticOrderAt (g - w₀) x₀ = 1` to `deriv g x₀ ≠ 0`.** -/
theorem deriv_ne_zero_of_analyticOrderAt_eq_one
    {g : ℂ → ℂ} {x₀ w₀ : ℂ}
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (1 : ℕ∞)) :
    deriv g x₀ ≠ 0 := by
  obtain ⟨R, hR_pos, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization (k := 1) (le_refl _) hg h_w₀ hord
  have hball_subset : Metric.ball x₀ R ⊆ Metric.closedBall x₀ R :=
    Metric.ball_subset_closedBall
  have hg_eq : ∀ z ∈ Metric.ball x₀ R, g z = w₀ + (z - x₀) * u z := by
    intro z hz
    have h1 := hfact z (hball_subset hz)
    have h2 : (z - x₀) ^ (1 : ℕ) * u z = (z - x₀) * u z := by rw [pow_one]
    have h3 : g z - w₀ = (z - x₀) * u z := h1.trans h2
    have := sub_eq_iff_eq_add'.mp h3
    linear_combination this
  set h : ℂ → ℂ := fun z => w₀ + (z - x₀) * u z with hh_def
  have hu_at_x₀ : AnalyticAt ℂ u x₀ :=
    hu_an x₀ (Metric.mem_closedBall_self hR_pos.le)
  have hu_diff : DifferentiableAt ℂ u x₀ := hu_at_x₀.differentiableAt
  have hsub_diff : DifferentiableAt ℂ (fun ζ : ℂ => ζ - x₀) x₀ :=
    differentiableAt_id.sub (differentiableAt_const x₀)
  have hball_nhds : Metric.ball x₀ R ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ hR_pos
  have hg_h_eventually : g =ᶠ[𝓝 x₀] h := by
    filter_upwards [hball_nhds] with z hz using hg_eq z hz
  have hderiv_sub : deriv (fun ζ : ℂ => ζ - x₀) x₀ = 1 := by
    -- Directly: `(z - x₀)` is `z ↦ z + (- x₀)`, derivative = 1.
    have h_eq : (fun ζ : ℂ => ζ - x₀) = (fun ζ : ℂ => ζ + (- x₀)) := by
      funext ζ; ring
    rw [h_eq, deriv_add_const]
    exact deriv_id x₀
  have hderiv_prod :
      deriv (fun z : ℂ => (z - x₀) * u z) x₀ = u x₀ := by
    have hp := deriv_mul (𝕜 := ℂ) hsub_diff hu_diff
    rw [hderiv_sub, sub_self, zero_mul, add_zero, one_mul] at hp
    exact hp
  have hsplit : deriv (fun z : ℂ => w₀ + (z - x₀) * u z) x₀
      = deriv (fun z : ℂ => (z - x₀) * u z) x₀ := by
    -- `deriv_const_add'` is an equation of functions; apply at x₀.
    have h := deriv_const_add' (𝕜 := ℂ) (f := fun z : ℂ => (z - x₀) * u z) (c := w₀)
    -- h : (deriv fun x => w₀ + (fun z => (z - x₀) * u z) x) = deriv fun z => (z - x₀) * u z
    exact congrFun h x₀
  have hderiv_h : deriv h x₀ = u x₀ := by
    show deriv (fun z : ℂ => w₀ + (z - x₀) * u z) x₀ = u x₀
    rw [hsplit, hderiv_prod]
  have hderiv_g : deriv g x₀ = deriv h x₀ := hg_h_eventually.deriv_eq
  rw [hderiv_g, hderiv_h]
  exact hu_x₀

/-! ## Step 2. Forward direction: `deriv ≠ 0` ⇒ locally injective -/

/-- **Locally injective from non-vanishing derivative.** -/
theorem injOn_nhds_of_deriv_ne_zero
    {g : ℂ → ℂ} {x₀ : ℂ}
    (hg : AnalyticAt ℂ g x₀) (hd : deriv g x₀ ≠ 0) :
    ∃ U ∈ 𝓝 x₀, Set.InjOn g U := by
  have hsd : HasStrictDerivAt g (deriv g x₀) x₀ := hg.hasStrictDerivAt
  have hsfd :
      HasStrictFDerivAt g
        (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv g x₀) hd) :
          ℂ →L[ℂ] ℂ) x₀ :=
    hsd.hasStrictFDerivAt_equiv hd
  let φ : OpenPartialHomeomorph ℂ ℂ := hsfd.toOpenPartialHomeomorph g
  have hx0_src : x₀ ∈ φ.source := hsfd.mem_toOpenPartialHomeomorph_source
  have h_src_nhds : φ.source ∈ 𝓝 x₀ := φ.open_source.mem_nhds hx0_src
  have h_inj : Set.InjOn (φ : ℂ → ℂ) φ.source := φ.injOn
  have h_coe : (φ : ℂ → ℂ) = g := hsfd.toOpenPartialHomeomorph_coe
  refine ⟨φ.source, h_src_nhds, ?_⟩
  rw [← h_coe]; exact h_inj

/-! ## Step 3. Reverse direction (under explicit order ≥ 2 hypothesis) -/

/-- **Order `≥ 2` ⇒ not locally injective.**

For analytic `g : ℂ → ℂ` at `x₀` with `g x₀ = w₀` and analytic order of
`g - w₀` at `x₀` equal to `k ≥ 2`, `g` is not injective on any
neighbourhood of `x₀`.

Proof: ZZ90 gives a factorization `g(z) - w₀ = (z - x₀)^k · u(z)` with
`u` analytic and non-vanishing on `closedBall x₀ R`. ZZ87 supplies an
analytic `k`-th root `r(z)` of `u(z)` on a smaller closed ball
`closedBall x₀ ρ'`. Set `v(z) := (z - x₀) · r(z)`. Then `v(x₀) = 0`,
`deriv v x₀ = r(x₀) ≠ 0`, and `v(z)^k = g(z) - w₀` on the small ball.

The inverse function theorem applied to `v` gives an
`OpenPartialHomeomorph ψ : ℂ → ℂ` with `v` as its underlying map,
`ψ.source` an open nbhd of `x₀`, and `ψ.target` an open nbhd of `0`.
For any open `U ∈ 𝓝 x₀`, shrink to `ball x₀ ε_top ⊆ U ∩ closedBall x₀ ρ'`,
then to `ball x₀ s ⊆ ψ.source ∩ ball x₀ ε_top`, then pull back to find
`τ > 0` such that for any `ξ ∈ ball 0 τ`, `ψ.symm ξ ∈ ball x₀ s`.

Pick `ξ := τ/2` (real, nonzero) and `ω := exp(2π i / k)` (a primitive
`k`-th root of unity, `≠ 1` because `k ≥ 2`). Then `ψ.symm ξ` and
`ψ.symm (ω · ξ)` are two distinct points in `ball x₀ ε_top ⊆ U` with
`v(·) = ξ, ω·ξ` respectively, hence `g(·) - w₀ = ξ^k, (ω·ξ)^k = ω^k ξ^k
= ξ^k`, i.e. equal `g`-values. Contradicts `InjOn g U`. -/
theorem notInjOn_of_analyticOrderAt_ge_two
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ}
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hk_ge_two : 2 ≤ k)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞)) :
    ¬ ∃ U ∈ 𝓝 x₀, Set.InjOn g U := by
  rintro ⟨U, hU_nhds, hU_inj⟩
  have hk_ge_one : 1 ≤ k := by linarith
  obtain ⟨R, hR_pos, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization hk_ge_one hg h_w₀ hord
  obtain ⟨r_root, ρ', hρ'_pos, hρ'_le, hr_an, hr_pow⟩ :=
    analytic_kth_root_of_nonvanishing hR_pos hu_an hu_x₀ hk_ge_one
  set v : ℂ → ℂ := fun z => (z - x₀) * r_root z with hv_def
  have hv_x₀ : v x₀ = 0 := by simp [hv_def]
  have hr_x₀_in : x₀ ∈ Metric.closedBall x₀ ρ' := Metric.mem_closedBall_self hρ'_pos.le
  have hr_x₀_pow : r_root x₀ ^ k = u x₀ := hr_pow x₀ hr_x₀_in
  have hr_x₀_ne : r_root x₀ ≠ 0 := by
    intro h
    have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk_ge_one
    have h1 : (0 : ℂ) ^ k = u x₀ := by rw [← h]; exact hr_x₀_pow
    rw [zero_pow hk0] at h1
    exact hu_x₀ h1.symm
  have hr_root_diff : DifferentiableAt ℂ r_root x₀ :=
    (hr_an x₀ hr_x₀_in).differentiableAt
  have hsub_diff : DifferentiableAt ℂ (fun ζ : ℂ => ζ - x₀) x₀ :=
    differentiableAt_id.sub (differentiableAt_const x₀)
  have hv_at_x₀ : AnalyticAt ℂ v x₀ := by
    have h1 : AnalyticAt ℂ (fun ζ : ℂ => ζ - x₀) x₀ :=
      analyticAt_id.sub analyticAt_const
    exact h1.mul (hr_an x₀ hr_x₀_in)
  have hderiv_v : deriv v x₀ = r_root x₀ := by
    have hp := deriv_mul (𝕜 := ℂ) hsub_diff hr_root_diff
    have hsub_d : deriv (fun ζ : ℂ => ζ - x₀) x₀ = 1 := by
      have h_eq : (fun ζ : ℂ => ζ - x₀) = (fun ζ : ℂ => ζ + (- x₀)) := by
        funext ζ; ring
      rw [h_eq, deriv_add_const]
      exact deriv_id x₀
    rw [hsub_d, sub_self, zero_mul, add_zero, one_mul] at hp
    exact hp
  have hderiv_v_ne : deriv v x₀ ≠ 0 := by rw [hderiv_v]; exact hr_x₀_ne
  -- Pick a small ball `ball x₀ ε_top` inside `U ∩ closedBall x₀ ρ'`.
  obtain ⟨ε_U, hε_U_pos, hε_U_sub_U⟩ := Metric.mem_nhds_iff.mp hU_nhds
  set ε_top : ℝ := min ε_U ρ' with hε_top_def
  have hε_top_pos : 0 < ε_top := lt_min hε_U_pos hρ'_pos
  have hε_top_le_U : ε_top ≤ ε_U := min_le_left _ _
  have hε_top_le_ρ' : ε_top ≤ ρ' := min_le_right _ _
  -- Inverse function theorem applied to v.
  have hsd_v : HasStrictDerivAt v (deriv v x₀) x₀ := hv_at_x₀.hasStrictDerivAt
  have hsfd_v :
      HasStrictFDerivAt v
        (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv v x₀) hderiv_v_ne) :
          ℂ →L[ℂ] ℂ) x₀ :=
    hsd_v.hasStrictFDerivAt_equiv hderiv_v_ne
  let ψ : OpenPartialHomeomorph ℂ ℂ := hsfd_v.toOpenPartialHomeomorph v
  have h_x0_src : x₀ ∈ ψ.source := hsfd_v.mem_toOpenPartialHomeomorph_source
  have h_v_x0_tgt : v x₀ ∈ ψ.target := hsfd_v.image_mem_toOpenPartialHomeomorph_target
  have h_coe_v : (ψ : ℂ → ℂ) = v := hsfd_v.toOpenPartialHomeomorph_coe
  have h_src_nhds : ψ.source ∈ 𝓝 x₀ := ψ.open_source.mem_nhds h_x0_src
  -- s with ball x₀ s ⊆ ψ.source ∩ ball x₀ ε_top.
  have h_inter_nhds : ψ.source ∩ Metric.ball x₀ ε_top ∈ 𝓝 x₀ :=
    Filter.inter_mem h_src_nhds (Metric.ball_mem_nhds x₀ hε_top_pos)
  obtain ⟨s, hs_pos, hs_sub⟩ := Metric.mem_nhds_iff.mp h_inter_nhds
  -- ψ.symm continuous at v x₀ = 0; preimage of ball x₀ s is a nbhd of 0.
  have h_symm_cont : ContinuousAt ψ.symm (v x₀) :=
    (ψ.continuousOn_symm).continuousAt (ψ.open_target.mem_nhds h_v_x0_tgt)
  have h_symm_v_x0 : ψ.symm (v x₀) = x₀ := by
    have := ψ.left_inv h_x0_src
    have hψx₀ : (ψ : ℂ → ℂ) x₀ = v x₀ := by rw [h_coe_v]
    rw [hψx₀] at this
    exact this
  have h_pre_nhds : ψ.symm ⁻¹' Metric.ball x₀ s ∈ 𝓝 (v x₀) := by
    have htend := h_symm_cont.tendsto
    rw [h_symm_v_x0] at htend
    exact htend (Metric.ball_mem_nhds x₀ hs_pos)
  have h_combo_nhds :
      ψ.target ∩ ψ.symm ⁻¹' Metric.ball x₀ s ∈ 𝓝 (v x₀) :=
    Filter.inter_mem (ψ.open_target.mem_nhds h_v_x0_tgt) h_pre_nhds
  rw [hv_x₀] at h_combo_nhds
  obtain ⟨τ, hτ_pos, hτ_sub⟩ := Metric.mem_nhds_iff.mp h_combo_nhds
  -- ξ = (τ/2 : ℂ).
  set ξ : ℂ := ((τ / 2 : ℝ) : ℂ) with hξ_def
  have hξ_norm : ‖ξ‖ = τ / 2 := by
    rw [hξ_def, Complex.norm_real]
    exact abs_of_pos (by linarith)
  have hξ_ne : ξ ≠ 0 := by
    intro h
    have h_norm : ‖ξ‖ = 0 := by rw [h]; simp
    rw [hξ_norm] at h_norm
    linarith
  have hξ_in : ξ ∈ Metric.ball (0 : ℂ) τ := by
    rw [Metric.mem_ball, dist_zero_right, hξ_norm]
    linarith
  -- ω = primitive k-th root of unity.
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / k) with hω_def
  have hk_ne : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk_ge_one)
  have hω_pow : ω ^ k = 1 := by
    rw [hω_def, ← Complex.exp_nat_mul]
    have heq : (k : ℂ) * (2 * Real.pi * Complex.I / k) = 2 * Real.pi * Complex.I := by
      field_simp
    rw [heq, Complex.exp_two_pi_mul_I]
  have hω_ne_one : ω ≠ 1 := by
    intro hcontra
    rw [hω_def, Complex.exp_eq_one_iff] at hcontra
    obtain ⟨n, hn⟩ := hcontra
    have hpi_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have h2 : (2 : ℂ) ≠ 0 := by norm_num
      exact mul_ne_zero (mul_ne_zero h2 hpi) Complex.I_ne_zero
    -- From `hn : 2 π i / k = n * (2 π i)`, multiply both sides by `k`:
    --   `2 π i = n * (2 π i) * k`. Then cancel `2 π i`: `1 = n * k`.
    have hk_ne_complex : (k : ℂ) ≠ 0 := hk_ne
    have hn_k : (2 * (Real.pi : ℂ) * Complex.I) =
                ((n : ℂ) * k) * (2 * (Real.pi : ℂ) * Complex.I) := by
      have h_mul : (2 * (Real.pi : ℂ) * Complex.I / (k : ℂ)) * (k : ℂ)
                   = ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (k : ℂ) := by
        rw [hn]
      rw [div_mul_cancel₀ _ hk_ne_complex] at h_mul
      linear_combination h_mul
    have h_one : (1 : ℂ) = ((n : ℂ) * k) := by
      have hh : (2 * (Real.pi : ℂ) * Complex.I) * 1 =
                (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * (k : ℂ)) := by
        rw [mul_one]
        linear_combination hn_k
      exact mul_left_cancel₀ hpi_ne hh
    have h_int : (n * (k : ℤ) : ℤ) = 1 := by
      have hcast : ((n * (k : ℤ) : ℤ) : ℂ) = (1 : ℤ) := by
        push_cast
        linear_combination -h_one
      exact_mod_cast hcast
    have h_k_int : (k : ℤ) ≥ 2 := by exact_mod_cast hk_ge_two
    have h_dvd : (k : ℤ) ∣ 1 := ⟨n, by linarith [h_int]⟩
    have h_k_le : (k : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) h_dvd
    linarith
  have hω_norm : ‖ω‖ = 1 := by
    rw [hω_def, Complex.norm_exp]
    have h_re_zero : (2 * (Real.pi : ℂ) * Complex.I / (k : ℂ)).re = 0 := by
      have h_num_re : (2 * (Real.pi : ℂ) * Complex.I).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      have h_num_im : (2 * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by
        simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      have hk_re : ((k : ℂ)).re = (k : ℝ) := Complex.natCast_re _
      have hk_im : ((k : ℂ)).im = 0 := Complex.natCast_im _
      rw [Complex.div_re, h_num_re, h_num_im, hk_re, hk_im]
      -- Goal: `0 * ↑k / Complex.normSq ↑k - 2 * Real.pi * 0 / Complex.normSq ↑k = 0`.
      ring
    rw [h_re_zero]; exact Real.exp_zero
  have hωξ_norm : ‖ω * ξ‖ = τ / 2 := by
    rw [norm_mul, hω_norm, one_mul, hξ_norm]
  have hωξ_in : ω * ξ ∈ Metric.ball (0 : ℂ) τ := by
    rw [Metric.mem_ball, dist_zero_right, hωξ_norm]
    linarith
  -- Pull back via `ψ.symm`.
  have h_ξ_in_target : ξ ∈ ψ.target := (hτ_sub hξ_in).1
  have h_ωξ_in_target : ω * ξ ∈ ψ.target := (hτ_sub hωξ_in).1
  have h_z₁ : ψ.symm ξ ∈ Metric.ball x₀ s := (hτ_sub hξ_in).2
  have h_z₂ : ψ.symm (ω * ξ) ∈ Metric.ball x₀ s := (hτ_sub hωξ_in).2
  set z₁ : ℂ := ψ.symm ξ with hz₁_def
  set z₂ : ℂ := ψ.symm (ω * ξ) with hz₂_def
  have hz₁_in_top : z₁ ∈ Metric.ball x₀ ε_top := (hs_sub h_z₁).2
  have hz₂_in_top : z₂ ∈ Metric.ball x₀ ε_top := (hs_sub h_z₂).2
  have _hz₁_src : z₁ ∈ ψ.source := (hs_sub h_z₁).1
  have _hz₂_src : z₂ ∈ ψ.source := (hs_sub h_z₂).1
  have hv_z₁ : v z₁ = ξ := by
    have hh : (ψ : ℂ → ℂ) (ψ.symm ξ) = ξ := ψ.right_inv h_ξ_in_target
    rw [h_coe_v] at hh; exact hh
  have hv_z₂ : v z₂ = ω * ξ := by
    have hh : (ψ : ℂ → ℂ) (ψ.symm (ω * ξ)) = ω * ξ := ψ.right_inv h_ωξ_in_target
    rw [h_coe_v] at hh; exact hh
  have hz₁_close : z₁ ∈ Metric.closedBall x₀ ρ' := by
    have hin : z₁ ∈ Metric.ball x₀ ε_top := hz₁_in_top
    rw [Metric.mem_ball] at hin
    rw [Metric.mem_closedBall]; linarith
  have hz₂_close : z₂ ∈ Metric.closedBall x₀ ρ' := by
    have hin : z₂ ∈ Metric.ball x₀ ε_top := hz₂_in_top
    rw [Metric.mem_ball] at hin
    rw [Metric.mem_closedBall]; linarith
  have h_factor : ∀ z ∈ Metric.closedBall x₀ ρ', g z - w₀ = (v z) ^ k := by
    intro z hz
    have h1 : r_root z ^ k = u z := hr_pow z hz
    have hz_in_R : z ∈ Metric.closedBall x₀ R :=
      (Metric.closedBall_subset_closedBall hρ'_le) hz
    have h2 : g z - w₀ = (z - x₀) ^ k * u z := hfact z hz_in_R
    show g z - w₀ = ((z - x₀) * r_root z) ^ k
    rw [mul_pow, h1]; exact h2
  have hg_z₁ : g z₁ - w₀ = ξ ^ k := by rw [h_factor z₁ hz₁_close, hv_z₁]
  have hg_z₂ : g z₂ - w₀ = (ω * ξ) ^ k := by rw [h_factor z₂ hz₂_close, hv_z₂]
  have h_ωξ_pow : (ω * ξ) ^ k = ξ ^ k := by rw [mul_pow, hω_pow, one_mul]
  have h_g_eq : g z₁ = g z₂ := by
    have h1 : g z₁ = w₀ + ξ ^ k := by linear_combination hg_z₁
    have h2 : g z₂ = w₀ + (ω * ξ) ^ k := by linear_combination hg_z₂
    rw [h1, h2, h_ωξ_pow]
  have hz₁_ne_z₂ : z₁ ≠ z₂ := by
    intro h_eq
    have h_v_eq : v z₁ = v z₂ := by rw [h_eq]
    rw [hv_z₁, hv_z₂] at h_v_eq
    -- ξ = ω * ξ ⟹ (1 - ω) * ξ = 0 ⟹ ω = 1 (since ξ ≠ 0).
    have h_zero : (1 - ω) * ξ = 0 := by linear_combination h_v_eq
    rcases mul_eq_zero.mp h_zero with hω1 | hξ0
    · -- hω1 : 1 - ω = 0. Hence ω = 1.
      apply hω_ne_one
      have := sub_eq_zero.mp hω1
      exact this.symm
    · exact hξ_ne hξ0
  have hz₁_U : z₁ ∈ U := by
    apply hε_U_sub_U
    exact (Metric.ball_subset_ball hε_top_le_U) hz₁_in_top
  have hz₂_U : z₂ ∈ U := by
    apply hε_U_sub_U
    exact (Metric.ball_subset_ball hε_top_le_U) hz₂_in_top
  exact hz₁_ne_z₂ (hU_inj hz₁_U hz₂_U h_g_eq)

/-! ## Step 4. Combined planar iff (under explicit order hypothesis) -/

/-- **Planar key lemma (under finite-order hypothesis).**

For analytic `g : ℂ → ℂ` at `x₀` with the analytic order of `g - g x₀` at
`x₀` equal to some natural `k ≥ 1`,

  `(¬ ∃ U ∈ 𝓝 x₀, Set.InjOn g U) ↔ deriv g x₀ = 0`,

equivalently `↔ k ≥ 2`. The "finite-order" hypothesis is the way the
"`g` not locally constant at its value" assumption enters: locally
constant ↔ `analyticOrderAt = ⊤`. -/
theorem notInjOn_iff_deriv_zero_of_analytic_of_order
    {g : ℂ → ℂ} {x₀ : ℂ} {k : ℕ}
    (hg : AnalyticAt ℂ g x₀)
    (hk_ge_one : 1 ≤ k)
    (hord : analyticOrderAt (fun z => g z - g x₀) x₀ = (k : ℕ∞)) :
    (¬ ∃ U ∈ 𝓝 x₀, Set.InjOn g U) ↔ deriv g x₀ = 0 := by
  refine ⟨?_, ?_⟩
  · intro h_notInj
    -- Forward: if not InjOn, then deriv g x₀ = 0.
    -- If deriv g x₀ ≠ 0, ZZ74 / IFT gives local injectivity, contradiction.
    by_contra hd_ne
    exact h_notInj (injOn_nhds_of_deriv_ne_zero hg hd_ne)
  · intro hd
    -- Reverse: if deriv g x₀ = 0, then `k ≥ 2` (else `k = 1` would give deriv ≠ 0
    -- by `deriv_ne_zero_of_analyticOrderAt_eq_one`). Then apply `notInjOn_of_analyticOrderAt_ge_two`.
    have hk_ge_two : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      have hk_eq_one : k = 1 := by linarith
      subst hk_eq_one
      have hord' : analyticOrderAt (fun z => g z - g x₀) x₀ = (1 : ℕ∞) := hord
      exact (deriv_ne_zero_of_analyticOrderAt_eq_one hg rfl hord') hd
    exact notInjOn_of_analyticOrderAt_ge_two hg rfl hk_ge_two hord

/-! ## Step 5. Manifold-side bridge -/

/-- **Chart bridge package.** Records a chart-pullback view of `f : X → Y`
near `x : X` together with the data needed to translate "no neighbourhood
of `x` is `InjOn` for `f`" into "no neighbourhood of the chart image is
`InjOn` for the chart pullback `F`", plus analyticity and the explicit
finite-order hypothesis. -/
structure ChartBridgePackage {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (x : X) where
  /-- The chart pullback of `f` near `x`. -/
  F : ℂ → ℂ
  /-- The chart image of `x`. -/
  z₀ : ℂ
  /-- Analyticity of the chart pullback at the chart image. -/
  hF_an : AnalyticAt ℂ F z₀
  /-- The local order of `F - F z₀` at `z₀`. -/
  k : ℕ
  hk_ge_one : 1 ≤ k
  hord : analyticOrderAt (fun z => F z - F z₀) z₀ = (k : ℕ∞)
  /-- The chart-side ↔ manifold-side non-injectivity transfer. -/
  inj_iff :
    (¬ ∃ U ∈ 𝓝 x, Set.InjOn f U) ↔ ¬ ∃ V ∈ 𝓝 z₀, Set.InjOn F V

/-- **Manifold-side bridge.** Under a `ChartBridgePackage`, "`x` is in the
critical set" (no neighbourhood is `InjOn` for `f`) is equivalent to
"the chart pullback has vanishing derivative at the chart image". -/
theorem criticalSet_iff_chart_pullback_deriv_zero
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X}
    (P : ChartBridgePackage f x) :
    (¬ ∃ U ∈ 𝓝 x, Set.InjOn f U) ↔ deriv P.F P.z₀ = 0 := by
  rw [P.inj_iff]
  -- Specialize the planar lemma at `g := P.F`, `x₀ := P.z₀`.
  -- `P.F z₀ = (P.F) (P.z₀)`, which equals `P.F P.z₀` definitionally.
  have h := notInjOn_iff_deriv_zero_of_analytic_of_order P.hF_an P.hk_ge_one P.hord
  exact h

end Manifold
end Jacobians.Discharge

end
