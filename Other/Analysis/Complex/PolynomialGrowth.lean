/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Entire functions of polynomial growth

Cauchy's estimates force Taylor coefficients above the growth degree to vanish.
Consequently an entire function with a global polynomial growth bound is a polynomial.
-/

public section

open Filter Metric Polynomial
open scoped Topology

namespace Complex

/-- Derivatives above the degree of a polynomial growth bound vanish at the origin. -/
theorem iteratedDeriv_zero_of_polynomial_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C) {N n : ℕ}
    (hgrowth : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N) (hn : N < n) :
    iteratedDeriv n f 0 = 0 := by
  apply norm_le_zero_iff.mp
  have hlim : Tendsto (fun R : ℝ => (n.factorial * C * 2 ^ N) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hRpos : 0 < R := by positivity
  calc
    ‖iteratedDeriv n f 0‖ ≤ n.factorial * (C * (1 + R) ^ N) / R ^ n :=
      norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hRpos hf.diffContOnCl
        (fun z hz => by simpa only [mem_sphere_zero_iff_norm.mp hz] using hgrowth z)
    _ ≤ n.factorial * (C * (2 * R) ^ N) / R ^ (N + 1) := by
      apply div_le_div₀ (by positivity)
      · gcongr
        linarith
      · positivity
      · exact pow_le_pow_right₀ hR hn
    _ = (n.factorial * C * 2 ^ N) / R := by
      rw [mul_pow, pow_succ]
      field_simp

/-- An entire complex function with growth of degree at most `N` is a polynomial
of degree at most `N`. -/
theorem exists_polynomial_of_polynomial_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ p : ℂ[X], p.natDegree ≤ N ∧ ∀ z, p.eval z = f z := by
  let p : ℂ[X] := ∑ n ∈ Finset.range (N + 1),
    monomial n ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0)
  refine ⟨p, ?_, ?_⟩
  · apply natDegree_sum_le_of_forall_le
    intro n hn
    exact (natDegree_monomial_le _).trans (by simpa using Finset.mem_range.mp hn)
  · intro z
    have htail (n : ℕ) (hn : n ∉ Finset.range (N + 1)) :
        (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * (z - 0) ^ n = 0 := by
      rw [iteratedDeriv_zero_of_polynomial_growth hf hC hgrowth (by simpa using hn)]
      simp
    rw [← taylorSeries_eq_of_entire' 0 z hf, tsum_eq_sum htail]
    simp [p, eval_finsetSum, eval_monomial]

end Complex
