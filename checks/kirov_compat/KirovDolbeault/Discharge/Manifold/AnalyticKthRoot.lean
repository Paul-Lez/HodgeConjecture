/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.Constructions
import KirovDolbeault.Discharge.Manifold.LocalKFoldMultiplicity

set_option autoImplicit true


/-! # Analytic `k`-th root branch on a disc around a non-vanishing point.

Let `u : ℂ → ℂ` be analytic on `closedBall x₀ ρ` with `u x₀ ≠ 0`. Set
`c₀ := u x₀`. The function `w(z) := u(z) / c₀` is analytic and
`w x₀ = 1`. By continuity, on a small enough disc `closedBall x₀ ρ'`,
`w(z)` stays inside `Metric.ball (1 : ℂ) (1/2)`, which lies in
`Complex.slitPlane`. On `slitPlane`, `Complex.log` is analytic. Define

  `r(z) := Complex.exp ((Complex.log c₀) / k)
            * Complex.exp ((Complex.log (w z)) / k)`.

Then `r(z) ^ k = c₀ * w(z) = u(z)`.
-/

namespace Jacobians.Discharge
namespace Manifold

open Complex Metric

/-- Points in `Metric.ball (1 : ℂ) (1/2)` lie in `Complex.slitPlane`. -/
lemma slitPlane_of_mem_ball_one {z : ℂ} (hz : z ∈ Metric.ball (1 : ℂ) (1/2)) :
    z ∈ Complex.slitPlane := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h_re : |z.re - 1| ≤ ‖z - 1‖ := by
    have := Complex.abs_re_le_norm (z - 1)
    simpa [Complex.sub_re] using this
  have h_re_lt : |z.re - 1| < 1/2 := lt_of_le_of_lt h_re hz
  have hpos : 0 < z.re := by
    have habs := abs_lt.mp h_re_lt
    linarith [habs.1]
  exact Or.inl hpos

/-- **Analytic `k`-th root branch on a disc.** -/
theorem analytic_kth_root_of_nonvanishing
    {u : ℂ → ℂ} {x₀ : ℂ} {ρ : ℝ} {k : ℕ}
    (hρ : 0 < ρ)
    (hu : AnalyticOnNhd ℂ u (Metric.closedBall x₀ ρ))
    (hux₀ : u x₀ ≠ 0) (hk : 1 ≤ k) :
    ∃ (r : ℂ → ℂ) (ρ' : ℝ), 0 < ρ' ∧ ρ' ≤ ρ ∧
      AnalyticOnNhd ℂ r (Metric.closedBall x₀ ρ') ∧
      ∀ z ∈ Metric.closedBall x₀ ρ', (r z) ^ k = u z := by
  set c₀ : ℂ := u x₀ with hc₀_def
  have hc₀_ne : c₀ ≠ 0 := hux₀
  have hu_x₀ : AnalyticAt ℂ u x₀ := hu x₀ (Metric.mem_closedBall_self hρ.le)
  have hu_cont : ContinuousAt u x₀ := hu_x₀.continuousAt
  have hw_cont : ContinuousAt (fun z => u z / c₀) x₀ := hu_cont.div_const c₀
  have hw_x₀ : (fun z => u z / c₀) x₀ = 1 := by
    show u x₀ / c₀ = 1
    rw [← hc₀_def]; exact div_self hc₀_ne
  -- preimage of `ball 1 (1/2)` under `w` is a neighborhood of `x₀`.
  have hball_open : IsOpen (Metric.ball (1 : ℂ) (1/2)) := Metric.isOpen_ball
  have h_one_mem : (1 : ℂ) ∈ Metric.ball (1 : ℂ) (1/2) := by
    rw [Metric.mem_ball]; simp
  have h_w_mem : (fun z => u z / c₀) x₀ ∈ Metric.ball (1 : ℂ) (1/2) := by
    rw [hw_x₀]; exact h_one_mem
  have h_pre :
      ∀ᶠ z in nhds x₀, (fun z => u z / c₀) z ∈ Metric.ball (1 : ℂ) (1/2) :=
    hw_cont.eventually_mem (hball_open.mem_nhds h_w_mem)
  rw [Metric.eventually_nhds_iff] at h_pre
  obtain ⟨ε, hε_pos, hε⟩ := h_pre
  set ρ' : ℝ := min (ρ/2) (ε/2) with hρ'_def
  have hρ'_pos : 0 < ρ' := lt_min (by linarith) (by linarith)
  have hρ'_le : ρ' ≤ ρ := le_trans (min_le_left _ _) (by linarith)
  have hρ'_lt_ε : ρ' < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hz_in_ε : ∀ z ∈ Metric.closedBall x₀ ρ',
      u z / c₀ ∈ Metric.ball (1 : ℂ) (1/2) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    have hdist : dist z x₀ < ε := lt_of_le_of_lt hz hρ'_lt_ε
    exact hε hdist
  have hsubset : Metric.closedBall x₀ ρ' ⊆ Metric.closedBall x₀ ρ :=
    Metric.closedBall_subset_closedBall hρ'_le
  -- the analytic k-th root
  refine ⟨fun z => Complex.exp ((Complex.log c₀) / k)
          * Complex.exp ((Complex.log (u z / c₀)) / k), ρ', hρ'_pos, hρ'_le, ?_, ?_⟩
  · -- analyticity
    intro z hz
    have hwz : u z / c₀ ∈ Complex.slitPlane :=
      slitPlane_of_mem_ball_one (hz_in_ε z hz)
    have hu_an : AnalyticAt ℂ u z := hu z (hsubset hz)
    have hw_an : AnalyticAt ℂ (fun ζ => u ζ / c₀) z := hu_an.div_const
    have hlog_an : AnalyticAt ℂ (fun ζ => Complex.log (u ζ / c₀)) z :=
      hw_an.clog hwz
    have hdiv_an : AnalyticAt ℂ (fun ζ => Complex.log (u ζ / c₀) / k) z :=
      hlog_an.div_const
    have hexp_an : AnalyticAt ℂ
        (fun ζ => Complex.exp (Complex.log (u ζ / c₀) / k)) z :=
      hdiv_an.cexp'
    exact analyticAt_const.mul hexp_an
  · -- pointwise equation
    intro z hz
    have hwz : u z / c₀ ∈ Complex.slitPlane :=
      slitPlane_of_mem_ball_one (hz_in_ε z hz)
    have hwz_ne : u z / c₀ ≠ 0 := Complex.slitPlane_ne_zero hwz
    have hk_ne : (k : ℂ) ≠ 0 := by
      have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
      exact_mod_cast hk0
    -- (exp (a/k))^k = exp a
    have key : ∀ a : ℂ, (Complex.exp (a / k)) ^ k = Complex.exp a := by
      intro a
      rw [← Complex.exp_nat_mul]
      congr 1
      field_simp
    show (Complex.exp ((Complex.log c₀) / k)
           * Complex.exp ((Complex.log (u z / c₀)) / k)) ^ k = u z
    rw [mul_pow, key, key, Complex.exp_log hc₀_ne, Complex.exp_log hwz_ne]
    -- c₀ * (u z / c₀) = u z
    field_simp

/-- **Discharge of the named gap** from `LocalKFoldMultiplicity`. -/
theorem analytic_kth_root_branch_exists
    (u : ℂ → ℂ) (x₀ : ℂ) (ρ : ℝ) (k : ℕ) (hρ : 0 < ρ) :
    analytic_kth_root_branch_exists_statement u x₀ ρ k := by
  intro hu hux₀ hk
  exact analytic_kth_root_of_nonvanishing hρ hu hux₀ hk

end Manifold
end Jacobians.Discharge
