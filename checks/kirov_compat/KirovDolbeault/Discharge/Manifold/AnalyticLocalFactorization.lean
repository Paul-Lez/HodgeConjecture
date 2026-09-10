/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option autoImplicit true


/-! # Local analytic factorization at a zero of finite order (ZZ90)

Discharge of the local-factorization hypothesis consumed by ZZ89
(`LocalKFoldMultiplicityUnconditional`):

> if `g : ℂ → ℂ` is analytic at `x₀`, `g x₀ = w₀`, and `g - w₀` has
> `analyticOrderAt` equal to a natural number `k ≥ 1` at `x₀`, then on
> some `closedBall x₀ R` with `R > 0` there is an analytic function
> `u : ℂ → ℂ` with `u x₀ ≠ 0` and `g z - w₀ = (z - x₀) ^ k * u z` for
> every `z ∈ closedBall x₀ R`.

The proof uses mathlib's `AnalyticAt.analyticOrderAt_eq_natCast` to
extract a local non-vanishing analytic factor `u₀` defined eventually
near `x₀`, upgrades the eventually-equal statement to an open-ball one
via `Metric.eventually_nhds_iff`, then uses
`AnalyticAt.exists_ball_analyticOnNhd` together with
`ContinuousAt.eventually_ne` (continuity of `u₀` from its analyticity)
to find a strictly smaller closed ball on which both the factorisation
and `u x₀ ≠ 0` properties survive. The final `u` is taken to be `u₀`
itself; positivity of the radius is the minimum of the three disk
witnesses, halved.

## Anti-cheat

* No `axiom`, no gaps. Only mathlib lemmas plus algebra.
* No signature of any pre-existing definition or theorem is changed.
* The output exactly matches the hypothesis shape consumed by ZZ89:
  `AnalyticOnNhd ℂ u (closedBall x₀ R)`, `u x₀ ≠ 0`, and the pointwise
  identity on `closedBall x₀ R`.
-/

noncomputable section

open scoped Topology
open Set Filter Metric

namespace Jacobians.Discharge
namespace Manifold

/-- **Local analytic factorization at a zero of finite order.**

If `g` is analytic at `x₀` with `g x₀ = w₀` and the analytic order of
`g - w₀` at `x₀` equals `k ∈ ℕ` with `k ≥ 1`, then on a closed disk
`closedBall x₀ R` (`R > 0`) there is a non-vanishing analytic factor
`u` realising `g z - w₀ = (z - x₀) ^ k * u z`. -/
theorem analytic_local_factorization
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ}
    (_hk : 1 ≤ k)
    (hg : AnalyticAt ℂ g x₀)
    (_h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞)) :
    ∃ R : ℝ, 0 < R ∧ ∃ u : ℂ → ℂ,
      AnalyticOnNhd ℂ u (Metric.closedBall x₀ R) ∧ u x₀ ≠ 0 ∧
        ∀ z ∈ Metric.closedBall x₀ R, g z - w₀ = (z - x₀) ^ k * u z := by
  classical
  -- Step 1. `f := g - w₀` is analytic at `x₀`.
  set f : ℂ → ℂ := fun z => g z - w₀ with hf_def
  have hf_an : AnalyticAt ℂ f x₀ :=
    hg.sub (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => w₀) x₀)
  -- Mathlib characterisation: a positive-natural analytic order means a
  -- local non-vanishing factor exists eventually near `x₀`.
  obtain ⟨u₀, hu₀_an, hu₀_x₀, hu₀_eq⟩ :=
    hf_an.analyticOrderAt_eq_natCast.mp hord
  -- Step 2. Extract a positive radius `r₁` on which `u₀` is analytic.
  obtain ⟨r₁, hr₁_pos, hu₀_anOn⟩ := hu₀_an.exists_ball_analyticOnNhd
  -- Step 3. Convert the eventually-equal statement to a metric ball.
  rw [Metric.eventually_nhds_iff] at hu₀_eq
  obtain ⟨r₂, hr₂_pos, hu₀_eq_ball⟩ := hu₀_eq
  -- Step 4. Use continuity (analytic ⇒ continuous) to keep `u₀ z ≠ 0` on a small ball.
  have hu₀_cont : ContinuousAt u₀ x₀ := hu₀_an.continuousAt
  have hu₀_ev_ne : ∀ᶠ z in 𝓝 x₀, u₀ z ≠ 0 :=
    hu₀_cont.eventually_ne hu₀_x₀
  rw [Metric.eventually_nhds_iff] at hu₀_ev_ne
  obtain ⟨r₃, hr₃_pos, _hu₀_ne_ball⟩ := hu₀_ev_ne
  -- Step 5. Choose `R` = (min of the three radii) / 2 so that `closedBall x₀ R`
  -- sits strictly inside each open ball.
  set r : ℝ := min r₁ (min r₂ r₃) with hr_def
  have hr_pos : 0 < r := lt_min hr₁_pos (lt_min hr₂_pos hr₃_pos)
  refine ⟨r / 2, by linarith, u₀, ?_, hu₀_x₀, ?_⟩
  · -- `AnalyticOnNhd ℂ u₀ (closedBall x₀ (r/2))`.
    intro z hz
    rw [Metric.mem_closedBall] at hz
    have hz_ball : z ∈ Metric.ball x₀ r₁ := by
      rw [Metric.mem_ball]
      have hle : r ≤ r₁ := min_le_left _ _
      linarith
    exact hu₀_anOn z hz_ball
  · -- The factorisation on `closedBall x₀ (r/2)`.
    intro z hz
    rw [Metric.mem_closedBall] at hz
    have hz_in_r₂ : dist z x₀ < r₂ := by
      have : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    -- `hu₀_eq_ball : ∀ z, dist z x₀ < r₂ → f z = (z - x₀) ^ k • u₀ z`.
    have h_eq : f z = (z - x₀) ^ k • u₀ z := hu₀_eq_ball hz_in_r₂
    -- In ℂ, `•` and `*` agree.
    have h_mul : f z = (z - x₀) ^ k * u₀ z := by simpa [smul_eq_mul] using h_eq
    -- Unfold `f` to get `g z - w₀ = (z - x₀)^k * u₀ z`.
    simpa [hf_def] using h_mul

end Manifold
end Jacobians.Discharge

end
