/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic

/-! # Analytic derivative-order facts (planar, sphere-free)

A small ℂ-analytic fact used by the critical-set finiteness argument: a
non-locally-constant analytic function has a non-eventually-vanishing
derivative. Pure planar complex analysis — no Riemann-sphere / divisor
machinery. Relocated here so the map-level critical-set finiteness does not
depend on the meromorphic-function-to-sphere framing. -/

open Filter Topology

namespace Jacobians.Discharge.Manifold

/-- **Non-locally-constant ⇒ derivative not eventually zero.** If `F : ℂ → ℂ`
is analytic at `z₀` and `F` is not eventually equal to `F z₀` on any
neighbourhood of `z₀`, then `deriv F` is not eventually zero on any
neighbourhood of `z₀`.

Reads off `AnalyticAt.analyticOrderAt_deriv_add_one`:
`analyticOrderAt (deriv F) z₀ + 1 = analyticOrderAt (F · - F z₀) z₀`. The
hypothesis forces the right-hand side ≠ ⊤ (else `F = F z₀` on a neighbourhood),
hence the left-hand side ≠ ⊤, i.e. `deriv F` is not eventually 0. -/
lemma deriv_not_eventually_zero_of_analyticAt_not_eventually_const
    {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F z₀)
    (hne : ¬ ∀ᶠ z in 𝓝 z₀, F z = F z₀) :
    ¬ ∀ᶠ z in 𝓝 z₀, deriv F z = 0 := by
  -- Suppose `deriv F` is eventually 0; derive `F` eventually `F z₀`,
  -- contradicting `hne`.
  intro h_dz
  -- `analyticOrderAt (deriv F) z₀ = ⊤` from `analyticOrderAt_eq_top`.
  have h_dz_top : analyticOrderAt (deriv F) z₀ = ⊤ :=
    analyticOrderAt_eq_top.mpr h_dz
  -- The mathlib lemma: order(deriv F) + 1 = order(F - F z₀).
  have h_eq : analyticOrderAt (deriv F) z₀ + 1 =
      analyticOrderAt (fun z => F z - F z₀) z₀ :=
    hF.analyticOrderAt_deriv_add_one
  -- So `order(F - F z₀) = ⊤ + 1 = ⊤`.
  have h_F_top : analyticOrderAt (fun z => F z - F z₀) z₀ = ⊤ := by
    rw [h_dz_top] at h_eq
    -- ⊤ + 1 = ⊤ in ℕ∞.
    simpa using h_eq.symm
  -- That means `F z = F z₀` eventually near `z₀`.
  have h_F_eq : ∀ᶠ z in 𝓝 z₀, F z - F z₀ = 0 :=
    analyticOrderAt_eq_top.mp h_F_top
  apply hne
  filter_upwards [h_F_eq] with z hz
  exact sub_eq_zero.mp hz

end Jacobians.Discharge.Manifold
