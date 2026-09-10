/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.LocalKFoldMultiplicityUnconditional
import KirovDolbeault.Discharge.Manifold.AnalyticLocalFactorization

set_option autoImplicit true


/-! # Fully unconditional planar k-fold local multiplicity (ZZ92)

Composition of ZZ89 (`localKFoldMultiplicity_preimage_card_unconditional`,
which still required a local analytic factorization
`g z - w₀ = (z - x₀)^k * u z` with `u x₀ ≠ 0` as a hypothesis) with ZZ90
(`analytic_local_factorization`, which discharges that factorization
hypothesis directly from `AnalyticAt ℂ g x₀` plus
`analyticOrderAt (g - w₀) x₀ = k`).

The result is a fully unconditional statement: from `AnalyticAt ℂ g x₀`,
`g x₀ = w₀`, and `analyticOrderAt (g - w₀) x₀ = k` with `k ≥ 1`, there
exist radii `ε, δ > 0` such that for every `w ∈ ball w₀ δ \ {w₀}` the
equation `g z = w` has exactly `k` solutions in `ball x₀ ε`.

## Anti-cheat

* No `axiom`, no gaps.
* No signature changes outside this new file.
* No bundle hypotheses: only `AnalyticAt`, the value condition, and the
  `analyticOrderAt = k` order condition.
-/

noncomputable section

open scoped Topology
open Set Filter Metric

namespace Jacobians.Discharge
namespace Manifold

/-- **Fully unconditional planar k-fold local multiplicity.**

For analytic `g : ℂ → ℂ` at `x₀` with `g x₀ = w₀`, if the local analytic
order of `g - w₀` at `x₀` equals `k ∈ ℕ` with `k ≥ 1`, then there exist
`ε, δ > 0` such that for every `w` in the punctured disk
`ball w₀ δ \ {w₀}` the equation `g z = w` has exactly `k` solutions in
`ball x₀ ε`. -/
theorem localKFoldMultiplicity_preimage_card_fully_unconditional
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ}
    (hk : 1 ≤ k)
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞)) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = k := by
  -- Discharge the factorization hypothesis via ZZ90.
  obtain ⟨R, hR_pos, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization hk hg h_w₀ hord
  -- Apply ZZ89 with the now-supplied factorization.
  exact localKFoldMultiplicity_preimage_card_unconditional
    hR_pos hk hu_an hu_x₀ h_w₀ hfact

end Manifold
end Jacobians.Discharge

end
