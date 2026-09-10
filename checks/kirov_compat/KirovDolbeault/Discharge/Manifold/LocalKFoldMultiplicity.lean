/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.LocalMultiplicityInvariance

set_option autoImplicit true


/-! # Local multiplicity invariance — branched (`k ≥ 1`) reduction

This file extends ZZ74's `k = 1` result
(`localMultiplicityOne_preimage_card`, in
`Jacobians.Discharge.Manifold.LocalMultiplicityInvariance`) toward the
**branched** case where the local order at `x₀` is `k ≥ 1`.

## Reduction strategy

If `g : ℂ → ℂ` is analytic at `x₀` with `g x₀ = w₀` and local order `k`,
then on a small disc

  `g(z) - w₀ = (z - x₀) ^ k · u(z)`,

with `u` analytic at `x₀` and `u(x₀) ≠ 0`. Choosing an analytic `k`-th
root branch of `u` on a small disc, set
`v(z) := (z - x₀) · u(z) ^ (1 / k)`. Then

  `g(z) - w₀ = v(z) ^ k`,    `v(x₀) = 0`,    `v'(x₀) ≠ 0`.

So `v` is a local biholomorphism (ZZ74's `k = 1` case applied to `v`).
Solving `g z = w` becomes solving `v(z) ^ k = w - w₀`, with exactly `k`
distinct `k`-th roots for `w ≠ w₀` near `w₀`, each producing one
preimage `z = v.symm w'` via the local inverse of `v`.

## What this file delivers

The packaging of "analytic `k`-th root branch of a non-vanishing analytic
function on a small disc" is **not** routed at the mathlib pin
`8e3c989` (15 April 2026). Per the brief's guidance for blocked content,
we therefore:

1. **State the analytic substitution as a hypothesis bundle**
   (`KthRootSubstitution g x₀ w₀ k`).

2. **Discharge the `k = 1` bundle unconditionally**
   (`kthRootSubstitution_of_localMultiplicityOne`): take
   `v(z) := g(z) - w₀`.

3. **Reduce the bundle's `k = 1` consequence to ZZ74**
   (`localKFoldMultiplicity_preimage_card_of_substitution_one`).

The general-`k` step (passing from `card = 1` for `v(z) = w'` to `card = k`
for `g(z) = w`) requires the analytic `k`-th root packaging mentioned
above — see the named statement
`analytic_kth_root_branch_exists_statement` — and an explicit `k`-th
roots-of-unity enumeration; both are unrouted at this pin.

## Status

* `KthRootSubstitution` — definition. No `axiom`, no gaps.
* `kthRootSubstitution_of_localMultiplicityOne` — `k = 1` bundle is
  unconditional. No gaps.
* `localKFoldMultiplicity_preimage_card_of_substitution_one` — full
  ε–δ count for `k = 1` from the bundle, by deriving `g`-side analyticity
  + nonvanishing-derivative directly from the bundle and re-invoking
  ZZ74 on `g` itself. No gaps.
* `analytic_kth_root_branch_exists_statement` — `Prop`-valued name for
  the missing-mathlib content, the only block on the general `k ≥ 2`
  step. No `axiom`; this is *only* a statement.

-/

noncomputable section

open scoped Topology
open Set Filter Metric

namespace Jacobians.Discharge
namespace Manifold

/-- **Hypothesis bundle for the `k`-th root substitution.**

For `g : ℂ → ℂ` analytic with `g x₀ = w₀` and local order `k` at `x₀`, the
analytic substitution `v` should satisfy, on a small closed disc of
radius `ρ`:

* `v` is analytic on `closedBall x₀ ρ`,
* `v x₀ = 0`,
* `deriv v x₀ ≠ 0`,
* `g z - w₀ = (v z) ^ k` for every `z ∈ closedBall x₀ ρ`.

These four conditions are exactly the data needed to reduce the `k`-fold
preimage-count theorem to ZZ74's `k = 1` case applied to `v`.

For `k = 1` the bundle is constructed unconditionally
(`kthRootSubstitution_of_localMultiplicityOne`). For `k ≥ 2` the
construction requires an analytic `k`-th root branch of the unit factor
`u` in the local form `g - w₀ = (z - x₀)^k · u`, which is the
named-only gap `analytic_kth_root_branch_exists_statement`. -/
structure KthRootSubstitution (g : ℂ → ℂ) (x₀ w₀ : ℂ) (k : ℕ) : Prop where
  exists_substitution :
    ∃ (v : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧
      AnalyticOnNhd ℂ v (Metric.closedBall x₀ ρ) ∧
      v x₀ = 0 ∧
      deriv v x₀ ≠ 0 ∧
      (∀ z ∈ Metric.closedBall x₀ ρ, g z - w₀ = (v z) ^ k)

/-- **Named statement of the missing-mathlib content.**

For `u : ℂ → ℂ` analytic on a closed disc `closedBall x₀ ρ` with
`u x₀ ≠ 0`, there exists an analytic function `r : ℂ → ℂ` on
some smaller closed disc `closedBall x₀ ρ'` (`0 < ρ' ≤ ρ`) with
`r(z) ^ k = u(z)` for all `z ∈ closedBall x₀ ρ'`.

This is the named-only gap blocking the general `k ≥ 2` construction of
`KthRootSubstitution`. The candidate proof routes through
`Complex.log`'s analyticity on `slitPlane` (and the uniform smallness of
`‖u(z) - u(x₀)‖` for `z` in a small disc, which keeps `u(z)` inside a
logarithm branch).

We state this as a `Prop` and *do not* discharge it here. -/
def analytic_kth_root_branch_exists_statement
    (u : ℂ → ℂ) (x₀ : ℂ) (ρ : ℝ) (k : ℕ) : Prop :=
  AnalyticOnNhd ℂ u (Metric.closedBall x₀ ρ) → u x₀ ≠ 0 → 1 ≤ k →
    ∃ (r : ℂ → ℂ) (ρ' : ℝ), 0 < ρ' ∧ ρ' ≤ ρ ∧
      AnalyticOnNhd ℂ r (Metric.closedBall x₀ ρ') ∧
      ∀ z ∈ Metric.closedBall x₀ ρ', (r z) ^ k = u z

/-- **`k = 1` substitution is unconditional.**

For `k = 1`, the substitution is `v(z) := g(z) - w₀`. Hypotheses:
`g` analytic on `closedBall x₀ R`, `g x₀ = w₀`, `deriv g x₀ ≠ 0`. -/
theorem kthRootSubstitution_of_localMultiplicityOne
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (h_an : AnalyticOnNhd ℂ g (Metric.closedBall x₀ R))
    (h_w₀ : g x₀ = w₀) (hd : deriv g x₀ ≠ 0) :
    KthRootSubstitution g x₀ w₀ 1 := by
  refine ⟨⟨fun z => g z - w₀, R, hR, ?_, ?_, ?_, ?_⟩⟩
  · intro z hz
    exact (h_an z hz).sub analyticAt_const
  · simp [h_w₀]
  · have hg_diff : DifferentiableAt ℂ g x₀ :=
      (h_an x₀ (Metric.mem_closedBall_self hR.le)).differentiableAt
    have hconst : DifferentiableAt ℂ (fun _ : ℂ => w₀) x₀ :=
      differentiableAt_const _
    have hderiv :
        deriv (fun z => g z - w₀) x₀ = deriv g x₀ - deriv (fun _ : ℂ => w₀) x₀ :=
      deriv_sub hg_diff hconst
    have hconst_d : deriv (fun _ : ℂ => w₀) x₀ = 0 := deriv_const x₀ w₀
    rw [hderiv, hconst_d, sub_zero]
    exact hd
  · intro z _
    simp

/-- **`k = 1` preimage count from the bundle, unconditionally via ZZ74.**

If the `k = 1` substitution bundle holds for `g` at `x₀, w₀`, and
`g x₀ = w₀`, there exist `ε, δ > 0` such that for every
`w ∈ ball w₀ δ` with `w ≠ w₀`, `{z ∈ ball x₀ ε | g z = w}` has cardinality
exactly `1`.

Proof strategy: from the bundle (with `k = 1`) we have `g z - w₀ = v z`
on `closedBall x₀ ρ`, with `v` analytic there, `v x₀ = 0`,
`deriv v x₀ ≠ 0`. Hence `g z = v z + w₀` near `x₀`, so `g` is analytic
at `x₀` with `deriv g x₀ = deriv v x₀ ≠ 0`. ZZ74 applied to `g`
directly gives the count of 1. -/
theorem localKFoldMultiplicity_preimage_card_of_substitution_one
    {g : ℂ → ℂ} {x₀ w₀ : ℂ}
    (hsub : KthRootSubstitution g x₀ w₀ 1)
    (_h_w₀ : g x₀ = w₀) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = 1 := by
  obtain ⟨v, ρ, hρ_pos, hv_an, hv_x₀, hv_d, hv_pow⟩ := hsub.exists_substitution
  -- Pointwise on closedBall x₀ ρ: g z = v z + w₀.
  have hgv : ∀ z ∈ Metric.closedBall x₀ ρ, g z = v z + w₀ := by
    intro z hz
    have h := hv_pow z hz
    rw [pow_one] at h
    -- h : g z - w₀ = v z, so g z = v z + w₀.
    have : g z = (g z - w₀) + w₀ := by ring
    rw [this, h]
  -- Hence g is analytic at every z ∈ closedBall x₀ ρ; in particular at x₀.
  -- We use the EventuallyEq form: g =ᶠ[𝓝 x₀] (fun z => v z + w₀).
  have h_eventually : g =ᶠ[𝓝 x₀] fun z => v z + w₀ := by
    have hclosed_nhds : Metric.closedBall x₀ ρ ∈ 𝓝 x₀ :=
      Metric.closedBall_mem_nhds x₀ hρ_pos
    filter_upwards [hclosed_nhds] with z hz using hgv z hz
  have hv_at_x₀ : AnalyticAt ℂ v x₀ :=
    hv_an x₀ (Metric.mem_closedBall_self hρ_pos.le)
  have h_g_an : AnalyticAt ℂ g x₀ := by
    have h_sum : AnalyticAt ℂ (fun z => v z + w₀) x₀ :=
      hv_at_x₀.add analyticAt_const
    exact h_sum.congr h_eventually.symm
  -- deriv g x₀ = deriv v x₀.
  have h_dg_eq : deriv g x₀ = deriv v x₀ := by
    have hv_diff : DifferentiableAt ℂ v x₀ := hv_at_x₀.differentiableAt
    have hconst : DifferentiableAt ℂ (fun _ : ℂ => w₀) x₀ :=
      differentiableAt_const _
    have h_sum_d :
        deriv (fun z => v z + w₀) x₀ = deriv v x₀ + deriv (fun _ : ℂ => w₀) x₀ :=
      deriv_add hv_diff hconst
    have hconst_d : deriv (fun _ : ℂ => w₀) x₀ = 0 := deriv_const x₀ w₀
    have : deriv g x₀ = deriv (fun z => v z + w₀) x₀ :=
      Filter.EventuallyEq.deriv_eq h_eventually
    rw [this, h_sum_d, hconst_d, add_zero]
  have h_dg_ne : deriv g x₀ ≠ 0 := h_dg_eq ▸ hv_d
  -- Apply ZZ74 to g at x₀.
  exact localMultiplicityOne_preimage_card h_g_an h_dg_ne

/-- **Closed-ball convenience corollary.**

The brief's signature shape: from analyticity of `g` on `closedBall x₀ R`
plus a `k = 1` substitution bundle (which here is just
`deriv g x₀ ≠ 0`), conclude the `1`-fold preimage count.

This is *exactly* `localMultiplicityOne_preimage_card_on_closedBall`
(ZZ74) re-exported through the bundle, demonstrating the bundle's
non-degeneracy at `k = 1`. -/
theorem localKFoldMultiplicity_preimage_card_one_unconditional
    {g : ℂ → ℂ} {x₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (h_an : AnalyticOnNhd ℂ g (Metric.closedBall x₀ R))
    (hd : deriv g x₀ ≠ 0) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = 1 := by
  have hsub :=
    kthRootSubstitution_of_localMultiplicityOne hR h_an rfl hd
  exact localKFoldMultiplicity_preimage_card_of_substitution_one hsub rfl

end Manifold
end Jacobians.Discharge

end
