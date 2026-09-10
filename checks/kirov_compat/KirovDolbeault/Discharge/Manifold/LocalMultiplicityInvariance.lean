/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.LocalNormalForm
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.OpenPartialHomeomorph.Defs

set_option autoImplicit true


/-! # Local multiplicity invariance — the `k = 1` (biholomorphic) case

This file proves the **`k = 1` slice** of the topological local-multiplicity
theorem (the "branched holomorphic degree" combinatorial fact):

> Let `g : ℂ → ℂ` be analytic at `x₀ : ℂ` with `g(x₀) = w₀` and
> `deriv g x₀ ≠ 0` (i.e. local multiplicity exactly `1`). Then there exist
> `ε > 0` and `δ > 0` such that for every `w ∈ ball w₀ δ` with `w ≠ w₀`,
> the equation `g z = w` has *exactly one* solution in `ball x₀ ε`.

In the language of branched-cover degree theory, this is the statement that
near a regular point (one with non-vanishing derivative), the analytic map
`g` is locally a homeomorphism onto an open set, so each value near `w₀` has
exactly one preimage in the chosen neighborhood.

## Status

* **`k = 1` proof**: complete, no gaps, no `axiom`. Routes through the
  **inverse function theorem** (`HasStrictFDerivAt.toOpenPartialHomeomorph`).
* **`k ≥ 2`**: not in this file. The general case requires the argument
  principle / Rouché theorem, which is not packaged at the mathlib pin
  `8e3c989` (15 April 2026); see the discussion in
  `Jacobians.Discharge.Manifold.LocalNormalForm` (the `Prop`-valued statement
  `localMultiplicity_eq_order_punctured_statement`, the
  `argumentPrinciple_disk_statement` named gap, and the trivial `k = 0`
  theorem `argumentPrinciple_disk_zero_case` that *is* discharged).

## Why a separate file

The companion file `LocalNormalForm.lean` already proves *injectivity* of
`g` on a neighborhood of a regular point
(`MMeromorphicAt.localMultiplicity_one_locally_injective`). The contribution
here is to upgrade that injectivity statement to the **explicit ε–δ
preimage-count form** used in the brief: for every value `w` close to (but
not equal to) `w₀`, the preimage set in a *specified* `ball x₀ ε` has
*exactly one* element.

## Main result

* `localMultiplicityOne_preimage_card`: the headline ε–δ count for `k = 1`.

## Proof sketch

1. Lift `AnalyticAt` to `HasStrictDerivAt` (via
   `AnalyticAt.hasStrictDerivAt`).
2. With non-vanishing derivative, repackage as `HasStrictFDerivAt` with a
   `ContinuousLinearEquiv` derivative
   (`HasStrictDerivAt.hasStrictFDerivAt_equiv`).
3. The inverse function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`)
   yields an `OpenPartialHomeomorph φ` realising `g` as a homeomorphism from
   an open neighborhood of `x₀` onto an open neighborhood of `w₀`.
4. Pick `ε > 0` small enough that `ball x₀ ε ⊆ φ.source`
   (`IsOpen.mem_nhds` on the source).
5. Pick `δ > 0` small enough that `ball w₀ δ ⊆ φ.target` *and*
   `φ.symm '' (ball w₀ δ) ⊆ ball x₀ ε` (via continuity of `φ.symm` at `w₀`).
6. For `w ∈ ball w₀ δ \ {w₀}`, the unique solution to `g z = w` in
   `φ.source` is `φ.symm w ∈ ball x₀ ε`, and by `φ.injOn` no other
   `z ∈ φ.source` solves it; in particular no other `z ∈ ball x₀ ε ⊆ φ.source`
   does. Therefore the preimage has cardinality exactly `1`.
-/

noncomputable section

open scoped Topology
open Set Filter Metric

namespace Jacobians.Discharge
namespace Manifold

/-- **Local multiplicity invariance, `k = 1` case.**

For `g : ℂ → ℂ` analytic at `x₀` with `deriv g x₀ ≠ 0`, there exist
`ε, δ > 0` such that for every `w` in `ball (g x₀) δ` with `w ≠ g x₀`, the
preimage set `{z ∈ ball x₀ ε | g z = w}` has exactly one element.

This is the order-`1` slice of the general "preimage count = local
multiplicity" theorem: when the local multiplicity is `1`, each nearby
value has a single preimage.

The proof routes through the inverse function theorem packaged as an
`OpenPartialHomeomorph` (`HasStrictFDerivAt.toOpenPartialHomeomorph`). -/
theorem localMultiplicityOne_preimage_card
    {g : ℂ → ℂ} {x₀ : ℂ}
    (h_an : AnalyticAt ℂ g x₀) (hd : deriv g x₀ ≠ 0) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = 1 := by
  -- Step 1: AnalyticAt ⟹ HasStrictDerivAt.
  have hsd : HasStrictDerivAt g (deriv g x₀) x₀ := h_an.hasStrictDerivAt
  -- Step 2: Repackage as HasStrictFDerivAt with a CLE derivative.
  have hsfd :
      HasStrictFDerivAt g
        (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv g x₀) hd) :
          ℂ →L[ℂ] ℂ) x₀ :=
    hsd.hasStrictFDerivAt_equiv hd
  -- Step 3: The inverse function theorem yields an OpenPartialHomeomorph φ for g.
  set φ : OpenPartialHomeomorph ℂ ℂ := hsfd.toOpenPartialHomeomorph g with hφ
  have h_x0_src : x₀ ∈ φ.source := hsfd.mem_toOpenPartialHomeomorph_source
  have h_w0_tgt : g x₀ ∈ φ.target := hsfd.image_mem_toOpenPartialHomeomorph_target
  have h_coe : (φ : ℂ → ℂ) = g := hsfd.toOpenPartialHomeomorph_coe
  -- Step 4: Pick ε > 0 with ball x₀ ε ⊆ φ.source.
  have h_src_nhds : φ.source ∈ 𝓝 x₀ := φ.open_source.mem_nhds h_x0_src
  obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.mem_nhds_iff.mp h_src_nhds
  -- Step 5: Pick δ > 0 with ball (g x₀) δ ⊆ φ.target ∩ φ.symm ⁻¹' ball x₀ ε.
  -- 5a. φ.symm is continuous at g x₀.
  have h_symm_cont : ContinuousAt φ.symm (g x₀) :=
    (φ.continuousOn_symm).continuousAt (φ.open_target.mem_nhds h_w0_tgt)
  -- 5b. φ.symm (g x₀) = x₀.
  have h_symm_w0 : φ.symm (g x₀) = x₀ := by
    have := φ.left_inv h_x0_src
    -- φ.symm (φ x₀) = x₀; rewrite φ x₀ to g x₀ via h_coe.
    have hφx₀ : (φ : ℂ → ℂ) x₀ = g x₀ := by rw [h_coe]
    rw [hφx₀] at this
    exact this
  -- 5c. Hence φ.symm tends to x₀ at g x₀; ball x₀ ε is a neighborhood of x₀.
  have h_ball_x0_nhds : Metric.ball x₀ ε ∈ 𝓝 x₀ :=
    Metric.ball_mem_nhds x₀ hε_pos
  have h_preimage_nhds : φ.symm ⁻¹' (Metric.ball x₀ ε) ∈ 𝓝 (g x₀) := by
    have := h_symm_cont.tendsto
    rw [h_symm_w0] at this
    exact this h_ball_x0_nhds
  -- 5d. Combine: target neighborhood ∩ preimage of ball x₀ ε is in 𝓝 (g x₀).
  have h_combo_nhds :
      φ.target ∩ φ.symm ⁻¹' (Metric.ball x₀ ε) ∈ 𝓝 (g x₀) :=
    Filter.inter_mem (φ.open_target.mem_nhds h_w0_tgt) h_preimage_nhds
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhds_iff.mp h_combo_nhds
  -- Step 6: Assemble the count.
  refine ⟨ε, hε_pos, δ, hδ_pos, ?_⟩
  intro w hw_ball hw_ne
  -- For w in ball (g x₀) δ: w ∈ φ.target, and φ.symm w ∈ ball x₀ ε.
  have hw_target : w ∈ φ.target := (hδ_sub hw_ball).1
  have hw_pre_in_ball : φ.symm w ∈ Metric.ball x₀ ε := (hδ_sub hw_ball).2
  -- φ.symm w ∈ φ.source.
  have h_symm_w_src : φ.symm w ∈ φ.source := φ.map_target hw_target
  -- g (φ.symm w) = w.
  have h_g_symm : g (φ.symm w) = w := by
    have hr : (φ : ℂ → ℂ) (φ.symm w) = w := φ.right_inv hw_target
    rw [h_coe] at hr
    exact hr
  -- The preimage set equals {φ.symm w}, by injectivity.
  have h_preimage_eq :
      {z ∈ Metric.ball x₀ ε | g z = w} = {φ.symm w} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨hw_pre_in_ball, h_g_symm⟩, ?_⟩
    intro z hz
    obtain ⟨hz_ball, hz_g⟩ := hz
    -- z ∈ ball x₀ ε ⊆ φ.source
    have hz_src : z ∈ φ.source := hε_sub hz_ball
    -- φ z = g z = w via h_coe.
    have hφz : (φ : ℂ → ℂ) z = w := by rw [h_coe]; exact hz_g
    -- φ (φ.symm w) = w since w ∈ φ.target.
    have hφ_symm_w : (φ : ℂ → ℂ) (φ.symm w) = w := by
      rw [h_coe]; exact h_g_symm
    -- Apply injectivity on φ.source.
    exact φ.injOn hz_src h_symm_w_src (hφz.trans hφ_symm_w.symm)
  rw [h_preimage_eq]
  exact Set.ncard_singleton _

/-- **Variant with `closedBall x₀ R` analyticity hypothesis.**

This is the `k = 1` form of the brief's stated theorem (which gives an
analyticity hypothesis on a closed ball of radius `R`). It follows from
`localMultiplicityOne_preimage_card` because `AnalyticOnNhd ℂ g
(closedBall x₀ R)` implies `AnalyticAt ℂ g x₀` (when `0 < R`, so `x₀` lies in
the closed ball).

The hypothesis "`g(z) ≠ w₀` for `z ∈ closedBall x₀ R \ {x₀}`" from the brief
is the *isolation-of-the-w₀-fiber* condition, which is automatic at `k = 1`
(local injectivity from non-vanishing derivative); we therefore do not need
it as a separate hypothesis here. The general `k ≥ 2` version (not in this
file) does require either the isolation hypothesis or the order-from-below
hypothesis. -/
theorem localMultiplicityOne_preimage_card_on_closedBall
    {g : ℂ → ℂ} {x₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (h_an : AnalyticOnNhd ℂ g (Metric.closedBall x₀ R))
    (hd : deriv g x₀ ≠ 0) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = 1 := by
  have hx0 : x₀ ∈ Metric.closedBall x₀ R := Metric.mem_closedBall_self hR.le
  exact localMultiplicityOne_preimage_card (h_an x₀ hx0) hd

end Manifold
end Jacobians.Discharge

end
