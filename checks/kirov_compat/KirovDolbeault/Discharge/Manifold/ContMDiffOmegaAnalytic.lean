/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit true


/-! # Bridge `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` to `AnalyticAt ℂ` on chart pullbacks

This file supplies the missing classical input flagged by ZZ22 in
`AnalyticFiberDiscrete.lean`: for `f : X → Y` with `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x`,
the chart-pulled-back representative
`(chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm` is `AnalyticAt ℂ` at the chart
image `(chartAt ℂ x) x`.

The proof is a routine chain through mathlib lemmas:

* `contMDiffAt_iff` rewrites manifold smoothness as
  `ContDiffWithinAt ℂ ω (extChartAt-pullback) (range 𝓘(ℂ)) (extChartAt 𝓘(ℂ) x x)`,
* `ModelWithCorners.range_eq_univ` (boundaryless) gives `range 𝓘(ℂ) = univ`,
* `contDiffWithinAt_univ` collapses to `ContDiffAt`,
* `ContDiffAt.analyticAt` (mathlib `Analysis/Calculus/ContDiff/Defs.lean:953`)
  is `C^ω → AnalyticAt`,
* `extChartAt 𝓘(𝕜, E) x` coincides with `chartAt _ x` as a function (since
  `𝓘(ℂ)` has identity coordinate map).

No gaps, no `axiom`. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## The bridge -/

/-- **Bridge `ContMDiffAt … ω → AnalyticAt ℂ` on chart pullbacks.**
For `f : X → Y` real-analytic at `x` between complex-analytic manifolds
modelled on `ℂ` (with corners model `𝓘(ℂ)`), the chart-pulled-back
representation
`(chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm`
is `AnalyticAt ℂ` at the chart image `(chartAt ℂ x) x`.

This is the missing classical hypothesis flagged in
`AnalyticFiberDiscrete.lean`. -/
theorem contMDiffAt_omega_analyticAt_chart_pullback
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} {x : X}
    (h : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) :
    AnalyticAt ℂ ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) := by
  -- Step 1: unfold `contMDiffAt_iff` to get a `ContDiffWithinAt` statement on
  -- the `extChartAt`-pullback at the basepoint.
  have h1 := (contMDiffAt_iff (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (f := f) (x := x) (n := ω)).mp h
  obtain ⟨_hcont, hCD⟩ := h1
  -- `hCD : ContDiffWithinAt ℂ ω
  --   (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm)
  --   (range 𝓘(ℂ)) (extChartAt 𝓘(ℂ) x x)`
  -- Step 2: `range 𝓘(ℂ) = univ` (boundaryless model with corners).
  have hrange : range (𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) = univ :=
    ModelWithCorners.Boundaryless.range_eq_univ
  rw [hrange, contDiffWithinAt_univ] at hCD
  -- Step 3: `C^ω` ⇒ `AnalyticAt ℂ`.
  have hA : AnalyticAt ℂ
      (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm)
      (extChartAt 𝓘(ℂ) x x) := hCD.analyticAt
  -- Step 4: `extChartAt 𝓘(𝕜, E) ·` coincides with `chartAt _ ·` as a function.
  -- We use `extChartAt_coe` and `extChartAt_coe_symm`, plus
  -- `modelWithCornersSelf_coe = id`. The simp set `mfld_simps` already collapses
  -- this, but we do the rewrite by hand to keep the elaboration cost down.
  -- The function `extChartAt 𝓘(ℂ) y` is definitionally `𝓘(ℂ) ∘ chartAt ℂ y`,
  -- and `𝓘(ℂ) = id` on `ℂ`; similarly the symm side.
  -- So pointwise equality of the composites holds. We finish by rewriting
  -- `hA` to the desired form.
  -- We prove pointwise equality of the composite functions and of the basepoint.
  have hbase : extChartAt 𝓘(ℂ) x x = (chartAt ℂ x) x := by
    simp
  have hfun : (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm)
      = ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) := by
    funext z
    simp
  rw [hfun, hbase] at hA
  exact hA

/-- **`ContMDiff` version.** If `f` is `C^ω` everywhere, then for every `x`
the chart pullback is `AnalyticAt`. -/
theorem contMDiff_omega_analyticAt_chart_pullback
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x : X) :
    AnalyticAt ℂ ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) :=
  contMDiffAt_omega_analyticAt_chart_pullback (hf x)

end Degree
end ContMDiff
end Jacobians.Discharge
