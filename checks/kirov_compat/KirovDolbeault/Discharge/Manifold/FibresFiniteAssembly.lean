/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.AnalyticFiberDiscrete
import KirovDolbeault.Discharge.Manifold.AnalyticContinuationGlobalization
import KirovDolbeault.Discharge.Manifold.ChartPullbackDataConstruction
import KirovDolbeault.Discharge.Manifold.ContMDiffOmegaAnalytic
import KirovDolbeault.Discharge.Manifold.Degree

set_option autoImplicit true


/-! # Full assembly: `fibres_finite_statement` modulo a single connectivity hypothesis

This file composes the landed pieces into the maximal unconditional reduction
of `Degree.fibres_finite_statement` available at this pin:

* ZZ20 (`Degree.lean`): `fibres_finite_of_all_fibers_isDiscrete` reduces the
  statement to per-fibre `IsDiscrete`.
* ZZ22 (`AnalyticFiberDiscrete.lean`): `fibres_finite_of_chart_pullback`
  reduces it further to a per-fibre-point `ChartPullbackData`.
* ZZ24 (`ContMDiffOmegaAnalytic.lean`): the bridge
  `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x → AnalyticAt ℂ` on chart pullbacks.
* ZZ25 (`AnalyticContinuationGlobalization.lean`): the within-chart globalisation
  of "not eventually constant" via the identity theorem.
* ZZ28 (`ChartPullbackDataConstruction.lean`):
  `chartPullbackData_of_contMDiff_global` builds `ChartPullbackData` from
  `ContMDiff … ω f` plus a per-fibre-point local non-degeneracy hypothesis.

The composition above is unconditional. The single remaining input is the
**connectivity-globalization** step: from "`f` is not (globally) constant" on a
connected `X`, derive "for every fibre point `x`, the chart pullback of `f`
is not eventually equal to its value at `(chartAt ℂ x) x`". This is the
analytic-continuation argument across charts whose chart-overlap analyticity
is in scope (mathlib at this pin) but whose path-walking has not yet been
formalised in this repository.

The deliverable of this file:

* `ConnectivityGlobalizationHypothesis` — a clean predicate on `X, Y`
  capturing exactly the missing globalisation step.
* `fibres_finite_of_connectivity_hypothesis` — proves
  `fibres_finite_statement X Y` from `ConnectivityGlobalizationHypothesis X Y`,
  unconditionally and by composition of the landed pieces above.

No gaps, no `axiom`. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## Connectivity-globalization hypothesis

The single input that is not unconditionally available at this pin: for every
non-constant `C^ω` map between (connected) complex manifolds, the chart
pullback near every fibre point is not eventually equal to its target
chart-value. Equivalently, "`f` non-constant globally" implies "the chart
pullback of `f` is not eventually constant at any fibre point". -/
def ConnectivityGlobalizationHypothesis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
    ∀ (y₀ : Y), ∀ x : X, f x = y₀ →
      ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
            = (chartAt ℂ (f x)) (f x)

/-! ## Assembly

The proof composes:

1. `chartPullbackData_of_contMDiff_global` (ZZ28) to turn the connectivity
   hypothesis into a `ChartPullbackData` at every fibre point, and
2. `fibres_finite_of_chart_pullback` (ZZ22) to turn per-fibre-point
   `ChartPullbackData` into the full `fibres_finite_statement`.
-/

/-- **Full assembly: `fibres_finite_statement` from the connectivity-
globalization hypothesis.** Given the single remaining input
`ConnectivityGlobalizationHypothesis X Y`, the classical statement
`fibres_finite_statement X Y` holds. The proof is unconditional and proceeds
by composing `chartPullbackData_of_contMDiff_global` with
`fibres_finite_of_chart_pullback`. -/
theorem fibres_finite_of_connectivity_hypothesis
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ConnectivityGlobalizationHypothesis X Y) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
        ∀ y : Y, (f ⁻¹' {y}).Finite := by
  -- Build the per-fibre-point chart-pullback assignment from `H`.
  refine fibres_finite_of_chart_pullback ?_
  intro f hf hnc y x hx
  -- `hx : x ∈ f ⁻¹' {y}`, i.e. `f x = y`.
  have hx_eq : f x = y := hx
  -- Apply ZZ28's globalised constructor; its non-degeneracy parameter is
  -- exactly the conclusion of `H` (after specialising `y₀ := y`).
  have hne : ∀ x' : X, f x' = y →
      ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x') x'),
          ((chartAt ℂ (f x')) ∘ f ∘ (chartAt ℂ x').symm) z
            = (chartAt ℂ (f x')) (f x') := fun x' hx' => H f hf hnc y x' hx'
  exact chartPullbackData_of_contMDiff_global hf hne x hx

/-! ## Discharge restated against `fibres_finite_statement`

We export the assembly as a direct conditional discharge of
`fibres_finite_statement`: under the connectivity hypothesis, the statement
holds. -/

/-- **Conditional discharge.** `fibres_finite_statement X Y` holds whenever the
connectivity-globalization hypothesis holds. Equivalent to
`fibres_finite_of_connectivity_hypothesis` but stated as a one-line
implication for ergonomic downstream use. -/
theorem fibres_finite_statement_holds_of_connectivity
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    ConnectivityGlobalizationHypothesis X Y →
      ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
        ¬ Jacobians.Discharge.IsConstantMap f →
          ∀ y : Y, (f ⁻¹' {y}).Finite :=
  fibres_finite_of_connectivity_hypothesis

end Degree
end ContMDiff
end Jacobians.Discharge
