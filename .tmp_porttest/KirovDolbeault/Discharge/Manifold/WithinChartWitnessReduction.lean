/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.ConnectivityGlobalizationReduction
import KirovDolbeault.Discharge.Manifold.ContMDiffOmegaAnalytic

set_option autoImplicit true


/-! # Reducing `WithinChartWitnessHypothesis` to a per-chart non-constancy hypothesis

`ConnectivityGlobalizationReduction.lean` (ZZ32) reduced
`ConnectivityGlobalizationHypothesis X Y` to
`WithinChartWitnessHypothesis X Y`. That hypothesis is *existential* on a
preconnected open `U ⊆ ℂ` plus a witness point `z₁`, and packages the
analyticity of the chart pullback on `U` in addition to a value-difference
witness.

This file isolates the genuinely classical content into a strictly smaller,
strictly different-shaped hypothesis: **per-chart non-constancy in every
neighborhood**. Concretely:

* For every non-constant `C^ω` map `f : X → Y` and every fibre point `x` of
  `y₀`, in every neighborhood of the chart image `(chartAt ℂ x) x`, the chart
  pullback takes a value other than the chart image of `f x`.

The analyticity half of the within-chart witness is now supplied
unconditionally via ZZ24 (`contMDiff_omega_analyticAt_chart_pullback`,
`Manifold/ContMDiffOmegaAnalytic.lean`): an `AnalyticAt` statement gives, by
`AnalyticAt.eventually_analyticAt` plus `Metric.eventually_nhds_iff`, an open
ball on which the pullback is `AnalyticOnNhd`. Open balls in `ℂ` are convex,
hence preconnected.

The preconnected-open `U` and the analyticity package are *derived*; the
caller need only provide the per-chart non-constancy. The shape is strictly
smaller because:

1.  It eliminates the existential `(U, z₁)` pair entirely (the caller
    quantifies over arbitrary neighborhoods `V` of the chart image and
    produces a value-witness in `V`).
2.  It does not mention `IsPreconnected`, `AnalyticOnNhd`, or any
    chart-pullback analyticity datum. The analyticity is supplied
    automatically from `ContMDiff … ω` via ZZ24.

The remaining *honest* obstruction (path-walking analytic continuation
across charts to derive per-chart non-constancy from global
`¬ IsConstantMap f`) is unchanged and remains the same parameter-input as
before.

No gaps, no `axiom`. -/

@[expose] public section

open Set Filter Topology Metric
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## Auxiliary: `AnalyticAt` ⇒ preconnected open ball of analyticity -/

/-- **`AnalyticAt` provides a preconnected open neighborhood of analyticity.**
If `F : ℂ → ℂ` is `AnalyticAt ℂ` at `z₀`, then there exists an open ball
around `z₀` on which `F` is `AnalyticOnNhd ℂ`. Open balls in `ℂ` are convex
hence preconnected.

The proof uses `AnalyticAt.eventually_analyticAt` to extract analyticity on
a neighborhood, and `Metric.eventually_nhds_iff` to pin down a metric ball
inside that neighborhood. -/
lemma exists_preconnected_open_ball_of_analyticAt
    {F : ℂ → ℂ} {z₀ : ℂ} (hF : AnalyticAt ℂ F z₀) :
    ∃ r : ℝ, 0 < r ∧ IsPreconnected (Metric.ball z₀ r) ∧
      z₀ ∈ Metric.ball z₀ r ∧
      AnalyticOnNhd ℂ F (Metric.ball z₀ r) := by
  have h_ev : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ F z := hF.eventually_analyticAt
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.eventually_nhds_iff.mp h_ev
  refine ⟨r, hr_pos, ?_, Metric.mem_ball_self hr_pos, ?_⟩
  · exact (convex_ball z₀ r).isPreconnected
  · intro z hz
    exact hr_sub hz

/-! ## The per-chart non-constancy hypothesis -/

/-- **Per-chart non-constancy hypothesis.** For every non-constant `C^ω` map
`f : X → Y` and every fibre point `x` of every `y₀ : Y`, the chart pullback
of `f` takes a value other than the chart image of `f x` in every
neighborhood of the chart image of `x`.

This is strictly weaker (and strictly different in shape) than
`WithinChartWitnessHypothesis`: the caller does not need to provide a
preconnected open `U`, an analyticity statement, or a specific witness
point. The analyticity of the chart pullback on a small open ball around
the chart image follows from ZZ24 (`contMDiff_omega_analyticAt_chart_pullback`);
the witness point `z₁` is extracted as a value-difference inside that ball. -/
def PerChartNonConstancyHypothesis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
    ∀ (y₀ : Y), ∀ x : X, f x = y₀ →
      ∀ V ∈ 𝓝 ((chartAt ℂ x) x), ∃ z ∈ V,
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          ≠ (chartAt ℂ (f x)) (f x)

/-! ## Reduction: per-chart non-constancy ⇒ within-chart witness -/

/-- **Reduction.** The per-chart non-constancy hypothesis implies the
within-chart witness hypothesis. The proof:

1. Get analyticity of the chart pullback at `(chartAt ℂ x) x` from ZZ24.
2. Extract a preconnected open ball `U = Metric.ball ((chartAt ℂ x) x) r`
   on which the pullback is `AnalyticOnNhd`, via
   `exists_preconnected_open_ball_of_analyticAt`.
3. The ball `U` is in `𝓝 ((chartAt ℂ x) x)` (it is open and contains the
   centre); apply per-chart non-constancy at `V := U` to extract a witness
   `z₁ ∈ U` with `F z₁ ≠ c`. -/
theorem withinChartWitness_of_perChartNonConstancy
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : PerChartNonConstancyHypothesis X Y) :
    WithinChartWitnessHypothesis X Y := by
  intro f hf hnc y₀ x hx
  -- (1) Chart pullback is `AnalyticAt ℂ` at the chart image of `x`, by ZZ24.
  have hFA_at :
      AnalyticAt ℂ ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) :=
    contMDiff_omega_analyticAt_chart_pullback hf x
  -- (2) Extract a preconnected open ball of analyticity.
  obtain ⟨r, hr_pos, hU_pc, hxU, hFA⟩ :=
    exists_preconnected_open_ball_of_analyticAt hFA_at
  -- (3) Apply per-chart non-constancy with `V := Metric.ball ((chartAt ℂ x) x) r`.
  have hV_nhds : Metric.ball ((chartAt ℂ x) x) r ∈ 𝓝 ((chartAt ℂ x) x) :=
    Metric.ball_mem_nhds _ hr_pos
  obtain ⟨z₁, hz₁_mem, hz₁_ne⟩ := H f hf hnc y₀ x hx _ hV_nhds
  exact ⟨Metric.ball ((chartAt ℂ x) x) r, hU_pc, hxU, hFA, z₁, hz₁_mem, hz₁_ne⟩

/-! ## End-to-end composition -/

/-- **Connectivity globalization from per-chart non-constancy.** Composing
this file's reduction with `connectivityGlobalization_of_withinChartWitness`
(ZZ32). -/
theorem connectivityGlobalization_of_perChartNonConstancy
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : PerChartNonConstancyHypothesis X Y) :
    ConnectivityGlobalizationHypothesis X Y :=
  connectivityGlobalization_of_withinChartWitness
    (withinChartWitness_of_perChartNonConstancy H)

/-- **End-to-end conditional discharge of `fibres_finite_statement` from
per-chart non-constancy.** Composing this file's reduction with the ZZ30
assembly (via ZZ32). -/
theorem fibres_finite_statement_holds_of_perChartNonConstancy
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : PerChartNonConstancyHypothesis X Y) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
        ∀ y : Y, (f ⁻¹' {y}).Finite :=
  fibres_finite_statement_holds_of_withinChartWitness
    (withinChartWitness_of_perChartNonConstancy H)

end Degree
end ContMDiff
end Jacobians.Discharge
