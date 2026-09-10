/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.WithinChartWitnessReduction

set_option autoImplicit true


/-! # Reducing `PerChartNonConstancyHypothesis` to non-constancy on chart balls

`WithinChartWitnessReduction.lean` (ZZ34) reduced
`WithinChartWitnessHypothesis X Y` to `PerChartNonConstancyHypothesis X Y`.
That hypothesis asserts that, for every non-constant `C^ω` map `f : X → Y`
and every fibre point `x` of `y₀ = f x`, the chart pullback `F` differs from
`F ((chartAt ℂ x) x)` in *every* neighborhood of `(chartAt ℂ x) x`.

This file (ZZ36) provides the **identity-theorem reduction** to a strictly
local, filter-free hypothesis: it suffices to exhibit, for *every* radius
`r > 0`, a single point `z₁ ∈ Metric.ball ((chartAt ℂ x) x) r` at which the
chart pullback differs from its value at the chart image of `x`.

The mechanism:

1. ZZ24 (`contMDiff_omega_analyticAt_chart_pullback`) supplies analyticity
   of the chart pullback at the chart image of `x`.
2. The `exists_preconnected_open_ball_of_analyticAt` helper from ZZ34 gives
   a preconnected open ball of analyticity of some radius `r₀ > 0`.
3. The all-radii hypothesis is applied at radius `r₀`, giving a witness
   `z₁` inside the *same* preconnected open ball where analyticity holds.
4. Mathlib's identity theorem
   (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) lifts that single
   off-centre value to non-constancy in *every* neighborhood of the centre:
   if `F` were eventually `F z₀` at `z₀`, identity would force
   `F = F z₀` on the whole preconnected ball, contradicting `F z₁ ≠ F z₀`.

The remaining obstruction is the existence of an off-centre value in
*every* small chart ball — a strictly local statement (no filters, no
preconnectedness, no analyticity of any kind in the input). Producing such
a witness from the global `¬ IsConstantMap f` is unchanged content, the
same parameter-input as in ZZ34.

No gaps, no `axiom`. -/

@[expose] public section

open Set Filter Topology Metric
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## Identity-theorem core: not eventually `F z₀` from a single off-centre witness -/

/-- **Single-point off-centre witness ⇒ not eventually constant.** If `F` is
analytic on a preconnected open set `U`, `z₀ ∈ U`, and there is some
`z₁ ∈ U` with `F z₁ ≠ F z₀`, then `F` is not eventually `F z₀` at `z₀`. This
is the contrapositive of mathlib's identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) against the constant
`fun _ => F z₀`. -/
lemma not_eventually_eq_self_of_witness
    {F : ℂ → ℂ} {U : Set ℂ} {z₀ z₁ : ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hU : IsPreconnected U)
    (h₀ : z₀ ∈ U) (h₁ : z₁ ∈ U) (h_ne : F z₁ ≠ F z₀) :
    ¬ ∀ᶠ z in 𝓝 z₀, F z = F z₀ := by
  intro hev
  -- If `F = F z₀` eventually at `z₀`, the identity theorem (against the
  -- constant `fun _ => F z₀`) forces `F = F z₀` on all of `U`.
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => F z₀) U := analyticOnNhd_const
  have hev' : F =ᶠ[𝓝 z₀] (fun _ : ℂ => F z₀) := hev
  have h_eqOn : EqOn F (fun _ => F z₀) U :=
    hF.eqOn_of_preconnected_of_eventuallyEq hg hU h₀ hev'
  exact h_ne (h_eqOn h₁)

/-- **Per-point form of the identity-theorem reduction.** From analyticity on
a preconnected open `U` and a single off-centre witness `z₁ ∈ U` with
`F z₁ ≠ F z₀` (where `z₀ ∈ U`), every neighborhood of `z₀` contains a point
at which `F` differs from `F z₀`.

This is the per-point shape consumed by `PerChartNonConstancyHypothesis`. -/
lemma exists_value_ne_in_nhds_of_witness
    {F : ℂ → ℂ} {U : Set ℂ} {z₀ z₁ : ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hU : IsPreconnected U)
    (h₀ : z₀ ∈ U) (h₁ : z₁ ∈ U) (h_ne : F z₁ ≠ F z₀) :
    ∀ V ∈ 𝓝 z₀, ∃ z ∈ V, F z ≠ F z₀ := by
  have h_not_ev : ¬ ∀ᶠ z in 𝓝 z₀, F z = F z₀ :=
    not_eventually_eq_self_of_witness hF hU h₀ h₁ h_ne
  intro V hV
  by_contra h_all
  push Not at h_all
  apply h_not_ev
  exact Filter.mem_of_superset hV (fun z hz => h_all z hz)

/-! ## Hypothesis: chart-ball off-centre witness at every small radius -/

/-- **Chart-ball off-centre witness hypothesis (all radii).** For every
non-constant `C^ω` map `f : X → Y`, every fibre point `x` of every
`y₀ : Y`, and *every* radius `r > 0`, there is a point `z₁` in the open
ball of radius `r` around the chart image of `x` at which the chart
pullback `F` differs from `F` at the chart image of `x`.

Equivalently: the chart pullback is not locally constant at the chart
image of `x`.

This shape is strictly smaller than `PerChartNonConstancyHypothesis`:

* It eliminates the universal quantifier over neighborhoods `V ∈ 𝓝 z₀`.
  The caller produces, for each radius `r > 0`, a single off-centre witness
  inside `Metric.ball z₀ r` — the identity theorem (mathlib's
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) lifts these
  witnesses to *every* neighborhood.
* It does not mention `Filter`, `𝓝`, or eventual equality at all.
* The metric structure is fixed (open balls in ℂ) — no preconnectedness,
  analyticity, or chart-data is required from the caller. -/
def ChartBallOffCentreWitnessHypothesis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
    ∀ (y₀ : Y), ∀ x : X, f x = y₀ →
      ∀ r : ℝ, 0 < r → ∃ z₁ ∈ Metric.ball ((chartAt ℂ x) x) r,
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z₁
          ≠ (chartAt ℂ (f x)) (f x)

/-! ## Reduction: chart-ball off-centre witness ⇒ per-chart non-constancy -/

/-- **Reduction.** The chart-ball off-centre witness hypothesis (all radii)
implies the per-chart non-constancy hypothesis. The proof:

1. From ZZ24 (`contMDiff_omega_analyticAt_chart_pullback`) the chart
   pullback is `AnalyticAt ℂ` at the chart image of `x`.
2. By `exists_preconnected_open_ball_of_analyticAt` (ZZ34 helper), there
   is a preconnected open ball of radius `r₀ > 0` on which the pullback is
   `AnalyticOnNhd ℂ`.
3. The hypothesis applied at radius `r₀` gives a witness `z₁` inside that
   same ball with `F z₁ ≠ F z₀`.
4. Mathlib's identity theorem (`exists_value_ne_in_nhds_of_witness` above)
   lifts this single off-centre witness to every neighborhood of `z₀`. -/
theorem perChartNonConstancy_of_chartBallOffCentreWitness
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ChartBallOffCentreWitnessHypothesis X Y) :
    PerChartNonConstancyHypothesis X Y := by
  intro f hf hnc y₀ x hx V hV
  -- Set up the chart pullback and its centre.
  set F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm with hF_def
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  -- (1) `AnalyticAt ℂ F z₀` from ZZ24.
  have hFA_at : AnalyticAt ℂ F z₀ :=
    contMDiff_omega_analyticAt_chart_pullback hf x
  -- (2) Extract a preconnected open ball of analyticity around `z₀`.
  obtain ⟨r₀, hr₀_pos, hU₀_pc, hz₀_mem₀, hFA₀⟩ :=
    exists_preconnected_open_ball_of_analyticAt hFA_at
  -- (3) Pick the witness radius to be exactly `r₀`, so the witness lies
  -- inside the analyticity ball.
  obtain ⟨z₁, hz₁_mem₀, h_ne⟩ := H f hf hnc y₀ x hx r₀ hr₀_pos
  -- (4) Bridge `F z₀ = (chartAt ℂ (f x)) (f x)` using `chart.symm (chart x x) = x`
  -- (chart left-inverse at the source).
  have hz₀_F : F z₀ = (chartAt ℂ (f x)) (f x) := by
    -- `chart.symm (chart x x) = x` from chart left-inverse at the source.
    have hx_src : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have h_inv : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
      (chartAt ℂ x).left_inv hx_src
    show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        = (chartAt ℂ (f x)) (f x)
    simp [Function.comp, h_inv]
  -- Translate the hypothesis witness from "≠ chart(f x)(f x)" to "≠ F z₀".
  have h_ne' : F z₁ ≠ F z₀ := by
    rw [hz₀_F]; exact h_ne
  -- (5) Apply the identity-theorem core.
  -- The result has `F z₀` on the rhs; rewrite back to `chart(f x)(f x)`.
  have h_lifted := exists_value_ne_in_nhds_of_witness hFA₀ hU₀_pc hz₀_mem₀
    hz₁_mem₀ h_ne' V hV
  obtain ⟨z, hz_mem, hz_ne⟩ := h_lifted
  refine ⟨z, hz_mem, ?_⟩
  rw [hz₀_F] at hz_ne
  exact hz_ne

/-! ## End-to-end composition through ZZ34 -/

/-- **Within-chart witness from the chart-ball hypothesis.** Composing this
file's reduction with `withinChartWitness_of_perChartNonConstancy` (ZZ34). -/
theorem withinChartWitness_of_chartBallOffCentreWitness
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ChartBallOffCentreWitnessHypothesis X Y) :
    WithinChartWitnessHypothesis X Y :=
  withinChartWitness_of_perChartNonConstancy
    (perChartNonConstancy_of_chartBallOffCentreWitness H)

/-- **Connectivity globalization from the chart-ball hypothesis.** End-to-end
through ZZ34 + ZZ32. -/
theorem connectivityGlobalization_of_chartBallOffCentreWitness
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ChartBallOffCentreWitnessHypothesis X Y) :
    ConnectivityGlobalizationHypothesis X Y :=
  connectivityGlobalization_of_perChartNonConstancy
    (perChartNonConstancy_of_chartBallOffCentreWitness H)

/-- **End-to-end conditional discharge of `fibres_finite_statement` from the
chart-ball hypothesis.** Composing through ZZ34 + ZZ32 + ZZ30. -/
theorem fibres_finite_statement_holds_of_chartBallOffCentreWitness
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ChartBallOffCentreWitnessHypothesis X Y) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
        ∀ y : Y, (f ⁻¹' {y}).Finite :=
  fibres_finite_statement_holds_of_perChartNonConstancy
    (perChartNonConstancy_of_chartBallOffCentreWitness H)

end Degree
end ContMDiff
end Jacobians.Discharge
