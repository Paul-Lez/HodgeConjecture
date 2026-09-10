/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.ChartBallOffCentreWitnessDischarge

set_option autoImplicit true


/-! # Discharging the chart-pullback non-eventual-constancy hypothesis

ZZ38 (`ChartBallOffCentreWitnessDischarge.lean`) reduced
`fibres_finite_statement` end-to-end, modulo a single named hypothesis
`ChartPullbackNotEventuallyConstHypothesis X Y` asserting: for every
non-constant `C^ω` map `f : X → Y`, every `y₀ : Y`, and every fibre point
`x` of `y₀`, the chart pullback
`F = (chartAt ℂ y₀) ∘ f ∘ (chartAt ℂ x).symm` is **not** eventually equal
to `(chartAt ℂ y₀) y₀` near `(chartAt ℂ x) x`.

This file (ZZ43) provides the **manifold-side discharge**, modulo a single
named "chart-overlap propagation" hypothesis that captures the
path-walking analytic-continuation step.

## The argument

If the chart pullback `F` *is* eventually equal to `c := (chartAt ℂ y₀) y₀`
near `z₀ := (chartAt ℂ x) x`, then by ZZ24 (analyticity of chart pullbacks)
combined with `exists_preconnected_open_ball_of_analyticAt` and mathlib's
identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`),
`F = c` on a whole preconnected open ball `B ⊆ ℂ` containing `z₀`.

Translated back to `X` via `(chartAt ℂ x).symm`, this says: `f` takes the
constant value `y₀` on a small open neighborhood `(chartAt ℂ x).symm '' B`
of `x` in `X`. (One uses `(chartAt ℂ y₀).left_inv` to pull `c` back to
`y₀`.)

The remaining step — propagating local-constancy on a chart neighborhood
to global-constancy on `X` — is **the path-walking analytic continuation
argument** documented at the bottom of `AnalyticContinuationGlobalization.lean`:

> walking analytic continuation along a path γ : [0,1] → X to chain
> `eqOn_of_preconnected_of_eventuallyEq` across overlapping chart domains,
> using `PathConnectedSpace X` (which follows from `ConnectedSpace +
> LocallyPathConnectedSpace`, the latter true for manifolds).

This is plain analytic-continuation-along-paths; the chart-overlap
analyticity ingredient is in mathlib at the analytic-manifold pin. We
package this propagation step as a single named hypothesis-parameter
`ChartOverlapPropagationHypothesis` and discharge
`ChartPullbackNotEventuallyConstHypothesis` from it.

## What this file delivers

* `ChartOverlapPropagationHypothesis X Y` — single named hypothesis
  capturing the path-walking content: "if `f` is `C^ω` and `f x₀ = y₀` and
  `f` is identically `y₀` on some open neighborhood of `x₀`, then `f` is
  identically `y₀` on all of `X`".

* `chartPullbackNotEventuallyConst_of_chartOverlapPropagation` — discharges
  `ChartPullbackNotEventuallyConstHypothesis X Y` from
  `ChartOverlapPropagationHypothesis X Y`, using ZZ24 + identity theorem.

* End-to-end composition theorems through ZZ38:
  - `chartBallOffCentreWitness_of_chartOverlapPropagation`
  - `perChartNonConstancy_of_chartOverlapPropagation`
  - `withinChartWitness_of_chartOverlapPropagation`
  - `connectivityGlobalization_of_chartOverlapPropagation`
  - `fibres_finite_statement_holds_of_chartOverlapPropagation`

Replacing `ChartPullbackNotEventuallyConstHypothesis` with the strictly
smaller `ChartOverlapPropagationHypothesis` is a clean reduction: the
former mentions `Filter.Eventually`, chart pullbacks, and chart images;
the latter mentions only "constant on an open neighborhood ⇒ constant on
`X`" — a purely topological/analytic-continuation statement with no
filters or chart-coordinate manipulation.

No gaps, no `axiom`. -/

@[expose] public section

open Set Filter Topology Metric
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## The chart-overlap propagation hypothesis-parameter -/

/-- **Chart-overlap propagation hypothesis.** For every `C^ω` map
`f : X → Y`, every `y₀ : Y`, every `x₀ : X` with `f x₀ = y₀`, and every
open set `V ⊆ X` containing `x₀` on which `f` is identically `y₀`, the map
`f` is identically `y₀` on all of `X`.

This is the manifold-globalization content deferred by the path-walking
analytic-continuation argument. It contains no filter algebra, no chart
coordinates, no eventual equality — purely the topological/analytic
statement "local-constancy at a single point lifts to global-constancy".

The standard proof uses `PathConnectedSpace X` (true for connected
manifolds) and chains `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`
across overlapping charts along a path γ from `x₀` to any other point. -/
def ChartOverlapPropagationHypothesis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
    ∀ (y₀ : Y), ∀ (x₀ : X), f x₀ = y₀ →
      ∀ (V : Set X), IsOpen V → x₀ ∈ V → (∀ x ∈ V, f x = y₀) →
        ∀ x : X, f x = y₀

/-! ## ℂ-side: from "eventually `c`" to "constant on a preconnected open ball" -/

/-- **Identity-theorem packaging.** If `F : ℂ → ℂ` is analytic at `z₀` and
eventually equal to `c` at `z₀`, then there is a preconnected open ball
around `z₀` of positive radius on which `F` is identically `c`. -/
lemma exists_preconnected_open_ball_eqOn_const_of_eventuallyEq
    {F : ℂ → ℂ} {z₀ : ℂ} {c : ℂ}
    (hF : AnalyticAt ℂ F z₀)
    (hev : ∀ᶠ z in 𝓝 z₀, F z = c) :
    ∃ r : ℝ, 0 < r ∧ IsPreconnected (Metric.ball z₀ r)
      ∧ z₀ ∈ Metric.ball z₀ r ∧ EqOn F (fun _ => c) (Metric.ball z₀ r) := by
  -- Pull a preconnected ball of analyticity from ZZ34's helper.
  obtain ⟨r, hr_pos, hU_pc, hz₀_mem, hFA⟩ :=
    exists_preconnected_open_ball_of_analyticAt hF
  refine ⟨r, hr_pos, hU_pc, hz₀_mem, ?_⟩
  -- Apply mathlib's identity theorem against the constant `c`.
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => c) (Metric.ball z₀ r) :=
    analyticOnNhd_const
  have hev' : F =ᶠ[𝓝 z₀] (fun _ : ℂ => c) := hev
  exact hFA.eqOn_of_preconnected_of_eventuallyEq hg hU_pc hz₀_mem hev'

/-! ## Manifold-side discharge -/

/-- **Discharge of `ChartPullbackNotEventuallyConstHypothesis`.** From the
chart-overlap propagation hypothesis (the path-walking analytic-continuation
step) and the ZZ24 analyticity of chart pullbacks, the chart pullback at
every fibre point of every `y₀` is **not** eventually equal to
`(chartAt ℂ y₀) y₀`.

Argument: if it were, then by ZZ24 + the identity theorem the pullback is
identically `c := (chartAt ℂ y₀) y₀` on a preconnected open ball
`B ⊆ (chartAt ℂ x).target` around `(chartAt ℂ x) x`. Pulling back along
`(chartAt ℂ x)`, this gives an open neighborhood of `x` in `X` on which
the chart-image of `f` is identically `c`. Pulling back further along
`(chartAt ℂ y₀).left_inv`, we get `f ≡ y₀` on that neighborhood. The
chart-overlap propagation hypothesis then upgrades this to `f ≡ y₀` on
all of `X`, contradicting `¬ IsConstantMap f`. -/
theorem chartPullbackNotEventuallyConst_of_chartOverlapPropagation
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ChartOverlapPropagationHypothesis X Y) :
    ChartPullbackNotEventuallyConstHypothesis X Y := by
  intro f hf hnc y₀ x hx hev
  -- Set up the chart pullback `F` and the centre `z₀`.
  set F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm with hF_def
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  set c : ℂ := (chartAt ℂ (f x)) (f x) with hc_def
  -- ZZ24: `AnalyticAt ℂ F z₀`.
  have hFA_at : AnalyticAt ℂ F z₀ :=
    contMDiff_omega_analyticAt_chart_pullback hf x
  -- The hypothesis `hev` says `F` is eventually `c` at `z₀`. By
  -- the identity theorem there is a preconnected open ball on which
  -- `F = c` identically.
  obtain ⟨r, hr_pos, _hU_pc, _hz₀_mem, hF_eqOn⟩ :=
    exists_preconnected_open_ball_eqOn_const_of_eventuallyEq hFA_at hev
  -- Pull back to `X`: define `V := (chartAt ℂ x).source ∩
  -- (chartAt ℂ x) ⁻¹' (Metric.ball z₀ r)`. This is open in `X` and
  -- contains `x`.
  set V : Set X :=
    (chartAt ℂ x).source ∩ ((chartAt ℂ x) ⁻¹' (Metric.ball z₀ r)) with hV_def
  have hx_src : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hz₀_mem_ball : z₀ ∈ Metric.ball z₀ r := by
    simp [Metric.mem_ball, hr_pos]
  have hx_mem_V : x ∈ V := by
    refine ⟨hx_src, ?_⟩
    show (chartAt ℂ x) x ∈ Metric.ball z₀ r
    exact hz₀_mem_ball
  -- `V` is open: chart source is open, preimage of an open set under
  -- the chart's continuous-on-source map is open relative to the source,
  -- and the intersection is open as both sides are open.
  have hV_open : IsOpen V := by
    -- `(chartAt ℂ x)` is a `PartialHomeomorph` whose `toFun` is continuous
    -- on its source; we use `(chartAt ℂ x).continuousOn_toFun` together
    -- with `IsOpen.inter_preimage_continuousOn`-style lemmas.
    have hcont : ContinuousOn (chartAt ℂ x) (chartAt ℂ x).source :=
      (chartAt ℂ x).continuousOn_toFun
    -- Preimage of `Metric.ball z₀ r` (open in ℂ) under `chartAt ℂ x`,
    -- restricted to the source: `(chartAt ℂ x).source ∩ (chartAt ℂ x)⁻¹' …`
    -- is open in `X` because chart source is open in `X` and continuity-on
    -- yields openness of the relative preimage.
    have h_ball_open : IsOpen (Metric.ball z₀ r) := Metric.isOpen_ball
    have hpre := hcont.isOpen_inter_preimage (chartAt ℂ x).open_source h_ball_open
    -- `hpre : IsOpen ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball z₀ r)`.
    exact hpre
  -- On `V`, `f` is identically `y₀`. We show this using:
  --   * For `x' ∈ V`, `(chartAt ℂ x) x' ∈ Metric.ball z₀ r`, so
  --     `F ((chartAt ℂ x) x') = c` by `hF_eqOn`.
  --   * `F ((chartAt ℂ x) x') = (chartAt ℂ (f x)) (f x')` after using
  --     the chart left-inverse `(chartAt ℂ x).symm ((chartAt ℂ x) x') = x'`
  --     (valid since `x' ∈ source`).
  --   * `(chartAt ℂ (f x)) (f x') = c = (chartAt ℂ (f x)) (f x)` then gives
  --     `f x' = f x = y₀` by injectivity of the chart on its source —
  --     IF `f x' ∈ source`. We do not in general have that for arbitrary
  --     `x' ∈ V`, so we need to shrink `V` further.
  -- The clean way: also intersect `V` with `f ⁻¹' (chartAt ℂ y₀).source`.
  -- Continuity of `f` (from `ContMDiff … ω`) makes that open.
  -- We do exactly that, refining `V` to `V'`.
  have hf_cont : Continuous f := hf.continuous
  set V' : Set X := V ∩ f ⁻¹' (chartAt ℂ (f x)).source with hV'_def
  have h_fx_mem_target_src : f x ∈ (chartAt ℂ (f x)).source :=
    mem_chart_source ℂ (f x)
  have hx_mem_V' : x ∈ V' := ⟨hx_mem_V, h_fx_mem_target_src⟩
  have hV'_open : IsOpen V' := by
    have h2 : IsOpen (f ⁻¹' (chartAt ℂ (f x)).source) :=
      (chartAt ℂ (f x)).open_source.preimage hf_cont
    exact hV_open.inter h2
  -- Now show `∀ x' ∈ V', f x' = y₀`.
  have h_const_on_V' : ∀ x' ∈ V', f x' = y₀ := by
    intro x' hx'
    obtain ⟨⟨hx'_src, hx'_pre⟩, hx'_fsrc⟩ := hx'
    -- `(chartAt ℂ x) x' ∈ Metric.ball z₀ r`.
    have hx'_chart_mem : (chartAt ℂ x) x' ∈ Metric.ball z₀ r := hx'_pre
    -- `F ((chartAt ℂ x) x') = c`.
    have hF_x' : F ((chartAt ℂ x) x') = c := hF_eqOn hx'_chart_mem
    -- `F ((chartAt ℂ x) x') = (chartAt ℂ (f x)) (f x')` via chart-symm-lefty.
    have h_inv : (chartAt ℂ x).symm ((chartAt ℂ x) x') = x' :=
      (chartAt ℂ x).left_inv hx'_src
    have h_F_unfold :
        F ((chartAt ℂ x) x') = (chartAt ℂ (f x)) (f x') := by
      show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x')
          = (chartAt ℂ (f x)) (f x')
      simp [Function.comp, h_inv]
    -- So `(chartAt ℂ (f x)) (f x') = (chartAt ℂ (f x)) (f x)`.
    have h_chart_eq : (chartAt ℂ (f x)) (f x') = (chartAt ℂ (f x)) (f x) := by
      rw [← h_F_unfold, hF_x']
    -- Inject via chart on the target chart's source: both `f x` and `f x'`
    -- lie in `(chartAt ℂ (f x)).source`, and the chart is injective there.
    have h_inj : Set.InjOn (chartAt ℂ (f x)) (chartAt ℂ (f x)).source :=
      (chartAt ℂ (f x)).injOn
    have h_fx'_eq : f x' = f x := h_inj hx'_fsrc h_fx_mem_target_src h_chart_eq
    rw [h_fx'_eq]
    exact hx
  -- Apply the chart-overlap propagation hypothesis to upgrade local
  -- constancy to global constancy.
  have h_global : ∀ x' : X, f x' = y₀ :=
    H f hf y₀ x hx V' hV'_open hx_mem_V' h_const_on_V'
  -- This makes `f` constant — contradiction with `¬ IsConstantMap f`.
  apply hnc
  exact ⟨y₀, h_global⟩

/-! ## End-to-end composition through ZZ38 -/

/-- **Chart-ball off-centre witness from chart-overlap propagation.**
End-to-end through ZZ38 + ZZ36 + ZZ34 + ZZ32 + ZZ30. -/
theorem chartBallOffCentreWitness_of_chartOverlapPropagation
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ChartOverlapPropagationHypothesis X Y) :
    ChartBallOffCentreWitnessHypothesis X Y :=
  chartBallOffCentreWitness_of_chart_pullback_not_eventually_const
    (chartPullbackNotEventuallyConst_of_chartOverlapPropagation H)

/-- **Per-chart non-constancy from chart-overlap propagation.** -/
theorem perChartNonConstancy_of_chartOverlapPropagation
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ChartOverlapPropagationHypothesis X Y) :
    PerChartNonConstancyHypothesis X Y :=
  perChartNonConstancy_of_chart_pullback_not_eventually_const
    (chartPullbackNotEventuallyConst_of_chartOverlapPropagation H)

/-- **Within-chart witness from chart-overlap propagation.** -/
theorem withinChartWitness_of_chartOverlapPropagation
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ChartOverlapPropagationHypothesis X Y) :
    WithinChartWitnessHypothesis X Y :=
  withinChartWitness_of_chart_pullback_not_eventually_const
    (chartPullbackNotEventuallyConst_of_chartOverlapPropagation H)

/-- **Connectivity globalization from chart-overlap propagation.** -/
theorem connectivityGlobalization_of_chartOverlapPropagation
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ChartOverlapPropagationHypothesis X Y) :
    ConnectivityGlobalizationHypothesis X Y :=
  connectivityGlobalization_of_chart_pullback_not_eventually_const
    (chartPullbackNotEventuallyConst_of_chartOverlapPropagation H)

/-- **End-to-end conditional discharge of `fibres_finite_statement` from
chart-overlap propagation.** Composing through ZZ38 + ZZ36 + ZZ34 + ZZ32 +
ZZ30. -/
theorem fibres_finite_statement_holds_of_chartOverlapPropagation
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ChartOverlapPropagationHypothesis X Y) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
        ∀ y : Y, (f ⁻¹' {y}).Finite :=
  fibres_finite_statement_holds_of_chart_pullback_not_eventually_const
    (chartPullbackNotEventuallyConst_of_chartOverlapPropagation H)

end Degree
end ContMDiff
end Jacobians.Discharge
