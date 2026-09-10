/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.ChartPullbackNotEventuallyConstDischarge

set_option autoImplicit true


/-! # Discharging chart-overlap propagation from clopen-ness of the locally-constant locus

ZZ43 (`ChartPullbackNotEventuallyConstDischarge.lean`) reduced
`fibres_finite_statement` end-to-end, modulo a single named hypothesis
`ChartOverlapPropagationHypothesis X Y` asserting: for every non-constant
`C^ω` map `f : X → Y`, every `y₀ : Y`, every `x₀ : X` with `f x₀ = y₀`,
and every open `V ∋ x₀` on which `f ≡ y₀`, the map `f` is identically
`y₀` on all of `X`.

This file (ZZ46) reduces that hypothesis to a strictly smaller residual
analytic-continuation statement: **the locally-constant locus is closed**.

## The argument

Define the locally-constant locus
`S := {x | ∀ᶠ x' in 𝓝 x, f x' = y₀}`.

* `S` is **open** by definition of the eventually filter (a point is in
  the interior of `S` because the same neighborhood that witnesses
  `x ∈ S` witnesses every nearby point).

* `S` contains `x₀` (the open `V` from the chart-overlap hypothesis is
  itself a neighborhood of `x₀` on which `f ≡ y₀`).

* `S` is **closed** — this is the residual analytic-continuation
  content, packaged as `ClopennessOfLocallyConstHypothesis`. The
  standard discharge walks a path from `x₀` to a candidate boundary
  point, covers the path with finitely many connected charts, and
  chains `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` across
  overlaps to propagate the local constancy. We isolate it as a single
  hypothesis-parameter at this pin.

* `S` clopen + nonempty in a connected space ⇒ `S = univ`. Since
  `x ∈ S` implies `f x = y₀` (the eventually-condition includes the
  point itself via `Filter.Eventually.self_of_nhds`), we conclude
  `f ≡ y₀` on all of `X`.

## What this file delivers

* `ClopennessOfLocallyConstHypothesis X Y` — single named hypothesis
  capturing the residual analytic-continuation content: the
  locally-constant locus of any `C^ω` map onto a fixed value `y₀` is
  closed.

* `chartOverlapPropagation_of_clopennessOfLocallyConst` — discharges
  `ChartOverlapPropagationHypothesis X Y` from
  `ClopennessOfLocallyConstHypothesis X Y` using the connected-clopen
  argument.

* End-to-end composition theorems through ZZ43:
  - `chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst`
  - `chartBallOffCentreWitness_of_clopennessOfLocallyConst`
  - `perChartNonConstancy_of_clopennessOfLocallyConst`
  - `withinChartWitness_of_clopennessOfLocallyConst`
  - `connectivityGlobalization_of_clopennessOfLocallyConst`
  - `fibres_finite_statement_holds_of_clopennessOfLocallyConst`

The reduction `ChartOverlapPropagationHypothesis ⇐
ClopennessOfLocallyConstHypothesis` is clean: the latter mentions only
the topological closedness of a single explicitly-defined set; the
former carries the open-neighborhood data that has to be turned into
constancy. Once the residual closedness is supplied, the connected-
clopen step is plain topology with no chart-coordinate manipulation.

No gaps, no `axiom`. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## The locally-constant locus -/

/-- The locally-constant locus of a map `f : X → Y` at a value `y₀`:
the set of points `x` such that `f` is eventually equal to `y₀` near
`x`. -/
def locallyConstLocus {X : Type u} [TopologicalSpace X] {Y : Type v}
    (f : X → Y) (y₀ : Y) : Set X :=
  {x | ∀ᶠ x' in 𝓝 x, f x' = y₀}

/-- The locally-constant locus is open: by definition, every point of
the locus admits a neighborhood on which `f ≡ y₀`, and that
neighborhood is contained in the locus. -/
lemma isOpen_locallyConstLocus {X : Type u} [TopologicalSpace X] {Y : Type v}
    (f : X → Y) (y₀ : Y) : IsOpen (locallyConstLocus f y₀) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  intro x hx
  -- `hx : ∀ᶠ x' in 𝓝 x, f x' = y₀`, so there's an open `W ∋ x` with `f ≡ y₀` on `W`.
  obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hx
  -- For each `x'' ∈ W`, `W` is a neighborhood of `x''` on which `f ≡ y₀`,
  -- so `x'' ∈ locallyConstLocus f y₀`.
  refine mem_nhds_iff.mpr ⟨W, ?_, hW_open, hxW⟩
  intro x'' hx''
  -- Show `x'' ∈ locallyConstLocus`: produce a neighborhood of `x''` on which `f = y₀`.
  show ∀ᶠ x' in 𝓝 x'', f x' = y₀
  exact mem_nhds_iff.mpr ⟨W, hW_sub, hW_open, hx''⟩

/-- A point of the locally-constant locus indeed has `f x = y₀`. This
uses `Filter.Eventually.self_of_nhds`. -/
lemma locallyConstLocus_apply {X : Type u} [TopologicalSpace X] {Y : Type v}
    {f : X → Y} {y₀ : Y} {x : X} (hx : x ∈ locallyConstLocus f y₀) :
    f x = y₀ :=
  hx.self_of_nhds

/-- Membership criterion via an open set: if `V` is open, contains `x`,
and `f ≡ y₀` on `V`, then `x ∈ locallyConstLocus f y₀`. -/
lemma mem_locallyConstLocus_of_isOpen {X : Type u} [TopologicalSpace X] {Y : Type v}
    {f : X → Y} {y₀ : Y} {V : Set X} (hV : IsOpen V) {x : X} (hx : x ∈ V)
    (hconst : ∀ x' ∈ V, f x' = y₀) :
    x ∈ locallyConstLocus f y₀ := by
  show ∀ᶠ x' in 𝓝 x, f x' = y₀
  exact mem_nhds_iff.mpr ⟨V, hconst, hV, hx⟩

/-! ## The clopen-ness hypothesis-parameter -/

/-- **Clopen-ness of the locally-constant locus.** For every `C^ω`
map `f : X → Y` and every `y₀ : Y`, the locally-constant locus
`{x | ∀ᶠ x' in 𝓝 x, f x' = y₀}` is closed.

Combined with the open-ness lemma above, this is the residual
analytic-continuation content deferred by the path-walking argument: along
a path `γ : [0,1] → X` from any boundary point of the locus, finitely
many overlapping charts let one chain
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` to extend the
local constancy across the boundary, contradicting boundary-ness.

Isolating only the closedness as a hypothesis lets the connected-clopen
step (open-ness + nonempty + connectedness ⇒ universe) be derived in
plain topology without invoking analyticity. -/
def ClopennessOfLocallyConstHypothesis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
    ∀ (y₀ : Y), IsClosed (locallyConstLocus f y₀)

/-! ## Discharge of `ChartOverlapPropagationHypothesis` -/

/-- **Discharge of `ChartOverlapPropagationHypothesis` from
`ClopennessOfLocallyConstHypothesis`.** The locally-constant locus is
open by definition, closed by the residual hypothesis, contains `x₀`
(via the open `V`-witness), so by connectedness of `X` it is all of
`X`. Hence `f x = y₀` for every `x : X`. -/
theorem chartOverlapPropagation_of_clopennessOfLocallyConst
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ClopennessOfLocallyConstHypothesis X Y) :
    ChartOverlapPropagationHypothesis X Y := by
  intro f hf y₀ x₀ hx₀ V hV_open hx₀_V hVconst
  -- The locally-constant locus.
  set S : Set X := locallyConstLocus f y₀ with hS_def
  -- `S` is open.
  have hS_open : IsOpen S := isOpen_locallyConstLocus f y₀
  -- `S` is closed by hypothesis.
  have hS_closed : IsClosed S := H f hf y₀
  -- `S` contains `x₀`.
  have hx₀_S : x₀ ∈ S :=
    mem_locallyConstLocus_of_isOpen hV_open hx₀_V hVconst
  -- `S` is therefore clopen and nonempty.
  have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
  have hS_nonempty : S.Nonempty := ⟨x₀, hx₀_S⟩
  -- By connectedness of `X`, `S = univ`.
  have hS_univ : S = Set.univ := by
    -- `IsClopen` in a connected space ⇒ `S = ∅ ∨ S = univ`.
    rcases (isClopen_iff (s := S)).mp hS_clopen with hE | hU
    · exact absurd hE hS_nonempty.ne_empty
    · exact hU
  -- For every `x : X`, `x ∈ S`, and therefore `f x = y₀`.
  intro x
  have hx_S : x ∈ S := by rw [hS_univ]; exact mem_univ x
  exact locallyConstLocus_apply hx_S

/-! ## End-to-end composition through ZZ43 + ZZ38 -/

/-- **Chart-pullback non-eventual-constancy from clopen-ness of the
locally-constant locus.** End-to-end through ZZ43. -/
theorem chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ClopennessOfLocallyConstHypothesis X Y) :
    ChartPullbackNotEventuallyConstHypothesis X Y :=
  chartPullbackNotEventuallyConst_of_chartOverlapPropagation
    (chartOverlapPropagation_of_clopennessOfLocallyConst H)

/-- **Chart-ball off-centre witness from clopen-ness of the
locally-constant locus.** -/
theorem chartBallOffCentreWitness_of_clopennessOfLocallyConst
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ClopennessOfLocallyConstHypothesis X Y) :
    ChartBallOffCentreWitnessHypothesis X Y :=
  chartBallOffCentreWitness_of_chartOverlapPropagation
    (chartOverlapPropagation_of_clopennessOfLocallyConst H)

/-- **Per-chart non-constancy from clopen-ness of the
locally-constant locus.** -/
theorem perChartNonConstancy_of_clopennessOfLocallyConst
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ClopennessOfLocallyConstHypothesis X Y) :
    PerChartNonConstancyHypothesis X Y :=
  perChartNonConstancy_of_chartOverlapPropagation
    (chartOverlapPropagation_of_clopennessOfLocallyConst H)

/-- **Within-chart witness from clopen-ness of the locally-constant
locus.** -/
theorem withinChartWitness_of_clopennessOfLocallyConst
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ClopennessOfLocallyConstHypothesis X Y) :
    WithinChartWitnessHypothesis X Y :=
  withinChartWitness_of_chartOverlapPropagation
    (chartOverlapPropagation_of_clopennessOfLocallyConst H)

/-- **Connectivity globalization from clopen-ness of the
locally-constant locus.** -/
theorem connectivityGlobalization_of_clopennessOfLocallyConst
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ClopennessOfLocallyConstHypothesis X Y) :
    ConnectivityGlobalizationHypothesis X Y :=
  connectivityGlobalization_of_chartOverlapPropagation
    (chartOverlapPropagation_of_clopennessOfLocallyConst H)

/-- **End-to-end conditional discharge of `fibres_finite_statement` from
clopen-ness of the locally-constant locus.** Composing through ZZ43 +
ZZ38 + ZZ36 + ZZ34 + ZZ32 + ZZ30. -/
theorem fibres_finite_statement_holds_of_clopennessOfLocallyConst
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : ClopennessOfLocallyConstHypothesis X Y) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
        ∀ y : Y, (f ⁻¹' {y}).Finite :=
  fibres_finite_statement_holds_of_chartOverlapPropagation
    (chartOverlapPropagation_of_clopennessOfLocallyConst H)

end Degree
end ContMDiff
end Jacobians.Discharge
