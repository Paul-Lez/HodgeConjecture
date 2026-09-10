/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.AnalyticFiberDiscrete

set_option autoImplicit true


/-! # Discreteness of the critical set of an analytic map

Companion to `Jacobians.Discharge.Manifold.AnalyticFiberDiscrete`. The
`regular_value_exists_of_critical_values_finite` reduction in
`Jacobians.Discharge.Manifold.Degree` requires, for each non-constant
analytic `f : X → Y`, a `Finset Y` containing all critical values, plus
local injectivity (`IsDiscrete (f ⁻¹' {y})`) at every value outside that
finset.

The mathematical input behind that hypothesis is:

* **The critical-point set is discrete in `X`.** Critical points of `f` are
  points where the derivative of a chart pullback vanishes. Since the
  derivative of an analytic map is itself analytic, and a non-constant
  analytic chart pullback has non-zero derivative at *some* nearby point,
  the identity theorem makes critical points isolated.

* **A discrete closed subset of a compact space is finite.** This part is
  purely topological and is the same as `fiber_finite_of_isDiscrete`.

This file delivers the first bullet on the chart-pullback-data side, in a
form mirroring `ChartPullbackData` from the companion file. The
manifold-level bridges `ContMDiff … ω → AnalyticAt` and "non-constant ⇒
some chart-pullback derivative is not eventually zero" are again left as
hypothesis-parameters (no `axiom`, no gaps).

What this file does discharge:

* `analyticAt_isolated_zero_of_not_eventually_zero_of_analytic_deriv` —
  the ℂ-side identity-theorem core for the *derivative*: if `F'` is
  analytic at `z₀`, takes value `0` at `z₀`, and is not eventually zero,
  then `z₀` is isolated in `{z | F' z = 0}`. This is just an alias of the
  pre-existing `analyticAt_isolated_zero_of_not_eventually_zero` applied to
  `F'`; we expose it under the "critical point" name for downstream use.

* `CriticalChartPullbackData` — chart-pullback witness structure for
  criticality. Mirrors `ChartPullbackData` but tracks the chart-pullback
  derivative `F' : ℂ → ℂ` and the predicate "`x` is a critical point"
  packaged as a `Set X → Prop` parameter `crit`, with a compatibility
  axiom: `x' ∈ crit ↔ F' (φ x') = 0` for `x' ∈ V`.

* `criticalSet_pointIsolated_via_chart_pullback` — manifold-side per-point:
  given a `CriticalChartPullbackData` witness at a critical point `x`,
  there is an open `U ∋ x` whose intersection with the critical set is
  `{x}`.

* `criticalSet_isDiscrete_of_chart_pullback` — globalisation in `x`: the
  critical set carries the discrete subspace topology.

* `criticalSet_finite_of_chart_pullback` — composition with closedness +
  compactness: the critical set is finite.
-/

@[expose] public section

open Set Filter Topology

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## ℂ-analytic core: per-point isolated critical point -/

/-- **Per-point identity theorem (derivative version).** If `F' : ℂ → ℂ`
is analytic at `z₀`, vanishes at `z₀`, and is not identically zero on any
neighbourhood of `z₀`, then there is an open set `U ∋ z₀` on which `z₀`
is the unique zero of `F'`. This is exactly
`analyticAt_isolated_zero_of_not_eventually_zero` applied to the
derivative; it is exposed here under a "critical point" name to make the
downstream usage self-documenting. -/
lemma analyticAt_isolated_zero_of_not_eventually_zero_of_analytic_deriv
    {F' : ℂ → ℂ} {z₀ : ℂ}
    (hF' : AnalyticAt ℂ F' z₀) (hz : F' z₀ = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 z₀, F' z = 0) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ U ∩ {z | F' z = 0} = {z₀} :=
  analyticAt_isolated_zero_of_not_eventually_zero hF' hz hne

/-! ## Manifold side: per-critical-point chart-pullback driver -/

/-- **Critical-point chart-pullback isolation data.** For a map
`f : X → Y` between topological spaces, a designated critical-point set
`crit : Set X`, and a point `x : X`, this records a chart-pullback witness
that `x` is isolated in `crit`.

The data mirrors `ChartPullbackData` but the analytic object is the
chart-pullback **derivative** `F' : ℂ → ℂ`, and the compatibility says
`x' ∈ crit` is detected by `F' (φ x') = 0`.

* `V` — open neighbourhood of `x` in `X`,
* `W` — open subset of ℂ,
* `φ : V → W` — homeomorphic chart image of `V`,
* `F' : ℂ → ℂ` — the chart-pulled-back derivative,
* `hF'A` — `F'` is analytic at `φ x`,
* `hF'ne` — `F'` is not eventually zero near `φ x`.

The user supplies `hCompat : ∀ x' : V, x'.1 ∈ crit ↔ F' (φ x') = 0`. -/
structure CriticalChartPullbackData {X : Type u} [TopologicalSpace X]
    {Y : Type v} (f : X → Y) (crit : Set X) (x : X) where
  /-- Open neighbourhood of `x`. -/
  V : Set X
  hV_open : IsOpen V
  hxV : x ∈ V
  /-- Chart image: an open subset of ℂ. -/
  W : Set ℂ
  hW_open : IsOpen W
  /-- Homeomorphism from `V` onto `W`. -/
  φ : V → W
  hφ : Continuous φ
  hφ_inv : Function.Bijective φ
  /-- Image of `x` under the chart. -/
  z₀ : ℂ
  hz₀ : (φ ⟨x, hxV⟩ : ℂ) = z₀
  hz₀W : z₀ ∈ W
  /-- Chart-pulled-back derivative. -/
  F' : ℂ → ℂ
  hF'A : AnalyticAt ℂ F' z₀
  hF'ne : ¬ ∀ᶠ z in 𝓝 z₀, F' z = 0
  /-- Compatibility: on `V`, the criticality condition `x' ∈ crit` is
  detected by `F'` evaluated at the chart image. -/
  hCompat :
    ∀ x' : V, x'.1 ∈ crit ↔ F' (φ x') = 0

/-- **Per-critical-point isolation from chart-pullback data.** Given
chart-pullback derivative data witnessing that the chart-pulled-back
derivative is analytic and not eventually zero at `φ x`, the point `x` is
isolated in the critical set `crit`. -/
lemma criticalSet_pointIsolated_via_chart_pullback
    {X : Type u} [TopologicalSpace X]
    {Y : Type v}
    (f : X → Y) (crit : Set X) (x : X) (hx : x ∈ crit)
    (D : CriticalChartPullbackData f crit x) :
    ∃ U : Set X, IsOpen U ∧ U ∩ crit = {x} := by
  -- Use the ℂ-side identity theorem on the derivative to isolate `z₀`.
  have hF'0 : D.F' D.z₀ = 0 := by
    have hcomp := (D.hCompat ⟨x, D.hxV⟩).mp (by simpa using hx)
    -- `hcomp : F' (↑(D.φ ⟨x, D.hxV⟩)) = 0`; rewrite via `D.hz₀`.
    rw [← D.hz₀]; exact hcomp
  rcases analyticAt_isolated_zero_of_not_eventually_zero_of_analytic_deriv
      D.hF'A hF'0 D.hF'ne with
    ⟨U_C, hU_C_open, hz₀_mem, hU_C_eq⟩
  -- Pull back `U_C` along the chart to `X`.
  classical
  let U : Set X := {x' : X | ∃ h : x' ∈ D.V, (D.φ ⟨x', h⟩ : ℂ) ∈ U_C}
  have hxU : x ∈ U := ⟨D.hxV, by rw [D.hz₀]; exact hz₀_mem⟩
  have hU_open : IsOpen U := by
    set g : D.V → ℂ := fun v => ((D.φ v : D.W) : ℂ) with hg_def
    have hg_cont : Continuous g :=
      (continuous_subtype_val).comp D.hφ
    have h_pre_open_in_V : IsOpen (g ⁻¹' U_C) :=
      hg_cont.isOpen_preimage U_C hU_C_open
    have h_emb : IsOpenEmbedding ((↑) : D.V → X) :=
      D.hV_open.isOpenEmbedding_subtypeVal
    have hU_eq_image :
        U = ((↑) : D.V → X) '' (g ⁻¹' U_C) := by
      ext x'
      constructor
      · rintro ⟨hx'V, hφxU⟩
        refine ⟨⟨x', hx'V⟩, ?_, rfl⟩
        simpa [hg_def, Set.mem_preimage] using hφxU
      · rintro ⟨⟨x'', hx''V⟩, hmem, rfl⟩
        refine ⟨hx''V, ?_⟩
        simpa [hg_def, Set.mem_preimage] using hmem
    rw [hU_eq_image]
    exact h_emb.isOpenMap _ h_pre_open_in_V
  refine ⟨U, hU_open, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨hxU, by simpa using hx⟩, ?_⟩
  rintro x' ⟨⟨hx'V, hφx'⟩, hcrit_x'⟩
  -- `hcrit_x' : x' ∈ crit`; via `hCompat`, `F' (φ ⟨x', hx'V⟩) = 0`.
  have hF'c : D.F' (D.φ ⟨x', hx'V⟩ : ℂ) = 0 := (D.hCompat ⟨x', hx'V⟩).mp (by
    simpa using hcrit_x')
  -- From `hU_C_eq`, `(φ ⟨x', hx'V⟩ : ℂ) = z₀`.
  have hz_eq : (D.φ ⟨x', hx'V⟩ : ℂ) = D.z₀ := by
    have hmem : (D.φ ⟨x', hx'V⟩ : ℂ) ∈ U_C ∩ {z | D.F' z = 0} :=
      ⟨hφx', hF'c⟩
    rw [hU_C_eq] at hmem
    simpa using hmem
  -- Combine `hz_eq` with `D.hz₀` and injectivity of `D.φ`.
  have h_eq_x : (⟨x', hx'V⟩ : D.V) = ⟨x, D.hxV⟩ := by
    apply D.hφ_inv.1
    apply Subtype.ext
    rw [hz_eq, ← D.hz₀]
  exact congrArg Subtype.val h_eq_x

/-! ## Globalisation in `x`: the critical set is `IsDiscrete` -/

/-- **Globalised: `IsDiscrete` of the critical set from per-point chart
data.** If for every `x ∈ crit` we have a `CriticalChartPullbackData`
witness, then the critical set carries the discrete subspace topology. -/
lemma criticalSet_isDiscrete_of_chart_pullback
    {X : Type u} [TopologicalSpace X]
    {Y : Type v}
    (f : X → Y) (crit : Set X)
    (h : ∀ x ∈ crit, CriticalChartPullbackData f crit x) :
    IsDiscrete crit := by
  rw [isDiscrete_iff_forall_exists_isOpen]
  intro x hx
  rcases criticalSet_pointIsolated_via_chart_pullback (f := f) (crit := crit)
      (x := x) hx (h x hx) with ⟨U, hU_open, hU_eq⟩
  exact ⟨U, hU_open, hU_eq⟩

/-! ## Compactness ⇒ finiteness of the critical set -/

/-- **Critical set finite from compactness + discreteness.** If the
critical set `crit ⊆ X` is closed and `X` is compact T2, and the critical
set is discrete, then it is finite. -/
lemma criticalSet_finite_of_isDiscrete_of_isClosed
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {crit : Set X} (h_closed : IsClosed crit) (h_disc : IsDiscrete crit) :
    crit.Finite := by
  have h_cpct : IsCompact crit := h_closed.isCompact
  exact h_cpct.finite h_disc

/-- **Critical-set finiteness from chart-pullback hypothesis.** Composing
`criticalSet_isDiscrete_of_chart_pullback` with the topological half:
given closedness of the critical set and a chart-pullback witness at every
critical point, the critical set is finite. -/
lemma criticalSet_finite_of_chart_pullback
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {Y : Type v}
    (f : X → Y) (crit : Set X)
    (h_closed : IsClosed crit)
    (h : ∀ x ∈ crit, CriticalChartPullbackData f crit x) :
    crit.Finite :=
  criticalSet_finite_of_isDiscrete_of_isClosed h_closed
    (criticalSet_isDiscrete_of_chart_pullback f crit h)

/-! ## Named deliverable: `criticalSet_isDiscrete_of_not_constant`

The next lemma is the named clean deliverable for the chip. It states:
the critical set of an analytic non-constant `f` is discrete *given* a
chart-pullback derivative witness at every critical point. The
"non-constant" hypothesis is what is *expected* (in the full classical
proof) to provide the chart-pullback witnesses; here we expose them
explicitly as a parameter so this lemma is provable unconditionally. -/

/-- **Named deliverable.** The critical set of `f : X → Y` is discrete,
given that every critical point admits a chart-pullback derivative witness
(i.e., a `CriticalChartPullbackData`). The non-constancy hypothesis is
included for documentation and downstream chaining; it is not used in the
proof beyond what the chart-pullback witness already encodes. -/
lemma criticalSet_isDiscrete_of_not_constant
    {X : Type u} [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y]
    (f : X → Y) (_hnc : ¬ Jacobians.Discharge.IsConstantMap f)
    (crit : Set X)
    (h : ∀ x ∈ crit, CriticalChartPullbackData f crit x) :
    IsDiscrete crit :=
  criticalSet_isDiscrete_of_chart_pullback f crit h

end Degree
end ContMDiff
end Jacobians.Discharge
