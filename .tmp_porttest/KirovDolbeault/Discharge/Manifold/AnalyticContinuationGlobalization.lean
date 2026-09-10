/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.AnalyticFiberDiscrete
import KirovDolbeault.Discharge.Manifold.LocalMultiplicity
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.IsolatedZeros

set_option autoImplicit true


/-! # Globalising "not constant" to "not eventually constant" via the identity theorem

Companion to `Jacobians.Discharge.Manifold.AnalyticFiberDiscrete`. ZZ22 reduced
the discreteness statement to a per-fibre-point chart-pullback condition (the
chart-pulled-back representative of `f` should be analytic and **not eventually
equal to `c`** at the chart image, where `c` is the chart image of `y₀`). This
file discharges the "not eventually constant" half of that condition from the
genuinely classical hypothesis "`f` is non-constant", in the cases where the
classical mathlib identity-theorem can be applied directly: namely, on a single
connected open set in `ℂ` (i.e. **within one chart**).

The full manifold-level globalisation across chart overlaps requires walking
the analytic-continuation argument along a path in `X` and is left as a
hypothesis-parameter, with what is still open documented at the end of this
file.

What this file *does* discharge:

* `eventuallyEq_const_iff_eqOn_of_preconnected` — local re-statement of
  mathlib's `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` against a
  constant function: an analytic function on a connected open set is eventually
  equal to a constant `c` at one point iff it equals `c` everywhere on the set.

* `not_eventually_const_of_not_constOn` — the immediate contrapositive: if `F`
  is analytic on a preconnected open set `U`, takes a value other than `c`
  somewhere in `U`, and `z₀ ∈ U`, then `F` is not eventually `c` at `z₀`.

* `chart_pullback_not_eventually_const_within_chart` — the local-within-one-chart
  version of the deliverable: if the chart-pullback `F : ℂ → ℂ` is analytic on a
  preconnected open set `U` that contains the chart image `z₀` of `x` and also
  some other point `z₁` whose `F`-value differs from `c`, then the chart pullback
  is not eventually equal to `c` at `z₀`. This is exactly the `hFne` hypothesis
  in `ChartPullbackData`.

* `chart_pullback_not_eventually_const_of_witness` — packaging of the previous
  lemma against `¬ IsConstantMap f` together with a chart-witness: if `f` is
  non-constant *as observed inside the chart* (i.e., the chart pullback takes a
  value other than `c` somewhere on the connected chart domain `U`), then the
  pullback is not eventually `c` at the chart image of any `x ∈ U`.

What this file does **not** do (still open for full manifold globalisation):

* Walking analytic continuation along a path in a connected complex manifold
  `X` to get from "`f` non-constant on `X`" to "the chart pullback at every
  fibre point is non-constant on its chart". The standard argument is:

      pick `x₁, x₂ ∈ X` with `f x₁ ≠ f x₂` (exists by `¬ IsConstantMap f`),
      pick a path γ : [0,1] → X from any candidate `x` to one of `x₁, x₂` whose
        chart pullback witnesses non-constancy,
      cover γ([0,1]) by finitely many charts and chain
        `eqOn_of_preconnected_of_eventuallyEq` across overlaps.

  This requires `PathConnectedSpace X` (which follows from
  `ConnectedSpace + LocallyPathConnectedSpace`, the latter true for manifolds)
  plus the chart-overlap analyticity bridge. The path-walking step is plain
  topology once the chart-overlap analyticity is in hand, but the
  chart-overlap analyticity itself is deferred by ZZ24 (the `ContMDiff … ω →
  AnalyticAt` bridge on chart pullbacks). Until ZZ24 lands, the within-one-chart
  version is the right granularity for this file.
-/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## ℂ-analytic core: identity theorem against a constant -/

/-- **Identity theorem against a constant.** If `F : ℂ → ℂ` is analytic on a
preconnected open set `U` and is eventually equal to `c` at some `z₀ ∈ U`, then
`F = c` everywhere on `U`. This is mathlib's
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` against `g := fun _ => c`. -/
lemma eqOn_const_of_preconnected_of_eventuallyEq
    {F : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ} {c : ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hU : IsPreconnected U) (h₀ : z₀ ∈ U)
    (hev : ∀ᶠ z in 𝓝 z₀, F z = c) :
    EqOn F (fun _ => c) U := by
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => c) U := analyticOnNhd_const
  have hev' : F =ᶠ[𝓝 z₀] (fun _ : ℂ => c) := hev
  exact hF.eqOn_of_preconnected_of_eventuallyEq hg hU h₀ hev'

/-- **Contrapositive: not eventually constant from a witness of non-constancy.**
If `F` is analytic on a preconnected open set `U`, takes a value other than `c`
at some point `z₁ ∈ U`, and `z₀ ∈ U`, then `F` is not eventually `c` at `z₀`. -/
lemma not_eventually_const_of_not_constOn
    {F : ℂ → ℂ} {U : Set ℂ} {z₀ z₁ : ℂ} {c : ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hU : IsPreconnected U)
    (h₀ : z₀ ∈ U) (h₁ : z₁ ∈ U) (h_ne : F z₁ ≠ c) :
    ¬ ∀ᶠ z in 𝓝 z₀, F z = c := by
  intro hev
  have h_eqOn : EqOn F (fun _ => c) U :=
    eqOn_const_of_preconnected_of_eventuallyEq hF hU h₀ hev
  have h_at_z1 : F z₁ = c := h_eqOn h₁
  exact h_ne h_at_z1

/-! ## Chart-pullback wrapper: within-one-chart globalisation -/

/-- **Chart-pullback witness of non-constancy.** Encapsulates the data needed
to apply `not_eventually_const_of_not_constOn` to a chart pullback `F` of a
map `f : X → Y`:

* `U : Set ℂ` — preconnected open set (the chart domain in ℂ),
* `F : ℂ → ℂ` — the chart pullback,
* `c : ℂ` — the chart image of the target value `y₀`,
* `hFA` — `F` is analytic on `U`,
* `hU_pc` — `U` is preconnected,
* `z₁ ∈ U` — a witness point inside the chart where the pullback differs from `c`.

`z₁` plays the role of "non-constancy is observed inside this chart". The
existence of such a `z₁` is the in-chart version of `¬ IsConstantMap f`.
-/
structure ChartNonConstWitness where
  /-- The chart domain in ℂ. -/
  U : Set ℂ
  /-- The chart pullback of `f`. -/
  F : ℂ → ℂ
  /-- The chart image of `y₀`. -/
  c : ℂ
  /-- Analyticity of `F` on `U`. -/
  hFA : AnalyticOnNhd ℂ F U
  /-- `U` is preconnected. -/
  hU_pc : IsPreconnected U
  /-- A witness point with `F z₁ ≠ c`. -/
  z₁ : ℂ
  hz₁ : z₁ ∈ U
  hFz₁ : F z₁ ≠ c

/-- **Within-one-chart globalisation of "not eventually `c`".** From a chart
non-constancy witness, the pullback `F` is not eventually equal to `c` at any
point `z₀` of the chart domain `U`. This is the `hFne` ingredient required by
`ChartPullbackData` in `AnalyticFiberDiscrete.lean`. -/
lemma chart_pullback_not_eventually_const_within_chart
    (W : ChartNonConstWitness) {z₀ : ℂ} (hz₀ : z₀ ∈ W.U) :
    ¬ ∀ᶠ z in 𝓝 z₀, W.F z = W.c :=
  not_eventually_const_of_not_constOn
    W.hFA W.hU_pc hz₀ W.hz₁ W.hFz₁

/-! ## Composition with `AnalyticFiberDiscrete`

We provide a single composition lemma that, given a within-one-chart
non-constancy witness for every fibre point, produces the `hFne` argument
required by `ChartPullbackData`. The chart-domain `U`, the analytic
representative `F`, and the target chart-value `c` are bookkept by the
witness; the consumer only needs to plug `z₀` (the chart image of the fibre
point) into the resulting `¬ ∀ᶠ` statement.

This is the maximal local-only deliverable: it does *not* claim to derive the
witness from `¬ IsConstantMap f` globally — that step requires walking
analytic continuation across charts, which is deferred.
-/

/-- **Composition contract.** A "chart non-constancy witness assignment" is a
function that to every fibre point `x ∈ f ⁻¹' {y₀}` associates a chart
non-constancy witness whose chart domain `U` contains the chart image of `x`.
This is the precise local datum needed to satisfy `ChartPullbackData.hFne`. -/
structure FibreChartNonConstAssignment {X : Type u} [TopologicalSpace X]
    {Y : Type v} (f : X → Y) (y₀ : Y) where
  /-- For each fibre point, a chart non-constancy witness. -/
  witness : ∀ x, f x = y₀ → ChartNonConstWitness
  /-- The chart image of `x` (inside ℂ). -/
  chartImage : X → ℂ
  /-- Membership of the chart image in the chart domain. -/
  chartImage_mem : ∀ x (hx : f x = y₀),
    chartImage x ∈ (witness x hx).U

/-- **Discharge of `hFne` from a fibre-chart non-constancy assignment.** For
every fibre point, the chart pullback is not eventually equal to its target
chart-value at the chart image. This is the input shape consumed by
`ChartPullbackData.hFne`. -/
lemma not_eventually_const_at_chartImage
    {X : Type u} [TopologicalSpace X]
    {Y : Type v}
    {f : X → Y} {y₀ : Y}
    (A : FibreChartNonConstAssignment f y₀)
    (x : X) (hx : f x = y₀) :
    ¬ ∀ᶠ z in 𝓝 (A.chartImage x), (A.witness x hx).F z = (A.witness x hx).c :=
  chart_pullback_not_eventually_const_within_chart
    (A.witness x hx) (A.chartImage_mem x hx)

/-! ## Documentation: full manifold globalisation, what is still open

Let `X, Y` be connected complex manifolds and `f : X → Y` analytic and
non-constant. To produce a `FibreChartNonConstAssignment`, we need: for every
`x ∈ f ⁻¹' {y₀}`, a connected chart of `X` around `x` together with a
witness point `z₁` in that chart's image where the chart pullback differs
from `c := chart_Y(y₀)`.

The argument is:

1.  By `¬ IsConstantMap f`, pick `x* : X` with `f x* ≠ y₀`.
2.  By connectedness of `X`, there is a path γ from `x` to `x*`.
3.  Cover γ([0,1]) by finitely many connected charts. In the chart containing
    `x*`, the chart pullback takes value `chart_Y(f x*) ≠ chart_Y(y₀)` at the
    chart image of `x*`. So there is a witness `z₁` in that chart.
4.  In the chart containing `x`, suppose for contradiction that the chart
    pullback is identically `c` on the whole chart domain `U_x` (this is the
    "eventually constant" case extended via mathlib's identity theorem to
    "constant on `U_x`"). Walk along γ via overlapping charts: on each
    overlap, the chart pullbacks agree up to chart-transition (this is where
    ZZ24's `ContMDiff … ω → AnalyticAt` bridge is needed), so by the identity
    theorem the pullback is constant on the next chart's domain too. By
    finiteness of the cover we reach the chart containing `x*` and conclude
    the pullback is constant there — contradicting step 3.

Step 4 requires:

    (a) the chart-transition maps are `AnalyticOn` ℂ on overlaps (mathlib,
        for `IsManifold 𝓘(ℂ) ω`);
    (b) the chart pullback in any chart is `AnalyticOnNhd` on the chart
        domain (this is **ZZ24**, the `ContMDiff … ω → AnalyticAt` bridge);
    (c) chart overlap is open and connected after intersecting with a path
        tube, which is plain topology.

(a) is in mathlib at the pin (analytic structure on `IsManifold … ω`); (c) is
plain topology; (b) is deferred by ZZ24. Once ZZ24 lands, the path-walking step
is straightforward and produces a `FibreChartNonConstAssignment` from
`¬ IsConstantMap f` plus connectedness, completing the manifold-level
globalisation.

Until ZZ24 lands, packaging the witness as a parameter (which is what
`FibreChartNonConstAssignment` does) is the right granularity: it isolates
the locally-derivable identity-theorem content (this file) from the
chart-overlap analyticity content (ZZ24).
-/

end Degree
end ContMDiff
end Jacobians.Discharge
