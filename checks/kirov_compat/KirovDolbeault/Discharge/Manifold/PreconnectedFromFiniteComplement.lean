/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Separation.Basic

/-! # Path-connected ⇒ preconnected reduction for the finite-puncture
case (ZZ159, scope-reduced)

For a connected complex 1-manifold `Y`, the complement of any finite set
is preconnected. This is the standard "go around the puncture" fact —
content `(M1)`: the path-connectedness of `Cᶜ` for finite `C` on a
connected 2-manifold.

`(M1)` itself is **not in mathlib at the project pin**
(`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`, lean v4.30.0-rc1). The
relevant ambient lemma — `Set.Countable.isPathConnected_compl_of_one_lt_rank`
in `Mathlib.Analysis.Normed.Module.Connected` — gives this for normed
ℝ-spaces of real rank ≥ 2 but does not lift through a chart structure.
A genuine manifold proof needs (a) local path-connectedness of `Y` from
`ChartedSpace ℂ Y` (mathlib's `ChartedSpace.locPathConnectedSpace` —
present, but as a theorem requiring `[LocPathConnectedSpace H]`) plus
(b) the chart-by-chart "go around" routing — not present.

This file therefore lands the **reduction-only headline**: given the
unproven manifold-lift `h_path` (`(M1)`), preconnectedness of the finite
complement follows. Downstream consumers (`ZZ160`) instantiate `h_path`
either via the missing manifold-lift content (when present) or — for
the strict-closure path of items 8/9/22/24 — re-package as an explicit
named hypothesis on the closure theorem.

No gaps, no `axiom`. -/

@[expose] public section

namespace Jacobians.Discharge
namespace Manifold

universe u

/-- **Reduction-only headline.** Given the path-connectedness of `Cᶜ`
(the manifold-lift content `(M1)`), preconnectedness follows.

Used by `RegularSubsetPreconnected.lean`'s `h_topo` parameter via the
convenience wrapper `h_topo_of_h_path` below. -/
theorem isPreconnected_compl_finite_of_isPathConnected
    {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    {C : Set Y} (_hC : C.Finite)
    (h_path : (Cᶜ : Set Y).Nonempty → IsPathConnected (Cᶜ : Set Y)) :
    IsPreconnected (Cᶜ : Set Y) := by
  by_cases h : (Cᶜ : Set Y) = ∅
  · rw [h]; exact isPreconnected_empty
  · have hne : (Cᶜ : Set Y).Nonempty := Set.nonempty_iff_ne_empty.mpr h
    exact (h_path hne).isConnected.isPreconnected

/-- **Convenience composition.** Provides the `h_topo` shape that
`RegularSubsetPreconnected.lean`'s reduction consumes, conditional on
the manifold-lift path-connectedness `h_path`. -/
theorem h_topo_of_h_path
    {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    (h_path : ∀ C : Set Y, C.Finite → (Cᶜ : Set Y).Nonempty →
      IsPathConnected (Cᶜ : Set Y)) :
    ∀ C : Set Y, C.Finite → IsPreconnected (Cᶜ : Set Y) := by
  intro C hC
  exact isPreconnected_compl_finite_of_isPathConnected hC (h_path C hC)

end Manifold
end Jacobians.Discharge
