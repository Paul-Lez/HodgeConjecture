/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingGenericChartData
public import Other.AlgebraicGeometry.ChernWindingNormalChartExistence

/-!
# What is left of the winding-chart obligation

`GenericWindingChartData X c x d q` is `GeometricWindingChartData` with the analytic chart pinned
to a flattening chart of the component at `q`, together with

* `normal_coordinate`: the analytified local equation is the normal coordinate of that chart **up
  to a nowhere vanishing factor on the whole chart neighbourhood** (this is the content of "the
  local equation generates the ideal of the component near `q`"; no implicit function theorem is
  needed, because a unit contributes nothing to the winding class —
  `ChernWinding.windingClass_eq_chartNormalProjectionCoclass_of_unit`), and
* `coclass_restrict`: the restriction of the repository's glued coclass section to the chart
  neighbourhood is the chart's own normal-projection coclass.

`GenericWindingChartData.normalizesCoclass` proves obligation (c) from these, and
`hasGeometricWindingCharts_of_genericFlatteningCharts` /
`hasNormalizedWindingCharts_of_genericFlatteningCharts` below turn their existence — off a
Zariski-closed subset `B` of the component not containing its generic point, as the obstruction of
`ChernWindingLocalFormObstruction.lean` forces — into the two obligations of §4.3 step 4 item 3 in
their current `∃ B` form.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Order AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernWindingGenericChartExistenceTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {X}

/-- **The residual obligation of §4.3 step 4 item 3 (b) + (c).**  Off a Zariski-closed subset of
the component not containing its generic point, generic winding chart data exists. -/
def HasGenericFlatteningCharts : Prop :=
  ∀ (c : Scheme.CartierData X.left) (x : X.left), coheight x = ((1 : ℕ) : ℕ∞) →
    ∃ B : Closeds X.left, (B : Set X.left) ⊆ closure ({x} : Set X.left) ∧ x ∉ B ∧
      ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x, q ∈ cycleComponentSupport X x →
        Point.underlying q ∉ B →
        Nonempty (GenericWindingChartData X c x (dim X.left) q)

/-- **Obligation (b) + (c) reduce to `HasGenericFlatteningCharts`.** -/
theorem hasGeometricWindingCharts_of_genericFlatteningCharts
    (h : HasGenericFlatteningCharts (X := X)) : HasGeometricWindingCharts (X := X) := by
  intro c x hx
  obtain ⟨B, hBsub, hxB, hcharts⟩ := h c x hx
  refine ⟨B, hBsub, hxB, fun q hq hqS hqB => ?_⟩
  obtain ⟨G⟩ := hcharts q hq hqS hqB
  exact ⟨G.toGeometric, G.normalizesCoclass hx⟩

/-- The same, spelled out for `HasNormalizedWindingCharts`. -/
theorem hasNormalizedWindingCharts_of_genericFlatteningCharts
    (h : HasGenericFlatteningCharts (X := X)) : HasNormalizedWindingCharts X :=
  hasNormalizedWindingCharts_of_geometricWindingCharts
    (hasGeometricWindingCharts_of_genericFlatteningCharts h)

end AlgebraicGeometry.ComplexPoint
