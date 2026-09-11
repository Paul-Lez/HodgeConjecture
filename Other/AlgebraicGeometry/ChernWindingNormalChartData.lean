/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingNormalChartClass
public import Other.AlgebraicGeometry.ChernWindingChartPeriods

/-!
# Normal winding charts, and the proof of `NormalizesCoclass`

`NormalWindingChartData X c x d q` refines `GeometricWindingChartData` by pinning the analytic
chart down to a **flattening chart** of the component at `q`, whose normal coordinate is the
analytified local equation:

* `chart` is a holomorphic chart of `X^an` at `q` with values in `(ℂ^{d-1}) × ℂ` that flattens the
  component (`flattens`) and is centred on it (`center`);
* the chart open is the repository's `flattenedSupportNeighborhood` of that chart, so all the
  normalisation machinery of `NormalProjectionCoclass.lean` applies to it verbatim;
* `normal_coordinate` says that the analytified local equation of the Cartier datum *is* the
  normal coordinate of the chart;
* `coclass_restrict` says that the restriction of the repository's glued coclass section to the
  chart open is the chart's own normal-projection coclass.

From these, `NormalWindingChartData.normalizesCoclass` **proves** obligation (c),
`ChernWindingChart.NormalizesCoclass`: the two inputs are
`ChernWinding.windingClass_eq_chartNormalProjectionCoclass` (the Lelong–Poincaré computation, with
the sign `+1`) and `coclass_restrict`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Order AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernWindingNormalChartDataTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable (c : Scheme.CartierData X.left) (x : X.left) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- Geometric chart data pinned to a flattening chart of the component whose normal coordinate is
the analytified local equation. -/
structure NormalWindingChartData (q : ComplexPoint X) where
  /-- index of a member of the Cartier cover containing `x` -/
  index : c.ι
  /-- the algebraic local form of the Cartier datum at `x` -/
  localForm : c.LocalForm index x
  /-- a holomorphic chart flattening the component of `x` -/
  chart : OpenPartialHomeomorph (ComplexPoint X) ((Fin (d - 1) → ℂ) × (Fin 1 → ℂ))
  mem_source : q ∈ chart.source
  /-- the chart flattens the component onto `{normal = 0}` -/
  flattens : ∀ y ∈ chart.source, y ∈ cycleComponentSupport X x ↔ (chart y).2 = 0
  /-- the chart is centred on the component -/
  center : (chart q).2 = 0
  le : flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source ≤
    cycleComponentSmoothSupportAmbientOpen X x
  le_analytic : flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source ≤
    analyticOpen X localForm.opens
  /-- the analytified local equation, as a unit on the punctured chart -/
  coord : (holomorphicUnitSheaf X d).obj.obj
    (op (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source ⊓
      (cycleComponentAnalyticClosedSupport X x).compl))
  coord_eq : ((Additive.toMul coord).val :
      (holomorphicRingSheaf X d).obj.obj
        (op (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source ⊓
          (cycleComponentAnalyticClosedSupport X x).compl))) =
    (holomorphicRingSheaf X d).obj.map
      (homOfLE (le_trans inf_le_left le_analytic)).op
      (analyticFunction X d localForm.opens localForm.equation)
  /-- every invertible holomorphic function on the chart is an exponential -/
  exists_log : ∀ u : (holomorphicUnitSheaf X d).obj.obj
      (op (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source)),
    ∃ f : (holomorphicAdditiveSheaf X d).obj.obj
      (op (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source)),
      (holomorphicExponential X d).hom.app
        (op (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source)) f = u
  /-- **the analytified local equation is the normal coordinate of the chart** -/
  normal_coordinate : ∀ w, windingUnitFunction X d
      (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source)
      (cycleComponentAnalyticClosedSupport X x) coord w =
    ChernWinding.complexLineCoordinate
      ((ChernWinding.flattenedNormalProjection (Fin (d - 1) → ℂ) chart
        (cycleComponentSupport X x) flattens q mem_source).left w)
  /-- **the glued coclass section restricts to the chart's normal-projection coclass** -/
  coclass_restrict : ∀ hx : coheight x = ((1 : ℕ) : ℕ∞),
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)).obj.map (homOfLE le).op
        (cycleComponentSmoothSupportCoclassSection X x (d := d) hx) =
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)).app
        (op (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source))
        (chartNormalProjectionCoclass (Fin (d - 1) → ℂ) 1 chart (cycleComponentSupport X x)
          flattens (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source)
          (flattenedSupportNeighborhood_subset_source (Fin (d - 1) → ℂ) 1 chart q mem_source))

namespace NormalWindingChartData

variable {X c x d} {q : ComplexPoint X} (G : NormalWindingChartData X c x d q)

/-- The underlying geometric winding chart data. -/
def toGeometric : GeometricWindingChartData X c x d q where
  index := G.index
  localForm := G.localForm
  carrier := flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 G.chart q G.mem_source
  mem := mem_flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 G.chart q G.mem_source
  le := G.le
  le_analytic := G.le_analytic
  coord := G.coord
  coord_eq := G.coord_eq
  exists_log := G.exists_log

/-- The winding chart determined by normal chart data. -/
abbrev toChart : ChernWindingChart X c x d 1 q := G.toGeometric.toChart

set_option maxHeartbeats 1000000 in
/-- **Obligation (c), proved.**  The constructed winding homomorphism of a normal winding chart
sends the analytified local equation to the normalised normal-chart coclass. -/
theorem normalizesCoclass (hx : coheight x = ((1 : ℕ) : ℕ∞)) :
    G.toChart.NormalizesCoclass hx := by
  show windingSheafHom
      (hasWindingPeriods X d (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 G.chart q
        G.mem_source) (cycleComponentAnalyticClosedSupport X x)) G.coord = _
  rw [windingSheafHom_apply]
  refine Eq.trans ?_ (G.coclass_restrict hx).symm
  congr 1
  exact ChernWinding.windingClass_eq_chartNormalProjectionCoclass (Fin (d - 1) → ℂ) G.chart
    G.flattens q G.mem_source G.center _ _ G.normal_coordinate

end NormalWindingChartData

end AlgebraicGeometry.ComplexPoint
