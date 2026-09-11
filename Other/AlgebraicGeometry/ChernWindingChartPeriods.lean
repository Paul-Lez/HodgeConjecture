/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingRational
public import Other.AlgebraicGeometry.ChernWindingNormalizedCharts

/-!
# The rationality hypothesis of a winding chart is automatic

`AlgebraicGeometry.ComplexPoint.HasWindingPeriods` — the rationality of the winding periods on a
chart, which was the one hypothesis of the construction of the winding homomorphism — is now a
**theorem** (`ChernWinding.hasRationalWindingPeriod`, `ChernWindingRational.lean`).

Consequently `WindingChartData` may be replaced by `GeometricWindingChartData`, which contains
only geometric data: an algebraic local form of the Cartier datum, an analytic chart inside the
smooth-support open and inside the analytification of the local form's affine open, the
analytified local equation, and the existence of a holomorphic logarithm on the chart.  The
reduction

  `hasNormalizedWindingCharts_of_geometricWindingCharts :
      HasGeometricWindingCharts X → HasNormalizedWindingCharts X`

therefore leaves exactly two obligations per chart: the *existence* of the chart data and the
normalisation `NormalizesCoclass`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Order AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

/-- **The rationality of the winding periods on a chart is automatic.** -/
theorem hasWindingPeriods (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (V : Opens (TopCat.of (ComplexPoint X)))
    (S : Closeds (ComplexPoint (X := X))) :
    HasWindingPeriods X d V S :=
  fun _ => ChernWinding.hasRationalWindingPeriod _ _ _ _

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernWindingChartPeriodsTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable (c : Scheme.CartierData X.left) (x : X.left) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- Purely geometric winding chart data: `WindingChartData` with the (now automatic) rationality
of the winding periods removed. -/
structure GeometricWindingChartData (q : ComplexPoint X) where
  /-- index of a member of the Cartier cover containing `x` -/
  index : c.ι
  /-- the algebraic local form of the Cartier datum at `x` -/
  localForm : c.LocalForm index x
  /-- the analytic chart -/
  carrier : Opens (ComplexPoint X)
  mem : q ∈ carrier
  le : carrier ≤ cycleComponentSmoothSupportAmbientOpen X x
  le_analytic : carrier ≤ analyticOpen X localForm.opens
  /-- the analytified local equation, as a unit on the punctured chart -/
  coord : (holomorphicUnitSheaf X d).obj.obj
    (op (carrier ⊓ (cycleComponentAnalyticClosedSupport X x).compl))
  coord_eq : ((Additive.toMul coord).val :
      (holomorphicRingSheaf X d).obj.obj
        (op (carrier ⊓ (cycleComponentAnalyticClosedSupport X x).compl))) =
    (holomorphicRingSheaf X d).obj.map
      (homOfLE (le_trans inf_le_left le_analytic)).op
      (analyticFunction X d localForm.opens localForm.equation)
  /-- every invertible holomorphic function on the chart is an exponential -/
  exists_log : ∀ u : (holomorphicUnitSheaf X d).obj.obj (op carrier),
    ∃ f : (holomorphicAdditiveSheaf X d).obj.obj (op carrier),
      (holomorphicExponential X d).hom.app (op carrier) f = u

namespace GeometricWindingChartData

variable {X c x d} {q : ComplexPoint X} (G : GeometricWindingChartData X c x d q)

/-- Geometric chart data is winding chart data: the rationality of the periods is automatic. -/
def toWindingChartData : WindingChartData X c x d q where
  index := G.index
  localForm := G.localForm
  carrier := G.carrier
  mem := G.mem
  le := G.le
  le_analytic := G.le_analytic
  coord := G.coord
  coord_eq := G.coord_eq
  exists_log := G.exists_log
  hasWindingPeriods := hasWindingPeriods X d G.carrier _

/-- The winding chart determined by geometric data. -/
abbrev toChart : ChernWindingChart X c x d 1 q := G.toWindingChartData.toChart

/-- Obligation (b) for a geometric chart. -/
theorem hasTrivialUnitWinding : G.toChart.HasTrivialUnitWinding :=
  G.toWindingChartData.hasTrivialUnitWinding

end GeometricWindingChartData

variable {X}

/-- **What is left of `HasNormalizedWindingCharts`.**  Purely geometric chart data at every point
of the smooth-support open lying on the component, whose constructed winding homomorphism
normalises the coclass. -/
def HasGeometricWindingCharts : Prop :=
  ∀ (c : Scheme.CartierData X.left) (x : X.left) (hx : coheight x = ((1 : ℕ) : ℕ∞)),
    ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x, q ∈ cycleComponentSupport X x →
      ∃ G : GeometricWindingChartData X c x (dim X.left) q, G.toChart.NormalizesCoclass hx

/-- **The reduction.** -/
theorem hasNormalizedWindingCharts_of_geometricWindingCharts
    (h : HasGeometricWindingCharts (X := X)) : HasNormalizedWindingCharts X := by
  intro c x hx q hq hqS
  obtain ⟨G, hG⟩ := h c x hx q hq hqS
  exact ⟨G.toChart, G.hasTrivialUnitWinding, hG⟩

end AlgebraicGeometry.ComplexPoint
