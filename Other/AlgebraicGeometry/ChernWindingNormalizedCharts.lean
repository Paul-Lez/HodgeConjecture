/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingUnitClass

/-!
# Winding charts whose winding homomorphism is constructed

`AlgebraicGeometry.ComplexPoint.ChernWindingChart` carries the winding homomorphism as *data*,
because when it was written the repository had neither the connecting map of the exponential
sequence nor the connecting map of a pair.  Both are now constructed
(`ChernWinding.relativeWindingPeriod`, `AlgebraicGeometry.ComplexPoint.windingSheafHom`), so a
chart can be produced from purely geometric data:

`WindingChartData X c x d q` is a chart in which the winding homomorphism has been *removed* and
replaced by `HasWindingPeriods`, the rationality of the winding periods.  Its associated chart
`WindingChartData.toChart` always satisfies `ChernWindingChart.HasTrivialUnitWinding`
(`WindingChartData.hasTrivialUnitWinding`), which was obligation **(b)** of §4.3 step 4 item 3 of
`docs/DIVISOR_HANDOFF.md`: the proof is that a unit on the chart which is an exponential there is
an exponential on the punctured chart too, and the winding class of an exponential vanishes.

Consequently `HasNormalizedWindingCharts X` follows from `HasWindingChartData X`, which asks only
for geometric charts satisfying the *normalisation* condition **(c)**.  Obligation (b) has
disappeared.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Order AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernWindingNormalizedChartsTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable (c : Scheme.CartierData X.left) (x : X.left) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- A winding chart without its winding homomorphism: the geometric data of
`ChernWindingChart`, together with the rationality of the winding periods on it. -/
structure WindingChartData (q : ComplexPoint X) where
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
  /-- the winding periods on the chart are rational -/
  hasWindingPeriods :
    HasWindingPeriods X d carrier (cycleComponentAnalyticClosedSupport X x)

namespace WindingChartData

variable {X c x d} {q : ComplexPoint X} (D : WindingChartData X c x d q)

/-- The winding chart determined by the geometric data: its winding homomorphism is the
constructed one, `windingSheafHom`. -/
def toChart : ChernWindingChart X c x d 1 q where
  index := D.index
  localForm := D.localForm
  carrier := D.carrier
  mem := D.mem
  le := D.le
  le_analytic := D.le_analytic
  coord := D.coord
  coord_eq := D.coord_eq
  winding := windingSheafHom D.hasWindingPeriods
  exists_log := D.exists_log

@[simp] theorem toChart_carrier : D.toChart.carrier = D.carrier := rfl

@[simp] theorem toChart_coord : D.toChart.coord = D.coord := rfl

@[simp] theorem toChart_winding :
    D.toChart.winding = windingSheafHom D.hasWindingPeriods := rfl

/-- **Obligation (b) is now a theorem.**  The constructed winding homomorphism kills every
invertible holomorphic function that extends across the component. -/
theorem hasTrivialUnitWinding : D.toChart.HasTrivialUnitWinding := by
  intro u
  obtain ⟨f, hf⟩ := D.exists_log u
  exact windingSheafHom_restrict_eq_zero D.hasWindingPeriods u f hf

end WindingChartData

variable {X}

/-- **The remaining half of `HasNormalizedWindingCharts`.**  At every point of the smooth-support
open lying on the component there is geometric chart data whose *constructed* winding
homomorphism normalises the coclass.  Compared with `HasNormalizedWindingCharts` this drops
obligation (b) — which is now the theorem `WindingChartData.hasTrivialUnitWinding` — and replaces
the assumed winding homomorphism by the rationality of the winding periods. -/
def HasWindingChartData : Prop :=
  ∀ (c : Scheme.CartierData X.left) (x : X.left) (hx : coheight x = ((1 : ℕ) : ℕ∞)),
    ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x, q ∈ cycleComponentSupport X x →
      ∃ D : WindingChartData X c x (dim X.left) q, D.toChart.NormalizesCoclass hx

/-- **The reduction.**  Geometric winding chart data give normalised winding charts. -/
theorem hasNormalizedWindingCharts_of_windingChartData (h : HasWindingChartData (X := X)) :
    HasNormalizedWindingCharts X := by
  intro c x hx q hq hqS
  obtain ⟨D, hD⟩ := h c x hx q hq hqS
  exact ⟨D.toChart, D.hasTrivialUnitWinding, hD⟩

end AlgebraicGeometry.ComplexPoint
