/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingNormalChartData
public import Other.AlgebraicGeometry.ChernWindingNormalChartLog

/-!
# Existence of normal winding charts off a proper closed subset of the component

`NormalWindingChartData.normalizesCoclass` proves obligation (c) for a normal winding chart, and
`WindingChartData.hasTrivialUnitWinding` proves obligation (b) for any winding chart built from
the constructed winding homomorphism.  What is left is the *existence* of normal winding chart
data, and — as `Other/AlgebraicGeometry/ChernWindingLocalFormObstruction.lean` shows — it can only
be asked for off a proper closed subset of the component `Z_x`, because the affine open of a
`LocalForm` never meets another component of the divisor.

This file states that residual obligation, `HasNormalFlatteningCharts`, in the `∃ B` shape, and
proves that it gives normalised winding charts off `B`
(`exists_closed_normalizedWindingCharts`).  It also records that the `exists_log` field of the
chart data is automatic (`exists_log_of_flattening`), so that `HasNormalFlatteningCharts` really
asks only for:

1. an algebraic local form of `c` at `x` whose affine open contains `q` — possible exactly off the
   other components of `|D|`, which meet `Z_x` in a closed subset of codimension at least two in
   `X`, hence in a proper closed subset of `Z_x`;
2. a holomorphic chart at `q` flattening `Z_x`, small enough, **whose normal coordinate is the
   analytified local equation** — possible exactly where the differential of the local equation is
   nonzero along the normal direction, again off a proper closed subset of `Z_x`; and
3. the identification of the restriction of the repository's glued coclass section with the
   chart's own normal-projection coclass (`coclass_restrict`) — a transport statement about
   `cycleComponentSmoothSupportCoclassSection`, with no new geometry in it.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Order AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernWindingNormalChartExistenceTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {X}

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- The `exists_log` field of `NormalWindingChartData` is automatic: a flattened-support
neighbourhood is homeomorphic to a vector space, hence simply connected and locally path
connected. -/
theorem exists_log_of_flattening {d : ℕ} [SmoothOfRelativeDimension d X.hom]
    {q : ComplexPoint X}
    (chart : OpenPartialHomeomorph (ComplexPoint X) ((Fin (d - 1) → ℂ) × (Fin 1 → ℂ)))
    (mem_source : q ∈ chart.source) :
    ∀ u : (holomorphicUnitSheaf X d).obj.obj
        (op (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source)),
      ∃ f : (holomorphicAdditiveSheaf X d).obj.obj
        (op (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source)),
        (holomorphicExponential X d).hom.app
          (op (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source)) f = u :=
  fun u => exists_holomorphicExponential_flattenedSupportNeighborhood
    (Fin (d - 1) → ℂ) 1 chart q mem_source u

/-- **The residual obligation.**  Off a proper closed subset of the component, normal winding
chart data exists.

The closed subset `B` must be allowed: by
`AlgebraicGeometry.ComplexPoint.exists_chernWindingChart_imp_divisor_eq_zero` no winding chart
whatsoever exists at a point lying on a second component of `|D|`. -/
def HasNormalFlatteningCharts : Prop :=
  ∀ (c : Scheme.CartierData X.left) (x : X.left), coheight x = ((1 : ℕ) : ℕ∞) →
    ∃ B : Set X.left, IsClosed B ∧ B ⊆ closure ({x} : Set X.left) ∧ x ∉ B ∧
      ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x, q ∈ cycleComponentSupport X x →
        Point.underlying q ∉ B →
        Nonempty (NormalWindingChartData X c x (dim X.left) q)

/-- **The `∃ B` form of the winding-chart obligation.**  Normal flattening charts give normalised
winding charts at every point of the component off a proper closed subset. -/
theorem exists_closed_normalizedWindingCharts (h : HasNormalFlatteningCharts (X := X))
    (c : Scheme.CartierData X.left) (x : X.left) (hx : coheight x = ((1 : ℕ) : ℕ∞)) :
    ∃ B : Set X.left, IsClosed B ∧ B ⊆ closure ({x} : Set X.left) ∧ x ∉ B ∧
      ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x, q ∈ cycleComponentSupport X x →
        Point.underlying q ∉ B →
        ∃ ch : ChernWindingChart X c x (dim X.left) 1 q,
          ch.HasTrivialUnitWinding ∧ ch.NormalizesCoclass hx := by
  obtain ⟨B, hBclosed, hBsub, hxB, hcharts⟩ := h c x hx
  refine ⟨B, hBclosed, hBsub, hxB, fun q hq hqS hqB => ?_⟩
  obtain ⟨G⟩ := hcharts q hq hqS hqB
  exact ⟨G.toChart, G.toGeometric.hasTrivialUnitWinding, G.normalizesCoclass hx⟩

end AlgebraicGeometry.ComplexPoint
