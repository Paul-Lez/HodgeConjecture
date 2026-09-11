/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingHolomorphicLog
public import Other.AlgebraicTopology.FlattenedSupportLocalHomology

/-!
# Holomorphic logarithms on a flattened-support neighbourhood

The flattened-support neighbourhood of a chart is, by construction, homeomorphic to the whole
model vector space `E × ℂ^c` (`flattenedSupportHomeomorph`), hence contractible and locally path
connected.  So `exists_holomorphicExponential_of_simplyConnected` applies to it: **the `exists_log`
field of a winding chart is automatic on a flattened-support neighbourhood.**
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace ChernWinding

variable {M : Type} [TopologicalSpace M] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (c : ℕ) (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (x : M) (hx : x ∈ e.source)

/-- The flattened-support neighbourhood is homeomorphic to the whole model vector space, viewed
as a convex subset of itself. -/
def flattenedSupportUnivHomeomorph :
    ((flattenedSupportNeighborhood E c e x hx : Opens M) : Set M) ≃ₜ
      (Set.univ : Set (E × (Fin c → ℂ))) :=
  (flattenedSupportHomeomorph E c e x hx).symm.trans (Homeomorph.Set.univ _).symm

instance flattenedSupportSimplyConnectedSpace :
    SimplyConnectedSpace ((flattenedSupportNeighborhood E c e x hx : Opens M) : Set M) :=
  simplyConnectedSpace_of_homeomorphConvex convex_univ ⟨0, trivial⟩
    (flattenedSupportUnivHomeomorph E c e x hx)

instance flattenedSupportLocallyPathConnectedSpace :
    LocallyPathConnectedSpace ((flattenedSupportNeighborhood E c e x hx : Opens M) : Set M) :=
  locallyPathConnectedSpace_of_homeomorphConvex convex_univ
    (flattenedSupportUnivHomeomorph E c e x hx)

end ChernWinding

namespace AlgebraicGeometry.ComplexPoint

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance chernWindingNormalChartLogTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- **`exists_log` is automatic on a flattened-support neighbourhood.** -/
theorem exists_holomorphicExponential_flattenedSupportNeighborhood
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin c → ℂ)))
    (z : ComplexPoint X) (hz : z ∈ e.source)
    (u : (holomorphicUnitSheaf X d).obj.obj
      (op (flattenedSupportNeighborhood E c e z hz))) :
    ∃ f : (holomorphicAdditiveSheaf X d).obj.obj
      (op (flattenedSupportNeighborhood E c e z hz)),
      (holomorphicExponential X d).hom.app
        (op (flattenedSupportNeighborhood E c e z hz)) f = u :=
  exists_holomorphicExponential_of_simplyConnected _ u

end AlgebraicGeometry.ComplexPoint
