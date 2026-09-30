/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingNormalChartValue
public import Other.AlgebraicGeometry.ChernWindingRational

/-!
# The winding class of the normal coordinate is the normalised coclass

Combining the unconditional rationality of the winding periods
(`ChernWinding.hasRationalWindingPeriod`) with the normalisation criterion
(`ChernWinding.windingRelativeClass_eq_chartNormalProjectionCoclass`) and the computation of the
winding number of the normal coordinate (`ChernWinding.windingPeriod_flattenedNormalClass`), the
winding class of the normal coordinate of a flattening chart **is** the normalised normal-chart
coclass, with no hypothesis beyond `g` being the normal coordinate.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial AlgebraicTopology.Singular

namespace ChernWinding

variable {M : Type} [TopologicalSpace M] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (e : OpenPartialHomeomorph M (E × (Fin 1 → ℂ))) {S : Set M}
  (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
  (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)

set_option maxHeartbeats 1000000 in
include h0 in
/-- **The winding class of the normal coordinate is the normalised coclass.** -/
theorem windingClass_eq_chartNormalProjectionCoclass
    (g : C(puncturedSpace
      ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S, ℂ))
    (hg : ∀ y, g y ≠ 0)
    (hcoord : ∀ w, g w =
      complexLineCoordinate ((flattenedNormalProjection E e S hS x hx).left w)) :
    windingClass ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M)
        S g hg =
      chartNormalProjectionCoclass E 1 e S hS (flattenedSupportNeighborhood E 1 e x hx)
        (flattenedSupportNeighborhood_subset_source E 1 e x hx) :=
  windingRelativeClass_eq_chartNormalProjectionCoclass E e hS x hx h0
    (hasRationalWindingPeriod _ _ g hg)
    (windingPeriod_flattenedNormalClass E e S hS x hx h0 g hg hcoord)

end ChernWinding
