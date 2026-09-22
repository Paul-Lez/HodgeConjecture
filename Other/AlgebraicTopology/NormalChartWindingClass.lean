/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.NormalChartWindingValue
public import Other.AlgebraicTopology.WindingRelativeClass

/-!
# Identifying the winding class in a normal chart

The winding cocycle of the normal coordinate evaluates to `1` on the literal normal relative
cycle.  The existing local-purity uniqueness principle therefore identifies its resulting
relative singular class with the normalized normal-projection coclass.  This is a direct
normalization calculation, not an invocation of a Chern- or cycle-class correspondence.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial AlgebraicTopology.Singular

namespace ChernWinding

variable {M : Type} [TopologicalSpace M] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (e : OpenPartialHomeomorph M (E × (Fin 1 → ℂ))) {S : Set M}
  (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
  (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)

/-- The normal coordinate, written as an actual continuous function on the punctured chart
neighborhood. -/
def flattenedNormalCoordinate : C(puncturedSpace
    ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S, ℂ) :=
  complexLineCoordinate.comp (topMap (flattenedNormalProjection E e S hS x hx).left)

lemma flattenedNormalCoordinate_ne_zero : ∀ z,
    flattenedNormalCoordinate E e hS x hx z ≠ 0 := by
  intro z
  change complexLineCoordinate ((flattenedNormalProjection E e S hS x hx).left z) ≠ 0
  exact complexLineCoordinate_ne_zero _

set_option maxHeartbeats 1000000 in
include h0 in
/-- The relative class defined by the literal winding cochain of a normal coordinate is the
normalized local coclass. -/
theorem windingRelativeClass_eq_chartNormalProjectionCoclass
    (g : C(puncturedSpace
      ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S, ℂ))
    (hg : ∀ y, g y ≠ 0)
    (hcoord : ∀ w, g w =
      complexLineCoordinate ((flattenedNormalProjection E e S hS x hx).left w)) :
    windingRelativeClass
      ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S g hg =
      chartNormalProjectionCoclass E 1 e S hS (flattenedSupportNeighborhood E 1 e x hx)
        (flattenedSupportNeighborhood_subset_source E 1 e x hx) := by
  apply chartNormalProjectionCoclass_unique E 1 e S hS x hx h0
  rw [windingRelativeClass_apply]
  have hperiod := LinearMap.congr_fun (rationalPeriod_windingRationalPeriod g hg)
    ((relativeSingularBoundary
      (supportPair ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M)
        S) 1).hom (flattenedSupportNormalClass E 1 e x hx S hS h0))
  have hnormal : windingPeriod g hg
      ((relativeSingularBoundary
        (supportPair ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M)
          S) 1).hom (flattenedSupportNormalClass E 1 e x hx S hS h0)) = 1 :=
    windingPeriod_flattenedNormalClass E e S hS x hx h0 g hg hcoord
  rw [hnormal] at hperiod
  change ((windingRationalPeriod g hg
    ((relativeSingularBoundary
      (supportPair ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M)
        S) 1).hom (flattenedSupportNormalClass E 1 e x hx S hS h0)) : ℚ) : ℂ) = 1 at hperiod
  exact_mod_cast hperiod

include h0 in
/-- The relative singular class obtained from the displayed normal-coordinate winding cochain is
the normalized local class used by the support construction. -/
theorem flattenedNormalCoordinate_class_eq_chartNormalProjectionCoclass :
    windingRelativeClass
      ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S
      (flattenedNormalCoordinate E e hS x hx)
      (flattenedNormalCoordinate_ne_zero E e hS x hx) =
      chartNormalProjectionCoclass E 1 e S hS (flattenedSupportNeighborhood E 1 e x hx)
        (flattenedSupportNeighborhood_subset_source E 1 e x hx) :=
  windingRelativeClass_eq_chartNormalProjectionCoclass E e hS x hx h0
    (flattenedNormalCoordinate E e hS x hx)
    (flattenedNormalCoordinate_ne_zero E e hS x hx) (by intro w; rfl)

include h0 in
/-- The actual relative mapping-cone cocycle `(0, windingIndex)` of the normal coordinate
represents the normalized local support coclass.  The proof is the explicit boundary-winding
calculation above, not a cycle-class or Chern-class comparison. -/
theorem flattenedNormalCoordinate_cochainClass_eq_chartNormalProjectionCoclass :
    windingRelativeCochainClass
      (X := supportPair
        ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S)
      (flattenedNormalCoordinate E e hS x hx)
      (flattenedNormalCoordinate_ne_zero E e hS x hx) =
      chartNormalProjectionCoclass E 1 e S hS (flattenedSupportNeighborhood E 1 e x hx)
        (flattenedSupportNeighborhood_subset_source E 1 e x hx) := by
  rw [windingRelativeCochainClass_eq_windingRelativeClass]
  exact flattenedNormalCoordinate_class_eq_chartNormalProjectionCoclass E e hS x hx h0

end ChernWinding
