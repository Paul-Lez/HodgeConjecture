/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.SingularLocusDimension

/-!
# Complex points of the constructed smooth decomposition

The finite algebraic decomposition induces an actual partition of complex-point sets into
the images of smooth complex schemes. The images are analytically locally closed. The
lifting assertion follows from the existing equivalence between complex points and closed
scheme points; it is not a supplied parametrization of a stratum.

No analytic triangulation, homology-dimension theorem, or frontier condition is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X Y : Scheme} (structureMap : X ⟶ Spec (.of ℂ))

local instance smoothStratificationAnalyticTopology :
    TopologicalSpace (ComplexPoint X structureMap) := Point.analyticTopology

/-- Forgetting a complex point to its underlying Zariski point is continuous for the actual
analytic topology. -/
theorem continuous_underlying_to_zariski :
    Continuous (Point.underlying : ComplexPoint X structureMap → X) := by
  rw [continuous_def]
  intro S hS
  exact Point.isOpen_overOpen ⟨S, hS⟩

/-- The complex points of a locally closed subscheme map onto exactly the complex points
whose underlying scheme point belongs to its range. -/
theorem range_map_of_isImmersion (i : Y ⟶ X)
    [IsImmersion i] [LocallyOfFiniteType structureMap] :
    Set.range (Point.map i (structureMap := i ≫ structureMap) rfl) =
      (Point.underlying : ComplexPoint X structureMap → X) ⁻¹' Set.range i := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.underlying, rfl⟩
  · rintro ⟨y, hy⟩
    have hyclosed : IsClosed ({y} : Set Y) := by
      have h := ((pointEquivClosedPoint structureMap) z).2.preimage i.continuous
      change IsClosed (i ⁻¹' ({z.underlying} : Set X)) at h
      have he : i ⁻¹' ({z.underlying} : Set X) = {y} := by
        rw [← hy]
        ext a
        exact i.isEmbedding.injective.eq_iff
      rwa [he] at h
    let w : ComplexPoint Y (i ≫ structureMap) :=
      (pointEquivClosedPoint (i ≫ structureMap)).symm ⟨y, hyclosed⟩
    refine ⟨w, ?_⟩
    apply (pointEquivClosedPoint structureMap).injective
    apply Subtype.ext
    change i w.underlying = z.underlying
    have hw : w.underlying = y :=
      congrArg Subtype.val
        ((pointEquivClosedPoint (i ≫ structureMap)).apply_symm_apply ⟨y, hyclosed⟩)
    rw [hw]
    exact hy

/-- Each algebraic locally closed immersion has analytically locally closed complex-point
image. This asserts the image topology property, not yet a homeomorphism onto that image. -/
theorem isLocallyClosed_range_map_of_isImmersion (i : Y ⟶ X)
    [IsImmersion i] [LocallyOfFiniteType structureMap] :
    IsLocallyClosed (Set.range (Point.map i (structureMap := i ≫ structureMap) rfl)) := by
  rw [range_map_of_isImmersion structureMap i]
  exact i.isLocallyClosed_range.preimage (continuous_underlying_to_zariski structureMap)

variable [LocallyOfFiniteType structureMap] [NoetherianSpace X]

/-- The actual smooth pieces cover precisely the complex points on the given closed set. -/
theorem reducedSmoothStratification_complexPoints_covers (S : Closeds X)
    (z : ComplexPoint X structureMap) :
    (∃ T ∈ reducedSmoothStratification structureMap S,
      z ∈ Set.range (Point.map (reducedClosedSmoothPieceι structureMap T)
        (structureMap := reducedClosedSmoothPieceι structureMap T ≫ structureMap) rfl)) ↔
        z.underlying ∈ S := by
  simp only [range_map_of_isImmersion structureMap, Set.mem_preimage]
  exact reducedSmoothStratification_covers structureMap S z.underlying

/-- The analytic images of the constructed smooth pieces are pairwise disjoint. -/
theorem reducedSmoothStratification_complexPoints_pairwiseDisjoint (S : Closeds X) :
    (reducedSmoothStratification structureMap S).Pairwise (fun T U =>
      Disjoint
        (Set.range (Point.map (reducedClosedSmoothPieceι structureMap T)
          (structureMap := reducedClosedSmoothPieceι structureMap T ≫ structureMap) rfl))
        (Set.range (Point.map (reducedClosedSmoothPieceι structureMap U)
          (structureMap := reducedClosedSmoothPieceι structureMap U ≫ structureMap) rfl))) := by
  apply (reducedSmoothStratification_pairwiseDisjoint structureMap S).imp
  intro T U hTU
  simp only [range_map_of_isImmersion structureMap]
  exact hTU.preimage Point.underlying

end AlgebraicGeometry.ComplexPoint
