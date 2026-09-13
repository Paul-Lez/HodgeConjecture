/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.SourceOpen

/-!
# Restricting the source of a closed immersion without losing closedness

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.SourceOpen`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Scheme} (i : Y ⟶ X) [IsClosedImmersion i] (A : Y.Opens)

end AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

/-- The actual immersion image formula, with structure-map compatibility bundled in `i`. -/
theorem range_map_of_isImmersion_of_comm (X Y : Over (Spec (.of ℂ)))
    (i : Y ⟶ X) [IsImmersion i.left] [LocallyOfFiniteType X.hom] :
    Set.range (Point.map i) =
      (Point.underlying : ComplexPoint X → X.left) ⁻¹' Set.range i.left := by
  let : LocallyOfFiniteType Y.hom := by
    rw [← i.w]
    infer_instance
  exact range_map_of_isImmersion X i

end AlgebraicGeometry.ComplexPoint
