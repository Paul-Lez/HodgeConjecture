/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Geometry.Manifold.TubularNeighbourhood
public import Other.AlgebraicTopology.RetractFiniteHomology

/-!
# Compact manifolds have finitely generated singular homology

A compact Hausdorff smooth manifold embeds into a Euclidean space as a retract of an open
neighbourhood (`exists_euclidean_retraction_of_compact`), and compact neighbourhood retracts have
finitely generated integral singular homology (`module_finite_scalarHomology_of_retract`).
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace AlgebraicTopology.Singular

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type} [TopologicalSpace H] (I : ModelWithCorners ℝ F H) [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I in
/-- The integral singular homology of a compact Hausdorff smooth manifold without boundary is
finitely generated in every degree. -/
theorem module_finite_homology_of_compactSpace_isManifold (n : ℕ) :
    Module.Finite ℤ
      (((TopCat.toSSet.obj (TopCat.of M)).chainComplex (ModuleCat.of ℤ ℤ)).homology n) := by
  obtain ⟨N, e, W, he, hemb, hWopen, hW, r, hr, hre⟩ :=
    exists_euclidean_retraction_of_compact (I := I) (M := M)
  exact module_finite_scalarHomology_of_retract ⟨e, hemb.continuous⟩ hWopen hW ⟨r, hr⟩ hre n

end AlgebraicTopology.Singular
