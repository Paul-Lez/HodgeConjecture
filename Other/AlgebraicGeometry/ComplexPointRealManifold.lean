/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexManifold
public import Other.AlgebraicGeometry.ProjectiveAnalytification
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# The analytic space as a real smooth manifold

The complex points of a smooth complex scheme form a complex-analytic manifold. Restricting
scalars, they form a real `C^∞` manifold on the same charts; together with compactness and the
Hausdorff property of the analytification of a projective scheme (`complexPoint_compactSpace`,
`complexPoint_t2Space`), this is the input to the Whitney embedding theorem.
-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Smooth complex points form a real `C^∞` manifold on the same charts. -/
instance isRealManifold_smooth [SmoothOfRelativeDimension d X.hom] :
    IsManifold 𝓘(ℝ, Fin d → ℂ) ∞ (ComplexPoint X) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨z, rfl⟩ := he
  obtain ⟨z', rfl⟩ := he'
  have h := (contDiffOn_localChart_transition X d z z').restrict_scalars ℝ
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    CompTriple.comp_eq, Function.id_comp, Function.comp_id, Set.preimage_id,
    Set.range_id, Set.inter_univ] using h.of_le le_top

end AlgebraicGeometry.ComplexPoint
