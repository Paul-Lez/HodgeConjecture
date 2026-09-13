/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Tactic.Bound
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective

/-!
# Projective, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public section
open CategoryTheory Metric Opposite TopologicalSpace Topology
open scoped LinearAlgebra.Projectivization
namespace AlgebraicGeometry
namespace ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Nonzero homogeneous coordinates satisfy the irrelevant-ideal condition in the universal
construction of a morphism to `Proj`. -/
lemma coordinate_irrelevant_map_eq_top {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    Ideal.map (coordinateGlobalSectionsHom v)
      (HomogeneousIdeal.irrelevant (UniversalGrading n)).toIdeal = ⊤ := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v hv
  apply Ideal.eq_top_of_isUnit_mem _
  · apply Ideal.mem_map_of_mem
    exact HomogeneousIdeal.mem_irrelevant_of_mem _ zero_lt_one
      (MvPolynomial.isHomogeneous_X _ i)
  · rw [coordinateGlobalSectionsHom_X]
    exact IsUnit.map (Scheme.ΓSpecIso ↧ℂ).inv.hom
      (isUnit_iff_ne_zero.mpr hi)

end ComplexProjectiveSpace
end AlgebraicGeometry
end
