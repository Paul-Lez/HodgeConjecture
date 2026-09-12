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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))

/-- In degree filtration `F⁰`, the filtered and full de Rham hypercohomology groups are
canonically equivalent. -/
def hodgeFiltrationZeroEquiv [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    FilteredDeRhamHypercohomology X 0 n ≃
      DeRhamHypercohomology X n := by
  letI : IsIso (hodgeFilteredDeRhamInclusion X 0) := by
    unfold hodgeFilteredDeRhamInclusion hodgeFilteredDeRhamComplex
    infer_instance
  exact Localization.SmallShiftedHom.postcompEquiv
    (hodgeFilteredDeRhamInclusion X 0)
    (by
      change QuasiIso (hodgeFilteredDeRhamInclusion X 0)
      infer_instance)


lemma filteredToDeRhamCohomology_zero_apply
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : FilteredDeRhamHypercohomology X 0 n) :
    filteredToDeRhamCohomology X 0 n α =
      hodgeFiltrationZeroEquiv X n α := rfl

/-- The zeroth Hodge filtration is the whole de Rham hypercohomology group. -/
lemma hodgeFiltration_zero_eq_top [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    hodgeFiltration X 0 n = ⊤ := by
  ext α
  simp only [hodgeFiltration, AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
  exact ⟨(hodgeFiltrationZeroEquiv X n).symm α,
    filteredToDeRhamCohomology_zero_apply X n _ |>.trans
      ((hodgeFiltrationZeroEquiv X n).apply_symm_apply α)⟩

/-- `F⁰ ⊓ conj F⁰` is everything, in every degree, because `F⁰` is. In degree `0` this says the
`(0,0)` piece is everything; in other degrees it is not a statement about a Hodge piece. -/
lemma hodgePiece_zero_eq_top [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    hodgePiece X 0 0 n = ⊤ := by
  refine eq_top_iff.mpr fun α _ ↦ ⟨?_, ?_⟩
  · show α ∈ hodgeFiltration X 0 n
    rw [hodgeFiltration_zero_eq_top X n]
    trivial
  · show deRhamConj X n α ∈ hodgeFiltration X 0 n
    rw [hodgeFiltration_zero_eq_top X n]
    trivial

/-- The complex subspace underlying `F⁰` is the whole de Rham hypercohomology group. -/
lemma hodgeFiltrationComplexSubmodule_zero_eq_top [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    hodgeFiltrationComplexSubmodule X 0 n = ⊤ := by
  refine SetLike.ext fun α ↦ ?_
  change α ∈ hodgeFiltration X 0 n ↔ α ∈ (⊤ :
    Submodule ℂ (DeRhamHypercohomology X n))
  rw [hodgeFiltration_zero_eq_top X n]
  simp

/-- Every rational degree-zero cohomology class belongs to the rational Hodge subgroup. -/
lemma hodgeClasses_zero_eq_top [IsIntegral X.left] [Smooth X.hom] :
    Hdg^0(K; X) = ⊤ := by
  refine SetLike.ext fun α ↦ ?_
  change fieldToDeRhamCohomology K X (2 * (0 : ℕ)) α ∈
      hodgePiece X ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) (2 * (0 : ℕ)) ↔ True
  simp only [Nat.cast_zero]
  rw [hodgePiece_zero_eq_top]
  trivial


end AlgebraicGeometry.ComplexPoint
