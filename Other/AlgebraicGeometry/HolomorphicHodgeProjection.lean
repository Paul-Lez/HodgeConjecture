/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicZeroForms
public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration

/-!
# Projection from de Rham cohomology to holomorphic-function cohomology

Projecting the holomorphic de Rham complex onto its degree-zero functions kills the first
Hodge filtration. The projection is built from evaluation of the project's analytic forms.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

/-- The degree-zero evaluation map on the natural-indexed de Rham complex. -/
def holomorphicDeRhamToFunctions (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    holomorphicDeRhamComplex X d ⟶
      (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj (holomorphicAdditiveSheaf X d) :=
  (CochainComplex.toSingle₀Equiv _ _).symm (holomorphicZeroFormToFunctionSheaf X d)

set_option backward.isDefEq.respectTransparency false in
/-- The projection of constant de Rham forms is the inclusion of constant functions. -/
theorem constantsToHolomorphicDeRhamComplex_comp_toFunctions
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    constantsToHolomorphicDeRhamComplex X d ≫ holomorphicDeRhamToFunctions X d =
      (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
        (complexConstantsToHolomorphicSheaf X d) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, constantsToHolomorphicDeRhamComplex,
    holomorphicDeRhamToFunctions, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    CochainComplex.toSingle₀Equiv_symm_apply_f_zero, CochainComplex.single₀_map_f_zero]
  exact constantsToHolomorphicDeRhamZeroSheaf_comp_toFunction X d

/-- The holomorphic-function sheaf, concentrated in degree zero. -/
def holomorphicFunctionComplexInt (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj (holomorphicAdditiveSheaf X d)

/-- The de Rham projection to holomorphic functions on integer-indexed complexes. -/
def holomorphicDeRhamToFunctionsComplexInt [IsIntegral X.left] [Smooth X.hom] :
    holomorphicDeRhamComplexInt X ⟶ holomorphicFunctionComplexInt X (dim X.left) :=
  HomologicalComplex.extendMap (holomorphicDeRhamToFunctions X (dim X.left))
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      (holomorphicAdditiveSheaf X (dim X.left)) 0 0 rfl).hom

/-- The first Hodge subcomplex has zero projection to holomorphic functions. -/
theorem hodgeFilteredDeRhamInclusion_one_comp_toFunctions [IsIntegral X.left] [Smooth X.hom] :
    hodgeFilteredDeRhamInclusion X 1 ≫ holomorphicDeRhamToFunctionsComplexInt X = 0 := by
  apply HomologicalComplex.to_single_hom_ext
  apply (HomologicalComplex.isZero_stupidTrunc_X (holomorphicDeRhamComplexInt X)
    (ComplexShape.embeddingUpIntGE 1) 0 ?_).eq_of_src
  intro n
  change 1 + (n : ℤ) ≠ 0
  omega

/-- The projection from de Rham hypercohomology to cohomology of holomorphic functions. -/
def deRhamToHolomorphicFunctionCohomology [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    DeRhamHypercohomology X n →+
      Hypercohomology X (holomorphicFunctionComplexInt X (dim X.left)) n :=
  hypercohomologyMap X (holomorphicDeRhamToFunctionsComplexInt X) n

/-- Classes in the first Hodge filtration vanish in holomorphic-function cohomology. -/
theorem deRhamToHolomorphicFunctionCohomology_eq_zero_of_mem
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (α : DeRhamHypercohomology X n)
    (hα : α ∈ hodgeFiltration X 1 n) :
    deRhamToHolomorphicFunctionCohomology X n α = 0 := by
  obtain ⟨β, rfl⟩ := hα
  change hypercohomologyMap X (holomorphicDeRhamToFunctionsComplexInt X) n
    (hypercohomologyMap X (hodgeFilteredDeRhamInclusion X 1) n β) = 0
  rw [← hypercohomologyMap_comp_apply, hodgeFilteredDeRhamInclusion_one_comp_toFunctions,
    hypercohomologyMap_zero]
  rfl

/-- A rational Hodge class of degree two has zero image in the second cohomology of
holomorphic functions under the canonical de Rham comparison. -/
theorem hodgeClass_one_toHolomorphicFunctionCohomology_eq_zero
    [IsIntegral X.left] [Smooth X.hom] (α : FieldCohomology ℚ X 2)
    (hα : α ∈ hodgeClasses ℚ X 1) :
    deRhamToHolomorphicFunctionCohomology X 2 (fieldToDeRhamCohomology ℚ X 2 α) = 0 := by
  rw [hodgeClasses_rat_eq_comap_hodgeFiltrationSubmodule] at hα
  exact deRhamToHolomorphicFunctionCohomology_eq_zero_of_mem X 2 _ hα

end AlgebraicGeometry.ComplexPoint
