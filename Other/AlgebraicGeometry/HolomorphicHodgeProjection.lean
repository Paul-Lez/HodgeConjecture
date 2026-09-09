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

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ)

/-- The degree-zero evaluation map on the natural-indexed de Rham complex. -/
def holomorphicDeRhamToFunctions (d : ℕ) [SmoothOfRelativeDimension d s] :
    holomorphicDeRhamComplex s d ⟶
      (CochainComplex.single₀ (AnalyticAdditiveSheaf s)).obj (holomorphicAdditiveSheaf s d) :=
  (CochainComplex.toSingle₀Equiv _ _).symm (holomorphicZeroFormToFunctionSheaf s d)

set_option backward.isDefEq.respectTransparency false in
/-- The projection of constant de Rham forms is the inclusion of constant functions. -/
theorem constantsToHolomorphicDeRhamComplex_comp_toFunctions
    (d : ℕ) [SmoothOfRelativeDimension d s] :
    constantsToHolomorphicDeRhamComplex s d ≫ holomorphicDeRhamToFunctions s d =
      (CochainComplex.single₀ (AnalyticAdditiveSheaf s)).map
        (complexConstantsToHolomorphicSheaf s d) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, constantsToHolomorphicDeRhamComplex,
    holomorphicDeRhamToFunctions, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    CochainComplex.toSingle₀Equiv_symm_apply_f_zero, CochainComplex.single₀_map_f_zero]
  exact constantsToHolomorphicDeRhamZeroSheaf_comp_toFunction s d

/-- The holomorphic-function sheaf, concentrated in degree zero. -/
def holomorphicFunctionComplexInt (d : ℕ) [SmoothOfRelativeDimension d s] :
    CochainComplex (AnalyticAdditiveSheaf s) ℤ :=
  (CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) 0).obj (holomorphicAdditiveSheaf s d)

/-- The de Rham projection to holomorphic functions on integer-indexed complexes. -/
def holomorphicDeRhamToFunctionsComplexInt [IsIntegral X] [Smooth s] :
    holomorphicDeRhamComplexInt s ⟶ holomorphicFunctionComplexInt s (dim X) :=
  HomologicalComplex.extendMap (holomorphicDeRhamToFunctions s (dim X))
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      (holomorphicAdditiveSheaf s (dim X)) 0 0 rfl).hom

/-- The first Hodge subcomplex has zero projection to holomorphic functions. -/
theorem hodgeFilteredDeRhamInclusion_one_comp_toFunctions [IsIntegral X] [Smooth s] :
    hodgeFilteredDeRhamInclusion s 1 ≫ holomorphicDeRhamToFunctionsComplexInt s = 0 := by
  apply HomologicalComplex.to_single_hom_ext
  apply (HomologicalComplex.isZero_stupidTrunc_X (holomorphicDeRhamComplexInt s)
    (ComplexShape.embeddingUpIntGE 1) 0 ?_).eq_of_src
  intro n
  change 1 + (n : ℤ) ≠ 0
  omega

/-- The projection from de Rham hypercohomology to cohomology of holomorphic functions. -/
def deRhamToHolomorphicFunctionCohomology [IsIntegral X] [Smooth s] (n : ℤ) :
    DeRhamHypercohomology s n →+
      Hypercohomology s (holomorphicFunctionComplexInt s (dim X)) n :=
  hypercohomologyMap s (holomorphicDeRhamToFunctionsComplexInt s) n

/-- Classes in the first Hodge filtration vanish in holomorphic-function cohomology. -/
theorem deRhamToHolomorphicFunctionCohomology_eq_zero_of_mem
    [IsIntegral X] [Smooth s] (n : ℤ) (α : DeRhamHypercohomology s n)
    (hα : α ∈ hodgeFiltration s 1 n) :
    deRhamToHolomorphicFunctionCohomology s n α = 0 := by
  obtain ⟨β, rfl⟩ := hα
  change hypercohomologyMap s (holomorphicDeRhamToFunctionsComplexInt s) n
    (hypercohomologyMap s (hodgeFilteredDeRhamInclusion s 1) n β) = 0
  rw [← hypercohomologyMap_comp_apply, hodgeFilteredDeRhamInclusion_one_comp_toFunctions,
    hypercohomologyMap_zero]
  rfl

/-- A rational Hodge class of degree two has zero image in the second cohomology of
holomorphic functions under the canonical de Rham comparison. -/
theorem hodgeClass_one_toHolomorphicFunctionCohomology_eq_zero
    [IsIntegral X] [Smooth s] (α : FieldCohomology ℚ s 2)
    (hα : α ∈ hodgeClasses ℚ s 1) :
    deRhamToHolomorphicFunctionCohomology s 2 (fieldToDeRhamCohomology ℚ s 2 α) = 0 :=
  deRhamToHolomorphicFunctionCohomology_eq_zero_of_mem s 2 _ hα

end AlgebraicGeometry.ComplexPoint
