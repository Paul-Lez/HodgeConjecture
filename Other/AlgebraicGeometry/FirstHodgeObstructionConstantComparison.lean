/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.FirstHodgeObstruction

/-!
# The first Hodge obstruction as a constant-sheaf map

The de Rham comparison followed by projection to holomorphic functions is
packaged directly as a map out of the constant complex.  This removes the
intermediate de Rham group when studying a rational class's first Hodge
obstruction.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
variable (K : Type) [Field K] [Algebra K ℂ]

/-- Complex constants mapped to holomorphic functions through the degree-zero
projection of the holomorphic de Rham complex. -/
def complexConstantsToHolomorphicFunctionComplexInt :
    constantComplexSheafComplexInt X ⟶ holomorphicFunctionComplexInt X :=
  constantsToHolomorphicDeRhamComplexInt X ≫
    deRhamToHolomorphicFunctions X

/-- The map on cohomology from complex constants to holomorphic-function
cohomology. -/
def complexConstantToHolomorphicFunctionCohomology (n : ℤ) :
    ComplexConstantCohomology X n →+
      HolomorphicFunctionCohomology X n :=
  hypercohomologyMap X
    (complexConstantsToHolomorphicFunctionComplexInt X) n

/-- Field-valued constants mapped directly to holomorphic functions. -/
def fieldConstantsToHolomorphicFunctionComplexInt :
    constantFieldSheafComplexInt K X ⟶ holomorphicFunctionComplexInt X :=
  fieldToComplexConstantSheafComplexInt K X ≫
    complexConstantsToHolomorphicFunctionComplexInt X

/-- The direct field-constant-to-holomorphic-function map is the de Rham
comparison followed by the first Hodge projection. -/
theorem fieldConstantsToHolomorphicFunctionComplexInt_eq :
    fieldConstantsToHolomorphicFunctionComplexInt X K =
      fieldToHolomorphicDeRhamComplexInt K X ≫
        deRhamToHolomorphicFunctions X := by
  rfl

/-- The first Hodge obstruction of a field-valued class factors through its
complex constant-sheaf image. -/
theorem firstHodgeObstruction_fieldToDeRham_factor
    (n : ℤ) (α : FieldCohomology K X n) :
    firstHodgeObstruction X n
        (fieldToDeRhamCohomology K X n α) =
      complexConstantToHolomorphicFunctionCohomology X n
        (fieldToComplexCohomology K X n α) := by
  unfold firstHodgeObstruction fieldToDeRhamCohomology
    complexConstantToHolomorphicFunctionCohomology
    complexConstantsToHolomorphicFunctionComplexInt
    fieldToComplexCohomology
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  rfl

/-- Equivalently, the obstruction is induced directly by the composite from
field constants to holomorphic functions. -/
theorem firstHodgeObstruction_fieldToDeRham_eq_direct
    (n : ℤ) (α : FieldCohomology K X n) :
    firstHodgeObstruction X n
        (fieldToDeRhamCohomology K X n α) =
      hypercohomologyMap X
        (fieldConstantsToHolomorphicFunctionComplexInt X K) n α := by
  rw [firstHodgeObstruction_fieldToDeRham_factor]
  unfold complexConstantToHolomorphicFunctionCohomology
    fieldConstantsToHolomorphicFunctionComplexInt fieldToComplexCohomology
  rw [hypercohomologyMap_comp_apply]

end AlgebraicGeometry.ComplexPoint
