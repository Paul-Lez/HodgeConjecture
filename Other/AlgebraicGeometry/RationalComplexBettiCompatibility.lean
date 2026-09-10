/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.BettiGlobalSectionsAdditivity
public import Other.AlgebraicGeometry.ComplexBettiGlobalSectionsComparison
public import Other.AlgebraicGeometry.HypercohomologyFlasqueNaturality
public import Other.AlgebraicTopology.SingularCochainConstantCoefficientNaturality

/-!
# Compatibility of rational and complex Betti comparisons

The constant-sheaf map `ℚ → ℂ` and coefficient extension on singular
cochains form a commutative square.  This file transports that square through
hypercohomology and the global singular-cochain comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec (.of ℂ)))

/-- Rational-to-complex coefficient extension between the integer-indexed
singular-cochain sheaf complexes on the analytification of `X`. -/
def rationalToComplexSingularCochainComplexInt :
    singularCochainSheafComplexInt X ℚ ⟶
      singularCochainSheafComplexInt X ℂ :=
  AlgebraicTopology.Singular.qToCSingularCochainSheafComplexInt
    (TopCat.of (ComplexPoint X))

/-- The constant-to-singular comparison commutes with extension of
coefficients from `ℚ` to `ℂ`. -/
theorem fieldToComplex_comp_complexToSingularCochainComplexInt :
    fieldToComplexConstantSheafComplexInt ℚ X ≫
        complexToSingularCochainComplexInt X =
      rationalToSingularCochainComplexInt X ≫
        rationalToComplexSingularCochainComplexInt X := by
  exact
    AlgebraicTopology.Singular.qToC_constantsToSingularCochainSheafComplexInt
      (TopCat.of (ComplexPoint X))

/-- The preceding square after applying hypercohomology. -/
theorem fieldToComplexCohomology_singularCochain_square
    [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (a : FieldCohomology ℚ X n) :
    hypercohomologyMap X (complexToSingularCochainComplexInt X) n
        (fieldToComplexCohomology ℚ X n a) =
      hypercohomologyMap X (rationalToComplexSingularCochainComplexInt X) n
        (hypercohomologyMap X
          (rationalToSingularCochainComplexInt X) n a) := by
  change hypercohomologyMap X (complexToSingularCochainComplexInt X) n
      (hypercohomologyMap X
        (fieldToComplexConstantSheafComplexInt ℚ X) n a) = _
  calc
    _ = hypercohomologyMap X
        (fieldToComplexConstantSheafComplexInt ℚ X ≫
          complexToSingularCochainComplexInt X) n a :=
      (hypercohomologyMap_comp_apply X _ _ n a).symm
    _ = hypercohomologyMap X
        (rationalToSingularCochainComplexInt X ≫
          rationalToComplexSingularCochainComplexInt X) n a := by
      rw [fieldToComplex_comp_complexToSingularCochainComplexInt]
    _ = _ := hypercohomologyMap_comp_apply X _ _ n a

end AlgebraicGeometry.ComplexPoint
