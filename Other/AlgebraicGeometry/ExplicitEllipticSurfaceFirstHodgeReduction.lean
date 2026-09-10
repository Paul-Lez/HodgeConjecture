/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceRationalSingularClass
public import Other.AlgebraicGeometry.FirstHodgeObstructionConstantComparison

/-!
# The first Hodge obstruction for the explicit rational surface class

This file reduces the remaining non-Hodge calculation to the map from complex constants to
holomorphic functions.  In particular, no choice of a de Rham representative remains in the
statement: the input is the concrete rational external-product Betti class.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

local instance surfaceVariety_smoothForFirstHodge : Smooth surfaceVariety.hom :=
  SmoothOfRelativeDimension.smooth 2 surfaceVariety.hom

/-- The first Hodge obstruction of the concrete rational surface class is its complex
constant-sheaf class mapped to holomorphic-function cohomology. -/
theorem explicitSurfaceFirstHodgeObstruction_eq :
    firstHodgeObstruction surfaceVariety 2
        (fieldToDeRhamCohomology ℚ surfaceVariety 2
          explicitSurfaceRationalExternalBettiClass) =
      complexConstantToHolomorphicFunctionCohomology surfaceVariety 2
        explicitSurfaceComplexifiedExternalBettiClass := by
  exact firstHodgeObstruction_fieldToDeRham_factor surfaceVariety ℚ 2
    explicitSurfaceRationalExternalBettiClass

/-- The concrete rational surface class is Hodge exactly when its image in degree-two
holomorphic-function cohomology vanishes. -/
theorem explicitSurfaceRationalExternalBettiClass_isHodge_iff :
    IsHodgeClass ℚ surfaceVariety 1 explicitSurfaceRationalExternalBettiClass ↔
      complexConstantToHolomorphicFunctionCohomology surfaceVariety 2
        explicitSurfaceComplexifiedExternalBettiClass = 0 := by
  rw [ComplexPoint.isHodgeClass_one_iff,
    explicitSurfaceFirstHodgeObstruction_eq]

/-- A nonzero holomorphic-function image proves that the concrete rational external-product
class is not a Hodge class. -/
theorem explicitSurfaceRationalExternalBettiClass_not_isHodge_of_image_ne_zero
    (h : complexConstantToHolomorphicFunctionCohomology surfaceVariety 2
      explicitSurfaceComplexifiedExternalBettiClass ≠ 0) :
    ¬ IsHodgeClass ℚ surfaceVariety 1 explicitSurfaceRationalExternalBettiClass := by
  rw [explicitSurfaceRationalExternalBettiClass_isHodge_iff]
  exact h

end AlgebraicGeometry.ExplicitEllipticCandidate
