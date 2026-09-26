/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernRelativeFinalAssembly
public import Other.AlgebraicGeometry.DivisorObligations
public import Other.AlgebraicGeometry.GAGAStatement
public import Other.AlgebraicGeometry.LefschetzOneOneFiniteHomology

/-!
# GAGA input for the Lefschetz reduction

This file connects the general line-bundle GAGA statement to the particular analytic line bundles
constructed by the Lefschetz development.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

omit [IsProjective X.hom] in
/-- General line-bundle GAGA algebraizes the section sheaf of every unit-sheaf extension. -/
theorem hasAlgebraicModel_of_analyticLineBundlesAlgebraize
    (h : AnalyticLineBundlesAlgebraize X) : HasAlgebraicModel X :=
  fun E ↦ h E.sectionSheafOfModules E.sectionSheafOfModules_isInvertible

/-- The rational Lefschetz `(1, 1)` theorem follows once the line bundles constructed from Hodge
classes have algebraic models. -/
theorem _root_.RationalLefschetzOneOne.of_algebraicModel
    (h : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasAlgebraicModel X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_divisor fun X _ _ _ ↦
    hasDivisorOfUnitExtension_of_algebraicModel X (h X)
      (hasDivisorOfAlgebraicModel_of_divisorClass X
        (hasDivisorClassOfSomeCartierData_of_cartierData X
          (hasDivisorClassOfCartierData (X := X))))

/-- The rational Lefschetz `(1, 1)` theorem follows from line-bundle GAGA. -/
theorem _root_.RationalLefschetzOneOne.of_analyticLineBundlesAlgebraize
    (h : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      AnalyticLineBundlesAlgebraize X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_algebraicModel fun X _ _ _ ↦
    hasAlgebraicModel_of_analyticLineBundlesAlgebraize X (h X)

end AlgebraicGeometry.ComplexPoint
