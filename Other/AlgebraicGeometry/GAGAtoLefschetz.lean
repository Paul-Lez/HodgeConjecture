/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.LefschetzOneOneReduction
public import Other.AlgebraicGeometry.GAGAStatement

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

end AlgebraicGeometry.ComplexPoint
