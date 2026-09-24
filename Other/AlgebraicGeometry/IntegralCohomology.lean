/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticSheafCohomologyExt

/-!
# Integral cohomology and change to rational coefficients
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance integralCohomologyTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- Integral constant-sheaf cohomology in an integer degree. -/
abbrev IntegralCohomology (n : ℤ) :=
  Hypercohomology X (constantIntegerSheafComplexInt X) n

/-- The canonical change from integral to rational coefficients. -/
def integralToRationalCohomology (n : ℕ) :
    IntegralCohomology X n →+ H^n(X; ℚ) :=
  (hypercohomologyAddEquivConstantCohomology ℚ X n).toAddMonoidHom.comp
    (hypercohomologyMap X (analyticSheafComplexIntMap X
      (integerToFieldConstantSheaf ℚ X 1)) n)

end AlgebraicGeometry.ComplexPoint
