/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
module

public import Other.AlgebraicGeometry.Hodge.CodimensionZeroNonvanishing
public import Other.AlgebraicGeometry.Hodge.Filtration

import Other.AlgebraicGeometry.Cycle.Codimension
import Other.AlgebraicGeometry.Cycle.ClassDimension
import Other.AlgebraicGeometry.ComplexPoint.ProjectiveConnected

/-!
# Dimension-zero Hodge classes

For a smooth projective complex variety of dimension zero, the Hodge-conjecture inclusion follows
from the codimension-zero theorem and out-of-range vanishing in positive codimension.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The Hodge-conjecture inclusion holds in every codimension for a smooth projective complex
variety of complex dimension zero. -/
theorem rationalHodgeClasses_le_algebraicCycleClassSpan_of_dimension_zero
    (hd : dim X.left = 0) (p : ℕ) :
    Hdg^p(ℚ; X) ≤ algebraicCycleClassSpan X p := by
  by_cases hp : p = 0
  · subst p
    rw [rationalHodgeClasses_zero_eq_algebraicCycleClassSpan]
  · have hdim : dim X.left < p := by omega
    let _ : SmoothOfRelativeDimension (dim X.left) X.hom := inferInstance
    rw [hodgeClasses_eq_bot_of_lt ℚ X hdim,
      algebraicCycleClassSpan_eq_bot_of_lt X (dim X.left) p hdim]

end AlgebraicGeometry.ComplexPoint
