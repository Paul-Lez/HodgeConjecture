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

public import Other.AlgebraicGeometry.CodimensionZeroCoclassNonvanishing

import Other.AlgebraicGeometry.HodgeCodimensionZero
import Other.AlgebraicGeometry.ProjectiveAnalytificationConnected

/-!
# The Hodge conjecture for smooth projective complex varieties of dimension zero

The generic component class is nonzero in every dimension. In dimension zero, connectedness
of the analytification identifies its span with degree-zero cohomology. In positive codimension,
the cohomology vanishes, proving the Hodge-conjecture inclusion in every codimension.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The two codimension-zero span constructions agree on a variety of complex dimension zero. -/
theorem algebraicCycleClassSpan_zero_eq_codimensionZeroCycleClassSpan_of_dimension_eq_zero
    (hd : dim X.left = 0) :
    algebraicCycleClassSpan X 0 = codimensionZeroCycleClassSpan X := by
  let : ConnectedSpace (ComplexPoint X) :=
    connectedSpaceOfDimensionEqZero X (dim X.left) hd
  exact algebraicCycleClassSpan_zero_eq_codimensionZeroCycleClassSpan X

/-- The Hodge-conjecture inclusion holds in every codimension for a smooth projective complex
variety of complex dimension zero. -/
theorem rationalHodgeClasses_le_algebraicCycleClassSpan_of_dimension_zero
    (hd : dim X.left = 0) (p : ℕ) :
    Hdg^p(ℚ; X) ≤ algebraicCycleClassSpan X p :=
  rationalHodgeClasses_le_algebraicCycleClassSpan_of_dimension_eq_zero X hd
    (algebraicCycleClassSpan_zero_eq_codimensionZeroCycleClassSpan_of_dimension_eq_zero X hd) p

end AlgebraicGeometry.ComplexPoint
