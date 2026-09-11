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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Coniveau
public import Other.AlgebraicGeometry.CycleClassLemmas
import Other.AlgebraicGeometry.CycleClassDimension
import Other.AlgebraicGeometry.ProjectiveAnalytificationConnected
import HodgeConjecture.Lemmas.AlgebraicGeometry.RationalCohomologyZero

/-!
# The Hodge conjecture in codimension zero

On a smooth projective variety with connected analytification, the codimension-zero Chow
cycle-class map is surjective. The Hodge-conjecture conclusions assume that its image equals the
constructed component-class span. In dimension zero, this comparison implies the inclusion in
every codimension.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

/-- On a connected projective analytification, the image of the genuine codimension-zero Chow
cycle-class map is all of degree-zero rational cohomology. -/
theorem codimensionZeroCycleClassSpan_eq_top_of_connected
    (hV : ConnectedSpace (ComplexPoint X)) :
    codimensionZeroCycleClassSpan X = ⊤ := by
  let : ConnectedSpace (ComplexPoint X) := hV
  rw [codimensionZeroCycleClassSpan_eq_span_unit, span_rationalCohomologyUnit_eq_top]

/-- On a connected projective analytification, the constructed codimension-zero algebraic
cycle-class span is the whole degree-zero rational cohomology group, provided it has been compared
with the separately constructed codimension-zero Chow-class span. -/
theorem algebraicCycleClassSpan_zero_eq_top_of_connected
    (hV : ConnectedSpace (ComplexPoint X))
    (hcompare : algebraicCycleClassSpan X 0 =
      codimensionZeroCycleClassSpan X) :
    algebraicCycleClassSpan X 0 = ⊤ := by
  rw [hcompare, codimensionZeroCycleClassSpan_eq_top_of_connected X hV]

/-- On a smooth projective variety with connected analytification, the degree-zero Hodge classes
equal the algebraic cycle-class span, assuming the comparison with the codimension-zero
Chow-class span. -/
theorem rationalHodgeClasses_zero_eq_algebraicCycleClassSpan_of_connected
    (hV : ConnectedSpace (ComplexPoint X))
    (hcompare : algebraicCycleClassSpan X 0 =
      codimensionZeroCycleClassSpan X) :
    Hdg^0(ℚ; X) = algebraicCycleClassSpan X 0 := by
  rw [hodgeClasses_zero_eq_top,
    algebraicCycleClassSpan_zero_eq_top_of_connected X hV hcompare]

/-- The codimension-zero Hodge-conjecture inclusion follows from analytic connectedness
and the comparison with the codimension-zero Chow-class span. -/
theorem rationalHodgeClasses_zero_le_algebraicCycleClassSpan_of_connected
    (hV : ConnectedSpace (ComplexPoint X))
    (hcompare : algebraicCycleClassSpan X 0 =
      codimensionZeroCycleClassSpan X) :
    Hdg^0(ℚ; X) ≤ algebraicCycleClassSpan X 0 := by
  rw [rationalHodgeClasses_zero_eq_algebraicCycleClassSpan_of_connected X hV hcompare]

/-- For a smooth projective complex variety of dimension zero, the Hodge-conjecture inclusion
in every codimension follows from the comparison with the codimension-zero Chow-class span. -/
theorem rationalHodgeClasses_le_algebraicCycleClassSpan_of_dimension_eq_zero
    (hd : dim X.left = 0)
    (hcompare : algebraicCycleClassSpan X 0 =
      codimensionZeroCycleClassSpan X) (p : ℕ) :
    Hdg^p(ℚ; X) ≤ algebraicCycleClassSpan X p := by
  by_cases hp : p = 0
  · subst p
    exact rationalHodgeClasses_zero_le_algebraicCycleClassSpan_of_connected X
      (connectedSpaceOfDimensionEqZero X (dim X.left) hd) hcompare
  · have hdim : dim X.left < p := by lia
    rw [hodgeClasses_eq_bot_of_lt ℚ X hdim,
      algebraicCycleClassSpan_eq_bot_of_lt X (dim X.left) p hdim]

end AlgebraicGeometry.ComplexPoint
