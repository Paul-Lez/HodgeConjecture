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

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.Complex.Basic
import HodgeConjecture.Mathlib.AlgebraicGeometry.PointClosure
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula
import HodgeConjecture.Mathlib.AlgebraicGeometry.GenericPoint
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.RingTheory.Unramified.LocalStructure
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension

/-!
# PointwiseDimension, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace
namespace AlgebraicGeometry
variable {X : Scheme} {f : X ⟶ Spec ↧ℂ} {d : ℕ}

/-- The pointwise dimension formula holds at a point whose coheight equals the ambient relative
dimension. -/
lemma SmoothOfRelativeDimension.height_add_coheight_eq_of_coheight_eq_dimension
    [IsIntegral X] [SmoothOfRelativeDimension d f] (x : X)
    (hx : Order.coheight x = d) :
    Order.height x + Order.coheight x = d := by
  have hsum := SmoothOfRelativeDimension.height_add_coheight_le_complex
    (f := f) (d := d) x
  rw [hx] at hsum ⊢
  have hheight : Order.height x = 0 :=
    bot_unique ((ENat.add_le_add_iff_right (ENat.natCast_ne_top d)).mp (by simpa using hsum))
  rw [hheight, zero_add]

end AlgebraicGeometry
end
