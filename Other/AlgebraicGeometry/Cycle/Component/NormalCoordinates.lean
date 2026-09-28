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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.Dimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension
import HodgeConjecture.Mathlib.AlgebraicGeometry.GenericPoint
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalCoordinates
public import Other.AlgebraicGeometry.Smooth.PointwiseDimension

/-!
# NormalCoordinates, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalCoordinates`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace
namespace AlgebraicGeometry
attribute [local instance] overSpecAlgebra
section SchemeGeometry
variable {X : Scheme} {f : X ⟶ Spec ↧ℂ} {d p : ℕ}

/-- A closed subvariety whose ambient generic point has coheight equal to the ambient dimension
has dimension zero. -/
lemma orderKrullDim_closedEmbedding_eq_zero_of_coheight_eq_dimension
    {Z : Scheme} (g : Z ⟶ X) [IsClosedImmersion g] [IrreducibleSpace Z]
    [IsIntegral X] [SmoothOfRelativeDimension d f]
    (hi : Order.coheight (g (genericPoint Z)) = d) :
    Order.krullDim Z = (↑(0 : ℕ∞) : WithBot ℕ∞) := by
  rw [orderKrullDim_eq_height_image_genericPoint g]
  have h := SmoothOfRelativeDimension.height_add_coheight_eq_of_coheight_eq_dimension
    (f := f) (d := d) (g (genericPoint Z)) hi
  rw [hi] at h
  have hheight : Order.height (g (genericPoint Z)) = 0 :=
    bot_unique ((ENat.add_le_add_iff_right (ENat.natCast_ne_top d)).mp (by simpa using h.le))
  rw [hheight]

end SchemeGeometry
end AlgebraicGeometry
end
