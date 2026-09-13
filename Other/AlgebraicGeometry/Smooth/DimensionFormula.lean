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

public import HodgeConjecture.Mathlib.RingTheory.SmoothKrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.Dimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula

/-!
# DimensionFormula, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Topology
namespace AlgebraicGeometry
variable {X : Scheme}
variable {f : X ⟶ Spec ↧ℂ} {d : ℕ}

/-- A smooth complex scheme of relative dimension `d` has no point of coheight `p` when
`d < p`. -/
lemma SmoothOfRelativeDimension.coheight_ne_of_lt
    [SmoothOfRelativeDimension d f] (x : X) {p : ℕ} (hp : d < p) :
    Order.coheight x ≠ p := by
  intro hx
  have hle : (p : ℕ∞) ≤ d := by
    rw [← hx]
    exact SmoothOfRelativeDimension.coheight_le_complex (f := f) (d := d) x
  exact (not_le_of_gt (by exact_mod_cast hp)) hle

end AlgebraicGeometry
end
