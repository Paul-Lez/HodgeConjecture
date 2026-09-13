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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.ResidueField
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion

/-!
# ClosedImmersion, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public section
open CategoryTheory Opposite TopologicalSpace Topology
namespace AlgebraicGeometry
namespace ComplexPoint
open Point
variable {X Y : Over (Spec ↧ℂ)}

/-- For a complex scheme locally of finite type, a complex point is determined by its underlying
closed point. -/
lemma underlying_injective_of_locallyOfFiniteType
    [LocallyOfFiniteType X.hom] :
    Function.Injective (@underlying ℂ _ _ X) := fun z w h ↦
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq X.hom (Over.w z) (Over.w w) h)

end ComplexPoint
end AlgebraicGeometry
end
