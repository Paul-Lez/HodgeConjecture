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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Support
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Cycle components and their support

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Support`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (x : X.left)

/-- The complex points of the cycle component at `x` are the complex points of `X` on it. -/
@[simp]
lemma range_map_cycleComponentOverι :
    Set.range (Point.map (cycleComponentOverι X x)) = cycleComponentSupport X x := by
  rw [range_map_of_closedImmersion]
  ext z
  simp

end AlgebraicGeometry.ComplexPoint
