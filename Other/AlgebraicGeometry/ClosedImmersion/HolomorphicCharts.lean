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

public import HodgeConjecture.Definitions.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts

/-!
# HolomorphicCharts, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Topology Filter
namespace AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : Point ℂ Y)
variable (z' : Point ℂ Y)

/-- The actual transition preserves the zero-normal plane in both directions. -/
theorem closedImmersionNormalTransition_preserves_support
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ))
    (hv : v ∈ (closedImmersionNormalTransition X Y i m d z z').source) :
    (closedImmersionNormalTransition X Y i m d z z' v).2 = 0 ↔ v.2 = 0 := by
  let e := closedImmersionHolomorphicFlatteningChart X Y i m d z
  have hy := e.map_target hv.1
  have h1 := closedImmersionHolomorphicFlatteningChart_mem_range_iff
    X Y i m d z (e.symm v) hy
  have h2 := closedImmersionHolomorphicFlatteningChart_mem_range_iff
    X Y i m d z' (e.symm v) hv.2
  rw [e.right_inv hv.1] at h1
  exact h2.symm.trans h1

end AlgebraicGeometry.ComplexPoint
end
