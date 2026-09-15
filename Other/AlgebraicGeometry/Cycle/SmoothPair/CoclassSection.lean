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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection
public import Other.AlgebraicGeometry.Cycle.SmoothPair.CoclassOverlap

/-!
# CoclassSection, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
open TopCat.Presheaf
namespace AlgebraicGeometry.ComplexPoint
variable {X Y : Over (Spec ↧ℂ)}
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- At every center, the global section has exactly the germ of the previously
constructed normal-slice coclass, on any prescribed local model neighborhood. -/
theorem smoothClosedSupportCoclassSection_germ_eq_normalCoclass
    (z : ComplexPoint Y) (V : Opens (ComplexPoint X))
    (hzV : Point.map i z ∈ V) :
    (smoothClosedSupportCoclassSheaf i m d).presheaf.Γgerm
      (Point.map i z) (smoothClosedSupportCoclassSection i m d) =
    @supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (Set.range (Point.map i)) (2 * (d - m))
      (smoothClosedSupportNeighborhood X Y i m d z V hzV) (Point.map i z)
      (mem_smoothClosedSupportNeighborhood X Y i m d z V hzV)
      (smoothClosedSupportNormalCoclass X Y i m d z V hzV) := by
  let C := smoothClosedSupportChartOpen i m d z
  let U := smoothClosedSupportNeighborhood X Y i m d z V hzV
  let W := C ⊓ U
  have hWC : W ≤ C := inf_le_left
  have hWU : W ≤ U := inf_le_right
  have hzW : Point.map i z ∈ W :=
    ⟨mem_smoothClosedSupportChartOpen i m d z,
      mem_smoothClosedSupportNeighborhood X Y i m d z V hzV⟩
  rw [smoothClosedSupportCoclassSection_germ_eq_chart i m d z
    (Point.map i z) (mem_smoothClosedSupportChartOpen i m d z)]
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq
    (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
    hWC hWU (Point.map i z) hzW
  rw [smoothClosedSupportChartCoclass_restrict,
    smoothClosedSupportNormalCoclass_restrict_eq_chart X Y i m d z V hzV W hWU hWC]

end AlgebraicGeometry.ComplexPoint
end
