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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.NormalCoordinates
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FlattenedSupport
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeCochainCone
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.LocalHomology

/-!
# LocalHomology, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.LocalHomology`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open AlgebraicTopology.Singular
namespace AlgebraicGeometry.ComplexPoint
variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)
  (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V)

/-- Generation is deduced from the explicit pair computation, never used to manufacture
the normal-slice comparison. -/
theorem span_smoothClosedSupportNormalClass_eq_top :
    Submodule.span ℚ {smoothClosedSupportNormalClass X Y i m d z V hzV} = ⊤ := by
  let e := (smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV
    (2 * (d - m))).symm.toLinearEquiv
  have h := congrArg (Submodule.map e.toLinearMap)
    (span_standardComplexLocalClass_eq_top_for_chart (d - m))
  rw [Submodule.map_span, Set.image_singleton, Submodule.map_top, LinearEquiv.range] at h
  exact h

/-- Exact normalization uniquely specifies the local coclass, since the constructed
normal class generates the already computed local relative homology. -/
theorem smoothClosedSupportNormalCoclass_unique
    (α : RelativeCohomology ℚ
      (smoothClosedSupportNeighborhoodPair X Y i m d z V hzV)
        (2 * (d - m)))
    (hα : relativeCohomologyEquivDualHomology ℚ
        (smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) (2 * (d - m)) α
      (smoothClosedSupportNormalClass X Y i m d z V hzV) = 1) :
    α = smoothClosedSupportNormalCoclass X Y i m d z V hzV :=
  normalizedRelativeCoclass_unique
    (smoothClosedSupportNormalClass_ne_zero X Y i m d z V hzV)
    (span_smoothClosedSupportNormalClass_eq_top X Y i m d z V hzV) α hα

end AlgebraicGeometry.ComplexPoint
end
