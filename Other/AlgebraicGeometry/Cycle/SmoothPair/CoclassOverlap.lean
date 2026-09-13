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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothPair.CoclassOverlap
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.CoclassOverlap

/-!
# CoclassOverlap, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.CoclassOverlap`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace
open AlgebraicTopology.Singular
namespace AlgebraicGeometry.ComplexPoint
variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- The old local pair-model coclass is exactly the chart-projection coclass.
The proof uses the explicit radial normal fiber, including its complex normalization. -/
theorem smoothClosedSupportNormalCoclass_eq_projection
    (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V) :
    smoothClosedSupportNormalCoclass X Y i m d z V hzV =
    chartNormalProjectionCoclass (Fin m → ℂ) (d - m)
      (smoothClosedSupportRestrictionChart X Y i m d z V)
      (Set.range (Point.map i))
      (smoothClosedSupportRestrictionChart_mem_range_iff X Y i m d z V)
      (smoothClosedSupportNeighborhood X Y i m d z V hzV)
      (flattenedSupportNeighborhood_subset_source _ _ _ _ _) := by
  apply chartNormalProjectionCoclass_unique
    (Fin m → ℂ) (d - m)
    (smoothClosedSupportRestrictionChart X Y i m d z V)
    (Set.range (Point.map i))
    (smoothClosedSupportRestrictionChart_mem_range_iff X Y i m d z V)
    (Point.map i z)
    (smoothClosedSupportRestrictionChart_mem_source X Y i m d z V hzV)
    (congrArg Prod.snd (smoothClosedSupportRestrictionChart_center X Y i m d z V))
  exact smoothClosedSupportNormalCoclass_apply_class X Y i m d z V hzV

/-- On a common smaller neighborhood, restriction of the old local coclass is exactly
the holomorphic-chart coclass. Both maps are the same literal normal projection. -/
theorem smoothClosedSupportNormalCoclass_restrict_eq_chart
    (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V)
    (W : Set (ComplexPoint X))
    (hWV : W ⊆ smoothClosedSupportNeighborhood X Y i m d z V hzV)
    (hW : W ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    relativeCohomologyMap ℚ (2 * (d - m))
      (neighborhoodSupportInclusionPairMap hWV (Set.range (Point.map i)))
      (smoothClosedSupportNormalCoclass X Y i m d z V hzV) =
    smoothClosedSupportChartCoclass X Y i m d z W hW := by
  rw [smoothClosedSupportNormalCoclass_eq_projection]
  exact chartNormalProjectionCoclass_restrict (Fin m → ℂ) (d - m)
    (smoothClosedSupportRestrictionChart X Y i m d z V)
    (Set.range (Point.map i))
    (smoothClosedSupportRestrictionChart_mem_range_iff X Y i m d z V)
    hWV (flattenedSupportNeighborhood_subset_source _ _ _ _ _)

end AlgebraicGeometry.ComplexPoint
end
