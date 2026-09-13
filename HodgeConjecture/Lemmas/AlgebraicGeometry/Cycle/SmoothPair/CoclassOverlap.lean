/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothPair.CoclassOverlap

/-!
# Exactly normalized smooth-support coclasses on overlaps

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothPair.CoclassOverlap`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- Restriction is the map induced by the inclusion of support-complement pairs. -/
theorem smoothClosedSupportChartCoclass_restrict
    {W V : Set (ComplexPoint X)} (hWV : W ⊆ V)
    (hV : V ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    relativeCohomologyMap ℚ (2 * (d - m))
      (neighborhoodSupportInclusionPairMap hWV (Set.range (Point.map i)))
      (smoothClosedSupportChartCoclass X Y i m d z V hV) =
    smoothClosedSupportChartCoclass X Y i m d z W (hWV.trans hV) :=
  chartNormalProjectionCoclass_restrict _ _ _ _ _ hWV hV

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

variable (z' : ComplexPoint Y)

/-- Exactly normalized ambient coclass agreement for the closed-immersion charts.
The only inputs are smoothness, the closed immersion, and membership in its chart
overlap and image. Holomorphicity and invertibility of the normal derivative are proved. -/
theorem exists_open_smoothClosedSupportChartCoclass_eq
    (x : ComplexPoint X) (hxS : x ∈ Set.range (Point.map i))
    (hx : x ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
    (hx' : x ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z').source) :
    ∃ (W : Opens (ComplexPoint X))
      (hW : (W : Set _) ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
      (hW' : (W : Set _) ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z').source),
      x ∈ W ∧ smoothClosedSupportChartCoclass X Y i m d z W hW =
        smoothClosedSupportChartCoclass X Y i m d z' W hW' := by
  let e := closedImmersionHolomorphicFlatteningChart X Y i m d z
  let e' := closedImmersionHolomorphicFlatteningChart X Y i m d z'
  have ht : e x ∈ (closedImmersionNormalTransition X Y i m d z z').source := by
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ e'.source
    rwa [e.left_inv hx]
  exact exists_open_chartNormalProjectionCoclass_eq (d - m) e e' (Set.range (Point.map i))
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z)
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z')
    x hx ((closedImmersionHolomorphicFlatteningChart_mem_range_iff
      X Y i m d z x hx).mp hxS) hx'
    (analyticAt_closedImmersionNormalTransition X Y i m d z z' (e x) ht)
    (analyticAt_closedImmersionNormalTransition_symm X Y i m d z z' (e x) ht)

end AlgebraicGeometry.ComplexPoint
