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
