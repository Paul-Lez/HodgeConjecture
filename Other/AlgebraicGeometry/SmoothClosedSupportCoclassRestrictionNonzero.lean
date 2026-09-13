/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.CoclassOverlap
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.RelativeCohomologySheaf

/-!
# Nonvanishing of normal coclasses after restriction

A normal coclass remains nonzero on every open neighborhood of its center: a smaller
normal-model neighborhood inside that open still has a normal class on which it evaluates to one.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)
  (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V)

/-- The normal coclass is nonzero, as witnessed by its normalized normal class. -/
theorem smoothClosedSupportNormalCoclass_ne_zero :
    smoothClosedSupportNormalCoclass X Y i m d z V hzV ≠ 0 := by
  intro h
  have heval := smoothClosedSupportNormalCoclass_apply_class X Y i m d z V hzV
  rw [h, map_zero, LinearMap.zero_apply] at heval
  exact zero_ne_one heval

/-- Restricting a normal coclass to any open neighborhood of its center preserves nonvanishing. -/
theorem smoothClosedSupportNormalCoclass_restrict_ne_zero
    (W : Opens (ComplexPoint X))
    (hWU : W ≤ smoothClosedSupportNeighborhood X Y i m d z V hzV)
    (hzW : Point.map i z ∈ W) :
    relativeCohomologyMap ℚ (2 * (d - m))
      (neighborhoodSupportInclusionPairMap hWU (Set.range (Point.map i)))
      (smoothClosedSupportNormalCoclass X Y i m d z V hzV) ≠ 0 := by
  let T := smoothClosedSupportNeighborhood X Y i m d z W hzW
  have hTW : T ≤ W := smoothClosedSupportNeighborhood_le X Y i m d z W hzW
  have hTU : T ≤ smoothClosedSupportNeighborhood X Y i m d z V hzV := hTW.trans hWU
  have heq : relativeCohomologyMap ℚ (2 * (d - m))
      (neighborhoodSupportInclusionPairMap hTU (Set.range (Point.map i)))
      (smoothClosedSupportNormalCoclass X Y i m d z V hzV) =
      smoothClosedSupportNormalCoclass X Y i m d z W hzW := by
    rw [smoothClosedSupportNormalCoclass_eq_projection,
      smoothClosedSupportNormalCoclass_eq_projection]
    exact chartNormalProjectionCoclass_restrict (Fin m → ℂ) (d - m)
      (smoothClosedSupportRestrictionChart X Y i m d z V) (Set.range (Point.map i))
      (smoothClosedSupportRestrictionChart_mem_range_iff X Y i m d z V)
      hTU (flattenedSupportNeighborhood_subset_source _ _ _ _ _)
  intro hzero
  have h := congrArg (relativeCohomologyMap ℚ (2 * (d - m))
    (neighborhoodSupportInclusionPairMap hTW (Set.range (Point.map i)))) hzero
  rw [map_zero, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    neighborhoodSupportInclusionPairMap_comp hTW hWU, heq] at h
  exact smoothClosedSupportNormalCoclass_ne_zero X Y i m d z W hzW h

end AlgebraicGeometry.ComplexPoint
