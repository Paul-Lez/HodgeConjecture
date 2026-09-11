/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothClosedSupportLocalHomology
public import HodgeConjecture.Lemmas.AlgebraicGeometry.HolomorphicClosedImmersionCharts
public import HodgeConjecture.Lemmas.AlgebraicTopology.NormalProjectionOverlap

/-!
# Exactly normalized smooth-support coclasses on actual overlaps

The previously constructed local normal coclass is the pullback of the fixed complex
normal coclass along the actual normal coordinate projection. The actual holomorphic
closed-immersion charts prove that these coclasses agree on sufficiently small common
ambient neighborhoods. No transition compatibility or purity equivalence is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- Actual normal-projection coclass on any subset of a holomorphic flattening chart. -/
def smoothClosedSupportChartCoclass (W : Set (ComplexPoint X))
    (hW : W ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    RelativeCohomology ℚ (neighborhoodSupportComplementPair W (Set.range (Point.map i)))
      (2 * (d - m)) :=
  chartNormalProjectionCoclass (Fin m → ℂ) (d - m)
    (closedImmersionHolomorphicFlatteningChart X Y i m d z)
    (Set.range (Point.map i))
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z) W hW

variable (z' : ComplexPoint Y)

end AlgebraicGeometry.ComplexPoint
