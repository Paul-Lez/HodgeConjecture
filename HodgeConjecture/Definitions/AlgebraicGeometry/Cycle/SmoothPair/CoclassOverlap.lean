/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.LocalHomology
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionOverlap

/-!
# Exactly normalized smooth-support coclasses on overlaps

The local normal coclass is the pullback of the fixed complex
normal coclass along the normal coordinate projection. The holomorphic
closed-immersion charts prove that these coclasses agree on sufficiently small common ambient
neighborhoods.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- Let `i : Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`. Put `S =
i(Y(ℂ))` and `c = d-m`. For `z ∈ Y(ℂ)` and a subset `W` of the chosen normal chart at `i(z)`,
this class in `H^{2c}(W,W \ S;ℚ)` is the pullback of the class in `H^{2c}(ℂ^c,ℂ^c \ {0};ℚ)`
evaluating to `1` on the complex orientation class. The map of pairs uses the normal coordinate,
whose zero set is `S`. -/
def smoothClosedSupportChartCoclass (W : Set (ComplexPoint X))
    (hW : W ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    RelativeCohomology ℚ (neighborhoodSupportComplementPair W
      -- `Y(ℂ) ⊆ X(ℂ)`, the image of the closed immersion `i`.
      (Set.range (Point.map i)))
      -- Twice the codimension of `Y` in `X`.
      (2 * (d - m)) :=
  chartNormalProjectionCoclass (Fin m → ℂ) (d - m)
    (closedImmersionHolomorphicFlatteningChart X Y i m d z)
    (Set.range (Point.map i))
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z) W hW

end AlgebraicGeometry.ComplexPoint
