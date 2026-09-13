/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.EuclideanVanishing
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.ChainStalk

/-!
# Local homology concentration on a smooth complex scheme

The compressed-chart map is an isomorphism in every local-homology degree, by
neighborhood excision. Euclidean local homology vanishing therefore proves concentration
in real dimension `2*d`, and stalk exactness gives the corresponding homology-sheaf
vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicTopology.Singular

/-- Complex coordinate space has local homology only in twice its complex dimension. -/
theorem standardComplexLocalHomology_isZero_of_ne (d n : ℕ) (hn : n ≠ 2 * d) :
    IsZero (RelativeHomology ℚ (standardComplexPuncturedPair d) n) :=
  (standardLocalHomology_isZero_of_ne (d * 2) n (by omega)).of_iso
    ((relativeHomologyFunctor ℚ n).mapIso (standardComplexRealPairIso d))

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ))) (d : ℕ)

end AlgebraicGeometry.ComplexPoint
