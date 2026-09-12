/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder
open scoped Simplicial

namespace AlgebraicTopology.Singular

/-- The homology isomorphism induced by affine realization of the standard simplicial
boundary. -/
def standardAffineBoundaryHomologyIso (n : ℕ) :
    ((∂Δ[n + 2] : SSet.{0}).chainComplex
      (ModuleCat.of ℚ ℚ)).homology (n + 1) ≅
    ((TopCat.toSSet.obj (standardPuncturedPair (n + 2)).snd).chainComplex
      (ModuleCat.of ℚ ℚ)).homology (n + 1) :=
  (standardAffineBoundaryChainHomotopyEquiv (n + 2)).toHomologyIso (n + 1)

@[simp]
lemma standardAffineBoundaryHomologyIso_hom (n : ℕ) :
    (standardAffineBoundaryHomologyIso n).hom =
      standardAffineBoundaryHomologyMap n :=
  rfl

end AlgebraicTopology.Singular
