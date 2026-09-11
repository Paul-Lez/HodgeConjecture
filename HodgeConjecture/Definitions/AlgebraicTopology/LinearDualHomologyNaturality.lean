/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.SingularCochainCohomology
public import HodgeConjecture.Lemmas.AlgebraicTopology.SingularSubdivisionCochainSheaf
public import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality

/-! # Naturality of the actual universal-coefficient pairing -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Field R]

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type u} [Field R]
  {K L : ChainComplex (ModuleCat.{u} R) ℕ}

/-- The actual cochain-complex universal-coefficient identification. -/
def linearDualHomologyEquiv (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.linearDualCochainComplex.homology n ≃ₗ[R] Module.Dual R (K.homology n) :=
  (ShortComplex.homologyMapIso (linearDualCochainComplexScIso K n)).toLinearEquiv.trans
    (K.sc n).linearDualHomologyEquiv

end HomologicalComplex
