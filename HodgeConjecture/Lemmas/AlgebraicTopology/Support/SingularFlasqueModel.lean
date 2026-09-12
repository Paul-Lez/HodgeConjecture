/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularFlasqueModel

/-!
# Constructions used only in proofs

These were built to prove the results about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularFlasqueModel`.
The statement of the conjecture never inspects them: every path from the statement to one
of them runs through a proof, so proof irrelevance makes their bodies immaterial.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomologicalComplex

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0})

variable (hX : ∀ (x : X) (V : Opens X), x ∈ V →
  ∃ (W : Opens X), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V)

variable [T2Space X] [∀ V : Opens X, ParacompactSpace V]

/-- Actual section-complex cohomology agrees through the normalized comparison. -/
def supportedSingularInjectiveHomologyIso (U V : Opens X) (n : ℤ) :
    ((((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj
      (supportedRationalSingularCochainComplex X U))).homology n ≅
    ((((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj
      (((TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex (.up ℤ)).obj
        (rationalConstantInjectiveComplex X)))).homology n := by
  let f := ((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℤ)).map
    (supportedSingularToInjectiveComplex X hX U)
  let : QuasiIso f := supportedSingularToInjectiveComplex_onOpen_quasiIso X hX U V
  exact asIso (HomologicalComplex.homologyMap f n)

end AlgebraicTopology.Singular
