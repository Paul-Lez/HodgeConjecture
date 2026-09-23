/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

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

/-- The comparison is a quasi-isomorphism on sections on every open set.
This stronger conclusion is essential for applying local normal-slice calculations. -/
theorem supportedSingularToInjectiveComplex_onOpen_quasiIso (U V : Opens X) :
    QuasiIso (((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
      (supportedSingularToInjectiveComplex X hX U)) :=
  TopCat.Sheaf.supportedSections_map_quasiIso_of_flasque X U V
    (singularToConstantInjectiveComplex X hX) 0 0 (fun _ => inferInstance) (fun _ => inferInstance)

/-- Let `X` be Hausdorff, with every open subset paracompact, and with a basis of contractible open
neighborhoods. Let `C` be the sheafified rational singular cochain complex and `I` an injective
resolution of the constant rational sheaf. For opens `U,V ⊆ X`, the augmentation-preserving
comparison `C → I` induces this isomorphism `H^n(Γ_{X \ U}(V,C)) ≅ H^n(Γ_{X \ U}(V,I))`. Here
supported sections on `V` are sections vanishing on `V ∩ U`, and `n` is any integer. -/
def supportedSingularInjectiveHomologyIso (U V : Opens X) (n : ℤ) :
    ((((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (supportedRationalSingularCochainComplex X U))).homology n ≅
    ((((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (((TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj
        (rationalConstantInjectiveComplex X)))).homology n :=
  let f := ((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
    (supportedSingularToInjectiveComplex X hX U)
  letI : QuasiIso f := supportedSingularToInjectiveComplex_onOpen_quasiIso X hX U V
  asIso (HomologicalComplex.homologyMap f n)

end AlgebraicTopology.Singular
