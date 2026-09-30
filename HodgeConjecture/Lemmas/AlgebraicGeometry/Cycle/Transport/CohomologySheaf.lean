/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedSingularModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.LocalHomology
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularSectionCohomology

/-!
# Cohomology-sheaf concentration for smooth closed supports

Concentration lemmas for the supported injective model.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- For a closed support `S`, this is the complex `Γ_S(I^•)` of subsheaves of the ambient rational
injective resolution `I^•` whose sections vanish outside `S`. -/
def complexSupportInjectiveComplex (S : Closeds (ComplexPoint X)) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  ((TopCat.Sheaf.sheafSectionsSupportedOutside
    (TopCat.of (ComplexPoint X))
    S.compl).mapHomologicalComplex ℤᵘᵖ).obj
      (ambientRationalInjectiveComplex X)

instance complexSupportInjectiveComplex_isStrictlyGE (S : Closeds (ComplexPoint X)) :
    (complexSupportInjectiveComplex X S).IsStrictlyGE 0 := by
  dsimp [complexSupportInjectiveComplex]
  infer_instance

/-- Let `X` be a smooth integral projective scheme over `ℂ`, `Y = X(ℂ)` with its analytic topology,
`S ⊆ Y` closed, and `V ⊆ Y` open. For an injective resolution `I` of the constant rational
sheaf, this additive equivalence identifies `H^n(Γ_S(V,I))` with relative singular cohomology
`H^n(V,V \ S;ℚ)`. Here `Γ_S(V,I^q)` consists of sections over `V` that vanish off `S`. -/
def complexSupportInjectiveSectionCohomologyEquiv (S : Closeds (ComplexPoint X))
    (V : Opens (ComplexPoint X)) (n : ℕ) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X S))).homology (n : ℤ) ≃+
        RelativeCohomology ℚ (neighborhoodSupportComplementPair
          (V : Set (ComplexPoint X)) (S : Set (ComplexPoint X))) n :=
  letI : ∀ W : Opens (ComplexPoint X), ParacompactSpace W := openParacompactSpace X
  (complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)).symm.addCommGroupIsoToAddEquiv
    |>.trans (supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint X)) S S.isClosed V n)

end AlgebraicGeometry.ComplexPoint

end
