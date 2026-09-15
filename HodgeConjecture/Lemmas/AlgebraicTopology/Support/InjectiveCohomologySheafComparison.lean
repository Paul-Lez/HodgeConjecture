/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularCohomologySheafComparison
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SingularFlasqueModel

/-!
# Supported injective cohomology and relative cohomology

The rational injective model agrees with relative cohomology on suitable spaces.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace TopCat.Sheaf

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0})
  (hX : ∀ (x : X) (V : Opens X), x ∈ V →
    ∃ W : Opens X, x ∈ W ∧ ContractibleSpace W ∧ W ≤ V)
  [T2Space X] [∀ V : Opens X, ParacompactSpace V]

/-- Supported injective sections compute relative cohomology of the local pair. -/
def supportedRationalInjectiveSectionCohomologyEquivRelative
    (S : Closeds X) (V : Opens X) (n : ℕ) :
    (((Γ_[V].mapHomologicalComplex (.up ℤ)).obj
      (((sectionsSupportedOutside X S.compl).mapHomologicalComplex (.up ℤ)).obj
          (rationalConstantInjectiveComplex X))).homology (n : ℤ)) ≃+
      RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (V : Set X) S) n :=
  (supportedSingularInjectiveHomologyIso X hX S.compl V
      (n : ℤ)).symm.addCommGroupIsoToAddEquiv
    |>.trans (supportedRationalSingularSectionCohomologyEquivSupportComplement
      X S S.isClosed V n)

/-- The supported injective cohomology sheaf is the local relative-cohomology sheaf. -/
def supportedRationalInjectiveCohomologySheafIsoRelative
    (S : Closeds X) (n : ℕ) :
    ((((sectionsSupportedOutside X S.compl).mapHomologicalComplex
      (.up ℤ)).obj
        (rationalConstantInjectiveComplex X)).homology (n : ℤ)) ≅
      supportRelativeCohomologySheaf X S n :=
  (asIso (HomologicalComplex.homologyMap
    (supportedSingularToInjectiveComplex X hX S.compl) (n : ℤ))).symm ≪≫
    supportedSingularCohomologySheafIsoRelative X S S.isClosed n

end AlgebraicTopology.Singular
