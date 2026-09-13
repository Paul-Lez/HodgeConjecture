/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.CohomologyStalkVanishing
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FlasqueComparison
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenRestriction
public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.ShortExactQuasiIso
public import Other.AlgebraicTopology.DerivedSheafSupportLocalization

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

/-- The canonical inclusion into the restriction fiber is a quasi-isomorphism
for actual flasque coefficient complexes. -/
lemma supportRestrictionToFiber_quasiIso_of_flasque
    (V : Opens X) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
    (hK : ∀ n, (K.X n).IsFlasque) :
    QuasiIso (supportRestrictionToFiber X U V K) :=
  CochainComplex.mappingCocone.quasiIso_liftShortComplex _
    (supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V K hK)
end TopCat.Sheaf
