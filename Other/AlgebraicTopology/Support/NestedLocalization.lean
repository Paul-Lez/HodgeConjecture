/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.NestedLocalization
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsNaturality
public import HodgeConjecture.Mathlib.CategoryTheory.Abelian.KernelCompositionShortExact
public import Mathlib.Algebra.Homology.HomologySequence
public import Other.AlgebraicTopology.Support.RestrictionFiber

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) {U V : Opens X} (h : V ≤ U)

/-- The canonical comparison from sections with the smaller closed support to
the homotopy fiber of restriction away from it inside the larger support. -/
def nestedSupportRestrictionToFiber (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    (nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁ ⟶
      CochainComplex.mappingCocone
        (nestedSupportRestrictionSectionsComplexShortComplex X h W K).g :=
  CochainComplex.mappingCocone.liftShortComplex _

lemma nestedSupportRestrictionToFiber_quasiIso (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    QuasiIso (nestedSupportRestrictionToFiber X h W K) :=
  CochainComplex.mappingCocone.quasiIso_liftShortComplex _
    (nestedSupportRestrictionSectionsComplexShortComplex_shortExact X h W K)

/-- The fiber comparison preserves the literal support-enlargement map. -/
@[reassoc (attr := simp)]
lemma nestedSupportRestrictionToFiber_fst (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    nestedSupportRestrictionToFiber X h W K ≫ CochainComplex.mappingCocone.fst _ =
      (nestedSupportRestrictionSectionsComplexShortComplex X h W K).f :=
  CochainComplex.mappingCocone.liftShortComplex_fst _

end TopCat.Sheaf
