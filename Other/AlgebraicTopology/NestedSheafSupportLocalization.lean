/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.NestedLocalization
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsNaturality
public import HodgeConjecture.Mathlib.CategoryTheory.Abelian.KernelCompositionShortExact
public import Mathlib.Algebra.Homology.HomologySequence
public import Other.AlgebraicTopology.DerivedSheafSupportLocalization

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

/-- The extension equivalence is the inverse of actual restriction, rather
than an arbitrarily chosen linear equivalence between cohomology groups. -/
def nestedSupportRestrictionHomologyIsoOfVanishing (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)]
    (n : ℤ)
    (hn : IsZero ((nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁.homology n))
    (hn₁ : IsZero
      ((nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁.homology (n + 1))) :
    (nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₂.homology n ≅
      (nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₃.homology n := by
  have := nestedSupportRestriction_homologyMap_isIso_of_vanishing X h W K n hn hn₁
  exact asIso (HomologicalComplex.homologyMap
    (nestedSupportRestrictionSectionsComplexShortComplex X h W K).g n)

@[simp]
lemma nestedSupportRestrictionHomologyIsoOfVanishing_hom (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)]
    (n : ℤ)
    (hn : IsZero ((nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁.homology n))
    (hn₁ : IsZero
      ((nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁.homology (n + 1))) :
    (nestedSupportRestrictionHomologyIsoOfVanishing X h W K n hn hn₁).hom =
      HomologicalComplex.homologyMap
        (nestedSupportRestrictionSectionsComplexShortComplex X h W K).g n := rfl
end TopCat.Sheaf
