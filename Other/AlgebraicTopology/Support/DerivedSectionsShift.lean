/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsShift

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

attribute [local instance] supportSheafHasDerivedCategory

attribute [local instance] supportGroupsHasDerivedCategory

/-- The canonical natural isomorphism `RΓ_Z(K[n]) ≅ (RΓ_Z K)[n]`. -/
def derivedSheafSectionsWithClosedSupportShiftIso (Z : Closeds X) (n : ℤ) :
    shiftFunctor (DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X)) n ⋙
        derivedSheafSectionsWithClosedSupport X Z ≅
      derivedSheafSectionsWithClosedSupport X Z ⋙
        shiftFunctor (DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X)) n :=
  (derivedSheafSectionsWithClosedSupport X Z).commShiftIso n
end TopCat.Sheaf
