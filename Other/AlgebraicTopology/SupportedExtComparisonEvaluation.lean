/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.CohomologyInjectiveModel

@[expose] public noncomputable section

open CategoryTheory Limits Abelian Opposite TopologicalSpace

namespace TopCat.Sheaf

variable (X : TopCat.{0}) (U V W : Opens X) (hW : V ⊓ U = W)

variable [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]

local instance supportedExtComparisonHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat) :=
  HasDerivedCategory.standard _

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
lemma relHAddEquivSupportedSectionsHomology_apply
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    [I.IsKInjective]
    (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι]
    (n : ℕ) (x : CategoryTheory.Sheaf.relH F n (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    relHAddEquivSupportedSectionsHomology X U V W hW F I ι n x =
      (CategoryTheory.Iso.addCommGroupIsoToAddEquiv
        (HomologicalComplex.homologyMapIso
          (homComplexPairSheafIsoSupportedSections X U V W hW I) n))
        ((CochainComplex.HomComplex.homologyAddEquiv
          ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' X U V W hW)) I n).symm
          (CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass _ I n
            (isoHomCongrAddEquiv (Iso.refl _)
              ((shiftFunctor _ (n : ℤ)).mapIso
                (asIso (DerivedCategory.Q.map ι)))
              (Ext.homAddEquiv x)))) := by
  rfl

end TopCat.Sheaf
