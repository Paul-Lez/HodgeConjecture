/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.DerivedSheafSupportTruncation

/-!
# Good truncation and actual group-valued derived closed support

The actual group-valued derived unit after good truncation gives a canonical map from
the localization of the termwise supported-section complex. This does not require
supported sections to preserve quasi-isomorphisms, or the original complex to be
termwise bounded below. The normalization theorem fixes the map to the literal
truncation projection and the actual derived unit.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{u})

local instance closedSupportTruncationSheafDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) := HasDerivedCategory.standard _

local instance closedSupportTruncationGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _

variable (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) (n : ℤ) [K.IsGE n]

/-- Localized actual supported global sections map to the genuine group-valued derived
support functor by good truncation and its actual derived unit. -/
def termwiseToDerivedClosedSupport (S : Closeds X) :
    DerivedCategory.Q.obj
      (((closedSupportSections X S).mapHomologicalComplex (.up ℤ)).obj K) ⟶
    DerivedCategory.Plus.ι.obj
      ((derivedClosedSupportSections X S).obj (supportCoefficientPlus X K n)) :=
  DerivedCategory.Q.map
      (((closedSupportSections X S).mapHomologicalComplex (.up ℤ)).map (K.πTruncGE n)) ≫
    (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv.app
      (((closedSupportSections X S).mapHomologicalComplex (.up ℤ)).obj (K.truncGE n)) ≫
    DerivedCategory.Plus.ι.map
      ((derivedClosedSupportSectionsUnit X S).app (supportTruncationHomotopyPlus X K n)) ≫
    DerivedCategory.Plus.ι.map
      ((derivedClosedSupportSections X S).map (supportCoefficientTruncationIso X K n).inv)

/-- After transport to the truncated coefficient, the comparison is exactly termwise
truncation followed by the actual group-valued derived unit. -/
@[reassoc]
lemma termwiseToDerivedClosedSupport_truncation (S : Closeds X) :
    termwiseToDerivedClosedSupport X K n S ≫
      DerivedCategory.Plus.ι.map
        ((derivedClosedSupportSections X S).map (supportCoefficientTruncationIso X K n).hom) =
    DerivedCategory.Q.map
      (((closedSupportSections X S).mapHomologicalComplex (.up ℤ)).map (K.πTruncGE n)) ≫
    (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv.app
      (((closedSupportSections X S).mapHomologicalComplex (.up ℤ)).obj (K.truncGE n)) ≫
    DerivedCategory.Plus.ι.map
      ((derivedClosedSupportSectionsUnit X S).app (supportTruncationHomotopyPlus X K n)) := by
  have hcancel : DerivedCategory.Plus.ι.map
      ((derivedClosedSupportSections X S).map (supportCoefficientTruncationIso X K n).inv) ≫
      DerivedCategory.Plus.ι.map
        ((derivedClosedSupportSections X S).map (supportCoefficientTruncationIso X K n).hom) =
      𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [termwiseToDerivedClosedSupport, Category.assoc, hcancel]
  erw [Category.comp_id]

end TopCat.Sheaf
