/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.DerivedClosedSupportTruncation
public import Other.AlgebraicTopology.DerivedSheafSupportForget

/-!
# Support naturality of the termwise-to-derived comparison

The good-truncation comparison from termwise closed-support sections to derived
closed-support sections commutes with enlargement of the closed support.  This
pins the comparison to the actual kernel inclusions and, in particular, identifies
forgetting support with the literal inclusion of the underlying cocycle.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{u})

local instance truncationNaturalitySheafDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) := HasDerivedCategory.standard _

local instance truncationNaturalityGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _

variable (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) (n : ℤ) [K.IsGE n]

/-- The actual good-truncation comparison commutes with enlargement of closed support. -/
@[reassoc]
theorem termwiseToDerivedClosedSupport_naturality {S T : Closeds X} (h : S ≤ T) :
    termwiseToDerivedClosedSupport X K n S ≫
        DerivedCategory.Plus.ι.map
          ((derivedClosedSupportSectionsMap X h).app (supportCoefficientPlus X K n)) =
      DerivedCategory.Q.map
          (((closedSupportSectionsMap X h).mapHomologicalComplex (.up ℤ)).app K) ≫
        termwiseToDerivedClosedSupport X K n T := by
  simp only [termwiseToDerivedClosedSupport, Category.assoc]
  rw [← DerivedCategory.Plus.ι.map_comp]
  rw [(derivedClosedSupportSectionsMap X h).naturality
    (supportCoefficientTruncationIso X K n).inv]
  rw [DerivedCategory.Plus.ι.map_comp]
  rw [← Functor.map_comp_assoc]
  rw [derivedClosedSupportSectionsMap_unit_app]
  rw [Functor.map_comp_assoc]
  erw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  have hn := congrArg DerivedCategory.Q.map
    (NatTrans.mapHomologicalComplex_naturality
      (closedSupportSectionsMap X h) (K.πTruncGE n))
  simp only [Functor.map_comp] at hn
  dsimp only [supportTruncationHomotopyPlus] at *
  simp only [ObjectProperty.ι_obj, HomotopyCategory.quotient_obj_as] at *
  rw [← Category.assoc]
  erw [hn]
  simp only [Category.assoc]

/-- Forgetting closed support factors through the literal enlargement to whole-space
support and the canonical whole-space support-forgetting isomorphism. -/
@[reassoc]
theorem termwiseToDerivedClosedSupport_forget (S : Closeds X) :
    termwiseToDerivedClosedSupport X K n S ≫
        DerivedCategory.Plus.ι.map
          ((derivedForgetClosedSupport X S).app (supportCoefficientPlus X K n)) =
      DerivedCategory.Q.map
          (((closedSupportSectionsMap X (show S ≤ (⊤ : Closeds X) from le_top)).mapHomologicalComplex
            (.up ℤ)).app K) ≫
        termwiseToDerivedClosedSupport X K n ⊤ ≫
        DerivedCategory.Plus.ι.map
          ((derivedForgetClosedSupport X ⊤).app (supportCoefficientPlus X K n)) := by
  rw [← Category.assoc]
  rw [← termwiseToDerivedClosedSupport_naturality X K n le_top]
  rw [Category.assoc]
  rw [← DerivedCategory.Plus.ι.map_comp]
  rw [← NatTrans.comp_app]
  rw [derivedClosedSupportSectionsMap_forget]

end TopCat.Sheaf
