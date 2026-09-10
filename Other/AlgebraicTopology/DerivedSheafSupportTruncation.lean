/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.DerivedSheafSupport
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# From termwise supported chains to actual derived support by truncation

For a coefficient complex cohomologically bounded below by `n`, its good truncation
`τ≥n K` is termwise bounded below and `K → τ≥n K` is a proved quasi-isomorphism.
Applying termwise support to this actual map, then the actual `D⁺` derived-support unit,
and finally inverting derived support of the truncation isomorphism, constructs
`Q(Γ_S K) → RΓ_S(QK)` in the ambient derived category.

The construction does not assume that termwise support preserves quasi-isomorphisms.
It does not assert that the constructed comparison is an isomorphism. In particular,
no acyclicity of the original chain sheaves or termwise lower bound on them is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

local instance supportTruncationSheafDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) := HasDerivedCategory.standard _

variable (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) (n : ℤ)

/-- The actual good truncation as a termwise bounded-below homotopy object. -/
def supportTruncationHomotopyPlus : HomotopyCategory.Plus (Sheaf AddCommGrpCat.{u} X) :=
  ⟨(HomotopyCategory.quotient _ _).obj (K.truncGE n), by
    rw [HomotopyCategory.plus_quotient_obj_iff]
    exact ⟨n, inferInstance⟩⟩

variable [K.IsGE n]

/-- A complex with a proved cohomological lower bound gives its own `D⁺` object. -/
def supportCoefficientPlus : DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X) :=
  ⟨DerivedCategory.Q.obj K, n, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual truncation projection induces this `D⁺` isomorphism. -/
def supportCoefficientTruncationIso :
    supportCoefficientPlus X K n ≅
      DerivedCategory.Plus.Qh.obj (supportTruncationHomotopyPlus X K n) :=
  DerivedCategory.Plus.ι.preimageIso
    (asIso (DerivedCategory.Q.map (K.πTruncGE n)) ≪≫
      ((DerivedCategory.quotientCompQhIso (Sheaf AddCommGrpCat.{u} X)).app (K.truncGE n)).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Its normalization is the actual good-truncation map, not a chosen representative
equivalence. -/
@[reassoc]
lemma supportCoefficientTruncationIso_hom :
    DerivedCategory.Plus.ι.map (supportCoefficientTruncationIso X K n).hom ≫
      (DerivedCategory.quotientCompQhIso (Sheaf AddCommGrpCat.{u} X)).hom.app (K.truncGE n) =
      DerivedCategory.Q.map (K.πTruncGE n) := by
  let f : DerivedCategory.Plus.ι.obj (supportCoefficientPlus X K n) ⟶
      DerivedCategory.Plus.ι.obj
        (DerivedCategory.Plus.Qh.obj (supportTruncationHomotopyPlus X K n)) :=
    DerivedCategory.Q.map (K.πTruncGE n) ≫
      (DerivedCategory.quotientCompQhIso (Sheaf AddCommGrpCat.{u} X)).inv.app (K.truncGE n)
  change DerivedCategory.Plus.ι.map
    (DerivedCategory.Plus.ι.preimage (X := supportCoefficientPlus X K n)
      (Y := DerivedCategory.Plus.Qh.obj (supportTruncationHomotopyPlus X K n)) f) ≫ _ = _
  rw [Functor.map_preimage]
  dsimp only [f]
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The canonical map from localized termwise support to actual derived support, using a
proved lower bound only to select good truncation. This is not claimed to be invertible. -/
def termwiseToDerivedSheafSupport (S : Closeds X) :
    DerivedCategory.Q.obj
      (((sheafSectionsWithClosedSupport X S).mapHomologicalComplex (.up ℤ)).obj K) ⟶
    DerivedCategory.Plus.ι.obj
      ((derivedSheafSectionsWithClosedSupport X S).obj (supportCoefficientPlus X K n)) :=
  DerivedCategory.Q.map
      (((sheafSectionsWithClosedSupport X S).mapHomologicalComplex (.up ℤ)).map (K.πTruncGE n)) ≫
    (DerivedCategory.quotientCompQhIso (Sheaf AddCommGrpCat.{u} X)).inv.app
      (((sheafSectionsWithClosedSupport X S).mapHomologicalComplex (.up ℤ)).obj (K.truncGE n)) ≫
    DerivedCategory.Plus.ι.map
      ((derivedSheafSectionsWithClosedSupportUnit X S).app (supportTruncationHomotopyPlus X K n)) ≫
    DerivedCategory.Plus.ι.map
      ((derivedSheafSectionsWithClosedSupport X S).map (supportCoefficientTruncationIso X K n).inv)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Transporting the comparison to the truncated coefficient gives precisely the actual
termwise truncation map followed by the actual derived-support unit. -/
@[reassoc]
lemma termwiseToDerivedSheafSupport_truncation (S : Closeds X) :
    termwiseToDerivedSheafSupport X K n S ≫
      DerivedCategory.Plus.ι.map
        ((derivedSheafSectionsWithClosedSupport X S).map (supportCoefficientTruncationIso X K n).hom) =
    DerivedCategory.Q.map
      (((sheafSectionsWithClosedSupport X S).mapHomologicalComplex (.up ℤ)).map (K.πTruncGE n)) ≫
      (DerivedCategory.quotientCompQhIso (Sheaf AddCommGrpCat.{u} X)).inv.app
        (((sheafSectionsWithClosedSupport X S).mapHomologicalComplex (.up ℤ)).obj (K.truncGE n)) ≫
      DerivedCategory.Plus.ι.map
        ((derivedSheafSectionsWithClosedSupportUnit X S).app (supportTruncationHomotopyPlus X K n)) := by
  have hcancel : DerivedCategory.Plus.ι.map
      ((derivedSheafSectionsWithClosedSupport X S).map (supportCoefficientTruncationIso X K n).inv) ≫
      DerivedCategory.Plus.ι.map
        ((derivedSheafSectionsWithClosedSupport X S).map (supportCoefficientTruncationIso X K n).hom) =
      𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [termwiseToDerivedSheafSupport, Category.assoc, hcancel]
  erw [Category.comp_id]

end TopCat.Sheaf
