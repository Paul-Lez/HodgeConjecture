/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticNestedTransitionClass

/-!
# Relative residue criterion for nested analytic transition classes

This file separates the two summands of the outer Mayer--Vietoris restriction in degree one.
Consequently, a relative residue on overlap cohomology only has to vanish on restrictions from
each outer open separately in order to detect the nested degree-two class.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 5000

variable (X : Over (Spec (CommRingCat.of ℂ)))

local instance nestedRelativeResidueSheafAbelian : Abelian (AnalyticAdditiveSheaf X) :=
  CategoryTheory.sheafIsAbelian

local instance nestedRelativeResidueHasExt : HasExt.{1} (AnalyticAdditiveSheaf X) :=
  analyticHasExt X

/-- Restriction of degree-one sheaf cohomology from an analytic open to a smaller open. -/
def analyticOpenExtRestriction (F : AnalyticAdditiveSheaf X)
    {W U : Opens (TopCat.of (ComplexPoint X))} (hWU : W ≤ U) :
    Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X U) F 1 →+
      Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X W) F 1 :=
  (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
    (analyticOpenFreeAbelianMap X (homOfLE hWU))).precomp F rfl

/-- The outer Mayer--Vietoris restriction is the difference of the restrictions of its two
biproduct components. -/
theorem analyticOuterExtRestriction_eq_sub (F : AnalyticAdditiveSheaf X)
    (U V : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (γ : Abelian.Ext.{1}
      (analyticOpenFreeAbelianSheaf X U ⊞ analyticOpenFreeAbelianSheaf X V) F 1) :
    analyticOuterExtRestriction X F U V hcover γ =
      analyticOpenExtRestriction X F inf_le_left
        ((Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X) biprod.inl).comp γ rfl) -
      analyticOpenExtRestriction X F inf_le_right
        ((Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X) biprod.inr).comp γ rfl) := by
  unfold analyticOuterExtRestriction analyticOpenExtRestriction
  change (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
      (biprod.lift
        (analyticOpenFreeAbelianMap X (homOfLE inf_le_left))
        (-analyticOpenFreeAbelianMap X (homOfLE inf_le_right)))).comp γ rfl = _
  rw [biprod.lift_eq, Abelian.Ext.mk₀_add, Abelian.Ext.add_comp]
  change
    (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
      (analyticOpenFreeAbelianMap X (homOfLE inf_le_left) ≫ biprod.inl)).comp γ rfl +
    (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
      ((-analyticOpenFreeAbelianMap X (homOfLE inf_le_right)) ≫ biprod.inr)).comp γ rfl =
    (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
      (analyticOpenFreeAbelianMap X (homOfLE inf_le_left))).comp
        ((Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X) biprod.inl).comp γ rfl) rfl -
    (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
      (analyticOpenFreeAbelianMap X (homOfLE inf_le_right))).comp
        ((Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X) biprod.inr).comp γ rfl) rfl
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, Abelian.Ext.mk₀_comp_mk₀_assoc,
    Preadditive.neg_comp, Abelian.Ext.mk₀_neg, Abelian.Ext.neg_comp,
    sub_eq_add_neg]

/-- A relative residue detects the nested degree-two class when it vanishes separately on
degree-one classes extending across either outer open and is nonzero on the inner transition
class.  This is the exact interface needed from fiberwise Serre trace or proper base change. -/
theorem analyticNestedTransitionExtClass_ne_zero_of_relative_residue
    (F : AnalyticAdditiveSheaf X)
    (U V A B : Opens (TopCat.of (ComplexPoint X))) (hcover : U ⊔ V = ⊤)
    (hA : A ≤ U ⊓ V) (hB : B ≤ U ⊓ V) (hoverlap : A ⊔ B = U ⊓ V)
    (c : F.obj.obj (.op (A ⊓ B)))
    {G : Type*} [AddCommGroup G]
    (residue :
      Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X (U ⊓ V)) F 1 →+ G)
    (residue_left : ∀ α : Abelian.Ext.{1}
      (analyticOpenFreeAbelianSheaf X U) F 1,
      residue (analyticOpenExtRestriction X F inf_le_left α) = 0)
    (residue_right : ∀ α : Abelian.Ext.{1}
      (analyticOpenFreeAbelianSheaf X V) F 1,
      residue (analyticOpenExtRestriction X F inf_le_right α) = 0)
    (residue_inner : residue
      (analyticRelativeTransitionExtClass X F A B (U ⊓ V)
        hA hB hoverlap c) ≠ 0) :
    analyticNestedTransitionExtClass X F U V A B
      hcover hA hB hoverlap c ≠ 0 := by
  apply analyticNestedTransitionExtClass_ne_zero_of_ext_functional X F U V A B
    hcover hA hB hoverlap c residue
  · intro γ
    rw [analyticOuterExtRestriction_eq_sub]
    simp only [map_sub, residue_left, residue_right, sub_self]
  · exact residue_inner

end AlgebraicGeometry.ComplexPoint
