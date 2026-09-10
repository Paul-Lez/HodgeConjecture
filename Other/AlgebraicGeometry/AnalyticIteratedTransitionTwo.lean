/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticIteratedTransitionClass

/-!
# The explicit two-step iterated transition formula

This file records the degree-two expansion of an iterated analytic transition
class.  Keeping the expansion as a small reusable theorem avoids asking the
elaborator to unfold the entire concrete product-cover construction when one
compares it with a nested Mayer--Vietoris class.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec (CommRingCat.of ℂ)))

/-- The morphism between free abelian sheaves induced by the identity open
inclusion is the identity. -/
@[simp]
theorem analyticOpenFreeAbelianMap_id
    (U : Opens (TopCat.of (ComplexPoint X))) :
    analyticOpenFreeAbelianMap X (𝟙 U) = 𝟙 _ := by
  unfold analyticOpenFreeAbelianMap
  simp
  change (presheafToSheaf (Opens.grothendieckTopology
      (TopCat.of (ComplexPoint X))) AddCommGrpCat).map (𝟙 _) =
    𝟙 ((presheafToSheaf (Opens.grothendieckTopology
      (TopCat.of (ComplexPoint X))) AddCommGrpCat).obj _)
  exact (presheafToSheaf (Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))) AddCommGrpCat).map_id _

/-- A two-step iterated transition class is the Yoneda product of the two
successive relative Mayer--Vietoris extensions and evaluation at the deepest
section. -/
theorem analyticIteratedTransitionExtClass_two
    (D : AnalyticIteratedCover X 2) (F : AnalyticAdditiveSheaf X)
    (c : F.obj.obj (.op (D.ambient 2))) :
    analyticIteratedTransitionExtClass X D F c =
      (Abelian.Ext.mk₀ D.topMap).comp
        ((D.stepExt X 0).comp
          ((D.stepExt X 1).comp
            (Abelian.Ext.mk₀ (analyticSectionSheafHom X F (D.ambient 2) c))
            (show 1 + 0 = 1 from rfl))
          (show 1 + 1 = 2 from rfl))
        (show 0 + 2 = 2 from rfl) := by
  unfold analyticIteratedTransitionExtClass AnalyticIteratedCover.boundaryUpTo
  dsimp only
  unfold AnalyticIteratedCover.boundaryUpTo
  dsimp only
  unfold AnalyticIteratedCover.boundaryUpTo
  simp only [Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_assoc]
  rfl

end AlgebraicGeometry.ComplexPoint
