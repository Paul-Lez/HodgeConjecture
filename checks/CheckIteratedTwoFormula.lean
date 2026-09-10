import Other.AlgebraicGeometry.AnalyticIteratedTransitionClass

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec (.of ℂ)))

theorem check_analyticIteratedTransitionExtClass_two
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
