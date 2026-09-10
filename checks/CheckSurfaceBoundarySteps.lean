import Other.AlgebraicGeometry.ExplicitEllipticSurfaceDoubleDlog

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

@[expose] noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem check_analyticOpenFreeAbelianMap_id
    (X : Over (Spec (.of ℂ)))
    (U : Opens (TopCat.of (ComplexPoint X))) :
    analyticOpenFreeAbelianMap X (𝟙 U) = 𝟙 _ := by
  unfold analyticOpenFreeAbelianMap analyticOpenFreeAbelianSheaf
    analyticOpenFreeAbelianPresheaf
  simp

theorem check_surfaceCechIteratedCover_topMap :
    surfaceCechIteratedCover.topMap surfaceVariety =
    (analyticTopFreeAbelianSheafIso surfaceVariety).inv := by
  change (analyticTopFreeAbelianSheafIso surfaceVariety).inv ≫
    analyticOpenFreeAbelianMap surfaceVariety (𝟙 ⊤) = _
  rw [check_analyticOpenFreeAbelianMap_id, Category.comp_id]

theorem check_surfaceCechIteratedCover_stepExt_zero :
    AnalyticIteratedCover.stepExt (X := surfaceVariety)
      surfaceCechIteratedCover 0 = surfaceCechOuterBoundaryExtClass := by
  rfl

theorem check_surfaceCechIteratedCover_stepExt_one :
    AnalyticIteratedCover.stepExt (X := surfaceVariety)
      surfaceCechIteratedCover 1 = surfaceCechInnerBoundaryExtClass := by
  rfl

theorem check_surfaceCechIteratedCover_boundaryUpTo_two :
    AnalyticIteratedCover.boundaryUpTo (X := surfaceVariety)
      surfaceCechIteratedCover 2 le_rfl =
    surfaceCechOuterBoundaryExtClass.comp surfaceCechInnerBoundaryExtClass
      (show 1 + 1 = 2 from rfl) := by
  simp only [AnalyticIteratedCover.boundaryUpTo]
  erw [check_surfaceCechIteratedCover_stepExt_zero,
    check_surfaceCechIteratedCover_stepExt_one]
  rw [Abelian.Ext.mk₀_id_comp]

theorem check_surfaceCechIteratedCover_boundaryExtClass :
    AnalyticIteratedCover.boundaryExtClass (X := surfaceVariety)
      surfaceCechIteratedCover = surfaceCechYonedaBoundaryExtClass := by
  unfold AnalyticIteratedCover.boundaryExtClass
    surfaceCechYonedaBoundaryExtClass
  dsimp only
  rw [check_surfaceCechIteratedCover_topMap]
  erw [check_surfaceCechIteratedCover_boundaryUpTo_two]

theorem check_surfaceNestedTransitionExtClass_eq_yoneda
    (F : AnalyticAdditiveSheaf surfaceVariety)
    (c : F.obj.obj (.op surfaceCechDeepestOpen)) :
    analyticNestedTransitionExtClass surfaceVariety F
        (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
        (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
        surfaceFstCechOpen_cover inf_le_left inf_le_left
        surfaceCechInnerOpen_cover c =
      surfaceCechYonedaBoundaryExtClass.comp
        (Abelian.Ext.mk₀ (analyticSectionSheafHom surfaceVariety F
          surfaceCechDeepestOpen c)) (show 2 + 0 = 2 from rfl) := by
  let a₀ : Abelian.Ext.{1} (constantIntegerSheaf surfaceVariety)
      (analyticOpenFreeAbelianSheaf surfaceVariety ⊤) 0 :=
    Abelian.Ext.mk₀ (analyticTopFreeAbelianSheafIso surfaceVariety).inv
  let δ₀ := surfaceCechOuterBoundaryExtClass
  let δ₁ := surfaceCechInnerBoundaryExtClass
  let s : Abelian.Ext.{1}
      (analyticOpenFreeAbelianSheaf surfaceVariety surfaceCechDeepestOpen) F 0 :=
    Abelian.Ext.mk₀ (analyticSectionSheafHom surfaceVariety F
      surfaceCechDeepestOpen c)
  change a₀.comp (δ₀.comp (δ₁.comp s (show 1 + 0 = 1 from rfl))
      (show 1 + 1 = 2 from rfl)) (show 0 + 2 = 2 from rfl) =
    (a₀.comp (δ₀.comp δ₁ (show 1 + 1 = 2 from rfl))
      (show 0 + 2 = 2 from rfl)).comp s (show 2 + 0 = 2 from rfl)
  rw [← Abelian.Ext.comp_assoc δ₀ δ₁ s
    (show 1 + 1 = 2 from rfl) (show 1 + 0 = 1 from rfl)
    (show 1 + 1 = 2 from rfl)]
  exact (Abelian.Ext.comp_assoc a₀ (δ₀.comp δ₁ rfl) s
    (show 0 + 2 = 2 from rfl) (show 2 + 0 = 2 from rfl)
    (show 0 + 2 = 2 from rfl)).symm

example (F : AnalyticAdditiveSheaf surfaceVariety)
    (c : F.obj.obj (.op surfaceCechDeepestOpen)) :
    analyticNestedTransitionExtClass surfaceVariety F
        (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
        (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
        surfaceFstCechOpen_cover inf_le_left inf_le_left
        surfaceCechInnerOpen_cover c =
      analyticIteratedTransitionExtClass surfaceVariety
        surfaceCechIteratedCover F c := by
  rw [check_surfaceNestedTransitionExtClass_eq_yoneda]
  rw [analyticIteratedTransitionExtClass_eq_boundary_comp]
  rw [check_surfaceCechIteratedCover_boundaryExtClass]
  change surfaceCechYonedaBoundaryExtClass.comp
      (Abelian.Ext.mk₀ (analyticSectionSheafHom surfaceVariety F
        surfaceCechDeepestOpen c)) (show 2 + 0 = 2 from rfl) = _
  rfl

end


end AlgebraicGeometry.ExplicitEllipticCandidate
