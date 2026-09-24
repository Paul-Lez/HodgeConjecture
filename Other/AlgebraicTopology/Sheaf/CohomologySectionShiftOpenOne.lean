/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.Sheaf.CohomologySectionShiftOnOpen

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace TopCat.Sheaf

/-- The degree-one section shift commutes with actual open restriction. -/
lemma sectionCohomologyToSheafSection_shift_openRestriction_one
    (Y : TopCat.{0}) (U : Opens Y)
    (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ)
    (W : Opens (TopCat.of U))
    (x : (((supportEvaluation (TopCat.of U) W).mapHomologicalComplex (.up ℤ)).obj
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        (.up ℤ)).obj (K⟦(1 : ℤ)⟧))).homology 0) :
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let H := F.mapHomologicalComplex (.up ℤ)
    let V := U.isOpenEmbedding.functor.obj W
    (sectionCohomologySheafShiftMap Y K 1 0 1 (by omega)).hom.app (op V)
      (sectionCohomologyToSheafSection Y (K⟦(1 : ℤ)⟧) 0 V x) =
      ((K.sc 1).mapHomologyIso F).hom.hom.app (op W)
        ((sectionCohomologySheafShiftMap (TopCat.of U) (H.obj K)
          1 0 1 (by omega)).hom.app (op W)
          (sectionCohomologyToSheafSection (TopCat.of U) ((H.obj K)⟦(1 : ℤ)⟧)
            0 W
            (HomologicalComplex.homologyMap
              (((supportEvaluation (TopCat.of U) W).mapHomologicalComplex
                (.up ℤ)).map ((H.commShiftIso (1 : ℤ)).hom.app K)) 0 x))) := by
  dsimp only
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let H := F.mapHomologicalComplex (.up ℤ)
  let V := U.isOpenEmbedding.functor.obj W
  let Γ := (supportEvaluation (TopCat.of U) W).mapHomologicalComplex (.up ℤ)
  let x' := HomologicalComplex.homologyMap
    (Γ.map ((H.commShiftIso (1 : ℤ)).hom.app K)) 0 x
  let y' := ShortComplex.homologyMap
    (((evaluation (Opens (TopCat.of U))ᵒᵖ AddCommGrpCat).obj (op W)).mapShortComplex.map
      (sectionCohomologyPresheafShiftShortComplex (TopCat.of U) (H.obj K)
        1 0 1 (by omega))) x'
  have hY := ConcreteCategory.congr_hom
    (sectionCohomologyToSheafSection_shift_naturality Y K 1 0 1 (by omega) V) x
  have hU := ConcreteCategory.congr_hom
    (sectionCohomologyToSheafSection_shift_naturality
      (TopCat.of U) (H.obj K) 1 0 1 (by omega) W) x'
  have hK := ConcreteCategory.congr_hom
    (sectionCohomologyToSheafSection_openRestriction Y U K 1 W) y'
  simp only [ConcreteCategory.comp_apply] at hY hU hK
  dsimp only [H] at hU hK
  dsimp only [y'] at hK
  have hmap := sectionCohomologyShift_onOpen_homology_one Y U K W
  have hmap' := ConcreteCategory.congr_hom hmap x
  simp only [ConcreteCategory.comp_apply] at hmap'
  have hU' := congrArg (fun z =>
      (ConcreteCategory.hom (((K.sc 1).mapHomologyIso F).hom.hom.app (op W))) z)
    hU
  exact hY.symm.trans ((congrArg (fun z =>
    (ConcreteCategory.hom (sectionCohomologyToSheafSection Y K 1 V)) z) hmap').trans
    (hK.symm.trans hU'))

end TopCat.Sheaf
