/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicTopology.Sheaf.CohomologySectionShiftTransport
public import Other.AlgebraicTopology.Sheaf.CohomologyOpenRestriction
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSectionsLocalization
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TopCat.Sheaf
/-- Evaluation on an open set preserves the prescribed section-cohomology shift. -/
lemma sectionCohomologyPresheafShiftShortComplex_onOpen_homology
    (Y : TopCat.{0}) (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ)
    (s n n' : ℤ) (h : s + n = n') (V : Opens Y) :
    let Γ := supportEvaluation Y V
    let H := Γ.mapHomologicalComplex (.up ℤ)
    ShortComplex.homologyMap
      (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (op V)).mapShortComplex.map
        (sectionCohomologyPresheafShiftShortComplex Y K s n n' h)) =
      HomologicalComplex.homologyMap ((H.commShiftIso s).hom.app K) n ≫
        ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
          s n n' h).hom.app (H.obj K) := by
  dsimp only
  let Γ := supportEvaluation Y V
  let H := Γ.mapHomologicalComplex (.up ℤ)
  let φ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
      ((H.commShiftIso s).hom.app K) ≫
    (CochainComplex.shiftShortComplexFunctorIso AddCommGrpCat s n n' h).hom.app (H.obj K)
  have hm :
      (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (op V)).mapShortComplex.map
        (sectionCohomologyPresheafShiftShortComplex Y K s n n' h)).τ₂ = φ.τ₂ := by
    subst n'
    simp [φ, sectionCohomologyPresheafShiftShortComplex, HomologicalComplex.XIsoOfEq]
    exact (Category.id_comp _).symm
  exact (ShortComplex.homologyMap_eq_of_middle_eq _ _ hm).trans
    ((ShortComplex.homologyMap_comp _ _).trans
      (congrArg (fun f => HomologicalComplex.homologyMap
        ((H.commShiftIso s).hom.app K) n ≫ f)
        (CochainComplex.ShiftSequence.shiftIso_hom_app s n n' h (H.obj K)).symm))
/-- The degree-one shift commutes with evaluation after actual open restriction. -/
lemma sectionCohomologyShift_onOpen_homology_one (Y : TopCat.{0}) (U : Opens Y)
    (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ) (W : Opens (TopCat.of U)) :
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let H := F.mapHomologicalComplex (.up ℤ)
    let Γ := (supportEvaluation (TopCat.of U) W).mapHomologicalComplex (.up ℤ)
    let φY := ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj
      (op (U.isOpenEmbedding.functor.obj W))).mapShortComplex.map
        (sectionCohomologyPresheafShiftShortComplex Y K 1 0 1 (by omega))
    let φU := ((evaluation (Opens (TopCat.of U))ᵒᵖ AddCommGrpCat).obj
      (op W)).mapShortComplex.map
        (sectionCohomologyPresheafShiftShortComplex (TopCat.of U) (H.obj K) 1 0 1 (by omega))
    ShortComplex.homologyMap φY =
      HomologicalComplex.homologyMap (Γ.map ((H.commShiftIso (1 : ℤ)).hom.app K)) 0 ≫
        ShortComplex.homologyMap φU := by
  dsimp only
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let H := F.mapHomologicalComplex (.up ℤ)
  let Γ := (supportEvaluation (TopCat.of U) W).mapHomologicalComplex (.up ℤ)
  let φY := ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj
    (op (U.isOpenEmbedding.functor.obj W))).mapShortComplex.map
      (sectionCohomologyPresheafShiftShortComplex Y K 1 0 1 (by omega))
  let φU := ((evaluation (Opens (TopCat.of U))ᵒᵖ AddCommGrpCat).obj
    (op W)).mapShortComplex.map
      (sectionCohomologyPresheafShiftShortComplex (TopCat.of U) (H.obj K) 1 0 1 (by omega))
  let ψ := (shortComplexFunctor AddCommGrpCat (.up ℤ) 0).map
    (Γ.map ((H.commShiftIso (1 : ℤ)).hom.app K))
  have hmiddle : φY.τ₂ = (ψ ≫ φU).τ₂ := by
    simp [φY, φU, ψ, Γ, H, sectionCohomologyPresheafShiftShortComplex,
      CochainComplex.shiftShortComplexFunctorIso, CochainComplex.shiftShortComplexFunctor',
      CochainComplex.shiftEval, HomologicalComplex.XIsoOfEq]
    rfl
  have hh := ShortComplex.homologyMap_eq_of_middle_eq φY (ψ ≫ φU) hmiddle
  rw [ShortComplex.homologyMap_comp] at hh
  exact hh

end TopCat.Sheaf
