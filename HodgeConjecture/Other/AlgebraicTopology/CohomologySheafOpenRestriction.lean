/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicTopology.CohomologySheafOpenComparison

/-! # The canonical local cohomology-sheaf map under actual open restriction -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{u}) (U : Opens X)
  (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- The canonical local-class presheaf map commutes with actual open restriction. -/
@[reassoc]
lemma sectionCohomologyPresheafToSheaf_openRestriction (n : ℤ) :
    sectionCohomologyPresheafToSheaf (TopCat.of U)
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj K) n ≫
      ((K.sc n).mapHomologyIso (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u})).hom.hom =
    (openRestrictionSectionCohomologyPresheafIso X U K n).hom ≫
      (cohomologyOpenPresheafRestriction X U).map (sectionCohomologyPresheafToSheaf X K n) := by
  have h := congrArg
    (sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}).map
    (openRestrictionSectionCohomologySheafificationIso X U K n)
  simp only [Functor.map_comp] at h
  dsimp only [sectionCohomologyPresheafToSheaf]
  rw [Category.assoc]
  erw [← h]
  change toSheafify _ _ ≫
      (sheafifyMap (Opens.grothendieckTopology (TopCat.of U))
        (openRestrictionSectionCohomologyPresheafIso X U K n).hom ≫
      (openRestrictionSheafificationIso X U (sectionCohomologyPresheaf X K n)).hom.hom ≫ _) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  erw [toSheafify_openRestrictionSheafificationIso_assoc X U (sectionCohomologyPresheaf X K n)]
  rfl

/-- The evaluation/homology comparison uses the literal open-image equality. -/
@[reassoc]
lemma openRestrictionSectionCohomologyPresheafIso_onOpen (n : ℤ)
    (W : Opens (TopCat.of U)) :
    (sectionCohomologyPresheafOnOpenIso (TopCat.of U)
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj K) n W).hom ≫
      (openRestrictionSectionCohomologyPresheafIso X U K n).hom.app (op W) =
    (sectionCohomologyPresheafOnOpenIso X K n (U.isOpenEmbedding.functor.obj W)).hom := by
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    (((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).obj K).sc n
  exact (ShortComplex.mapHomologyIso_comp_hom S (cohomologyOpenPresheafRestriction X U)
    ((evaluation (Opens (TopCat.of U))ᵒᵖ AddCommGrpCat.{u}).obj (op W))).symm

/-- The original-ambient canonical section map agrees with the one on the
actual open-restricted coefficient complex, through its exact homology comparison. -/
@[reassoc]
lemma sectionCohomologyToSheafSection_openRestriction (n : ℤ)
    (W : Opens (TopCat.of U)) :
    sectionCohomologyToSheafSection (TopCat.of U)
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj K) n W ≫
      ((K.sc n).mapHomologyIso (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u})).hom.hom.app (op W) =
    sectionCohomologyToSheafSection X K n (U.isOpenEmbedding.functor.obj W) := by
  dsimp only [sectionCohomologyToSheafSection]
  rw [Category.assoc, ← NatTrans.comp_app, sectionCohomologyPresheafToSheaf_openRestriction,
    NatTrans.comp_app, ← Category.assoc, openRestrictionSectionCohomologyPresheafIso_onOpen]
  rfl

end TopCat.Sheaf
