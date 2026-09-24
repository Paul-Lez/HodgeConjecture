/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RelativeChernOriginalRestriction
public import Other.AlgebraicGeometry.HolomorphicExponentialSingularSections
public import Other.AlgebraicGeometry.ChernRelativeChartFormulaSplitting
public import Other.AlgebraicGeometry.RationalSupportConeBoundaryComparison

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.HomComplex AlgebraicTopology.Singular

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint

local instance originalRawWindingTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable [IsIntegral X.left] [Smooth X.hom]
variable (Ω U : Opens (TopCat.of (ComplexPoint X)))

/-- The local frame-difference boundary mapped into the fixed ambient cone. -/
def originalLocalBoundaryMap
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let H := F.mapHomologicalComplex (.up ℤ)
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
        ((analyticSingleFunctor X).obj (𝓒(↧(ComplexPoint X); ℤ))) ⟶
      (H.obj ((CochainComplex.mappingCone
        (ambientRationalInjectiveRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
          Ω.isOpen.isClosed_compl))⟦(1 : ℤ)⟧)) := by
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let H := F.mapHomologicalComplex (.up ℤ)
  let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let J := CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0
  let βΩ := CochainComplex.HomComplex.Cocycle.equivHomShift.symm
    (restrictedSingularOneCocycle X d Ω)
  exact I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫
    J.map (restrictedOverlapUnitHom X d Ω U (-w)) ≫
    I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)) ≫
    H.map (βΩ ≫
      (CochainComplex.mappingCone.inr
        (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)))⟦(1 : ℤ)⟧' ≫
      (rationalSupportConeToAmbientInjectiveCone X ((Ω : Set (ComplexPoint X))ᶜ)
        Ω.isOpen.isClosed_compl)⟦(1 : ℤ)⟧')

omit [IsIntegral X.left] [Smooth X.hom] in
lemma restrictedOverlapUnitHom_integerOne_apply
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let e := TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
      (AddCommGrpCat.of ℤ)
    (restrictedOverlapUnitHom X d Ω U w).hom.app (op ⊤)
      (e.hom.app (op ⊤) (TopCat.Sheaf.integerOne (Y := TopCat.of U))) =
      restrictedOverlapSection X d Ω U w := by
  dsimp only
  let e : ((restrictToOpen X U).obj (𝓒(↧(ComplexPoint X); ℤ))) ≅
      𝓒[↧U; AddCommGrpCat.of ℤ] :=
    { hom := TopCat.Sheaf.openSheafRestrictionToConstant (TopCat.of (ComplexPoint X)) U
          (AddCommGrpCat.of ℤ)
      inv := TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
          (AddCommGrpCat.of ℤ)
      hom_inv_id := TopCat.Sheaf.openSheafRestrictionToConstant_constantToOpen
        (TopCat.of (ComplexPoint X)) U (AddCommGrpCat.of ℤ)
      inv_hom_id := TopCat.Sheaf.constantToOpen_openSheafRestrictionToConstant
        (TopCat.of (ComplexPoint X)) U (AddCommGrpCat.of ℤ) }
  let s := restrictedOverlapUnitHom X d Ω U w
  have hs : e.inv ≫ s = TopCat.Sheaf.constHomOfSection
      ((restrictToOpen X U).obj ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)))
      (restrictedOverlapSection X d Ω U w) := by
    dsimp [e, s, restrictedOverlapUnitHom]
    rw [← Category.assoc,
      TopCat.Sheaf.constantToOpen_openSheafRestrictionToConstant, Category.id_comp]
  have hs' := congrArg (fun f =>
      (ConcreteCategory.hom (f.hom.app (op ⊤)))
        (TopCat.Sheaf.integerOne (Y := TopCat.of U))) hs
  dsimp [e, s] at hs'
  rw [TopCat.Sheaf.constHomOfSection_integerOne_apply] at hs'
  exact hs'

omit [IsIntegral X.left] [Smooth X.hom] in
lemma originalLocalBoundaryMap_prefix_integerOne_apply
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
    let J := CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0
    let s := restrictedOverlapUnitHom X d Ω U (-w)
    let oneU :=
      (TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
        (AddCommGrpCat.of ℤ)).hom.app (op ⊤)
        (TopCat.Sheaf.integerOne (Y := TopCat.of U))
    (((I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫ J.map s ≫
      I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))).f 0).hom.app
        (op ⊤)) oneU =
      (((I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))).f 0).hom.app
        (op ⊤)) (restrictedOverlapSection X d Ω U (-w)) := by
  dsimp only
  simp only [HomologicalComplex.comp_f, TopCat.Sheaf.comp_app,
    ConcreteCategory.comp_apply]
  have hIone :
      (((HomologicalComplex.singleMapHomologicalComplex
          (U.isOpenEmbedding.sheafPullback AddCommGrpCat) (.up ℤ) 0).hom.app
          (𝓒(↧(ComplexPoint X); ℤ))).f 0).hom.app (op ⊤)
          ((TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
            (AddCommGrpCat.of ℤ)).hom.app (op ⊤)
            (TopCat.Sheaf.integerOne (Y := TopCat.of U))) =
        ((TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
          (AddCommGrpCat.of ℤ)).hom.app (op ⊤)
            (TopCat.Sheaf.integerOne (Y := TopCat.of U))) := by
    rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
    rfl
  have hJ :
      (((CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
        (restrictedOverlapUnitHom X d Ω U (-w))).f 0).hom.app (op ⊤)
          ((TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
            (AddCommGrpCat.of ℤ)).hom.app (op ⊤)
            (TopCat.Sheaf.integerOne (Y := TopCat.of U))) =
        (restrictedOverlapUnitHom X d Ω U (-w)).hom.app (op ⊤)
          ((TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
            (AddCommGrpCat.of ℤ)).hom.app (op ⊤)
            (TopCat.Sheaf.integerOne (Y := TopCat.of U))) := by
    rfl
  rw [hIone]
  exact (congrArg (fun z =>
      (ConcreteCategory.hom
        ((((HomologicalComplex.singleMapHomologicalComplex
          (U.isOpenEmbedding.sheafPullback AddCommGrpCat) (.up ℤ) 0).inv.app
          ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))).f 0).hom.app
          (op ⊤))) z) hJ).trans
    (congrArg (fun z =>
      (ConcreteCategory.hom
        ((((HomologicalComplex.singleMapHomologicalComplex
          (U.isOpenEmbedding.sheafPullback AddCommGrpCat) (.up ℤ) 0).inv.app
          ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))).f 0).hom.app
          (op ⊤))) z)
      (restrictedOverlapUnitHom_integerOne_apply X d Ω U (-w)))

lemma originalLocalBoundaryMap_f_zero_on_constant
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let H := F.mapHomologicalComplex (.up ℤ)
    let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
    let b :=
      (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (restrictedSingularOneCocycle X d Ω) ≫
        (CochainComplex.mappingCone.inr
          (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)))⟦(1 : ℤ)⟧' ≫
        (rationalSupportConeToAmbientInjectiveCone X ((Ω : Set (ComplexPoint X))ᶜ)
          Ω.isOpen.isClosed_compl)⟦(1 : ℤ)⟧')
    let oneU :=
      (TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
        (AddCommGrpCat.of ℤ)).hom.app (op ⊤)
        (TopCat.Sheaf.integerOne (Y := TopCat.of U))
    ((originalLocalBoundaryMap X d Ω U w).f 0).hom.app (op ⊤) oneU =
      ((H.map b).f 0).hom.app (op ⊤)
        (((I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))).f 0).hom.app
          (op ⊤)
          ((restrictedOverlapSection X d Ω U (-w)))) := by
  dsimp only
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let H := F.mapHomologicalComplex (.up ℤ)
  let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let J := CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0
  let b :=
      (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (restrictedSingularOneCocycle X d Ω) ≫
        (CochainComplex.mappingCone.inr
          (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)))⟦(1 : ℤ)⟧' ≫
        (rationalSupportConeToAmbientInjectiveCone X ((Ω : Set (ComplexPoint X))ᶜ)
          Ω.isOpen.isClosed_compl)⟦(1 : ℤ)⟧')
  let oneU :=
      (TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
        (AddCommGrpCat.of ℤ)).hom.app (op ⊤)
        (TopCat.Sheaf.integerOne (Y := TopCat.of U))
  change ((H.map b).f 0).hom.app (op ⊤)
      (((I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫ J.map
        (restrictedOverlapUnitHom X d Ω U (-w)) ≫
        I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))).f 0).hom.app
        (op ⊤) oneU) =
    ((H.map b).f 0).hom.app (op ⊤)
      (((I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))).f 0).hom.app
        (op ⊤) (restrictedOverlapSection X d Ω U (-w)))
  exact congrArg (fun z =>
    (ConcreteCategory.hom (((H.map b).f 0).hom.app (op ⊤))) z)
    (originalLocalBoundaryMap_prefix_integerOne_apply X d Ω U w)

lemma restrictedSingularOneCocycle_equivHomShift_f_one
    (Ω : Opens (TopCat.of (ComplexPoint X))) :
    (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (restrictedSingularOneCocycle X d Ω)).f 0 =
      restrictedSingularOneCoefficient X d Ω := by
  rfl

omit [IsIntegral X.left] [Smooth X.hom] in
lemma originalLocalBoundaryMap_restrictedSingle_inverse
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
    (((I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))).f 0).hom.app
      (op ⊤)) (restrictedOverlapSection X d Ω U w) =
      (openRestrictionTopEval U).inv.app ((openRestrictionFunctor Ω).obj
        (holomorphicUnitSheaf X d))
        ((TopCat.Sheaf.supportedOutsideIntersectionIso (TopCat.of (ComplexPoint X)) Ω U
          (holomorphicUnitSheaf X d)).inv w) := by
  dsimp [restrictedOverlapSection, openRestrictionTopEval,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    TopCat.Sheaf.openRestrictionPushforwardTopEvaluationIso,
    TopCat.Sheaf.supportedOutsideIntersectionIso]
  simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rfl

lemma originalLocalBoundaryMap_beta_integerOne_raw
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let H := F.mapHomologicalComplex (.up ℤ)
    let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
    let β := CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (restrictedSingularOneCocycle X d Ω)
    ((H.map β).f 0).hom.app (op ⊤)
      (((I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))).f 0).hom.app
        (op ⊤) (restrictedOverlapSection X d Ω U (-w))) =
    (openRestrictionTopEval U).inv.app
        ((derivedPushforwardComplementConstantRationalComplexInt X
          ((Ω : Set (ComplexPoint X))ᶜ)).X 1)
      ((restrictedSingularOneCoefficient X d Ω).hom.app (op U)
        ((TopCat.Sheaf.supportedOutsideIntersectionIso (TopCat.of (ComplexPoint X)) Ω U
          (holomorphicUnitSheaf X d)).inv (-w))) := by
  dsimp only
  rw [Functor.mapHomologicalComplex_map_f]
  have hv := originalLocalBoundaryMap_restrictedSingle_inverse X d Ω U (-w)
  have hn := (openRestrictionTopEval U).inv.naturality
    ((CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (restrictedSingularOneCocycle X d Ω)).f 0)
  have hna := ConcreteCategory.congr_hom hn
    ((TopCat.Sheaf.supportedOutsideIntersectionIso (TopCat.of (ComplexPoint X)) Ω U
      (holomorphicUnitSheaf X d)).inv (-w))
  dsimp only [HomologicalComplex.comp_f] at hna
  simp only [ConcreteCategory.comp_apply] at hna
  rw [hv]
  have hbeta := hna.symm
  change
    (ConcreteCategory.hom
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat).map
        ((CochainComplex.HomComplex.Cocycle.equivHomShift.symm
          (restrictedSingularOneCocycle X d Ω)).f 0)).hom.app (op ⊤)))
        ((ConcreteCategory.hom
          ((openRestrictionTopEval U).inv.app
            ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))))
          ((ConcreteCategory.hom
            ((TopCat.Sheaf.supportedOutsideIntersectionIso
              (TopCat.of (ComplexPoint X)) Ω U (holomorphicUnitSheaf X d)).inv)) (-w))) =
      (ConcreteCategory.hom
        ((openRestrictionTopEval U).inv.app
          ((derivedPushforwardComplementConstantRationalComplexInt X
            ((Ω : Set (ComplexPoint X))ᶜ)).X 1)))
        ((ConcreteCategory.hom
          (((CochainComplex.HomComplex.Cocycle.equivHomShift.symm
            (restrictedSingularOneCocycle X d Ω)).f 0).hom.app (op U)))
          ((ConcreteCategory.hom
            ((TopCat.Sheaf.supportedOutsideIntersectionIso
              (TopCat.of (ComplexPoint X)) Ω U (holomorphicUnitSheaf X d)).inv)) (-w))) at hbeta
  have hcoef :
      ((CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (restrictedSingularOneCocycle X d Ω)).f 0).hom.app (op U)
          ((TopCat.Sheaf.supportedOutsideIntersectionIso (TopCat.of (ComplexPoint X)) Ω U
            (holomorphicUnitSheaf X d)).inv (-w)) =
        (restrictedSingularOneCoefficient X d Ω).hom.app (op U)
          ((TopCat.Sheaf.supportedOutsideIntersectionIso (TopCat.of (ComplexPoint X)) Ω U
            (holomorphicUnitSheaf X d)).inv (-w)) := by
    rw [restrictedSingularOneCocycle_equivHomShift_f_one]
    rfl
  exact hbeta.trans (congrArg (fun z =>
    (ConcreteCategory.hom
      ((openRestrictionTopEval U).inv.app
        ((derivedPushforwardComplementConstantRationalComplexInt X
          ((Ω : Set (ComplexPoint X))ᶜ)).X 1))) z) hcoef)

lemma originalLocalBoundaryMap_f_zero_raw
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let H := F.mapHomologicalComplex (.up ℤ)
    let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
    let β := CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (restrictedSingularOneCocycle X d Ω)
    let c := (CochainComplex.mappingCone.inr
      (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)))⟦(1 : ℤ)⟧'
    let m := (rationalSupportConeToAmbientInjectiveCone X ((Ω : Set (ComplexPoint X))ᶜ)
      Ω.isOpen.isClosed_compl)⟦(1 : ℤ)⟧'
    let raw :=
      ((naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1).hom.app (op U)
        ((TopCat.Sheaf.supportedOutsideIntersectionIso (TopCat.of (ComplexPoint X)) Ω U
          ((singularCochainSheafComplexInt X ℚ).X 1)).inv
            (((singularCochainSheafTermIso X 1).inv.hom.app (op (U ⊓ Ω)))
              ((openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) (U ⊓ Ω)).f 1
                (ChernWinding.rationalWindingCochain
                  (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
                  (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))).hom)))
    ((H.map (β ≫ c ≫ m)).f 0).hom.app (op ⊤)
      (((I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))).f 0).hom.app
        (op ⊤) (restrictedOverlapSection X d Ω U (-w))) =
    ((H.map (c ≫ m)).f 0).hom.app (op ⊤)
      ((openRestrictionTopEval U).inv.app
        ((derivedPushforwardComplementConstantRationalComplexInt X
          ((Ω : Set (ComplexPoint X))ᶜ)).X 1) raw) := by
  dsimp only
  simp only [Functor.map_comp, HomologicalComplex.comp_f, TopCat.Sheaf.comp_app,
    ConcreteCategory.comp_apply]
  have hbeta := originalLocalBoundaryMap_beta_integerOne_raw X d Ω U w
  have hraw := restrictedSingularOneCoefficient_apply_on_open_raw
    X d Ω U (-w)
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let H := F.mapHomologicalComplex (.up ℤ)
  let c := (CochainComplex.mappingCone.inr
      (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)))⟦(1 : ℤ)⟧'
  let m := (rationalSupportConeToAmbientInjectiveCone X ((Ω : Set (ComplexPoint X))ᶜ)
      Ω.isOpen.isClosed_compl)⟦(1 : ℤ)⟧'
  have h := hbeta.trans (congrArg (fun z =>
      (ConcreteCategory.hom
        ((openRestrictionTopEval U).inv.app
          ((derivedPushforwardComplementConstantRationalComplexInt X
            ((Ω : Set (ComplexPoint X))ᶜ)).X 1))) z) hraw)
  exact congrArg (fun z =>
    (ConcreteCategory.hom
      (((H.map (c ≫ m)).f 0).hom.app (op ⊤))) z) h

/-- The actual boundary map sends integer one to the image of the raw winding cochain. -/
lemma originalLocalBoundaryMap_integerOne_raw_winding
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let H := F.mapHomologicalComplex (.up ℤ)
    let c := (CochainComplex.mappingCone.inr
      (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)))⟦(1 : ℤ)⟧'
    let m := (rationalSupportConeToAmbientInjectiveCone X ((Ω : Set (ComplexPoint X))ᶜ)
      Ω.isOpen.isClosed_compl)⟦(1 : ℤ)⟧'
    let raw :=
      ((naturalSingularOutsideResolutionComparisonOnOpen X Ω).f 1).hom.app (op U)
        ((TopCat.Sheaf.supportedOutsideIntersectionIso (TopCat.of (ComplexPoint X)) Ω U
          ((singularCochainSheafComplexInt X ℚ).X 1)).inv
            (((singularCochainSheafTermIso X 1).inv.hom.app (op (U ⊓ Ω)))
              ((openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) (U ⊓ Ω)).f 1
                (ChernWinding.rationalWindingCochain
                  (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
                  (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))).hom)))
    let oneU :=
      (TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
        (AddCommGrpCat.of ℤ)).hom.app (op ⊤)
        (TopCat.Sheaf.integerOne (Y := TopCat.of U))
    ((originalLocalBoundaryMap X d Ω U w).f 0).hom.app (op ⊤) oneU =
      ((H.map (c ≫ m)).f 0).hom.app (op ⊤)
        ((openRestrictionTopEval U).inv.app
          ((derivedPushforwardComplementConstantRationalComplexInt X
            ((Ω : Set (ComplexPoint X))ᶜ)).X 1) raw) := by
  dsimp only
  exact (originalLocalBoundaryMap_f_zero_on_constant X d Ω U w).trans
    (originalLocalBoundaryMap_f_zero_raw X d Ω U w)

end AlgebraicGeometry.ComplexPoint
