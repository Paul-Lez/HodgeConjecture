/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.Cohomology.OriginalChernRawWindingClassMap
public import Other.AlgebraicGeometry.Cohomology.OriginalChernRawWindingLocalMap
public import Other.AlgebraicGeometry.RationalSupportConeBoundaryComparison
public import Other.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open AlgebraicTopology.Singular

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace AlgebraicGeometry.ComplexPoint

local instance originalRawAmbientTransportTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
variable (Ω U : Opens (TopCat.of (ComplexPoint X)))

/-- The original raw map becomes the direct ambient map after top-evaluation restriction. -/
lemma originalLocalRawToAmbientCone_comp_restriction_eq :
    let Y := TopCat.of (ComplexPoint X)
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X
      ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl)
    let e := (NatIso.mapHomologicalComplex
      (TopCat.Sheaf.openRestrictionPushforwardTopEvaluationIso Y U) (.up ℤ)).app C
    originalLocalRawToAmbientCone X Ω U ≫ e.hom =
      openRawToSupportedSingularOutside Y Ω U ≫
        ((TopCat.Sheaf.supportEvaluation Y U).mapHomologicalComplex (.up ℤ)).map
          (naturalSingularOutsideResolutionComparisonOnOpen X Ω) ≫
        ((TopCat.Sheaf.supportEvaluation Y U).mapHomologicalComplex (.up ℤ)).map
          (CochainComplex.mappingCone.inr
            (ambientRationalInjectiveRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
              Ω.isOpen.isClosed_compl)) := by
  let Y := TopCat.of (ComplexPoint X)
  let P := derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)
  let c := CochainComplex.mappingCone.inr
    (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))
  let m := rationalSupportConeToAmbientInjectiveCone X ((Ω : Set (ComplexPoint X))ᶜ)
    Ω.isOpen.isClosed_compl
  let e := NatIso.mapHomologicalComplex
    (TopCat.Sheaf.openRestrictionPushforwardTopEvaluationIso Y U) (.up ℤ)
  let R := (TopCat.Sheaf.supportEvaluation Y U).mapHomologicalComplex (.up ℤ)
  let L := (TopCat.Sheaf.openRestrictionPushforward Y U ⋙
    TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex (.up ℤ)
  have hn := e.hom.naturality (c ≫ m)
  have hc : (e.app P).inv ≫ L.map (c ≫ m) ≫ (e.app _).hom = R.map (c ≫ m) := by
    exact (congrArg (fun q => (e.app P).inv ≫ q) hn).trans
      ((e.app P).inv_hom_id_assoc _)
  have hr := congrArg (fun q =>
    openRawToSupportedSingularOutside Y Ω U ≫
      R.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω) ≫ q) hc
  have hcone : c ≫ m = CochainComplex.mappingCone.inr
      (ambientRationalInjectiveRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
        Ω.isOpen.isClosed_compl) := rationalSupportConeToAmbientInjectiveCone_inr X _ _
  have hr' := hr.trans (congrArg (fun f =>
    openRawToSupportedSingularOutside Y Ω U ≫
      R.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω) ≫ R.map f) hcone)
  change ((openRawToSupportedSingularOutside Y Ω U ≫
      R.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω) ≫ (e.app P).inv) ≫
        L.map (c ≫ m)) ≫ (e.app _).hom = _
  let a := openRawToSupportedSingularOutside Y Ω U
  let b := R.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω)
  let p := (e.app P).inv
  let l := L.map (c ≫ m)
  let k := (e.app (CochainComplex.mappingCone
    (ambientRationalInjectiveRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
      Ω.isOpen.isClosed_compl))).hom
  exact (Category.assoc (a ≫ b ≫ p) l k).trans
    ((Category.assoc a (b ≫ p) (l ≫ k)).trans
      ((congrArg (fun q => a ≫ q) (Category.assoc b p (l ≫ k))).trans hr'))

/-- The direct ambient raw map gives the same section on `U` as restricting the
original raw section from the top open of the restricted space. -/
lemma originalLocalRawToAmbientCone_direct_section_eq_restricted_original
    (z : ((openRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X)) (U ⊓ Ω)).extend
      ComplexShape.embeddingUpNat).homology 1) :
    let Y := TopCat.of (ComplexPoint X)
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X
      ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl)
    let R := (TopCat.Sheaf.supportEvaluation Y U).mapHomologicalComplex (.up ℤ)
    let r := originalLocalRawToAmbientCone X Ω U
    let rDirect := openRawToSupportedSingularOutside Y Ω U ≫
      R.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω) ≫
      R.map (CochainComplex.mappingCone.inr
        (ambientRationalInjectiveRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
          Ω.isOpen.isClosed_compl))
    (ConcreteCategory.hom
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 U))
        ((HomologicalComplex.homologyMap rDirect 1).hom z) =
      ConcreteCategory.hom
        (TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1
            (U.isOpenEmbedding.functor.obj ⊤) ≫
          (TopCat.Sheaf.openRestrictionTopSectionsIso Y U).hom.app (C.homology 1))
        ((HomologicalComplex.homologyMap r 1).hom z) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X
    ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl)
  let R := (TopCat.Sheaf.supportEvaluation Y U).mapHomologicalComplex (.up ℤ)
  let r := originalLocalRawToAmbientCone X Ω U
  let rDirect := openRawToSupportedSingularOutside Y Ω U ≫
    R.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω) ≫
    R.map (CochainComplex.mappingCone.inr
      (ambientRationalInjectiveRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
        Ω.isOpen.isClosed_compl))
  let e := TopCat.Sheaf.openRestrictionTopSectionComplexIso Y U C
  have hraw := originalLocalRawToAmbientCone_comp_restriction_eq X Ω U
  dsimp only at hraw
  have he :
      ((NatIso.mapHomologicalComplex
        (TopCat.Sheaf.openRestrictionPushforwardTopEvaluationIso Y U) (.up ℤ)).app C).hom =
        e.hom := by
    rfl
  rw [he] at hraw
  have hmap :
      HomologicalComplex.homologyMap rDirect 1 =
        HomologicalComplex.homologyMap r 1 ≫
          HomologicalComplex.homologyMap e.hom 1 := by
    dsimp only [rDirect, r, e, R] at hraw ⊢
    rw [← hraw, HomologicalComplex.homologyMap_comp]
  have hsection := TopCat.Sheaf.openRestrictionTopSectionComplexIso_homology_section
    Y C U 1
  have hcat :
      HomologicalComplex.homologyMap rDirect 1 ≫
          TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 U =
        HomologicalComplex.homologyMap r 1 ≫
          (TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1
            (U.isOpenEmbedding.functor.obj ⊤) ≫
            (TopCat.Sheaf.openRestrictionTopSectionsIso Y U).hom.app (C.homology 1)) := by
    rw [hmap, Category.assoc, hsection]
  have hv := ConcreteCategory.congr_hom hcat z
  exact hv

end AlgebraicGeometry.ComplexPoint
