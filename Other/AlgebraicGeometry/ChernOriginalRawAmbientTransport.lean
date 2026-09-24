/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.Cohomology.OriginalChernRawWindingClassMap
public import Other.AlgebraicGeometry.Cohomology.OriginalChernRawWindingLocalMap
public import Other.AlgebraicGeometry.RationalSupportConeBoundaryComparison

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

end AlgebraicGeometry.ComplexPoint
