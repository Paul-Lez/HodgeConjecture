/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeBoundaryOnOpen
public import Other.AlgebraicGeometry.ActualSingularSupportWindingOnOpen
public import Other.AlgebraicGeometry.Cohomology.SupportSheafNormalization
public import Other.AlgebraicGeometry.HolomorphicExponentialSingularSections

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
namespace AlgebraicGeometry.ComplexPoint
local instance windingTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance windingParacompact (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] :
    ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)

omit [IsProjective X.hom] in
/-- The natural and ambient complement comparisons induce the same local homology map. -/
lemma naturalOutside_homologyMap_eq_ambient_on_open
    (V : Opens (TopCat.of (ComplexPoint X)))
    (zS : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ V
      (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₃.homology 1) :
    let Y := TopCat.of (ComplexPoint X)
    let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
    let SS := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (rationalSingularCochainComplex Y)
    let SI := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (ambientRationalInjectiveComplex X)
    let Γ := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
    let f : SS ⟶ SI := by
      change (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
        (rationalSingularCochainComplex Y)).map Γ ⟶
        (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
          (ambientRationalInjectiveComplex X)).map Γ
      exact Γ.mapShortComplex.map
        (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U
          (complexSingularToAmbientInjective X))
    HomologicalComplex.homologyMap
      (Γ.map (naturalSingularOutsideResolutionComparison X Z hZ)) 1 zS =
      HomologicalComplex.homologyMap
        (Γ.map (ambientRationalOpenResolutionComparison X Z hZ)) 1
        (HomologicalComplex.homologyMap f.τ₃ 1 zS) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let SS := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
    (rationalSingularCochainComplex Y)
  let SI := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
    (ambientRationalInjectiveComplex X)
  let Γ := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
  let f : SS ⟶ SI := by
    change (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
      (rationalSingularCochainComplex Y)).map Γ ⟶
      (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
        (ambientRationalInjectiveComplex X)).map Γ
    exact Γ.mapShortComplex.map
      (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U
        (complexSingularToAmbientInjective X))
  have h := naturalSingularOutsideResolutionComparison_homologyMap X Z hZ V 1
  have hz := ConcreteCategory.congr_hom h zS
  change _ = _ at hz
  dsimp only [ambientSingularOutsideResolutionComparison] at hz
  simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp] at hz
  exact hz

/-- The fixed support normalization sends the local cone boundary to positive winding. -/
lemma supportSheafSection_shift_eq_normalized_winding_on_open
    (V : Opens (TopCat.of (ComplexPoint X)))
    (g : C(ChernWinding.puncturedSpace (V : Set (ComplexPoint X)) Z, ℂ))
    (hg : ∀ y, g y ≠ 0)
    (h : ChernWinding.HasRationalWindingPeriod (V : Set (ComplexPoint X)) Z g hg) :
    let Y := TopCat.of (ComplexPoint X)
    let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
    let q := openIntersectionPairIsoSupportComplement Y Z hZ V
    let z := ChernWinding.openRawRationalWindingClass Y (V ⊓ U)
      (g.comp (ChernWinding.topMap q.hom.left))
      (fun y => hg (q.hom.left y))
    let SS := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (rationalSingularCochainComplex Y)
    let SI := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (ambientRationalInjectiveComplex X)
    let Γ := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
    let f : SS ⟶ SI := by
      change (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
        (rationalSingularCochainComplex Y)).map Γ ⟶
        (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
          (ambientRationalInjectiveComplex X)).map Γ
      exact Γ.mapShortComplex.map
        (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U
          (complexSingularToAmbientInjective X))
    let zI := HomologicalComplex.homologyMap f.τ₃ 1
      (HomologicalComplex.homologyMap
        (openRawToSupportedSingularOutside Y U V) 1 z)
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
    let H := Γ
    let t := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.mapHomologicalComplexIso
          (ambientRationalInjectiveRestriction X Z hZ) (TopCat.Sheaf.supportEvaluation Y V)).inv 1
        (HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr (H.map
            (ambientRationalInjectiveRestriction X Z hZ))) 1
          (HomologicalComplex.homologyMap
            (H.map (ambientRationalOpenResolutionComparison X Z hZ)) 1 zI)))
    let K := (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
      (ambientRationalInjectiveComplex X)).X₁
    let m := supportSheafToAmbientInjectiveCone X Z hZ
    let : IsIso ((HomologicalComplex.homologyMap m 1).hom.app (op V)) := by
      have : IsIso (HomologicalComplex.homologyMap m 1) :=
        (quasiIsoAt_iff_isIso_homologyMap m 1).mp inferInstance
      infer_instance
    (complexSupportInjectiveCohomologySheafIsoRelative X ⟨Z, hZ⟩ 2).hom.hom.app (op V)
      ((TopCat.Sheaf.sectionCohomologySheafShiftMap Y K 1 1 2 (by omega)).hom.app
        (op V) (inv ((HomologicalComplex.homologyMap m 1).hom.app (op V)) t)) =
      (supportRelativeCohomologyToSheaf Y (Z : Set (ComplexPoint X)) 2).app (op V)
        (ChernWinding.windingRelativeClass (V : Set (ComplexPoint X)) Z h) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let q := openIntersectionPairIsoSupportComplement Y Z hZ V
  let z := ChernWinding.openRawRationalWindingClass Y (V ⊓ U)
    (g.comp (ChernWinding.topMap q.hom.left))
    (fun y => hg (q.hom.left y))
  let SS := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
    (rationalSingularCochainComplex Y)
  let SI := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
    (ambientRationalInjectiveComplex X)
  let Γ := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
  let f : SS ⟶ SI := by
    change (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
      (rationalSingularCochainComplex Y)).map Γ ⟶
      (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
        (ambientRationalInjectiveComplex X)).map Γ
    exact Γ.mapShortComplex.map
      (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U
        (complexSingularToAmbientInjective X))
  let eI := CochainComplex.mappingCocone.shortExactHomologyIsoCone SI
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact
      Y U V _) 1 2 (by omega)
  let zI := HomologicalComplex.homologyMap f.τ₃ 1
    (HomologicalComplex.homologyMap
      (openRawToSupportedSingularOutside Y U V) 1 z)
  let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
  let H := Γ
  let t := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
    (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.mapHomologicalComplexIso
        (ambientRationalInjectiveRestriction X Z hZ) (TopCat.Sheaf.supportEvaluation Y V)).inv 1
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (H.map
          (ambientRationalInjectiveRestriction X Z hZ))) 1
        (HomologicalComplex.homologyMap
          (H.map (ambientRationalOpenResolutionComparison X Z hZ)) 1 zI)))
  let K := (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
    (ambientRationalInjectiveComplex X)).X₁
  let m := supportSheafToAmbientInjectiveCone X Z hZ
  let : IsIso ((HomologicalComplex.homologyMap m 1).hom.app (op V)) := by
    have : IsIso (HomologicalComplex.homologyMap m 1) :=
      (quasiIsoAt_iff_isIso_homologyMap m 1).mp inferInstance
    infer_instance
  have hlocal := supportSheafSection_shift_eq_local_boundary X Z hZ V zI
  dsimp only at hlocal
  have hwind := complexSupportInjectiveSectionCohomologyEquiv_winding_boundary_on_open
    X Z hZ V g hg h
  dsimp only at hwind
  have hnorm := complexSupportInjectiveCohomologySheafIsoRelative_section_apply
    X ⟨Z, hZ⟩ 2 V
      (eI.inv (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr SI.g) 1 zI))
  dsimp only at hnorm
  have hshift :
      (TopCat.Sheaf.sectionCohomologySheafShiftMap Y K 1 1 2 (by omega)).hom.app
        (op V) (inv ((HomologicalComplex.homologyMap m 1).hom.app (op V)) t) =
        TopCat.Sheaf.sectionCohomologyToSheafSection Y K 2 V
          (eI.inv (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr SI.g) 1 zI)) := by
    exact hlocal
  rw [hshift]
  exact hnorm.trans (congrArg
    ((supportRelativeCohomologyToSheaf Y (Z : Set (ComplexPoint X)) 2).app (op V)) hwind)
end AlgebraicGeometry.ComplexPoint
