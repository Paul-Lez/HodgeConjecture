/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeWindingOnOpen
public import Other.AlgebraicTopology.SupportedSingularSupportMap
public import Other.AlgebraicGeometry.ChernWindingChartPeriods

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open AlgebraicTopology.Singular

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
namespace AlgebraicGeometry.ComplexPoint

local instance originalWindingComparisonTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance originalWindingComparisonParacompact (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (Ω V : Opens (TopCat.of (ComplexPoint X)))
omit [IsProjective X.hom] in
/-- The original complement map agrees with the canonical ambient map on raw winding classes. -/
lemma originalRawToAmbientResolution_homologyMap_eq_canonical_on_open
    (w : (holomorphicUnitSheaf X d).obj.obj (op (V ⊓ Ω))) :
    let Y := TopCat.of (ComplexPoint X)
    let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
    let hZ : IsClosed Z := Ω.isOpen.isClosed_compl
    let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
    let hU : U ≤ Ω := by intro y hy; exact not_not.mp hy
    let j : V ⊓ U ⟶ V ⊓ Ω := homOfLE (inf_le_inf_left V hU)
    let zΩ := ChernWinding.openRawRationalWindingClass Y (V ⊓ Ω)
      (holomorphicUnitFunction X d (V ⊓ Ω) (-w))
      (holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) (-w))
    let zU := ChernWinding.openRawRationalWindingClass Y (V ⊓ U)
      ((holomorphicUnitFunction X d (V ⊓ Ω) (-w)).comp
        (ChernWinding.topMap ((Opens.toTopCat Y).map j)))
      (fun y => holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) (-w) ((Opens.toTopCat Y).map j y))
    let Γ := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
  let fI : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (rationalSingularCochainComplex Y)) ⟶
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
        (ambientRationalInjectiveComplex X)) := by
    change (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
      (rationalSingularCochainComplex Y)).map Γ ⟶
      (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
        (ambientRationalInjectiveComplex X)).map Γ
    exact Γ.mapShortComplex.map
      (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U
        (complexSingularToAmbientInjective X))
  HomologicalComplex.homologyMap
      (Γ.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω)) 1
      (HomologicalComplex.homologyMap
        (openRawToSupportedSingularOutside Y Ω V) 1 zΩ) =
      HomologicalComplex.homologyMap
        (Γ.map (ambientRationalOpenResolutionComparison X Z hZ)) 1
        (HomologicalComplex.homologyMap fI.τ₃ 1
          (HomologicalComplex.homologyMap
            (openRawToSupportedSingularOutside Y U V) 1 zU)) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
  let hZ : IsClosed Z := Ω.isOpen.isClosed_compl
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let hU : U ≤ Ω := by intro y hy; exact not_not.mp hy
  let j : V ⊓ U ⟶ V ⊓ Ω := homOfLE (inf_le_inf_left V hU)
  let zΩ := ChernWinding.openRawRationalWindingClass Y (V ⊓ Ω)
    (holomorphicUnitFunction X d (V ⊓ Ω) (-w))
    (holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) (-w))
  let zU := ChernWinding.openRawRationalWindingClass Y (V ⊓ U)
    ((holomorphicUnitFunction X d (V ⊓ Ω) (-w)).comp
        (ChernWinding.topMap ((Opens.toTopCat Y).map j)))
    (fun y => holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) (-w) ((Opens.toTopCat Y).map j y))
  let Γ := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
  let f := TopCat.Sheaf.supportRestrictionSectionsSupportMap hU
      (rationalSingularCochainComplex Y) V
  let fI : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (rationalSingularCochainComplex Y)) ⟶
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
        (ambientRationalInjectiveComplex X)) := by
    change (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
      (rationalSingularCochainComplex Y)).map Γ ⟶
      (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
        (ambientRationalInjectiveComplex X)).map Γ
    exact Γ.mapShortComplex.map
      (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U
        (complexSingularToAmbientInjective X))
  have hz := ChernWinding.openRawRationalWindingClass_restriction
    Y j (holomorphicUnitFunction X d (V ⊓ Ω) (-w))
      (holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) (-w))
  dsimp only [zU, zΩ] at hz
  have hs := AlgebraicTopology.Singular.openRawToSupportedSingularOutside_supportMap Y hU V
  have hsH := congrArg (fun k => HomologicalComplex.homologyMap k 1) hs
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsH
  have hsZ := ConcreteCategory.congr_hom hsH zΩ
  simp only [ConcreteCategory.comp_apply] at hsZ
  have hr := hsZ
  rw [hz] at hr
  have hnat := naturalSingularOutsideResolutionComparisonOnOpen_eq_canonical X Ω
  dsimp only at hnat
  have hnatH := congrArg (fun k => HomologicalComplex.homologyMap (Γ.map k) 1) hnat
  rw [Functor.map_comp, HomologicalComplex.homologyMap_comp] at hnatH
  have hf : f.τ₃ = (Γ.map (((TopCat.Sheaf.openRestrictionPushforwardMap Y hU).mapHomologicalComplex
      (.up ℤ)).app (singularCochainSheafComplexInt X ℚ))) := by
    rfl
  have hleft := ConcreteCategory.congr_hom hnatH
    (HomologicalComplex.homologyMap
      (openRawToSupportedSingularOutside Y Ω V) 1 zΩ)
  simp only [ConcreteCategory.comp_apply] at hleft
  rw [← hf] at hleft
  dsimp only [f] at hleft
  have hfr := congrArg
    (fun q => (ConcreteCategory.hom
      (HomologicalComplex.homologyMap
        (Γ.map (naturalSingularOutsideResolutionComparison X
          ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl)) 1)) q) hr
  have hleft2 := hfr.symm.trans hleft
  have hcanonical := naturalOutside_homologyMap_eq_ambient_on_open X Z hZ V
    (HomologicalComplex.homologyMap
      (openRawToSupportedSingularOutside Y U V) 1 zU)
  exact hleft2.symm.trans hcanonical

omit [IsProjective X.hom] in
/-- The original and canonical raw winding classes give the same ambient cone section. -/
lemma originalRawAmbientSection_eq_canonical_on_open
    (w : (holomorphicUnitSheaf X d).obj.obj (op (V ⊓ Ω))) :
    let Y := TopCat.of (ComplexPoint X)
    let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
    let hZ : IsClosed Z := Ω.isOpen.isClosed_compl
    let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
    let hU : U ≤ Ω := by intro y hy; exact not_not.mp hy
    let j : V ⊓ U ⟶ V ⊓ Ω := homOfLE (inf_le_inf_left V hU)
    let zΩ := ChernWinding.openRawRationalWindingClass Y (V ⊓ Ω)
      (holomorphicUnitFunction X d (V ⊓ Ω) (-w))
      (holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) (-w))
    let zU := ChernWinding.openRawRationalWindingClass Y (V ⊓ U)
      ((holomorphicUnitFunction X d (V ⊓ Ω) (-w)).comp
        (ChernWinding.topMap ((Opens.toTopCat Y).map j)))
      (fun y => holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) (-w)
        ((Opens.toTopCat Y).map j y))
    let Γ := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
    let H := Γ
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
    let e := CochainComplex.mappingCone.mapHomologicalComplexIso
      (ambientRationalInjectiveRestriction X Z hZ)
      (TopCat.Sheaf.supportEvaluation Y V)
    let fI : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
        (rationalSingularCochainComplex Y)) ⟶
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
          (ambientRationalInjectiveComplex X)) := by
      change (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
        (rationalSingularCochainComplex Y)).map H ⟶
        (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
          (ambientRationalInjectiveComplex X)).map H
      exact H.mapShortComplex.map
        (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U
          (complexSingularToAmbientInjective X))
    let zI := HomologicalComplex.homologyMap fI.τ₃ 1
      (HomologicalComplex.homologyMap
        (openRawToSupportedSingularOutside Y U V) 1 zU)
    let aΩ := HomologicalComplex.homologyMap
      (Γ.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω)) 1
      (HomologicalComplex.homologyMap
        (openRawToSupportedSingularOutside Y Ω V) 1 zΩ)
    let aU := HomologicalComplex.homologyMap
      (Γ.map (ambientRationalOpenResolutionComparison X Z hZ)) 1 zI
    let bΩ := HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr
        (H.map (ambientRationalInjectiveRestriction X Z hZ))) 1 aΩ
    let bU := HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr
        (H.map (ambientRationalInjectiveRestriction X Z hZ))) 1 aU
    let tΩ := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
      (HomologicalComplex.homologyMap e.inv 1 bΩ)
    let tU := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
      (HomologicalComplex.homologyMap e.inv 1 bU)
    tΩ = tU := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
  let hZ : IsClosed Z := Ω.isOpen.isClosed_compl
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let hU : U ≤ Ω := by intro y hy; exact not_not.mp hy
  let j : V ⊓ U ⟶ V ⊓ Ω := homOfLE (inf_le_inf_left V hU)
  let zΩ := ChernWinding.openRawRationalWindingClass Y (V ⊓ Ω)
    (holomorphicUnitFunction X d (V ⊓ Ω) (-w))
    (holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) (-w))
  let zU := ChernWinding.openRawRationalWindingClass Y (V ⊓ U)
    ((holomorphicUnitFunction X d (V ⊓ Ω) (-w)).comp
      (ChernWinding.topMap ((Opens.toTopCat Y).map j)))
    (fun y => holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) (-w)
      ((Opens.toTopCat Y).map j y))
  let Γ := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
  let H := Γ
  let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
  let e := CochainComplex.mappingCone.mapHomologicalComplexIso
    (ambientRationalInjectiveRestriction X Z hZ)
    (TopCat.Sheaf.supportEvaluation Y V)
  let fI : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (rationalSingularCochainComplex Y)) ⟶
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
        (ambientRationalInjectiveComplex X)) := by
    change (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
      (rationalSingularCochainComplex Y)).map H ⟶
      (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
        (ambientRationalInjectiveComplex X)).map H
    exact H.mapShortComplex.map
      (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U
        (complexSingularToAmbientInjective X))
  let zI := HomologicalComplex.homologyMap fI.τ₃ 1
    (HomologicalComplex.homologyMap
      (openRawToSupportedSingularOutside Y U V) 1 zU)
  let aΩ := HomologicalComplex.homologyMap
    (Γ.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω)) 1
    (HomologicalComplex.homologyMap
      (openRawToSupportedSingularOutside Y Ω V) 1 zΩ)
  let aU := HomologicalComplex.homologyMap
    (Γ.map (ambientRationalOpenResolutionComparison X Z hZ)) 1 zI
  let bΩ := HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.inr
      (H.map (ambientRationalInjectiveRestriction X Z hZ))) 1 aΩ
  let bU := HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.inr
      (H.map (ambientRationalInjectiveRestriction X Z hZ))) 1 aU
  let tΩ := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
    (HomologicalComplex.homologyMap e.inv 1 bΩ)
  let tU := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
    (HomologicalComplex.homologyMap e.inv 1 bU)
  have hnat := originalRawToAmbientResolution_homologyMap_eq_canonical_on_open X d Ω V w
  dsimp only at hnat
  have hb : bΩ = bU := by
    simpa only [bΩ, bU, aΩ, aU, zI, fI, ConcreteCategory.comp_apply] using
      congrArg (fun q =>
        HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr (H.map
            (ambientRationalInjectiveRestriction X Z hZ))) 1 q) hnat
  exact congrArg (fun q =>
    TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
      (HomologicalComplex.homologyMap e.inv 1 q)) hb

end AlgebraicGeometry.ComplexPoint
