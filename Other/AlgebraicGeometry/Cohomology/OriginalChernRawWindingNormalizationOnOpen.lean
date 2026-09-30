/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.Cohomology.OriginalChernRawWindingOnOpen
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open AlgebraicTopology.Singular

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000
namespace AlgebraicGeometry.ComplexPoint

local instance originalWindingNormalizationTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance originalWindingNormalizationParacompact (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (Ω V : Opens (TopCat.of (ComplexPoint X)))
/-- The prescribed support normalization sends the negative raw boundary to positive winding. -/
lemma originalRawAmbientSection_shift_eq_winding_on_open
    (w : (holomorphicUnitSheaf X d).obj.obj (op (V ⊓ Ω))) :
    let Y := TopCat.of (ComplexPoint X)
    let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
    let hZ : IsClosed Z := Ω.isOpen.isClosed_compl
    let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
    let hU : U ≤ Ω := by intro y hy; exact not_not.mp hy
    let S : Closeds Y := ⟨Z, hZ⟩
    let u₀ := (holomorphicUnitSheaf X d).obj.map
      (homOfLE (inf_le_inf_left V hU)).op w
    let hp := hasWindingPeriods X d V S
    let Γ := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
    let aΩ := HomologicalComplex.homologyMap
      (Γ.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω)) 1
      (HomologicalComplex.homologyMap
        (openRawToSupportedSingularOutside Y Ω V) 1
        (ChernWinding.openRawRationalWindingClass Y (V ⊓ Ω)
          (holomorphicUnitFunction X d (V ⊓ Ω) (-w))
          (holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) (-w))))
    let tΩ := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
      (HomologicalComplex.homologyMap
        (Γ.map (CochainComplex.mappingCone.inr
          (ambientRationalInjectiveRestriction X Z hZ))) 1 aΩ)
    let N := complexSupportInjectiveCohomologySheafIsoRelative X S 2
    let sh := TopCat.Sheaf.sectionCohomologySheafShiftMap Y
      (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
        (ambientRationalInjectiveComplex X)).X₁ 1 1 2 (by omega)
    let Hm := (HomologicalComplex.homologyMap
      (supportSheafToAmbientInjectiveCone X Z hZ) 1).hom.app (op V)
    let : IsIso Hm := by
      have : IsIso (HomologicalComplex.homologyMap
          (supportSheafToAmbientInjectiveCone X Z hZ) 1) :=
        (quasiIsoAt_iff_isIso_homologyMap
          (supportSheafToAmbientInjectiveCone X Z hZ) 1).mp inferInstance
      infer_instance
    (-(N.hom.hom.app (op V) (sh.hom.app (op V) (inv Hm tΩ))) =
      windingSheafHom hp u₀) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
  let hZ : IsClosed Z := Ω.isOpen.isClosed_compl
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let hU : U ≤ Ω := by intro y hy; exact not_not.mp hy
  let j : V ⊓ U ⟶ V ⊓ Ω := homOfLE (inf_le_inf_left V hU)
  let S : Closeds Y := ⟨Z, hZ⟩
  let u₀ := (holomorphicUnitSheaf X d).obj.map
    (homOfLE (inf_le_inf_left V hU)).op w
  let g := windingUnitFunction X d V S (-u₀)
  let hg := windingUnitFunction_ne_zero X d V S (-u₀)
  let hp := hasWindingPeriods X d V S
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
  let bU := HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.inr
      (H.map (ambientRationalInjectiveRestriction X Z hZ))) 1
      (HomologicalComplex.homologyMap
        (Γ.map (ambientRationalOpenResolutionComparison X Z hZ)) 1 zI)
  let aΩ := HomologicalComplex.homologyMap
    (Γ.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω)) 1
    (HomologicalComplex.homologyMap
      (openRawToSupportedSingularOutside Y Ω V) 1
      (ChernWinding.openRawRationalWindingClass Y (V ⊓ Ω)
        (holomorphicUnitFunction X d (V ⊓ Ω) (-w))
        (holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) (-w))))
  let bΩ := HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.inr
      (H.map (ambientRationalInjectiveRestriction X Z hZ))) 1 aΩ
  let zW := ChernWinding.openRawRationalWindingClass Y (V ⊓ U)
    (g.comp (ChernWinding.topMap
      (openIntersectionPairIsoSupportComplement Y Z hZ V).hom.left))
    (fun y => hg ((openIntersectionPairIsoSupportComplement Y Z hZ V).hom.left y))
  let bW := HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.inr
      (H.map (ambientRationalInjectiveRestriction X Z hZ))) 1
    (HomologicalComplex.homologyMap
      (Γ.map (ambientRationalOpenResolutionComparison X Z hZ)) 1
      (HomologicalComplex.homologyMap fI.τ₃ 1
        (HomologicalComplex.homologyMap
          (openRawToSupportedSingularOutside Y U V) 1 zW)))
  let tW := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
    (HomologicalComplex.homologyMap e.inv 1 bW)
  let tU := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
    (HomologicalComplex.homologyMap e.inv 1 bU)
  let tΩ := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
    (HomologicalComplex.homologyMap e.inv 1 bΩ)
  let tΩdirect := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
    (HomologicalComplex.homologyMap
      (Γ.map (CochainComplex.mappingCone.inr
        (ambientRationalInjectiveRestriction X Z hZ))) 1 aΩ)
  have hwind := supportSheafSection_shift_eq_normalized_winding_on_open X Z hZ V g hg (hp (-u₀))
  dsimp only at hwind
  have hz : zU = ChernWinding.openRawRationalWindingClass Y (V ⊓ U)
      (g.comp (ChernWinding.topMap
        (openIntersectionPairIsoSupportComplement Y Z hZ V).hom.left))
      (fun y => hg ((openIntersectionPairIsoSupportComplement Y Z hZ V).hom.left y)) := by
    dsimp only [zU, g, hg, u₀, S, U, hU, j]
    congr 1
  have ht : tU = tW := by
    dsimp only [tU, tW, bU, bW, zI, zW]
    rw [hz]
  let : IsIso ((HomologicalComplex.homologyMap
      (supportSheafToAmbientInjectiveCone X Z hZ) 1).hom.app (op V)) := by
    have : IsIso (HomologicalComplex.homologyMap
        (supportSheafToAmbientInjectiveCone X Z hZ) 1) :=
      (quasiIsoAt_iff_isIso_homologyMap
        (supportSheafToAmbientInjectiveCone X Z hZ) 1).mp inferInstance
    infer_instance
  have hnneg :
      (complexSupportInjectiveCohomologySheafIsoRelative X S 2).hom.hom.app (op V)
        ((TopCat.Sheaf.sectionCohomologySheafShiftMap Y
          (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
            (ambientRationalInjectiveComplex X)).X₁ 1 1 2 (by omega)).hom.app
          (op V)
          (inv ((HomologicalComplex.homologyMap
            (supportSheafToAmbientInjectiveCone X Z hZ) 1).hom.app (op V)) tU)) =
      (supportRelativeCohomologyToSheaf Y Z 2).app (op V)
        (ChernWinding.windingRelativeClass (V : Set (ComplexPoint X)) Z
          (hp (-u₀))) := by
    rw [ht]
    simpa [tW, bW, zW, Y, C, e, H, Γ, fI, U, S] using hwind
  have hclass :
      ChernWinding.windingRelativeClass (V : Set (ComplexPoint X)) Z (hp (-u₀)) =
        -ChernWinding.windingRelativeClass (V : Set (ComplexPoint X)) Z (hp u₀) := by
    change windingRelativeHom hp (-u₀) = -windingRelativeHom hp u₀
    exact map_neg (windingRelativeHom hp) u₀
  have hsheaf :
      (supportRelativeCohomologyToSheaf Y Z 2).app (op V)
          (ChernWinding.windingRelativeClass (V : Set (ComplexPoint X)) Z (hp (-u₀))) =
        -windingSheafHom hp u₀ := by
    rw [windingSheafHom_apply]
    simpa [S] using congrArg ((supportRelativeCohomologyToSheaf Y Z 2).app (op V)) hclass
  let N := complexSupportInjectiveCohomologySheafIsoRelative X S 2
  let sh := TopCat.Sheaf.sectionCohomologySheafShiftMap Y
    (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
      (ambientRationalInjectiveComplex X)).X₁ 1 1 2 (by omega)
  let Hm := (HomologicalComplex.homologyMap
    (supportSheafToAmbientInjectiveCone X Z hZ) 1).hom.app (op V)
  have htarget :
      -(N.hom.hom.app (op V) (sh.hom.app (op V) (inv Hm tU))) =
        windingSheafHom hp u₀ := by
    rw [hnneg, hsheaf]
    simp
  have hraw := originalRawAmbientSection_eq_canonical_on_open X d Ω V w
  dsimp only at hraw
  have hraw' : tΩ = tU := by
    simpa [tΩ, tU, aΩ, bΩ, bU, zI, fI, Y, C, e, H, Γ, U] using hraw
  have hinr := supportConeToAmbientInjectiveConeOnOpen_inr_mapIso X Z hZ V
  dsimp only at hinr
  have hinr' := (Iso.eq_comp_inv e).2 hinr
  have hinrH := congrArg (fun f => HomologicalComplex.homologyMap f 1) hinr'
  simp only [HomologicalComplex.homologyMap_comp] at hinrH
  have helem := ConcreteCategory.congr_hom hinrH aΩ
  simp only [ConcreteCategory.comp_apply] at helem
  have hdirect : tΩ = tΩdirect := by
    exact congrArg (fun x =>
      ConcreteCategory.hom (TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V) x)
      helem.symm
  have hfinal :
      -(N.hom.hom.app (op V) (sh.hom.app (op V) (inv Hm tΩdirect))) =
        windingSheafHom hp u₀ := by
    rw [← hdirect, hraw']
    exact htarget
  exact hfinal

/-- The signed original raw boundary is the inverse normalization of positive winding. -/
lemma originalRawAmbientSection_shift_inv_eq_winding_on_open
    (w : (holomorphicUnitSheaf X d).obj.obj (op (V ⊓ Ω))) :
    let Y := TopCat.of (ComplexPoint X)
    let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
    let hZ : IsClosed Z := Ω.isOpen.isClosed_compl
    let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
    let hU : U ≤ Ω := by intro y hy; exact not_not.mp hy
    let S : Closeds Y := ⟨Z, hZ⟩
    let u₀ := (holomorphicUnitSheaf X d).obj.map
      (homOfLE (inf_le_inf_left V hU)).op w
    let hp := hasWindingPeriods X d V S
    let Γ := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
    let aΩ := HomologicalComplex.homologyMap
      (Γ.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω)) 1
      (HomologicalComplex.homologyMap
        (openRawToSupportedSingularOutside Y Ω V) 1
        (ChernWinding.openRawRationalWindingClass Y (V ⊓ Ω)
          (holomorphicUnitFunction X d (V ⊓ Ω) (-w))
          (holomorphicUnitFunction_ne_zero X d (V ⊓ Ω) (-w))))
    let tΩ := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
      (HomologicalComplex.homologyMap
        (Γ.map (CochainComplex.mappingCone.inr
          (ambientRationalInjectiveRestriction X Z hZ))) 1 aΩ)
    let N := complexSupportInjectiveCohomologySheafIsoRelative X S 2
    let sh := TopCat.Sheaf.sectionCohomologySheafShiftMap Y
      (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
        (ambientRationalInjectiveComplex X)).X₁ 1 1 2 (by omega)
    let Hm := (HomologicalComplex.homologyMap
      (supportSheafToAmbientInjectiveCone X Z hZ) 1).hom.app (op V)
    let : IsIso Hm := by
      have : IsIso (HomologicalComplex.homologyMap
          (supportSheafToAmbientInjectiveCone X Z hZ) 1) :=
        (quasiIsoAt_iff_isIso_homologyMap
          (supportSheafToAmbientInjectiveCone X Z hZ) 1).mp inferInstance
      infer_instance
    (-(sh.hom.app (op V) (inv Hm tΩ)) =
      (N.inv.hom.app (op V)) (windingSheafHom hp u₀)) := by
  dsimp only
  have h := originalRawAmbientSection_shift_eq_winding_on_open X d Ω V w
  dsimp only at h
  let N := complexSupportInjectiveCohomologySheafIsoRelative X
    ⟨(Ω : Set (ComplexPoint X))ᶜ, Ω.isOpen.isClosed_compl⟩ 2
  let Y := TopCat.of (ComplexPoint X)
  let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
  let hZ : IsClosed Z := Ω.isOpen.isClosed_compl
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let sh := TopCat.Sheaf.sectionCohomologySheafShiftMap Y
    (TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
      (ambientRationalInjectiveComplex X)).X₁ 1 1 2 (by omega)
  let Hm := (HomologicalComplex.homologyMap
    (supportSheafToAmbientInjectiveCone X Z hZ) 1).hom.app (op V)
  let : IsIso Hm := by
    have : IsIso (HomologicalComplex.homologyMap
        (supportSheafToAmbientInjectiveCone X Z hZ) 1) :=
      (quasiIsoAt_iff_isIso_homologyMap
        (supportSheafToAmbientInjectiveCone X Z hZ) 1).mp inferInstance
    infer_instance
  have h' := congrArg (fun x => (N.inv.hom.app (op V)) x) h
  have hcancel (x : _) : (N.inv.hom.app (op V))
      ((N.hom.hom.app (op V)) x) = x := by
    have hc := congrArg (fun f => f.hom.app (op V)) N.hom_inv_id
    exact ConcreteCategory.congr_hom hc x
  rw [map_neg] at h'
  change -(N.inv.hom.app (op V)
      (N.hom.hom.app (op V) (sh.hom.app (op V) (inv Hm _)))) = _ at h'
  rw [hcancel] at h'
  exact h'

end AlgebraicGeometry.ComplexPoint
