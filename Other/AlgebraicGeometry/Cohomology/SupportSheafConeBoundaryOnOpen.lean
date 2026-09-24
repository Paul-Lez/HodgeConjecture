/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeComparisonOnOpen
public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeSectionTransport
public import Other.Algebra.Homology.DerivedCategory.MappingCoconeBoundary
public import Other.AlgebraicTopology.Sheaf.CohomologySectionShiftOnOpen

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)

/-- The fixed inverse and shift send a local cone boundary to its supported section. -/
lemma supportSheafSection_shift_eq_local_boundary
    (V : Opens (TopCat.of (ComplexPoint X)))
    (z : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ V
      (ambientRationalInjectiveComplex X)).X₃.homology 1) :
    let Y := TopCat.of (ComplexPoint X)
    let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
    let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
      (ambientRationalInjectiveComplex X)
    let K := S.X₁
    let Ssec := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (ambientRationalInjectiveComplex X)
    let H := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
    let eI := CochainComplex.mappingCocone.shortExactHomologyIsoCone Ssec
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U V _) 1 2
      (by omega)
    let m := supportSheafToAmbientInjectiveCone X Z hZ
    let Hm := HomologicalComplex.homologyMap m 1
    let : IsIso (Hm.hom.app (op V)) := by
      have : IsIso (HomologicalComplex.homologyMap m 1) :=
        (quasiIsoAt_iff_isIso_homologyMap m 1).mp inferInstance
      infer_instance
    let e := CochainComplex.mappingCone.mapHomologicalComplexIso
      (ambientRationalInjectiveRestriction X Z hZ)
      (TopCat.Sheaf.supportEvaluation Y V)
    let zC := HomologicalComplex.homologyMap
      (H.map (ambientRationalOpenResolutionComparison X Z hZ)) 1 z
    let zCone := HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr (H.map
        (ambientRationalInjectiveRestriction X Z hZ))) 1 zC
    let a := (eI.inv
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr Ssec.g) 1 z))
    let t := TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
      (HomologicalComplex.homologyMap e.inv 1 zCone)
    (TopCat.Sheaf.sectionCohomologySheafShiftMap Y K 1 1 2 (by omega)).hom.app
      (op V) (inv (Hm.hom.app (op V)) t) =
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y K 2 V a) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
    (ambientRationalInjectiveComplex X)
  let K := S.X₁
  let Γ := TopCat.Sheaf.supportEvaluation Y V
  let H := Γ.mapHomologicalComplex (.up ℤ)
  let Ssec := S.map H
  let z' : Ssec.X₃.homology 1 := by
    change (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V
      (ambientRationalInjectiveComplex X)).X₃.homology 1
    exact z
  let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
  let : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex Ssec) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex Ssec
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U V _)
  let eI := CochainComplex.mappingCocone.shortExactHomologyIsoCone Ssec
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U V _) 1 2
    (by omega)
  let m := supportSheafToAmbientInjectiveCone X Z hZ
  let HmLocal := HomologicalComplex.homologyMap (H.map m) 1
  let Hm := HomologicalComplex.homologyMap m 1
  let e := CochainComplex.mappingCone.mapHomologicalComplexIso
    (ambientRationalInjectiveRestriction X Z hZ) Γ
  let eH := HomologicalComplex.homologyMapIso e 1
  let He := eH.hom
  let z₀ : (H.obj (((TopCat.Sheaf.openRestrictionPushforward Y U).mapHomologicalComplex
      (.up ℤ)).obj (ambientRationalInjectiveComplex X))).homology 1 := by
    dsimp only [H, Γ]
    exact z
  let zC := HomologicalComplex.homologyMap
    (H.map (ambientRationalOpenResolutionComparison X Z hZ)) 1 z₀
  let zCone := HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.inr (H.map
      (ambientRationalInjectiveRestriction X Z hZ))) 1 zC
  let t₀ := HomologicalComplex.homologyMap e.inv 1 zCone
  let Kshift := (H.obj K)⟦(1 : ℤ)⟧
  let HcIso := HomologicalComplex.homologyMapIso
    (((Γ.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).app S.X₁) 1
  let Hc : (H.obj (K⟦(1 : ℤ)⟧)).homology 1 ⟶ Kshift.homology 1 := by
    dsimp only [Kshift]
    exact HcIso.hom
  let Hl : Kshift.homology 1 ⟶
      (CochainComplex.mappingCone Ssec.g).homology 1 := by
    dsimp only [Kshift, Ssec]
    exact HomologicalComplex.homologyMap
      (CochainComplex.mappingCocone.shiftedLiftShortComplex Ssec) 1
  let : IsIso Hc := by
    exact HcIso.isIso_hom
  let : IsIso Hl := by
    dsimp only [Hl]
    exact (quasiIsoAt_iff_isIso_homologyMap
      (CochainComplex.mappingCocone.shiftedLiftShortComplex Ssec) 1).mp inferInstance
  let Hq := HomologicalComplex.homologyMap
    (supportConeToAmbientInjectiveConeOnOpen X Z hZ V) 1
  let Hinr := HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.inr Ssec.g) 1
  let Hs : Kshift.homology 1 ⟶ Ssec.X₁.homology 2 := by
    dsimp only [Kshift]
    exact ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
      (1 : ℤ) (1 : ℤ) (2 : ℤ) (by omega)).hom.app Ssec.X₁
  let a : (H.obj (K⟦(1 : ℤ)⟧)).homology 1 :=
    inv Hc (inv Hl (Hinr z'))
  let : IsIso (Hm.hom.app (op V)) := by
    have : IsIso (HomologicalComplex.homologyMap m 1) :=
      (quasiIsoAt_iff_isIso_homologyMap m 1).mp inferInstance
    infer_instance
  have hmap := congrArg (fun f => HomologicalComplex.homologyMap f 1)
    (supportSheafToAmbientInjectiveCone_on_open X Z hZ V)
  simp only [HomologicalComplex.homologyMap_comp] at hmap
  have hinr := congrArg (fun f => HomologicalComplex.homologyMap f 1)
    (supportConeToAmbientInjectiveConeOnOpen_inr X Z hZ V)
  simp only [HomologicalComplex.homologyMap_comp] at hinr
  have ha : HmLocal a = t₀ := by
    have ha' := ConcreteCategory.congr_hom hmap a
    change HmLocal a = HomologicalComplex.homologyMap e.inv 1 zCone
    have hR : (Hc ≫ Hl ≫ Hq) a = zCone := by
      have hzCone := ConcreteCategory.congr_hom hinr z'
      simp only [ConcreteCategory.comp_apply] at hzCone
      dsimp only [a]
      simp only [← ConcreteCategory.comp_apply, Category.assoc,
        IsIso.inv_hom_id_assoc]
      exact hzCone
    have h' : (ConcreteCategory.hom He) ((ConcreteCategory.hom HmLocal) a) = zCone := by
      simpa [He, eH, HmLocal] using ha'.trans hR
    apply (ConcreteCategory.isIso_iff_bijective He).mp inferInstance |>.1
    have hzE := ConcreteCategory.congr_hom eH.inv_hom_id zCone
    exact h'.trans hzE.symm
  have hnat := ConcreteCategory.congr_hom
    (TopCat.Sheaf.sectionCohomologyToSheafSection_naturality Y m 1 V) a
  simp only [ConcreteCategory.comp_apply] at hnat
  have hsec :
      TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V t₀ =
        Hm.hom.app (op V)
          (TopCat.Sheaf.sectionCohomologyToSheafSection Y (K⟦(1 : ℤ)⟧) 1 V a) := by
    rw [← ha]
    exact hnat
  have hshift := TopCat.Sheaf.sectionCohomologyToSheafSection_shift_naturality
    Y K 1 1 2 (by omega) V
  have hshift' := ConcreteCategory.congr_hom hshift a
  simp only [ConcreteCategory.comp_apply] at hshift'
  have hshiftmap :
      ShortComplex.homologyMap
          (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (op V)).mapShortComplex.map
            (TopCat.Sheaf.sectionCohomologyPresheafShiftShortComplex Y K 1 1 2 (by omega))) =
        Hc ≫ Hs := by
    dsimp only [Hc, HcIso, Hs, Kshift]
    rw [HomologicalComplex.homologyMapIso_hom]
    exact TopCat.Sheaf.sectionCohomologyPresheafShiftShortComplex_onOpen_homology
      Y K 1 1 2 (by omega) V
  have hxa : Hs (Hc a) =
      eI.inv (Hinr z') := by
    let y := inv Hl (Hinr z')
    have hc := ConcreteCategory.congr_hom (IsIso.inv_hom_id Hc) y
    have hc' := congrArg (ConcreteCategory.hom Hs) hc
    dsimp only [a, y, eI, Hs] at hc' ⊢
    exact hc'
  rw [hshiftmap] at hshift'
  have hinvsec :
      inv (Hm.hom.app (op V))
          (TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V t₀) =
      TopCat.Sheaf.sectionCohomologyToSheafSection Y (K⟦(1 : ℤ)⟧) 1 V a := by
    rw [hsec]
    have hi := ConcreteCategory.congr_hom
      (IsIso.hom_inv_id (Hm.hom.app (op V)))
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y (K⟦(1 : ℤ)⟧) 1 V a)
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using hi
  simp only [ConcreteCategory.comp_apply] at hshift'
  exact (congrArg
    ((TopCat.Sheaf.sectionCohomologySheafShiftMap Y K 1 1 2 (by omega)).hom.app (op V))
    hinvsec).trans
    (hshift'.symm.trans
      (congrArg (TopCat.Sheaf.sectionCohomologyToSheafSection Y K 2 V) hxa))

end AlgebraicGeometry.ComplexPoint
