/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeLocalVanishing
public import Other.AlgebraicTopology.Sheaf.CohomologySectionTransport

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint

lemma coneSupportSection_restrict_eq_neg_supportSheaf
    (X : Over (Spec ↧ℂ))
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (α : RationalCohomologyWithSupport X Z n)
    (W : Opens (TopCat.of (ComplexPoint X))) :
    let Y := TopCat.of (ComplexPoint X)
    let K := (TopCat.Sheaf.supportRestrictionComplexShortComplex Y
      ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)).X₁
    let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n
    let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
    let a := inv
      (HomologicalComplex.homologyMap
        (((Γ.mapHomologicalComplex (.up ℤ)).map
          (supportSheafToAmbientInjectiveCone X Z hZ))) (n - 1)) (e α)
    (K.homology n).obj.map
      (homOfLE (le_top : W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤
        (coneSupportAddEquivSupportedInjectiveHomology X Z hZ n α)) =
      -(K.homology n).obj.map
        (homOfLE (le_top : W ≤ ⊤)).op
        (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤
          (ShortComplex.homologyMap
            (TopCat.Sheaf.globalSectionsShiftShortComplex Y K 1 (n - 1) n (by omega)) a)) := by
  dsimp only
  rw [coneSupportAddEquivSupportedInjectiveHomology_eq_supportSheaf]
  simp only [map_neg]

lemma supportConeSection_restrict_eq_inv_local_section
    (X : Over (Spec ↧ℂ))
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (α : RationalCohomologyWithSupport X Z n)
    (W : Opens (TopCat.of (ComplexPoint X)))
    (t : ((CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)).homology
      (n - 1)).obj.obj (op W))
    (ht : ((CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)).homology
      (n - 1)).obj.map (homOfLE (le_top : W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ))
        (n - 1) ⊤
        (rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n α)) = t) :
    let Y := TopCat.of (ComplexPoint X)
    let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y
      ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)
    let K := S.X₁
    let m := supportSheafToAmbientInjectiveCone X Z hZ
    let : IsIso ((HomologicalComplex.homologyMap m (n - 1)).hom.app (op W)) := by
      have : IsIso (HomologicalComplex.homologyMap m (n - 1)) :=
        (quasiIsoAt_iff_isIso_homologyMap m (n - 1)).mp inferInstance
      infer_instance
    let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
    let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n
    let HΓ := HomologicalComplex.homologyMap
      (((Γ.mapHomologicalComplex (.up ℤ)).map m)) (n - 1)
    let a := inv HΓ (e α)
    ((K⟦(1 : ℤ)⟧).homology (n - 1)).obj.map (homOfLE (le_top : W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y (K⟦(1 : ℤ)⟧)
        (n - 1) ⊤ a) =
      inv ((HomologicalComplex.homologyMap m (n - 1)).hom.app (op W)) t := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y
    ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)
  let K := S.X₁
  let m := supportSheafToAmbientInjectiveCone X Z hZ
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n
  let HΓ := HomologicalComplex.homologyMap
    (((Γ.mapHomologicalComplex (.up ℤ)).map m)) (n - 1)
  let a := inv HΓ (e α)
  let H := HomologicalComplex.homologyMap m (n - 1)
  have : IsIso HΓ := (quasiIsoAt_iff_isIso_homologyMap
    (((Γ.mapHomologicalComplex (.up ℤ)).map m)) (n - 1)).mp inferInstance
  have : IsIso H := (quasiIsoAt_iff_isIso_homologyMap m (n - 1)).mp inferInstance
  have ha : HΓ a = e α := by
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id HΓ) (e α)
  have htransport := TopCat.Sheaf.sectionCohomologyToSheafSection_restrict_eq_of_homologyMap
    Y (K⟦(1 : ℤ)⟧) (CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ))
      m (n - 1) a (e α) ha W t ht
  apply ((ConcreteCategory.isIso_iff_bijective (H.hom.app (op W))).mp inferInstance).1
  rw [htransport]
  change t = (H.hom.app (op W))
    ((inv (H.hom.app (op W))) t)
  exact (ConcreteCategory.congr_hom (IsIso.inv_hom_id (H.hom.app (op W))) t).symm

lemma coneSupportSection_restrict_eq_neg_inv_shift_local_section
    (X : Over (Spec ↧ℂ))
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (α : RationalCohomologyWithSupport X Z n)
    (W : Opens (TopCat.of (ComplexPoint X)))
    (t : ((CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)).homology
      (n - 1)).obj.obj (op W))
    (ht : ((CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)).homology
      (n - 1)).obj.map (homOfLE (le_top : W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ))
        (n - 1) ⊤
        (rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n α)) = t) :
    let Y := TopCat.of (ComplexPoint X)
    let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y
      ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)
    let K := S.X₁
    let m := supportSheafToAmbientInjectiveCone X Z hZ
    let : IsIso ((HomologicalComplex.homologyMap m (n - 1)).hom.app (op W)) := by
      have : IsIso (HomologicalComplex.homologyMap m (n - 1)) :=
        (quasiIsoAt_iff_isIso_homologyMap m (n - 1)).mp inferInstance
      infer_instance
    (K.homology n).obj.map (homOfLE (le_top : W ≤ ⊤)).op
        (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤
        (coneSupportAddEquivSupportedInjectiveHomology X Z hZ n α)) =
      -(TopCat.Sheaf.sectionCohomologySheafShiftMap Y K 1 (n - 1) n (by omega)).hom.app
        (op W)
        (inv ((HomologicalComplex.homologyMap m (n - 1)).hom.app (op W)) t) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y
    ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)
  let K := S.X₁
  let m := supportSheafToAmbientInjectiveCone X Z hZ
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n
  let HΓ := HomologicalComplex.homologyMap
    (((Γ.mapHomologicalComplex (.up ℤ)).map m)) (n - 1)
  let a := inv HΓ (e α)
  have hneg := coneSupportSection_restrict_eq_neg_supportSheaf X Z hZ n α
    W
  have hshift := TopCat.Sheaf.sectionCohomologyShift_restrict_eq Y K n a W
    (((K⟦(1 : ℤ)⟧).homology (n - 1)).obj.map (homOfLE (le_top : W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y (K⟦(1 : ℤ)⟧)
        (n - 1) ⊤ a)) rfl
  have hinv := supportConeSection_restrict_eq_inv_local_section X Z hZ n α W t ht
  rw [hneg, hshift, hinv]

end AlgebraicGeometry.ComplexPoint
