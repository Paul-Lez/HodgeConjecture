/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeQuasiIso
public import Other.AlgebraicGeometry.Cohomology.HypercohomologyShift

open CategoryTheory CategoryTheory.Limits TopologicalSpace HomologicalComplex
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)

/-- Global sections of the actual support-to-cone map give a quasi-isomorphism. -/
instance supportSheafToAmbientInjectiveCone_globalSections_quasiIso :
    QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
        (supportSheafToAmbientInjectiveCone X Z hZ)) := by
  let Y := TopCat.of (ComplexPoint X)
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y
    ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤ (ambientRationalInjectiveComplex X)
  let : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y _ ⊤ _)
  have hc : QuasiIso
      ((Γ.mapHomologicalComplex (.up ℤ)).map (supportSheafToAmbientInjectiveCone X Z hZ) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso
          (ambientRationalInjectiveRestriction X Z hZ) Γ).hom) := by
    rw [supportSheafToAmbientInjectiveCone_globalSections]
    infer_instance
  exact quasiIso_of_comp_right _
    (CochainComplex.mappingCone.mapHomologicalComplexIso
      (ambientRationalInjectiveRestriction X Z hZ) Γ).hom

/-- The prescribed support normalization sends the shifted kernel class to its negative unshift. -/
lemma coneSupportAddEquivSupportedInjectiveHomology_supportSheaf
    (n : ℤ)
    (a : (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      ((TopCat.Sheaf.supportRestrictionComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩
        (ambientRationalInjectiveComplex X)).X₁⟦(1 : ℤ)⟧)).homology (n - 1)) :
    coneSupportAddEquivSupportedInjectiveHomology X Z hZ n
      ((rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n).symm
        (homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
              (supportSheafToAmbientInjectiveCone X Z hZ)) (n - 1) a)) =
    -ShortComplex.homologyMap
      (TopCat.Sheaf.globalSectionsShiftShortComplex (TopCat.of (ComplexPoint X))
        (TopCat.Sheaf.supportRestrictionComplexShortComplex
          (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩
          (ambientRationalInjectiveComplex X)).X₁ 1 (n - 1) n (by omega)) a := by
  let Y := TopCat.of (ComplexPoint X)
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y
    ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤ (ambientRationalInjectiveComplex X)
  let : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y _ ⊤ _)
  have hm := congrArg (fun f => homologyMap f (n - 1))
    (supportSheafToAmbientInjectiveCone_globalSections X Z hZ)
  simp only [homologyMap_comp] at hm
  simp only [coneSupportAddEquivSupportedInjectiveHomology, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply]
  rw [TopCat.Sheaf.globalSectionsShiftShortComplex_homologyMap]
  apply congrArg Neg.neg
  let Hm := homologyMap ((Γ.mapHomologicalComplex (.up ℤ)).map
    (supportSheafToAmbientInjectiveCone X Z hZ)) (n - 1)
  let He := homologyMap (CochainComplex.mappingCone.mapHomologicalComplexIso
    (ambientRationalInjectiveRestriction X Z hZ) Γ).hom (n - 1)
  let Hq := homologyMap (supportConeToAmbientInjectiveGlobalCone X Z hZ) (n - 1)
  let Hl := homologyMap (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)
  let Hc := homologyMap (((Γ.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app
    (TopCat.Sheaf.supportRestrictionComplexShortComplex Y ⟨Zᶜ, hZ.isOpen_compl⟩
      (ambientRationalInjectiveComplex X)).X₁) (n - 1)
  let Hs := ((homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
    1 (n - 1) n (by omega)).hom.app S.X₁
  change (Hm ≫ He ≫ inv Hq ≫ inv Hl ≫ Hs) a = (Hc ≫ Hs) a
  apply ConcreteCategory.congr_hom
  change Hm ≫ He = Hc ≫ Hl ≫ Hq at hm
  rw [← Category.assoc, hm]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

/-- The original support equivalence factors through the actual sheaf map, shift, and negation. -/
lemma coneSupportAddEquivSupportedInjectiveHomology_eq_supportSheaf
    (n : ℤ) (α : RationalCohomologyWithSupport X Z n) :
    coneSupportAddEquivSupportedInjectiveHomology X Z hZ n α =
      -ShortComplex.homologyMap
        (TopCat.Sheaf.globalSectionsShiftShortComplex (TopCat.of (ComplexPoint X))
          (TopCat.Sheaf.supportRestrictionComplexShortComplex
            (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩
            (ambientRationalInjectiveComplex X)).X₁ 1 (n - 1) n (by omega))
        (inv (homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
              (supportSheafToAmbientInjectiveCone X Z hZ)) (n - 1))
          (rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n α)) := by
  let Hm := homologyMap
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
        (supportSheafToAmbientInjectiveCone X Z hZ)) (n - 1)
  let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n
  have h := coneSupportAddEquivSupportedInjectiveHomology_supportSheaf X Z hZ n
    (inv Hm (e α))
  have ha : Hm (inv Hm (e α)) = e α := by
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id Hm) (e α)
  change coneSupportAddEquivSupportedInjectiveHomology X Z hZ n
    (e.symm (Hm (inv Hm (e α)))) = _ at h
  rw [ha, AddEquiv.symm_apply_apply] at h
  exact h

end AlgebraicGeometry.ComplexPoint
