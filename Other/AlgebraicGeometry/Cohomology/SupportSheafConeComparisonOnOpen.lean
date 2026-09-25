/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeComparison

/-! # Local sections of the support-to-cone comparison -/

open CategoryTheory CategoryTheory.Limits TopologicalSpace HomologicalComplex
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)

/-- The local cone map obtained by evaluating the ambient open-resolution comparison. -/
def supportConeToAmbientInjectiveConeOnOpen (V : Opens (TopCat.of (ComplexPoint X))) :
    CochainComplex.mappingCone
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ V
        (ambientRationalInjectiveComplex X)).g ⟶
    CochainComplex.mappingCone
      (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
        (.up ℤ)).map (ambientRationalInjectiveRestriction X Z hZ)) :=
  let Y := TopCat.of (ComplexPoint X)
  let H := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y
    ⟨Zᶜ, hZ.isOpen_compl⟩ V (ambientRationalInjectiveComplex X)
  let r : S.X₃ ⟶ H.obj (derivedPushforwardComplementConstantRationalComplexInt X Z) := by
    change H.obj (((TopCat.Sheaf.openRestrictionPushforward (TopCat.of (ComplexPoint X))
      ⟨Zᶜ, hZ.isOpen_compl⟩).mapHomologicalComplex (.up ℤ)).obj
        (ambientRationalInjectiveComplex X)) ⟶ _
    exact H.map (ambientRationalOpenResolutionComparison X Z hZ)
  CochainComplex.mappingCone.map _ _ (𝟙 _) r (by
    rw [Category.id_comp]
    change S.g ≫ r = H.map (ambientRationalInjectiveRestriction X Z hZ)
    dsimp only [r]
    change H.map _ ≫ H.map (ambientRationalOpenResolutionComparison X Z hZ) = _
    rw [← Functor.map_comp]
    exact congrArg (fun q => H.map q) (supportRestriction_comp_openResolutionComparison X Z hZ))

lemma supportConeToAmbientInjectiveConeOnOpen_inr
    (V : Opens (TopCat.of (ComplexPoint X))) :
    let Y := TopCat.of (ComplexPoint X)
    let H := (TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)
    let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y
      ⟨Zᶜ, hZ.isOpen_compl⟩ V (ambientRationalInjectiveComplex X)
    CochainComplex.mappingCone.inr S.g ≫
        supportConeToAmbientInjectiveConeOnOpen X Z hZ V =
      (H.map (ambientRationalOpenResolutionComparison X Z hZ)) ≫
        CochainComplex.mappingCone.inr (H.map
          (ambientRationalInjectiveRestriction X Z hZ)) := by
  dsimp only
  simp [supportConeToAmbientInjectiveConeOnOpen, CochainComplex.mappingCone.map]

lemma supportConeToAmbientInjectiveConeOnOpen_inr_mapIso
    (V : Opens (TopCat.of (ComplexPoint X))) :
    let Y := TopCat.of (ComplexPoint X)
    let Γ := TopCat.Sheaf.supportEvaluation Y V
    let H := Γ.mapHomologicalComplex (.up ℤ)
    H.map (CochainComplex.mappingCone.inr (ambientRationalInjectiveRestriction X Z hZ)) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso
          (ambientRationalInjectiveRestriction X Z hZ) Γ).hom =
      CochainComplex.mappingCone.inr (H.map
        (ambientRationalInjectiveRestriction X Z hZ)) := by
  dsimp only
  exact CochainComplex.mappingCone.map_inr
    (ambientRationalInjectiveRestriction X Z hZ)
    (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V)

set_option maxHeartbeats 1600000 in
lemma supportSheafToAmbientInjectiveCone_on_open (V : Opens (TopCat.of (ComplexPoint X))) :
    let Y := TopCat.of (ComplexPoint X)
    let Γ := TopCat.Sheaf.supportEvaluation Y V
    let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y
      ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)
    let Ssec := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y
      ⟨Zᶜ, hZ.isOpen_compl⟩ V (ambientRationalInjectiveComplex X)
    ((Γ.mapHomologicalComplex (.up ℤ)).map (supportSheafToAmbientInjectiveCone X Z hZ)) ≫
      (CochainComplex.mappingCone.mapHomologicalComplexIso
        (ambientRationalInjectiveRestriction X Z hZ) Γ).hom =
    (((Γ.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app S.X₁) ≫
      CochainComplex.mappingCocone.shiftedLiftShortComplex Ssec ≫
      supportConeToAmbientInjectiveConeOnOpen X Z hZ V := by
  dsimp only
  rw [supportSheafToAmbientInjectiveCone, Functor.map_comp, Category.assoc,
    CochainComplex.mappingCone.mapHomologicalComplexIso_naturality,
    ← Category.assoc, CochainComplex.mappingCocone.map_shiftedLiftShortComplex]
  rfl
end AlgebraicGeometry.ComplexPoint
