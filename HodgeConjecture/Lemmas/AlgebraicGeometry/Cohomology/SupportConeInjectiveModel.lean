/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel

/-!
# Normalized injective models for the rational support cone

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance supportConeInjectiveModelSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance supportConeInjectiveModelAddCommGrpDerivedCategory :
    HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard AddCommGrpCat

/-- Restriction from the ambient injective resolution to the fixed complement
resolution, using the strict comparison on the actual open complement. -/
def ambientRationalInjectiveRestriction
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    ambientRationalInjectiveComplex X ⟶
      derivedPushforwardComplementConstantRationalComplexInt X Z :=
  HomologicalComplex.extendMap
    (TopCat.Sheaf.ambientToOpenInjectiveResolution
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩
      (AddCommGrpCat.of ℚ)) ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
/-- The comparison extends the original rational restriction strictly. -/
@[reassoc]
lemma ambientRationalAugmentation_comp_restriction
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    ambientRationalInjectiveAugmentation X ≫
      ambientRationalInjectiveRestriction X Z hZ =
        rationalRestrictionComplexInt X Z := by
  change (ComplexShape.embeddingUpNat.extendFunctor
    (AnalyticAdditiveSheaf X)).map _ ≫
      (ComplexShape.embeddingUpNat.extendFunctor
        (AnalyticAdditiveSheaf X)).map _ = _
  rw [← Functor.map_comp]
  exact congrArg
    ((ComplexShape.embeddingUpNat.extendFunctor (AnalyticAdditiveSheaf X)).map)
    (TopCat.Sheaf.ambientAugmentation_comp_openResolution
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩
      (AddCommGrpCat.of ℚ))

/-- The actual map from the old rational support cone to its ambient-injective
source replacement. -/
def rationalSupportConeToAmbientInjectiveCone
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    rationalCohomologyWithSupportComplex X Z ⟶
      CochainComplex.mappingCone
        (ambientRationalInjectiveRestriction X Z hZ) :=
  CochainComplex.mappingCone.map _ _
    (ambientRationalInjectiveAugmentation X) (𝟙 _)
    (by simpa using (ambientRationalAugmentation_comp_restriction X Z hZ).symm)

instance rationalSupportConeToAmbientInjectiveCone_quasiIso
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (rationalSupportConeToAmbientInjectiveCone X Z hZ) :=
  CochainComplex.mappingCone.quasiIso_map_of_quasiIso _ _ _ _ _

/-- The replacement cone is bounded below. -/
instance ambientRationalInjectiveCone_isStrictlyGE
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    (CochainComplex.mappingCone
      (ambientRationalInjectiveRestriction X Z hZ)).IsStrictlyGE (-1) := by
  let : (derivedPushforwardComplementConstantRationalComplexInt X Z).IsStrictlyGE 0 := by
    dsimp only [derivedPushforwardComplementConstantRationalComplexInt]
    infer_instance
  exact CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1) (by omega) (by omega)

/-- The replacement cone is genuinely termwise injective: its terms are
finite biproducts of ambient injectives and open direct images of injectives. -/
instance ambientRationalInjectiveCone_injective
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (q : ℤ) :
    Injective ((CochainComplex.mappingCone
      (ambientRationalInjectiveRestriction X Z hZ)).X q) := by
  let : Injective
      ((derivedPushforwardComplementConstantRationalComplexInt X Z).X q) :=
    derivedPushforwardComplementConstantRationalComplexInt_injective X Z hZ q
  exact Injective.of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (ambientRationalInjectiveRestriction X Z hZ) q (q + 1) rfl).symm inferInstance

instance ambientRationalInjectiveCone_isKInjective
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    (CochainComplex.mappingCone
      (ambientRationalInjectiveRestriction X Z hZ)).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ (-1)

/-- The normalized ambient-injective cone as a bounded-below complex. -/
abbrev ambientRationalInjectiveConePlus
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
  ⟨(shiftFunctor _ (-1 : ℤ)).obj
      (CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)),
    ⟨0, CochainComplex.isStrictlyGE_shift _ (-1) (-1) 0 (by norm_num)⟩⟩

instance ambientRationalInjectiveConePlus_injective
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (i : ℤ) :
    Injective ((ambientRationalInjectiveConePlus X Z hZ).obj.X i) :=
  Injective.of_iso
    ((CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)).shiftFunctorObjXIso
      (-1) i (i - 1) (by omega)).symm inferInstance

/-- The support cone comparison, shifted to the normalized bounded-below models. -/
def rationalSupportConeToAmbientInjectiveConePlus
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    rationalCohomologyWithSupportComplexPlus X Z ⟶
      ambientRationalInjectiveConePlus X Z hZ :=
  ⟨(shiftFunctor _ (-1 : ℤ)).map
    (rationalSupportConeToAmbientInjectiveCone X Z hZ)⟩

instance rationalSupportConeToAmbientInjectiveConePlus_quasiIso
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (rationalSupportConeToAmbientInjectiveConePlus X Z hZ).hom :=
  (CochainComplex.quasiIso_shift_iff
    (rationalSupportConeToAmbientInjectiveCone X Z hZ) (-1)).2 inferInstance

/-- The existing support group is computed by the global sections of this
normalized ambient-injective cone. No smoothness assumption is needed. -/
def rationalSupportAddEquivAmbientInjectiveConeGlobalSections
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport X Z n ≃+
      (TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
        (TopCat.of (ComplexPoint X))
        (CochainComplex.mappingCone
          (ambientRationalInjectiveRestriction X Z hZ))).homology (n - 1) :=
  let f := rationalSupportConeToAmbientInjectiveConePlus X Z hZ
  let F := analyticHypercohomologyFunctor X n
  let _ : IsIso (DerivedCategory.Plus.Q.map f) := by infer_instance
  let _ : IsIso (F.map f) := by
    dsimp only [F, Functor.comp_map]
    infer_instance
  let e₁ := (asIso (F.map f)).addCommGroupIsoToAddEquiv
  let e₂ := hypercohomologyAddEquivGlobalSectionsKInjective X
    (ambientRationalInjectiveConePlus X Z hZ) n
  let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
    (TopCat.of (ComplexPoint X))
  let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
  let G := (Γ.mapHomologicalComplex (.up ℤ)).obj C
  let e₃ : ((Γ.mapHomologicalComplex (.up ℤ)).obj
      ((shiftFunctor _ (-1 : ℤ)).obj C)).homology n ≅
      ((shiftFunctor _ (-1 : ℤ)).obj G).homology n :=
    HomologicalComplex.homologyMapIso
      (((Γ.mapHomologicalComplex (.up ℤ)).commShiftIso (-1)).app C) n
  let e₄ : ((shiftFunctor _ (-1 : ℤ)).obj G).homology n ≅ G.homology (n - 1) := by
    exact ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
      (-1) n (n - 1) (by omega)).app G
  e₁.trans <| e₂.trans <| (e₃ ≪≫ e₄).addCommGroupIsoToAddEquiv

/-- Compare actual restriction of the integer-indexed ambient resolution with
the independently chosen complement resolution. The map/extension isomorphism
is displayed explicitly, rather than requiring the two models to be equal. -/
def ambientRationalOpenResolutionComparison
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    ((TopCat.Sheaf.openRestrictionPushforward
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩).mapHomologicalComplex
      (.up ℤ)).obj (ambientRationalInjectiveComplex X) ⟶
        derivedPushforwardComplementConstantRationalComplexInt X Z :=
  (HomologicalComplex.mapExtendCanonicalIso
    (TopCat.Sheaf.openRestrictionPushforward
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩)
    (TopCat.Sheaf.ambientConstantInjectiveResolution
      (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ)).cocomplex
      ComplexShape.embeddingUpNat).hom ≫
    HomologicalComplex.extendMap
      (((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticComplementInclusion X Z)).mapHomologicalComplex (.up ℕ)).map
        (TopCat.Sheaf.restrictedAmbientToOpenResolution
          (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩
          (AddCommGrpCat.of ℚ))) ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma actualRestriction_comp_openResolutionComparison
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    (TopCat.Sheaf.supportRestrictionComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩
      (ambientRationalInjectiveComplex X)).g ≫
        ambientRationalOpenResolutionComparison X Z hZ =
      ambientRationalInjectiveRestriction X Z hZ := by
  dsimp only [ambientRationalOpenResolutionComparison]
  change ((TopCat.Sheaf.toOpenRestrictionPushforward _ _).mapHomologicalComplex _).app _ ≫
    (HomologicalComplex.mapExtendCanonicalIso _ _ _).hom ≫ _ = _
  rw [HomologicalComplex.mapExtendCanonicalIso_hom_naturality_from_id_assoc]
  exact (ComplexShape.embeddingUpNat.extendFunctor (AnalyticAdditiveSheaf X)).map_comp _ _
    |>.symm

/-- Global sections of the actual open-resolution comparison. -/
def globalAmbientRationalOpenResolutionComparison
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :=
  ((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
    (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
      (ambientRationalOpenResolutionComparison X Z hZ)

set_option backward.isDefEq.respectTransparency false in
instance globalAmbientRationalOpenResolutionComparison_quasiIso
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (globalAmbientRationalOpenResolutionComparison X Z hZ) := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
  let k := ((TopCat.Sheaf.pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex
    (.up ℕ)).map (TopCat.Sheaf.restrictedAmbientToOpenResolution Y U (AddCommGrpCat.of ℚ))
  let : QuasiIso ((Γ.mapHomologicalComplex (.up ℕ)).map k) :=
    TopCat.Sheaf.globalRestrictedAmbientToOpenResolution_quasiIso Y U (AddCommGrpCat.of ℚ)
  let : QuasiIso ((Γ.mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap k ComplexShape.embeddingUpNat)) :=
    CochainComplex.quasiIso_map_extendMap_nat Γ k
  dsimp only [globalAmbientRationalOpenResolutionComparison,
    ambientRationalOpenResolutionComparison]
  rw [Functor.map_comp]
  change QuasiIso ((Γ.mapHomologicalComplex (.up ℤ)).map _ ≫
    (Γ.mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap k ComplexShape.embeddingUpNat))
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual group-level restriction cone maps to the cone of the independent
complement resolution. Both the ambient component and the prescribed
restriction square are fixed. -/
def actualSupportConeToAmbientInjectiveGlobalCone
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    CochainComplex.mappingCone
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).g ⟶
    CochainComplex.mappingCone
      (((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
          (ambientRationalInjectiveRestriction X Z hZ)) :=
  CochainComplex.mappingCone.map _ _ (𝟙 _)
    (globalAmbientRationalOpenResolutionComparison X Z hZ) (by
      let Γ := (TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)
      change Γ.map _ ≫ Γ.map _ = 𝟙 _ ≫ Γ.map _
      rw [Category.id_comp, ← Functor.map_comp,
        actualRestriction_comp_openResolutionComparison])

set_option backward.isDefEq.respectTransparency false in
instance actualSupportConeToAmbientInjectiveGlobalCone_quasiIso
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (actualSupportConeToAmbientInjectiveGlobalCone X Z hZ) :=
  CochainComplex.mappingCone.quasiIso_map_of_quasiIso _ _ _ _ _

/-- The existing rational support group is the homology of the actual
kernel-defined supported sections of the ambient rational injective
resolution. The shift `n - 1` in the old cone model is reconciled by the
explicit homology/shift isomorphism. The final negation corrects the
standard cone triangle's negative connecting projection, so that the
comparison preserves the actual support-forgetting inclusion. -/
def rationalSupportAddEquivSupportedInjectiveHomology
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport X Z n ≃+
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).X₁.homology n :=
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
    (ambientRationalInjectiveComplex X)
  let e₁ := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n
  let e₂ := HomologicalComplex.homologyMapIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso
      (ambientRationalInjectiveRestriction X Z hZ) Γ) (n - 1)
  let e₃ := (asIso (HomologicalComplex.homologyMap
    (actualSupportConeToAmbientInjectiveGlobalCone X Z hZ) (n - 1))).symm
  letI : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U ⊤ _)
  let e₄ := (asIso (HomologicalComplex.homologyMap
    (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1))).symm
  let e₅ := ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
    1 (n - 1) n (by omega)).app S.X₁
  (e₁.trans (e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅).addCommGroupIsoToAddEquiv).trans
    (AddEquiv.neg _)

end AlgebraicGeometry.ComplexPoint

end
