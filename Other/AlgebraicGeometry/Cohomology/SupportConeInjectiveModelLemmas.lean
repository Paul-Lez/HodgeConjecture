/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.AmbientInjectiveResolution
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenInjectiveResolution
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsLocalization
public import HodgeConjecture.Lemmas.Algebra.Homology.MapExtendNaturality
public import Other.AlgebraicGeometry.Cohomology.HypercohomologyNaturalityDef

/-!
# Normalized injective models for the rational support cone

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.AmbientInjectiveResolution`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

/-- Let `X` be a scheme over `ℂ`, `Y = X(ℂ)`, and `j : U → Y` the inclusion of the complement of a
closed subset `Z`. Let `I,J` be the chosen injective resolutions of the constant rational
sheaves on `Y,U`. This map `I → j_*J` restricts to `U` and applies the comparison `I|_U → J`
extending the identity on constants. The complexes are zero in negative degrees. -/
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

/-- Let `X` be a scheme over `ℂ`, `Y = X(ℂ)`, and `j : U → Y` the inclusion of the complement of a
closed subset `Z`. Let `I,J` be the chosen injective resolutions of the constant rational
sheaves on `Y,U`. This map `Cone(ℚ_Y[0] → j_*J) → Cone(I → j_*J)` applies the augmentation
`ℚ_Y[0] → I` and the identity on `j_*J`. -/
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

/-- The replacement cone is termwise injective: its terms are
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

/-- Let `X` be a scheme over `ℂ`, `Y = X(ℂ)`, and `j : U → Y` the inclusion of the complement of a
closed subset `Z`. Let `I,J` be the chosen injective resolutions of the constant rational
sheaves on `Y,U`. Replacing `ℚ_Y[0]` by `I` gives this additive equivalence `H_Z^n(Y;ℚ) ≃
H^{n-1}(Γ(Y,Cone(I → j_*J)))` from cohomology with support in `Z`. -/
def rationalSupportAddEquivAmbientInjectiveConeGlobalSections
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport X Z n ≃+
      (TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
        (TopCat.of (ComplexPoint X))
        (CochainComplex.mappingCone
          (ambientRationalInjectiveRestriction X Z hZ))).homology (n - 1) :=
  let e : RationalCohomologyWithSupport X Z n ≃+
      Hypercohomology X (CochainComplex.mappingCone
        (ambientRationalInjectiveRestriction X Z hZ)) (n - 1) :=
    { toEquiv := Localization.SmallShiftedHom.postcompEquiv
        (rationalSupportConeToAmbientInjectiveCone X Z hZ)
        ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
      map_add' α β := (hypercohomologyMap X
        (rationalSupportConeToAmbientInjectiveCone X Z hZ) (n - 1)).map_add α β }
  e.trans (hypercohomologyAddEquivGlobalSectionsKInjective X _ (n - 1))

/-- Let `X` be a scheme over `ℂ`, `Y = X(ℂ)`, and `j : U → Y` the inclusion of the complement of a
closed subset `Z`. Let `I,J` be the chosen injective resolutions of the constant rational
sheaves on `Y,U`. This map `j_*(I|_U) → j_*J` is the direct image of the comparison extending
the identity on constants, with both complexes zero in negative degrees. -/
def ambientRationalOpenResolutionComparison
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    ((TopCat.Sheaf.openRestrictionPushforward
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩).mapHomologicalComplex
      ℤᵘᵖ).obj (ambientRationalInjectiveComplex X) ⟶
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
lemma supportRestriction_comp_openResolutionComparison
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

/-- Let `X` be a scheme over `ℂ` and `U` the complement of a closed subset of `Y = X(ℂ)`. For the
chosen injective resolutions `I,J` of the constant rational sheaves on `Y,U`, this map
`Γ(U,I|_U) → Γ(U,J)` takes sections of the comparison `I|_U → J` extending the identity on
constants. -/
def globalAmbientRationalOpenResolutionComparison
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :=
  ((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
    (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
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
  let : QuasiIso ((Γ.mapHomologicalComplex ℤᵘᵖ).map
      (HomologicalComplex.extendMap k ComplexShape.embeddingUpNat)) :=
    CochainComplex.quasiIso_map_extendMap_nat Γ k
  dsimp only [globalAmbientRationalOpenResolutionComparison,
    ambientRationalOpenResolutionComparison]
  rw [Functor.map_comp]
  change QuasiIso ((Γ.mapHomologicalComplex ℤᵘᵖ).map _ ≫
    (Γ.mapHomologicalComplex ℤᵘᵖ).map
      (HomologicalComplex.extendMap k ComplexShape.embeddingUpNat))
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Let `X` be a scheme over `ℂ` and `U` the complement of a closed subset of `Y = X(ℂ)`. For the
chosen injective resolutions `I,J` of the constant rational sheaves on `Y,U`, this map
`Cone(Γ(Y,I) → Γ(U,I|_U)) → Cone(Γ(Y,I) → Γ(U,J))` uses the identity on ambient sections and the
comparison `I|_U → J` extending the identity on constants. -/
def supportConeToAmbientInjectiveGlobalCone
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    CochainComplex.mappingCone
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).g ⟶
    CochainComplex.mappingCone
      (((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
          (ambientRationalInjectiveRestriction X Z hZ)) :=
  CochainComplex.mappingCone.map _ _ (𝟙 _)
    (globalAmbientRationalOpenResolutionComparison X Z hZ) (by
      let Γ := (TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ
      change Γ.map _ ≫ Γ.map _ = 𝟙 _ ≫ Γ.map _
      rw [Category.id_comp, ← Functor.map_comp,
        supportRestriction_comp_openResolutionComparison])

set_option backward.isDefEq.respectTransparency false in
instance supportConeToAmbientInjectiveGlobalCone_quasiIso
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (supportConeToAmbientInjectiveGlobalCone X Z hZ) :=
  CochainComplex.mappingCone.quasiIso_map_of_quasiIso _ _ _ _ _

/-- Let `X` be a scheme over `ℂ`, `Z ⊆ Y = X(ℂ)` closed, and `I` the chosen injective resolution of
the constant rational sheaf on `Y`. This additive equivalence identifies cohomology with support
`H_Z^n(Y;ℚ)` with `H^n(Γ_Z(Y,I))`, where `Γ_Z(Y,I^q) = ker(I^q(Y) → I^q(Y \ Z))`. Its sign makes
forgetting support correspond to inclusion into `Γ(Y,I)`. -/
def coneSupportAddEquivSupportedInjectiveHomology
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
    (supportConeToAmbientInjectiveGlobalCone X Z hZ) (n - 1))).symm
  letI : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U ⊤ _)
  let e₄ := (asIso (HomologicalComplex.homologyMap
    (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1))).symm
  let e₅ := ((HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftIso
    1 (n - 1) n (by omega)).app S.X₁
  (e₁.trans (e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅).addCommGroupIsoToAddEquiv).trans
    (AddEquiv.neg _)

end AlgebraicGeometry.ComplexPoint

end
