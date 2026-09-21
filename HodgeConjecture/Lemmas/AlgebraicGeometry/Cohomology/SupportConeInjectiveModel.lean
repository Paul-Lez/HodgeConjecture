/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

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

/-- Let `X` be a scheme over `ℂ`, let `Y = X(ℂ)`, and let `Z ⊆ Y` be closed with complement `U`.
Write `I` for the chosen injective resolution of the constant rational sheaf on `Y`, `J` for the
chosen resolution on `U`, and `j : U → Y` for inclusion. This map `I → j_*J` first restricts to
`U`, then applies the comparison `I|_U → J` extending the identity on constant sheaves. Both
complexes are extended by zero to negative degrees. -/
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

/-- Let `X` be a scheme over `ℂ`, let `Y = X(ℂ)`, and let `Z ⊆ Y` be closed with complement `U`.
Write `I` for the chosen injective resolution of the constant rational sheaf on `Y`, `J` for the
chosen resolution on `U`, and `j : U → Y` for inclusion. This map `Cone(ℚ_Y[0] → j_*J) → Cone(I
→ j_*J)` is induced by the augmentation `ℚ_Y[0] → I` and the identity of `j_*J`. -/
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

/-- Let `X` be a scheme over `ℂ`, let `Y = X(ℂ)`, and let `Z ⊆ Y` be closed with complement `U`.
Write `I` for the chosen injective resolution of the constant rational sheaf on `Y`, `J` for the
chosen resolution on `U`, and `j : U → Y` for inclusion. This additive equivalence identifies
cohomology with support `H_Z^n(Y;ℚ)` with `H^{n-1}(Γ(Y,Cone(I → j_*J)))`. It replaces the
constant sheaf in the defining support cone by its injective resolution. -/
def rationalSupportAddEquivAmbientInjectiveConeGlobalSections
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport X Z n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
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

/-- Let `X` be a scheme over `ℂ`, let `Y = X(ℂ)`, and let `Z ⊆ Y` be closed with complement `U`.
Write `I` for the chosen injective resolution of the constant rational sheaf on `Y`, `J` for the
chosen resolution on `U`, and `j : U → Y` for inclusion. This is the direct image under `j` of
the comparison `I|_U → J` extending the identity on the constant rational sheaf, after extension
by zero to negative degrees. -/
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

/-- Let `X` be a scheme over `ℂ`, let `Y = X(ℂ)`, and let `Z ⊆ Y` be closed with complement `U`.
Write `I` for the chosen injective resolution of the constant rational sheaf on `Y`, `J` for the
chosen resolution on `U`, and `j : U → Y` for inclusion. Taking global sections of the direct
image of `I|_U → J` gives this map of complexes `Γ(U,I|_U) → Γ(U,J)`, with both sides expressed
as sections on `Y`. -/
def globalAmbientRationalOpenResolutionComparison
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :=
  ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
      (ambientRationalOpenResolutionComparison X Z hZ)

set_option backward.isDefEq.respectTransparency false in
instance globalAmbientRationalOpenResolutionComparison_quasiIso
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (globalAmbientRationalOpenResolutionComparison X Z hZ) := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
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
/-- Let `X` be a scheme over `ℂ`, let `Y = X(ℂ)`, and let `Z ⊆ Y` be closed with complement `U`.
Write `I` for the chosen injective resolution of the constant rational sheaf on `Y`, `J` for the
chosen resolution on `U`, and `j : U → Y` for inclusion. This map `Cone(Γ(Y,I) → Γ(U,I|_U)) →
Cone(Γ(Y,I) → Γ(U,J))` uses the identity on the ambient sections and the augmentation-preserving
comparison on `U`. -/
def supportConeToAmbientInjectiveGlobalCone
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    CochainComplex.mappingCone
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).g ⟶
    CochainComplex.mappingCone
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
          (ambientRationalInjectiveRestriction X Z hZ)) :=
  CochainComplex.mappingCone.map _ _ (𝟙 _)
    (globalAmbientRationalOpenResolutionComparison X Z hZ) (by
      let Γ := (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ
      change Γ.map _ ≫ Γ.map _ = 𝟙 _ ≫ Γ.map _
      rw [Category.id_comp, ← Functor.map_comp,
        supportRestriction_comp_openResolutionComparison])

set_option backward.isDefEq.respectTransparency false in
instance supportConeToAmbientInjectiveGlobalCone_quasiIso
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (supportConeToAmbientInjectiveGlobalCone X Z hZ) :=
  CochainComplex.mappingCone.quasiIso_map_of_quasiIso _ _ _ _ _

/-- Let `X` be a scheme over `ℂ`, let `Y = X(ℂ)`, and let `Z ⊆ Y` be closed with complement `U`.
Write `I` for the chosen injective resolution of the constant rational sheaf on `Y`, `J` for the
chosen resolution on `U`, and `j : U → Y` for inclusion. Cohomology with support `H_Z^n(Y;ℚ)` is
additively isomorphic to `H^n(Γ_Z(Y,I))`, where `Γ_Z(Y,I^q) = ker(I^q(Y) → I^q(U))`. This
equivalence passes from the defining shifted restriction cone to that kernel complex. A final
negation accounts for the sign of the cone triangle, so forgetting support corresponds to
including the kernel into `Γ(Y,I)`. -/
def rationalSupportAddEquivSupportedInjectiveHomology
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    RationalCohomologyWithSupport X Z n ≃+
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).X₁.homology n :=
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
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
