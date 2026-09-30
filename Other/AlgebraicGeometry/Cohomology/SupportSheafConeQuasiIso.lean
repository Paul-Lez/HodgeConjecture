/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeComparison
public import Other.AlgebraicTopology.Sheaf.FlasquePushforwardQuasiIso
public import Other.AlgebraicTopology.SingularChainSheafPushforward

/-! # The supported sheaf complex and the ambient injective cone -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The direct image of the fixed complement-resolution comparison is a quasi-isomorphism.
Both resolutions on the complement are termwise flasque. -/
instance ambientRationalOpenResolutionComparison_quasiIso :
    QuasiIso (ambientRationalOpenResolutionComparison X Z hZ) := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let K := TopCat.Sheaf.restrictedAmbientConstantResolution Y U (AddCommGrpCat.of ℚ)
  let L := (TopCat.Sheaf.ambientConstantInjectiveResolution (TopCat.of U)
    (AddCommGrpCat.of ℚ)).cocomplex
  let f : K ⟶ L := TopCat.Sheaf.restrictedAmbientToOpenResolution Y U (AddCommGrpCat.of ℚ)
  let F := TopCat.Sheaf.pushforward AddCommGrpCat U.inclusion'
  let : QuasiIso f := TopCat.Sheaf.restrictedAmbientToOpenResolution_quasiIso Y U _
  let fInt := HomologicalComplex.extendMap f ComplexShape.embeddingUpNat
  have hK : ∀ n, (K.X n).IsFlasque :=
    TopCat.Sheaf.restrictedAmbientConstantResolution_isFlasque Y U _
  have hL : ∀ n, (L.X n).IsFlasque := fun n =>
    @TopCat.Sheaf.injective_isFlasque _ _
      ((TopCat.Sheaf.ambientConstantInjectiveResolution (TopCat.of U)
        (AddCommGrpCat.of ℚ)).injective n)
  let : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map fInt) :=
    TopCat.Sheaf.pushforward_map_quasiIso_of_flasque U.inclusion' fInt 0 0
      (TopCat.Sheaf.extendNat_term_isFlasque K hK)
      (TopCat.Sheaf.extendNat_term_isFlasque L hL)
  let eK := HomologicalComplex.mapExtendCanonicalIso F K ComplexShape.embeddingUpNat
  let k := (F.mapHomologicalComplex (.up ℕ)).map f
  have hcomp : QuasiIso
      (eK.hom ≫ HomologicalComplex.extendMap k ComplexShape.embeddingUpNat) := by
    rw [← HomologicalComplex.mapExtendCanonicalIso_naturality]
    infer_instance
  let : QuasiIso (HomologicalComplex.extendMap k ComplexShape.embeddingUpNat) :=
    quasiIso_of_comp_left eK.hom _
  dsimp only [ambientRationalOpenResolutionComparison]
  change QuasiIso (_ ≫ HomologicalComplex.extendMap k ComplexShape.embeddingUpNat)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual support-to-cone map is a quasi-isomorphism of sheaf complexes. -/
instance supportSheafToAmbientInjectiveCone_quasiIso :
    QuasiIso (supportSheafToAmbientInjectiveCone X Z hZ) := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y U
    (ambientRationalInjectiveComplex X)
  have hS : S.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
      dsimp [S, TopCat.Sheaf.supportRestrictionComplexShortComplex]
      exact
        { exact := ShortComplex.exact_kernel _
          mono_f := inferInstanceAs (Mono (kernel.ι _))
          epi_g := inferInstanceAs
            (Epi ((TopCat.Sheaf.toOpenRestrictionPushforward Y U).app
              ((ambientRationalInjectiveComplex X).X n))) }
  let : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S hS
  let : QuasiIso (CochainComplex.mappingCone.map S.g
      (ambientRationalInjectiveRestriction X Z hZ) (𝟙 _)
      (ambientRationalOpenResolutionComparison X Z hZ)
      (by rw [Category.id_comp]; exact supportRestriction_comp_openResolutionComparison X Z hZ)) :=
    CochainComplex.mappingCone.quasiIso_map_of_quasiIso _ _ _ _ _
  unfold supportSheafToAmbientInjectiveCone
  exact quasiIso_comp (CochainComplex.mappingCocone.shiftedLiftShortComplex S) _

end AlgebraicGeometry.ComplexPoint
