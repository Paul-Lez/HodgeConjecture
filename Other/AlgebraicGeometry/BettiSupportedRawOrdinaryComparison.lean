/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.BettiSupportedOrdinaryConeComparison
public import Other.AlgebraicTopology.RelativeCochainConeForgetComparison

/-!
# The ordinary target of the original raw singular support comparison

The global raw-to-sheaf cone map commutes with the actual cone connecting map.
This gives an exact formula for the old support-forgetting construction in terms
of raw singular cochains, before comparing its sign with kernel-defined support.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The prescribed global raw-to-natural cone map preserves the actual connecting
map, followed by the prescribed ambient singular-to-injective comparison. -/
@[reassoc]
theorem globalRawSupportConeToNatural_ambient_connecting
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    globalRawSupportConeToGlobalNaturalSingularCone X Z hZ ≫
      (CochainComplex.mappingCone.triangle
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
          (naturalSingularResolutionRestriction X Z hZ))).mor₃ ≫
      ((((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
        (complexSingularToAmbientInjective X)))⟦(1 : ℤ)⟧' =
    (CochainComplex.mappingCone.triangle
      (globalRawSingularRestrictionInt ℚ (TopCat.of (ComplexPoint X))
        Zᶜ)).mor₃ ≫
      (globalRawToSingularSheafInt X ≫
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
          (complexSingularToAmbientInjective X))⟦(1 : ℤ)⟧' := by
  have h := (CochainComplex.mappingCone.triangleMap
    (globalRawSingularRestrictionInt ℚ (TopCat.of (ComplexPoint X))
      Zᶜ)
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
      (naturalSingularResolutionRestriction X Z hZ))
    (globalRawToSingularSheafInt X)
    (globalRawComplementToDerivedPushforwardInt X Z hZ)
    (globalNaturalSingularResolutionRestrictionInt_naturality X Z hZ).symm).comm₃
  change _ = globalRawSupportConeToGlobalNaturalSingularCone X Z hZ ≫ _ at h
  rw [← Category.assoc, ← h, Category.assoc, ← Functor.map_comp]
  rfl

variable [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2400000 in
/-- The old support-forgetting construction is the raw cone connecting map,
followed by the actual raw-to-sheaf and singular-to-injective maps. -/
theorem rationalCohomologyAmbient_forgetSupport_rawSingularCone
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (a : RationalCohomologyWithSupport X Z n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X n (forgetSupport X Z n a) =
      HomologicalComplex.homologyMap
        (globalRawToSingularSheafInt X ≫
          ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (complexSingularToAmbientInjective X)) n
        ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
          (CochainComplex.mappingCone.triangle
            (globalRawSingularRestrictionInt ℚ (TopCat.of (ComplexPoint X))
              Zᶜ)).mor₃ (n - 1) n (by omega)
          ((inv (HomologicalComplex.homologyMap
            (globalRawSupportConeToGlobalNaturalSingularCone X Z hZ) (n - 1)))
            (HomologicalComplex.homologyMap
              (globalSectionsNaturalSingularConeIsoMappingCone X Z hZ).hom (n - 1)
              (rationalSupportHypercohomologyAddEquivNaturalSingularConeGlobalSections
                X Z hZ n a)))) := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  let F := Γ.mapHomologicalComplex (.up ℤ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  let b := naturalSingularResolutionRestriction X Z hZ
  let u := complexSingularToAmbientInjective X
  let c := globalRawSupportConeToGlobalNaturalSingularCone X Z hZ
  let e := globalSectionsNaturalSingularConeIsoMappingCone X Z hZ
  let r := globalRawSingularRestrictionInt ℚ (TopCat.of (ComplexPoint X))
    Zᶜ
  let y := rationalSupportHypercohomologyAddEquivNaturalSingularConeGlobalSections X Z hZ n a
  have hmap : ShiftedHom.map ((CochainComplex.mappingCone.triangle b).mor₃ ≫ u⟦(1 : ℤ)⟧') F =
      ShiftedHom.map (CochainComplex.mappingCone.triangle b).mor₃ F ≫ (F.map u)⟦(1 : ℤ)⟧' := by
    simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]
    exact congrArg (fun f => F.map (CochainComplex.mappingCone.triangle b).mor₃ ≫ f)
      ((F.commShiftIso (1 : ℤ)).hom.naturality u)
  have he := CochainComplex.mappingCone.mapHomologicalComplexIso_homology_connecting
    b Γ (n - 1) n (by omega)
  have hc : HomologicalComplex.homologyMap c (n - 1) ≫
      H.shiftMap (CochainComplex.mappingCone.triangle (F.map b)).mor₃ (n - 1) n (by omega) ≫
        HomologicalComplex.homologyMap (F.map u) n =
      H.shiftMap (CochainComplex.mappingCone.triangle r).mor₃ (n - 1) n (by omega) ≫
        HomologicalComplex.homologyMap
          (globalRawToSingularSheafInt X ≫ F.map u) n := by
    have hh := congrArg (fun f => H.shiftMap f (n - 1) n (show (1 : ℤ) + (n - 1) = n by omega))
      (globalRawSupportConeToNatural_ambient_connecting X Z hZ)
    erw [Functor.shiftMap_comp' H c] at hh
    simp only [Functor.shiftMap_comp] at hh
    dsimp only [F, Γ, b, r, u, c]
    exact hh
  have hc' := congrArg
    (fun f => inv (HomologicalComplex.homologyMap c (n - 1)) ≫ f) hc
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at hc'
  rw [rationalCohomologyAmbient_forgetSupport_naturalSingularCone]
  change H.shiftMap (ShiftedHom.map
    ((CochainComplex.mappingCone.triangle b).mor₃ ≫ u⟦(1 : ℤ)⟧') F)
    (n - 1) n (by omega) y = _
  rw [hmap, Functor.shiftMap_comp]
  erw [← he]
  change (HomologicalComplex.homologyMap e.hom (n - 1) ≫
    H.shiftMap (CochainComplex.mappingCone.triangle (F.map b)).mor₃
      (n - 1) n (by omega) ≫ HomologicalComplex.homologyMap (F.map u) n) y = _
  exact ConcreteCategory.congr_hom (congrArg
    (fun f => HomologicalComplex.homologyMap e.hom (n - 1) ≫ f) hc') y

set_option maxHeartbeats 1000000 in
/-- For an actual relative singular class, the old ordinary coclass is obtained
from its raw-cone representative by the signed connecting map. This formula
retains every augmentation and comparison used in the original definition. -/
theorem rationalCohomologyAmbient_forgetSupport_of_singular
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) Z n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X (n : ℤ)
      (forgetSupport X Z (n : ℤ)
        ((rationalCohomologyWithSupportAddEquivSingular X Z hZ n).symm a)) =
      HomologicalComplex.homologyMap
        (globalRawToSingularSheafInt X ≫
          ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (complexSingularToAmbientInjective X)) (n : ℤ)
        ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
          (CochainComplex.mappingCone.triangle
            (globalRawSingularRestrictionInt ℚ (TopCat.of (ComplexPoint X))
              Zᶜ)).mor₃ ((n : ℤ) - 1) (n : ℤ) (by omega)
          ((globalRawSingularRestrictionConeCohomologyEquivSupport ℚ
            (TopCat.of (ComplexPoint X)) Z n).symm a)) := by
  rw [rationalCohomologyAmbient_forgetSupport_rawSingularCone X Z hZ]
  congr 2
  apply (globalRawSingularRestrictionConeCohomologyEquivSupport ℚ
    (TopCat.of (ComplexPoint X)) Z n).injective
  rw [AddEquiv.apply_symm_apply]
  exact (rationalCohomologyWithSupportAddEquivSingular X Z hZ n).apply_symm_apply a

end AlgebraicGeometry.ComplexPoint
