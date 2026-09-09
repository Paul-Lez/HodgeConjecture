/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HypercohomologyFlasqueNaturality
public import Other.AlgebraicGeometry.DerivedSupportRationalConeForget
public import Other.AlgebraicGeometry.ComplexSupportedSingularModel

/-!
# Ordinary-target normalization of the original Betti support-cone pipeline

The natural singular support cone and the actual ambient injective resolution are
connected through their prescribed rational augmentations. Forgetting support is
computed by the actual cone connecting map followed by the normalized singular-to-
injective map. In particular its sign is not replaced by a chosen group comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

/-- The actual singular-to-injective comparison preserves the very augmentation used
by the original rational Betti support cone. -/
@[reassoc]
theorem rationalToSingular_comp_complexSingularToAmbientInjective :
    rationalToSingularCochainComplexInt X ≫ complexSingularToAmbientInjective X =
      ambientRationalInjectiveAugmentation X := by
  change HomologicalComplex.extendMap (constantsToSingularCochainSheafComplex ℚ
      (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      (singularToConstantInjectiveResolution (TopCat.of (ComplexPoint X))
        (exists_contractibleOpen_le X)) ComplexShape.embeddingUpNat = _
  rw [← HomologicalComplex.extendMap_comp, constants_comp_singularToConstantInjectiveResolution]
  rfl

/-- The original support-cone map commutes with the actual shifted ambient-injective
connecting map, including its existing cone sign. -/
@[reassoc]
theorem rationalSupportConeToNaturalSingularCone_ambient_connecting
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    rationalSupportConeToNaturalSingularCone X Z hZ ≫
      (CochainComplex.mappingCone.triangle (naturalSingularResolutionRestriction X Z hZ)).mor₃ ≫
        (complexSingularToAmbientInjective X)⟦(1 : ℤ)⟧' =
      (CochainComplex.mappingCone.triangle (rationalRestrictionComplexInt X Z)).mor₃ ≫
        (ambientRationalInjectiveAugmentation X)⟦(1 : ℤ)⟧' := by
  have h := (CochainComplex.mappingCone.triangleMap
    (rationalRestrictionComplexInt X Z) (naturalSingularResolutionRestriction X Z hZ)
    (rationalToSingularCochainComplexInt X) (𝟙 _)
    (by simpa using (rationalToSingular_comp_naturalSingularResolutionRestriction X Z hZ).symm)).comm₃
  change (CochainComplex.mappingCone.triangle (rationalRestrictionComplexInt X Z)).mor₃ ≫
      (rationalToSingularCochainComplexInt X)⟦(1 : ℤ)⟧' =
    rationalSupportConeToNaturalSingularCone X Z hZ ≫
      (CochainComplex.mappingCone.triangle (naturalSingularResolutionRestriction X Z hZ)).mor₃ at h
  rw [← Category.assoc, ← h, Category.assoc, ← Functor.map_comp,
    rationalToSingular_comp_complexSingularToAmbientInjective]

variable [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]

/-- The old support-forgetting map, computed through its natural singular support cone,
lands in the actual ambient injective homology with the unaltered connecting sign. -/
theorem rationalCohomologyAmbient_forgetSupport_naturalSingularCone
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (a : RationalCohomologyWithSupport X Z n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X n (forgetSupport X Z n a) =
      (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
        (ShiftedHom.map
          ((CochainComplex.mappingCone.triangle (naturalSingularResolutionRestriction X Z hZ)).mor₃ ≫
            (complexSingularToAmbientInjective X)⟦(1 : ℤ)⟧')
          ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)))
        (n - 1) n (by omega)
        (rationalSupportHypercohomologyAddEquivNaturalSingularConeGlobalSections X Z hZ n a) := by
  let K := CochainComplex.mappingCone (naturalSingularResolutionRestriction X Z hZ)
  let : K.IsStrictlyGE (-1) := naturalSingularSupportCone_isStrictlyGE X Z hZ
  change hypercohomologyAddEquivGlobalSectionsKInjective X _ n
    (hypercohomologyMap X (ambientRationalInjectiveAugmentation X) n
      (a.comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (CochainComplex.mappingCone.triangle (rationalRestrictionComplexInt X Z)).mor₃) (by omega))) = _
  exact (congrArg (hypercohomologyAddEquivGlobalSectionsKInjective X
    (ambientRationalInjectiveComplex X) n)
    (hypercohomologyMap_comp_shifted X 1 (n - 1) n (by omega)
      (rationalSupportConeToNaturalSingularCone X Z hZ) _ _ _
      (rationalSupportConeToNaturalSingularCone_ambient_connecting X Z hZ) a)).trans
    (hypercohomologyAddEquivGlobalSections_shifted_naturality_to_kInjective
      X K (ambientRationalInjectiveComplex X) (-1)
      (naturalSingularSupportCone_term_isFlasque X Z hZ) 1 (n - 1) n (by omega) _ _)

end AlgebraicGeometry.ComplexPoint
