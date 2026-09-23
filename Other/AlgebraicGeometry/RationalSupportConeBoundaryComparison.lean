/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HypercohomologyFlasqueMapNaturality
public import Other.AlgebraicGeometry.DerivedSupportRationalConeComparison

/-!
# The common boundary of the fixed rational support-cone models

The natural singular model and ambient-injective model use the same independently
resolved complement. Both prescribed comparison maps preserve its positive cone
inclusion. Naturality of the actual global-section comparisons identifies the two
models on the image of that boundary, without asserting coherence on arbitrary
relative classes.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)

lemma rationalSupportConeToAmbientInjectiveCone_inr :
    CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X Z) ≫
      rationalSupportConeToAmbientInjectiveCone X Z hZ =
    CochainComplex.mappingCone.inr (ambientRationalInjectiveRestriction X Z hZ) := by
  simp [rationalSupportConeToAmbientInjectiveCone, CochainComplex.mappingCone.map]

local instance complementRationalComplexGEZero :
    (derivedPushforwardComplementConstantRationalComplexInt X Z).IsStrictlyGE 0 := by
  dsimp only [derivedPushforwardComplementConstantRationalComplexInt]
  infer_instance

local instance complementRationalComplexGEMinusOne :
    (derivedPushforwardComplementConstantRationalComplexInt X Z).IsStrictlyGE (-1) :=
  CochainComplex.isStrictlyGE_of_ge _ (-1) 0 (by omega)

/-- Global sections compute the actual complement-resolution hypercohomology. -/
def complementRationalHypercohomologyAddEquivGlobalSections (n : ℤ) :
    Hypercohomology X (derivedPushforwardComplementConstantRationalComplexInt X Z) n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
        (derivedPushforwardComplementConstantRationalComplexInt X Z)).homology n :=
  hypercohomologyAddEquivGlobalSections X _ (-1)
    (derivedPushforwardComplementConstantRationalComplexInt_term_isFlasque X Z) n

/-- The ambient-injective replacement preserves the actual complement boundary. -/
lemma rationalSupportAddEquivAmbientInjectiveConeGlobalSections_boundary (n : ℤ)
    (b : Hypercohomology X (derivedPushforwardComplementConstantRationalComplexInt X Z) (n - 1)) :
    rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n
      (hypercohomologyMap X
        (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X Z)) (n - 1) b) =
    HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCone.inr (ambientRationalInjectiveRestriction X Z hZ))) (n - 1)
      (complementRationalHypercohomologyAddEquivGlobalSections X Z (n - 1) b) := by
  change hypercohomologyAddEquivGlobalSectionsKInjective X _ (n - 1)
    (hypercohomologyMap X (rationalSupportConeToAmbientInjectiveCone X Z hZ) (n - 1)
      (hypercohomologyMap X
        (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X Z)) (n - 1) b)) = _
  rw [← hypercohomologyMap_comp_apply, rationalSupportConeToAmbientInjectiveCone_inr]
  exact hypercohomologyAddEquivGlobalSections_naturality_to_kInjective X _ _ (-1)
    (derivedPushforwardComplementConstantRationalComplexInt_term_isFlasque X Z) _ _ b

variable [IsIntegral X.left] [Smooth X.hom]

lemma rationalSupportConeToNaturalSingularCone_inr :
    CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X Z) ≫
      rationalSupportConeToNaturalSingularCone X Z hZ =
    CochainComplex.mappingCone.inr (naturalSingularResolutionRestriction X Z hZ) := by
  simp [rationalSupportConeToNaturalSingularCone, CochainComplex.mappingCone.map]

variable [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]

/-- The natural singular replacement preserves the same complement boundary. -/
lemma rationalSupportHypercohomologyAddEquivNaturalSingularConeGlobalSections_boundary (n : ℤ)
    (b : Hypercohomology X (derivedPushforwardComplementConstantRationalComplexInt X Z) (n - 1)) :
    rationalSupportHypercohomologyAddEquivNaturalSingularConeGlobalSections X Z hZ n
      (hypercohomologyMap X
        (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X Z)) (n - 1) b) =
    HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCone.inr (naturalSingularResolutionRestriction X Z hZ))) (n - 1)
      (complementRationalHypercohomologyAddEquivGlobalSections X Z (n - 1) b) := by
  let K := CochainComplex.mappingCone (naturalSingularResolutionRestriction X Z hZ)
  let : K.IsStrictlyGE (-1) := naturalSingularSupportCone_isStrictlyGE X Z hZ
  change hypercohomologyAddEquivGlobalSections X K (-1)
    (naturalSingularSupportCone_term_isFlasque X Z hZ) (n - 1)
      (hypercohomologyMap X (rationalSupportConeToNaturalSingularCone X Z hZ) (n - 1)
        (hypercohomologyMap X
          (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X Z)) (n - 1) b)) = _
  rw [← hypercohomologyMap_comp_apply, rationalSupportConeToNaturalSingularCone_inr]
  exact hypercohomologyAddEquivGlobalSections_naturality X _ K (-1)
    (derivedPushforwardComplementConstantRationalComplexInt_term_isFlasque X Z)
    (naturalSingularSupportCone_term_isFlasque X Z hZ) _ _ b

/-- The fixed singular and ambient-injective replacements agree on every class in the
image of the complement boundary. No equality away from that image is asserted. -/
lemma rationalSupportAmbientInjective_of_naturalSingular_boundary (n : ℤ)
    (z : (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (derivedPushforwardComplementConstantRationalComplexInt X Z)).homology (n - 1)) :
    rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n
      ((rationalSupportHypercohomologyAddEquivNaturalSingularConeGlobalSections X Z hZ n).symm
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (CochainComplex.mappingCone.inr (naturalSingularResolutionRestriction X Z hZ)))
            (n - 1) z)) =
    HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCone.inr (ambientRationalInjectiveRestriction X Z hZ)))
        (n - 1) z := by
  obtain ⟨b, rfl⟩ := (complementRationalHypercohomologyAddEquivGlobalSections X Z (n - 1)).surjective z
  rw [← rationalSupportHypercohomologyAddEquivNaturalSingularConeGlobalSections_boundary,
    AddEquiv.symm_apply_apply, rationalSupportAddEquivAmbientInjectiveConeGlobalSections_boundary]

end AlgebraicGeometry.ComplexPoint
