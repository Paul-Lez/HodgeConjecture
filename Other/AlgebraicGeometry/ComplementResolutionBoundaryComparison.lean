/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.Homology.PrecompFactorization
public import Other.AlgebraicGeometry.BettiSupportedOrdinaryConeComparison
public import Other.AlgebraicGeometry.OpenRestrictionDerivedFactorization

/-!
# Homotopy comparison on the actual open complement

The natural singular-to-complement map factors through actual restriction because
every term of the complement-resolution target is local on that open. The factor
is homotopic to the prescribed singular-to-ambient-injective map followed by its
actual complement-resolution comparison. Both extend the same rational constant
augmentation; no Chern-class or local-chart identity is assumed.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
variable (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)

lemma complementResolution_precomp_bijective
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (p q : ℤ) :
    Function.Bijective (fun f :
      (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X))
        ⟨Zᶜ, hZ.isOpen_compl⟩ K).X₃.X p ⟶
        (derivedPushforwardComplementConstantRationalComplexInt X Z).X q =>
      (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X))
        ⟨Zᶜ, hZ.isOpen_compl⟩ K).g.f p ≫ f) :=
  isOpenRestrictionLocal_derivedPushforward X ⟨Zᶜ, hZ.isOpen_compl⟩ Z rfl q (K.X p)

variable [IsIntegral X.left] [Smooth X.hom]

/-- The natural singular-to-complement map, factored through actual open restriction. -/
def naturalSingularOutsideResolutionComparison :
    (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X))
      ⟨Zᶜ, hZ.isOpen_compl⟩ (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₃ ⟶
    derivedPushforwardComplementConstantRationalComplexInt X Z :=
  HomologicalComplex.descOfPrecompBijective _
    (complementResolution_precomp_bijective X Z hZ _)
    (naturalSingularResolutionRestriction X Z hZ)

@[reassoc]
lemma actualSingularRestriction_comp_naturalOutsideResolutionComparison :
    (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X))
      ⟨Zᶜ, hZ.isOpen_compl⟩ (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).g ≫
      naturalSingularOutsideResolutionComparison X Z hZ =
    naturalSingularResolutionRestriction X Z hZ :=
  HomologicalComplex.comp_descOfPrecompBijective _ _ _

/-- The actual singular-to-ambient-injective map restricted to the complement and followed
by the fixed independent complement resolution comparison. -/
def ambientSingularOutsideResolutionComparison :
    (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X))
      ⟨Zᶜ, hZ.isOpen_compl⟩ (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₃ ⟶
    derivedPushforwardComplementConstantRationalComplexInt X Z :=
  ((TopCat.Sheaf.openRestrictionPushforward (TopCat.of (ComplexPoint X))
    ⟨Zᶜ, hZ.isOpen_compl⟩).mapHomologicalComplex (.up ℤ)).map
      (complexSingularToAmbientInjective X) ≫ ambientRationalOpenResolutionComparison X Z hZ

@[reassoc]
lemma actualSingularRestriction_comp_ambientOutsideResolutionComparison :
    (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X))
      ⟨Zᶜ, hZ.isOpen_compl⟩ (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).g ≫
      ambientSingularOutsideResolutionComparison X Z hZ =
    complexSingularToAmbientInjective X ≫ ambientRationalInjectiveRestriction X Z hZ := by
  let f := TopCat.Sheaf.supportRestrictionComplexShortComplexMap
    (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ (complexSingularToAmbientInjective X)
  change _ ≫ (_ ≫ ambientRationalOpenResolutionComparison X Z hZ) = _
  erw [← Category.assoc, ← f.comm₂₃, Category.assoc,
    actualRestriction_comp_openResolutionComparison]
  rfl

local instance complementComparisonDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _

/-- The natural and ambient-injective restriction maps have homotopic normalized augmentations. -/
def naturalSingularResolutionRestrictionHomotopy :
    Homotopy (naturalSingularResolutionRestriction X Z hZ)
      (complexSingularToAmbientInjective X ≫ ambientRationalInjectiveRestriction X Z hZ) := by
  letI := derivedPushforwardComplementConstantRationalComplexInt_isKInjective X Z hZ
  letI : QuasiIso (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_quasiIso X
  refine CochainComplex.homotopyOfPrecompQuasiIso
    (rationalToSingularCochainComplexInt X) _ _ ?_
  calc
    _ = rationalRestrictionComplexInt X Z :=
      rationalToSingular_comp_naturalSingularResolutionRestriction X Z hZ
    _ = rationalToSingularCochainComplexInt X ≫
        (complexSingularToAmbientInjective X ≫ ambientRationalInjectiveRestriction X Z hZ) := by
      rw [← Category.assoc, rationalToSingular_comp_complexSingularToAmbientInjective,
        ambientRationalAugmentation_comp_restriction]

/-- The two actual complement comparisons are homotopic. Their normalizations on rational
constants agree, and the target terms are local on the complement. -/
def naturalSingularOutsideResolutionComparisonHomotopy :
    Homotopy (naturalSingularOutsideResolutionComparison X Z hZ)
      (ambientSingularOutsideResolutionComparison X Z hZ) :=
  HomologicalComplex.homotopyOfPrecompBijective
    (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X))
      ⟨Zᶜ, hZ.isOpen_compl⟩ (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).g
    (complementResolution_precomp_bijective X Z hZ _)
    ((Homotopy.ofEq (actualSingularRestriction_comp_naturalOutsideResolutionComparison X Z hZ)).trans
      ((naturalSingularResolutionRestrictionHomotopy X Z hZ).trans
        (Homotopy.ofEq (actualSingularRestriction_comp_ambientOutsideResolutionComparison X Z hZ).symm)))

/-- Equality of the actual complement comparison maps on section cohomology over every open. -/
lemma naturalSingularOutsideResolutionComparison_homologyMap
    (V : Opens (ComplexPoint X)) (n : ℤ) :
    HomologicalComplex.homologyMap
      (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
        (.up ℤ)).map (naturalSingularOutsideResolutionComparison X Z hZ)) n =
    HomologicalComplex.homologyMap
      (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
        (.up ℤ)).map (ambientSingularOutsideResolutionComparison X Z hZ)) n :=
  ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomotopy
    (naturalSingularOutsideResolutionComparisonHomotopy X Z hZ)).homologyMap_eq n
end AlgebraicGeometry.ComplexPoint
