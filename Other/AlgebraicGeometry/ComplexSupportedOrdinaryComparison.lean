/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf
public import Other.AlgebraicTopology.SupportedSingularOrdinaryComparison
public import Other.AlgebraicTopology.TopOpenRelativeCochainNormalization
public import Other.AlgebraicGeometry.SingularSupportedOrdinarySign

/-! # Actual positive ordinary normalization of the ambient supported injective model -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicTopology.Singular

/-- The literal top-open sheafification unit agrees with the original
plus-construction global comparison, not just with some quasi-isomorphism. -/
theorem openRawToSingularCochainSheafComplex_top (R : Type) [Field R] (X : TopCat.{0}) :
    openRawToSingularCochainSheafComplex R X ⊤ =
      topOpenToGlobalSingularCochainSheafComplex R X := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [topOpenToGlobalSingularCochainSheafComplex_f]
  rfl

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ)))

/-- Top-open raw-to-sheaf normalization survives both actual grading comparisons. -/
theorem complexOpenRawToSheafTop_eq_global :
    HomologicalComplex.extendMap
        (openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) ⊤)
        ComplexShape.embeddingUpNat ≫
      (HomologicalComplex.mapExtendCanonicalIso
        (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤)
        (singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
        ComplexShape.embeddingUpNat).inv = globalRawToSingularSheafInt X := by
  rw [openRawToSingularCochainSheafComplex_top]
  rfl

variable [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance complexSupportedOrdinaryComparisonAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance complexSupportedOrdinaryComparisonOpenParacompact :
    ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual positive singular supported-kernel class on the whole ambient
space agrees with the positive raw ambient relative inclusion. -/
theorem complexSupportedSingularTop_inclusion_of_relative
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) S n) :
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) S.compl ⊤
        (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).f (n : ℤ)
      ((supportedRationalSingularSectionCohomologyEquivRelative
        (TopCat.of (ComplexPoint X)) S.compl ⊤ n).symm
          (relativeCohomologyMap ℚ n
            (topOpenIntersectionPairIso (TopCat.of (ComplexPoint X)) S.compl).hom a)) =
    HomologicalComplex.homologyMap (globalRawToSingularSheafInt X) (n : ℤ)
      (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X)) S.compl n a) := by
  have h := supportedRationalSingularSectionCohomologyEquivRelative_inclusion
    (TopCat.of (ComplexPoint X)) S.compl ⊤ n
    (relativeCohomologyMap ℚ n
      (topOpenIntersectionPairIso (TopCat.of (ComplexPoint X)) S.compl).hom a)
  rwa [openRawRelativeCochainClass_top, complexOpenRawToSheafTop_eq_global] at h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original ambient supported-injective inverse comparison on the top open
is the actual supported singular-to-injective map of the prescribed relative class. -/
theorem complexSupportInjectiveSectionCohomologyEquiv_symm_top
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) S n) :
    (complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n).symm
      (relativeCohomologyMap ℚ n
        (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X)) S).hom a) =
    (complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ (n : ℤ)).hom
      ((supportedRationalSingularSectionCohomologyEquivRelative
        (TopCat.of (ComplexPoint X)) S.compl ⊤ n).symm
        (relativeCohomologyMap ℚ n
          (topOpenIntersectionPairIso (TopCat.of (ComplexPoint X)) S.compl).hom a)) := by
  let Y := TopCat.of (ComplexPoint X)
  let e := complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ (n : ℤ)
  apply (complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n).injective
  rw [AddEquiv.apply_symm_apply]
  change relativeCohomologyMap ℚ n (topOpenNeighborhoodSupportPairIso Y S).hom a =
    supportedRationalSingularSectionCohomologyEquivSupportComplement Y S S.isClosed ⊤ n
      (e.inv (e.hom _))
  rw [Iso.hom_inv_id_apply, supportedSingularSupportComplementEquiv_apply]
  erw [AddEquiv.apply_symm_apply]
  exact congrArg (fun f => f a)
    (relativeCohomologyMap_comp ℚ n
      (openIntersectionPairIsoSupportComplement Y S S.isClosed ⊤).inv
      (topOpenIntersectionPairIso Y S.compl).hom)

/-- The actual singular-to-injective supported comparison commutes with literal
kernel inclusion; it is induced by the genuine map of support short complexes. -/
theorem complexSupportedSingularInjectiveHomologyIso_inclusion
    (U V : Opens (ComplexPoint X)) (n : ℤ) :
    (complexSupportedSingularInjectiveHomologyIso X U V n).hom ≫
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X)) U V (ambientRationalInjectiveComplex X)).f n =
    HomologicalComplex.homologyMap
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X)) U V
          (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).f n ≫
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
          (.up ℤ)).map (complexSingularToAmbientInjective X)) n := by
  let Y := TopCat.of (ComplexPoint X)
  let f := (((TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)).mapShortComplex).map
    (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U (complexSingularToAmbientInjective X))
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n) f.comm₁₂
  rwa [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual supported-injective inverse-relative comparison followed by
positive kernel inclusion is the actual positive raw relative inclusion followed
by the prescribed sheafification and ambient injective comparison. -/
theorem complexSupportInjectiveSectionCohomologyEquiv_inclusion_positive
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) S n) :
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) S.compl ⊤ (ambientRationalInjectiveComplex X)).f (n : ℤ)
      ((complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n).symm
        (relativeCohomologyMap ℚ n
          (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X)) S).hom a)) =
    HomologicalComplex.homologyMap
      (globalRawToSingularSheafInt X ≫
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
          (complexSingularToAmbientInjective X)) (n : ℤ)
      (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X)) S.compl n a) := by
  rw [complexSupportInjectiveSectionCohomologyEquiv_symm_top]
  let b := (supportedRationalSingularSectionCohomologyEquivRelative
    (TopCat.of (ComplexPoint X)) S.compl ⊤ n).symm
      (relativeCohomologyMap ℚ n
        (topOpenIntersectionPairIso (TopCat.of (ComplexPoint X)) S.compl).hom a)
  have h := ConcreteCategory.congr_hom
    (complexSupportedSingularInjectiveHomologyIso_inclusion X S.compl ⊤ (n : ℤ)) b
  refine h.trans ?_
  have hp := congrArg
    (HomologicalComplex.homologyMap
      (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        (.up ℤ)).map (complexSingularToAmbientInjective X)) (n : ℤ))
    (complexSupportedSingularTop_inclusion_of_relative X S n a)
  refine hp.trans ?_
  rw [HomologicalComplex.homologyMap_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The definitive signed ordinary-target square: the newer actual positive
supported-kernel class is the NEGATIVE of the old support-singular comparison
followed by its cone-defined support-forgetting map. -/
theorem complexSupportInjectiveSectionCohomologyEquiv_inclusion_eq_neg_legacy
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) S n) :
    (rationalCohomologyAddEquivAmbientInjectiveHomology X (n : ℤ)).symm
      (HomologicalComplex.homologyMap
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X)) S.compl ⊤ (ambientRationalInjectiveComplex X)).f (n : ℤ)
        ((complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n).symm
          (relativeCohomologyMap ℚ n
            (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X)) S).hom a))) =
    -(forgetSupport X S (n : ℤ)
      ((rationalCohomologyWithSupportAddEquivSingular X S S.isClosed n).symm a)) := by
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology X (n : ℤ)).injective
  rw [AddEquiv.apply_symm_apply, map_neg,
    complexSupportInjectiveSectionCohomologyEquiv_inclusion_positive,
    rationalCohomologyAmbient_forgetSupport_of_singular_signed X S S.isClosed,
    neg_neg]
  rfl

end AlgebraicGeometry.ComplexPoint
