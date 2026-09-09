/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SmoothClosedSupportCohomologySheaf
public import Other.AlgebraicTopology.SupportedSingularOrdinaryComparison
public import Other.AlgebraicTopology.TopOpenRelativeCochainNormalization
public import Other.Algebra.Homology.MapExtendBettiComparison
public import Other.AlgebraicGeometry.BettiSupportedOrdinarySign

/-! # Actual positive ordinary normalization of the ambient supported injective model -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicTopology.Singular

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))

/-- Top-open raw-to-sheaf normalization survives both actual grading comparisons. -/
theorem complexOpenRawToSheafTop_eq_global :
    HomologicalComplex.extendMap
        (openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X s)) ⊤)
        ComplexShape.embeddingUpNat ≫
      (HomologicalComplex.mapExtendCanonicalIso
        (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) ⊤)
        (singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X s)))
        ComplexShape.embeddingUpNat).inv = globalRawToSingularSheafInt s := by
  rw [openRawToSingularCochainSheafComplex_top,
    HomologicalComplex.mapExtendCanonicalIso_eq_bettiMapExtendIso]
  rfl

variable [IsIntegral X] [Smooth s] [IsProjective s]

local instance complexSupportedOrdinaryComparisonAnalyticTopology :
    TopologicalSpace (ComplexPoint X s) := Point.analyticTopology

local instance complexSupportedOrdinaryComparisonOpenParacompact :
    ∀ V : Opens (ComplexPoint X s), ParacompactSpace V := openParacompactSpace s

/-- The actual positive singular supported-kernel class on the whole ambient
space agrees with the positive raw ambient relative inclusion. -/
theorem complexSupportedSingularTop_inclusion_of_relative
    (S : Closeds (ComplexPoint X s)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X s)) S n) :
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X s)) S.compl ⊤
        (rationalSingularCochainComplex (TopCat.of (ComplexPoint X s)))).f (n : ℤ)
      ((supportedRationalSingularSectionCohomologyEquivRelative
        (TopCat.of (ComplexPoint X s)) S.compl ⊤ n).symm
          (relativeCohomologyMap ℚ n
            (topOpenIntersectionPairIso (TopCat.of (ComplexPoint X s)) S.compl).hom a)) =
    HomologicalComplex.homologyMap (globalRawToSingularSheafInt s) (n : ℤ)
      (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X s)) S.compl n a) := by
  have h := supportedRationalSingularSectionCohomologyEquivRelative_inclusion
    (TopCat.of (ComplexPoint X s)) S.compl ⊤ n
    (relativeCohomologyMap ℚ n
      (topOpenIntersectionPairIso (TopCat.of (ComplexPoint X s)) S.compl).hom a)
  rw [openRawRelativeCochainClass_top, complexOpenRawToSheafTop_eq_global] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- The original ambient supported-injective inverse comparison on the top open
is the actual supported singular-to-injective map of the prescribed relative class. -/
theorem complexSupportInjectiveSectionCohomologyEquiv_symm_top
    (S : Closeds (ComplexPoint X s)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X s)) S n) :
    (complexSupportInjectiveSectionCohomologyEquiv s S ⊤ n).symm
      (relativeCohomologyMap ℚ n
        (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X s)) S).hom a) =
    (complexSupportedSingularInjectiveHomologyIso s S.compl ⊤ (n : ℤ)).hom
      ((supportedRationalSingularSectionCohomologyEquivRelative
        (TopCat.of (ComplexPoint X s)) S.compl ⊤ n).symm
        (relativeCohomologyMap ℚ n
          (topOpenIntersectionPairIso (TopCat.of (ComplexPoint X s)) S.compl).hom a)) := by
  let Y := TopCat.of (ComplexPoint X s)
  let e := complexSupportedSingularInjectiveHomologyIso s S.compl ⊤ (n : ℤ)
  apply (complexSupportInjectiveSectionCohomologyEquiv s S ⊤ n).injective
  rw [AddEquiv.apply_symm_apply]
  change relativeCohomologyMap ℚ n (topOpenNeighborhoodSupportPairIso Y S).hom a =
    supportedRationalSingularSectionCohomologyEquivSupportComplement Y S S.isClosed ⊤ n
      (e.inv (e.hom _))
  rw [Iso.hom_inv_id_apply]
  rw [supportedSingularSupportComplementEquiv_apply]
  erw [AddEquiv.apply_symm_apply]
  exact congrArg (fun f => f a)
    (relativeCohomologyMap_comp ℚ n
      (openIntersectionPairIsoSupportComplement Y S S.isClosed ⊤).inv
      (topOpenIntersectionPairIso Y S.compl).hom)

/-- The actual singular-to-injective supported comparison commutes with literal
kernel inclusion; it is induced by the genuine map of support short complexes. -/
theorem complexSupportedSingularInjectiveHomologyIso_inclusion
    (U V : Opens (ComplexPoint X s)) (n : ℤ) :
    (complexSupportedSingularInjectiveHomologyIso s U V n).hom ≫
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X s)) U V (ambientRationalInjectiveComplex s)).f n =
    HomologicalComplex.homologyMap
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X s)) U V
          (rationalSingularCochainComplex (TopCat.of (ComplexPoint X s)))).f n ≫
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) V).mapHomologicalComplex
          (.up ℤ)).map (complexSingularToAmbientInjective s)) n := by
  let Y := TopCat.of (ComplexPoint X s)
  let f := (((TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex (.up ℤ)).mapShortComplex).map
    (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U (complexSingularToAmbientInjective s))
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n) f.comm₁₂
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  exact h

set_option maxHeartbeats 1200000 in
/-- The actual supported-injective inverse-relative comparison followed by
positive kernel inclusion is the actual positive raw relative inclusion followed
by the prescribed sheafification and ambient injective comparison. -/
theorem complexSupportInjectiveSectionCohomologyEquiv_inclusion_positive
    (S : Closeds (ComplexPoint X s)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X s)) S n) :
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X s)) S.compl ⊤ (ambientRationalInjectiveComplex s)).f (n : ℤ)
      ((complexSupportInjectiveSectionCohomologyEquiv s S ⊤ n).symm
        (relativeCohomologyMap ℚ n
          (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X s)) S).hom a)) =
    HomologicalComplex.homologyMap
      (globalRawToSingularSheafInt s ≫
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X s))).mapHomologicalComplex (.up ℤ)).map
          (complexSingularToAmbientInjective s)) (n : ℤ)
      (globalRawRelativeCochainClass ℚ (TopCat.of (ComplexPoint X s)) S.compl n a) := by
  rw [complexSupportInjectiveSectionCohomologyEquiv_symm_top]
  let b := (supportedRationalSingularSectionCohomologyEquivRelative
    (TopCat.of (ComplexPoint X s)) S.compl ⊤ n).symm
      (relativeCohomologyMap ℚ n
        (topOpenIntersectionPairIso (TopCat.of (ComplexPoint X s)) S.compl).hom a)
  have h := ConcreteCategory.congr_hom
    (complexSupportedSingularInjectiveHomologyIso_inclusion s S.compl ⊤ (n : ℤ)) b
  refine h.trans ?_
  have hp := congrArg
    (HomologicalComplex.homologyMap
      (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) ⊤).mapHomologicalComplex
        (.up ℤ)).map (complexSingularToAmbientInjective s)) (n : ℤ))
    (complexSupportedSingularTop_inclusion_of_relative s S n a)
  refine hp.trans ?_
  rw [HomologicalComplex.homologyMap_comp]
  rfl

set_option maxHeartbeats 1000000 in
/-- The definitive signed ordinary-target square: the newer actual positive
supported-kernel class is the NEGATIVE of the old support-singular comparison
followed by its cone-defined support-forgetting map. -/
theorem complexSupportInjectiveSectionCohomologyEquiv_inclusion_eq_neg_legacy
    (S : Closeds (ComplexPoint X s)) (n : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X s)) S n) :
    (rationalCohomologyAddEquivAmbientInjectiveHomology s (n : ℤ)).symm
      (HomologicalComplex.homologyMap
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X s)) S.compl ⊤ (ambientRationalInjectiveComplex s)).f (n : ℤ)
        ((complexSupportInjectiveSectionCohomologyEquiv s S ⊤ n).symm
          (relativeCohomologyMap ℚ n
            (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X s)) S).hom a))) =
    -(forgetSupport s S (n : ℤ)
      ((rationalCohomologyWithSupportAddEquivSingular s S S.isClosed n).symm a)) := by
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology s (n : ℤ)).injective
  rw [AddEquiv.apply_symm_apply, map_neg,
    complexSupportInjectiveSectionCohomologyEquiv_inclusion_positive,
    rationalCohomologyAmbient_forgetSupport_of_singular_signed s S S.isClosed,
    neg_neg]
  rfl

end AlgebraicGeometry.ComplexPoint
