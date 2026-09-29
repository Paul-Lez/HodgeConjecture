/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ActualSingularSupportBoundary
public import Other.AlgebraicTopology.SupportedSingularBoundaryRelative
public import Other.AlgebraicGeometry.Cohomology.SupportSheafNormalization

/-!
# Relative normalization of the fixed rational support boundary

The existing rational support comparison followed by the prescribed section-to-relative
comparison sends a positive raw complement boundary to its negative relative boundary.
This identifies the actual comparison, including its sign; no divisor formula is assumed.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (S : Closeds (ComplexPoint X))

local instance rationalSupportBoundaryRelativeOpenParacompact :
    ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

/-- The fixed injective-to-relative comparison cancels the actual supported
singular-to-injective map on every open. -/
lemma complexSupportInjectiveSectionCohomologyEquiv_supported_singular
    (V : Opens (ComplexPoint X)) (n : ℕ)
    (a : ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (.up ℤ)).obj (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) S.compl))).homology
        (n : ℤ)) :
    complexSupportInjectiveSectionCohomologyEquiv X S V n
      ((complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)).hom a) =
    supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint X)) S S.isClosed V n a := by
  let e := complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)
  change supportedRationalSingularSectionCohomologyEquivSupportComplement
    (TopCat.of (ComplexPoint X)) S S.isClosed V n (e.inv (e.hom a)) = _
  exact congrArg (supportedRationalSingularSectionCohomologyEquivSupportComplement
    (TopCat.of (ComplexPoint X)) S S.isClosed V n)
    (e.addCommGroupIsoToAddEquiv.symm_apply_apply a)

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- The literal global raw complement sheafification factors through the actual
top-open intersection map used in the local relative comparison. -/
lemma globalRawComplementToActualSingularOutside_eq_topOpen :
    globalRawComplementToActualSingularOutside X S S.isClosed =
    globalRawComplementToTopOpenCochains ℚ (TopCat.of (ComplexPoint X)) S.compl ≫
      openRawToSupportedSingularOutside (TopCat.of (ComplexPoint X)) S.compl ⊤ := rfl

/-- The fixed rational support comparison, followed by the existing relative
section comparison, sends a raw positive boundary to the negative raw relative
boundary on the literal top-open pair. -/
lemma coneSupportAddEquivSupportedInjectiveHomology_raw_boundary_relative (n : ℕ)
    (z : (globalRawPushforwardSingularCochainComplexInt ℚ
      (TopCat.of (ComplexPoint X)) ((S : Set (ComplexPoint X))ᶜ)).homology ((n : ℤ) - 1)) :
    complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n
      (coneSupportAddEquivSupportedInjectiveHomology X S S.isClosed n
        (hypercohomologyMap X
          (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X S)) ((n : ℤ) - 1)
          ((complementRationalHypercohomologyAddEquivGlobalSections X S ((n : ℤ) - 1)).symm
            (HomologicalComplex.homologyMap
              (globalRawComplementToDerivedPushforwardInt X S S.isClosed) ((n : ℤ) - 1) z)))) =
    -(relativeCohomologyMap ℚ n
      (openIntersectionPairIsoSupportComplement (TopCat.of (ComplexPoint X)) S S.isClosed ⊤).inv
      (openRawSingularRestrictionConeCohomologyEquivRelative ℚ (TopCat.of (ComplexPoint X))
        (Opens.infLELeft ⊤ S.compl) n
        (HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr
            (HomologicalComplex.extendMap
              (openRawSingularRestriction ℚ (TopCat.of (ComplexPoint X)) (Opens.infLELeft ⊤ S.compl))
              ComplexShape.embeddingUpNat)) ((n : ℤ) - 1)
          (HomologicalComplex.homologyMap
            (globalRawComplementToTopOpenCochains ℚ (TopCat.of (ComplexPoint X)) S.compl)
            ((n : ℤ) - 1) z)))) := by
  let Y := TopCat.of (ComplexPoint X)
  let z' := HomologicalComplex.homologyMap
    (globalRawComplementToTopOpenCochains ℚ Y S.compl) ((n : ℤ) - 1) z
  let k := CochainComplex.mappingCone.inr
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y S.compl ⊤
      (rationalSingularCochainComplex Y)).g
  let a := (actualSingularSupportHomologyIsoCone X S S.isClosed (n : ℤ)).inv
    (HomologicalComplex.homologyMap k ((n : ℤ) - 1)
      (HomologicalComplex.homologyMap
        (globalRawComplementToActualSingularOutside X S S.isClosed) ((n : ℤ) - 1) z))
  let e := complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n
  let eS := supportedRationalSingularSectionCohomologyEquivSupportComplement Y S S.isClosed ⊤ n
  let eI := complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ (n : ℤ)
  have hb := congrArg e
    (coneSupportAddEquivSupportedInjectiveHomology_raw_boundary X S S.isClosed (n : ℤ) z)
  have hm : e (-eI.hom a) = -eS a :=
    (e.map_neg (eI.hom a)).trans
      (congrArg Neg.neg
        (complexSupportInjectiveSectionCohomologyEquiv_supported_singular X S ⊤ n a))
  refine hb.trans (hm.trans (congrArg Neg.neg ?_))
  have hr : HomologicalComplex.homologyMap
      (globalRawComplementToActualSingularOutside X S S.isClosed) ((n : ℤ) - 1) z =
    HomologicalComplex.homologyMap (openRawToSupportedSingularOutside Y S.compl ⊤)
      ((n : ℤ) - 1) z' := by
    rw [globalRawComplementToActualSingularOutside_eq_topOpen, HomologicalComplex.homologyMap_comp]
    rfl
  have ha := congrArg (fun b =>
    (actualSingularSupportHomologyIsoCone X S S.isClosed (n : ℤ)).inv
      (HomologicalComplex.homologyMap k ((n : ℤ) - 1) b)) hr
  exact (congrArg eS ha).trans
    (congrArg (relativeCohomologyMap ℚ n
      (openIntersectionPairIsoSupportComplement Y S S.isClosed ⊤).inv)
      (supportedSingularSectionCohomologyEquivRelative_boundary Y S.compl ⊤ n z'))

end AlgebraicGeometry.ComplexPoint
