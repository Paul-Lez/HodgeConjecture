/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.FundamentalClass
public import Other.AlgebraicGeometry.Cycle.Component.PointCoclassNormalization
public import Other.AlgebraicGeometry.Cohomology.SupportSheafNormalization
public import Other.AlgebraicGeometry.Cycle.SheafClass
public import Other.AlgebraicTopology.Sheaf.CohomologySectionRestriction
public import Other.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology
public import Other.AlgebraicGeometry.Cohomology.SupportConeForget
public import Other.AlgebraicGeometry.Cycle.FundamentalClass
public import Other.AlgebraicGeometry.Cycle.Support

/-!
# Positive-kernel point normalization of the actual general cycle class

The comparison target is the old exactly normalized point coclass transported
through the actual relative/supported-injective comparison and the literal
positive supported-kernel inclusion. It is NOT a point branch in the cycle map.
The separate comparison with the legacy ordinary class has its own cone sign.
-/

@[expose] public noncomputable section

set_option maxRecDepth 4000

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

/-- Actual restriction followed by the cohomology-sheaf comparison is the
restriction of the literal relative sheafification unit. -/
theorem complexSupportInjectiveCohomologySheafIsoRelative_restriction_section
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    {V W : Opens (ComplexPoint X)} (a : W ⟶ V) :
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
        (complexSupportInjectiveComplex X S) a) (n : ℤ) ≫
      TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X S) (n : ℤ) W ≫
      (complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.app (op W) =
    (complexSupportInjectiveSectionCohomologyEquiv X S V n).toAddCommGrpIso.hom ≫
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) S n).app (op V) ≫
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) S n).obj.map a.op := by
  rw [TopCat.Sheaf.sectionCohomologyToSheafSection_restriction_assoc,
    (complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.naturality,
    complexSupportInjectiveCohomologySheafIsoRelative_section_assoc]

section Point

variable (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)))

/-- The OLD point coclass on the literal whole-open/full-component pair.
The pair map simply forgets all removed support except the chosen point. -/
def analyticComponentPointRelativeCoclass :
    RelativeCohomology ℚ
      (neighborhoodSupportComplementPair
        ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
        (cycleComponentSupport X x)) (2 * d) :=
  relativeCohomologyMap ℚ (2 * d)
    (neighborhoodSupportToPointPairMap
      ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
      (cycleComponentSupport X x) (cycleComponentMap X x z)
      (range_cycleComponentMap_subset X x ⟨z, rfl⟩))
    (analyticPointLocalCoclass X d (cycleComponentMap X x z))

/-- The old point coclass transported through the ACTUAL relative/supported-injective
comparison; this is an explicit comparison target, not the definition of the general class. -/
def analyticComponentPointSupportedInjectiveCoclass :
    (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (2 * (d : ℤ)) :=
  (complexSupportInjectiveSectionCohomologyEquiv X
    (cycleComponentAnalyticClosedSupport X x) ⊤ (2 * d)).symm
      (analyticComponentPointRelativeCoclass X x d z)

/-- The point coclass included into ordinary rational cohomology through the independent
    ambient-injective support-forgetting model. -/
def analyticComponentPointPositiveKernelClass : H^(2 * (d : ℤ))(X; ℚ) :=
  (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (d : ℤ))).symm
    (HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl ⊤
        (ambientRationalInjectiveComplex X)).f (2 * (d : ℤ))
      (analyticComponentPointSupportedInjectiveCoclass X x d z))

private lemma forgetSupportToGlobalSectionsHomology_supportedInjective
    (Z : Closeds (ComplexPoint X)) (n : ℕ)
    (c : (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X Z)).homology n) :
    forgetSupportToGlobalSectionsHomology ℚ X Z n
        ((rationalSupportAddEquivSupportedInjectiveHomology X Z n).symm c) =
      HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) Z.compl ⊤ (ambientRationalInjectiveComplex X)).f n c := by
  change HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) Z.compl ⊤ (ambientRationalInjectiveComplex X)).f n
      ((rationalSupportAddEquivSupportedInjectiveHomology X Z n)
        ((rationalSupportAddEquivSupportedInjectiveHomology X Z n).symm c)) = _
  rw [AddEquiv.apply_symm_apply]

private lemma constantFieldInjectiveResolutionAugmentation_eq_ambient
    (X : Over (Spec ↧ℂ)) :
    (constantFieldSheafComplexIntIsoSingle ℚ X).hom ≫
        TopCat.Sheaf.injectiveResolutionAugmentation (TopCat.of (ComplexPoint X))
          ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) =
      ambientRationalInjectiveAugmentation X := by
  letI e := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    𝓒(↧(ComplexPoint X); ℚ) 0 0 (by simp)
  change e.hom ≫ e.inv ≫
      HomologicalComplex.extendMap
        (TopCat.Sheaf.ambientConstantInjectiveResolution
          (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ)).ι
        ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      (TopCat.Sheaf.ambientConstantInjectiveResolution
        (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ)).ι
      ComplexShape.embeddingUpNat
  simp

/-- The comparison target retains exactly the old normalized relative point coclass. -/
@[simp]
theorem analyticComponentPointSupportedInjectiveCoclass_relative :
    complexSupportInjectiveSectionCohomologyEquiv X
      (cycleComponentAnalyticClosedSupport X x) ⊤ (2 * d)
      (analyticComponentPointSupportedInjectiveCoclass X x d z) =
        analyticComponentPointRelativeCoclass X x d z :=
  AddEquiv.apply_symm_apply _ _

/-- Its literal sheafification image is the old point section on the whole ambient open. -/
theorem analyticComponentPointRelativeCoclass_toSheaf :
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * d)).app (op ⊤)
        (analyticComponentPointRelativeCoclass X x d z) =
      analyticPointCoclassSupportSection X d (cycleComponentSupport X x)
        (cycleComponentMap X x z) (range_cycleComponentMap_subset X x ⟨z, rfl⟩) ⊤ := rfl

/-- The old point candidate has the EXACT general smooth-locus section as its
canonical sheaf normalization, using actual maps throughout. -/
theorem analyticComponentPointSupportedInjectiveCoclass_section_normalization
    (hx : Order.coheight x = d) :
    (complexSupportInjectiveCohomologySheafIsoRelative X
      (cycleComponentAnalyticClosedSupport X x) (2 * d)).hom.hom.app
        (op (cycleComponentSmoothSupportAmbientOpen X x))
      (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
        (2 * (d : ℤ)) (cycleComponentSmoothSupportAmbientOpen X x)
        (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x)
          (2 * (d : ℤ)) (analyticComponentPointSupportedInjectiveCoclass X x d z))) =
      cycleComponentSmoothSupportCoclassSection X x hx := by
  obtain rfl : dim X.left = d := SmoothOfRelativeDimension.dim_eq X.hom d
  have h := ConcreteCategory.congr_hom
    (complexSupportInjectiveCohomologySheafIsoRelative_restriction_section X
      (cycleComponentAnalyticClosedSupport X x) (2 * dim X.left)
      (homOfLE (show cycleComponentSmoothSupportAmbientOpen X x ≤ ⊤ from le_top)))
        (analyticComponentPointSupportedInjectiveCoclass X x (dim X.left) z)
  refine h.trans ?_
  change (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * dim X.left)).obj.map (homOfLE le_top).op
    ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * dim X.left)).app (op ⊤)
      (complexSupportInjectiveSectionCohomologyEquiv X
        (cycleComponentAnalyticClosedSupport X x) ⊤ (2 * dim X.left)
        (analyticComponentPointSupportedInjectiveCoclass X x (dim X.left) z))) = _
  rw [analyticComponentPointSupportedInjectiveCoclass_relative,
    analyticComponentPointRelativeCoclass_toSheaf]
  exact cycleComponentSmoothSupportCoclassSection_global_point_normalization X x hx z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem cycleComponentSupportedInjectiveClass_point_normalization_aux
    (hx : Order.coheight x = d) (a : CycleComponentSupportedCohomology X x d)
    (ha : (rationalSupportAddEquivSupportedInjectiveHomology X
      (cycleComponentAnalyticClosedSupport X x) (2 * d)) a =
        analyticComponentPointSupportedInjectiveCoclass X x d z) :
    (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom a =
      cycleComponentSmoothSupportCoclassSection X x hx := by
  have hnorm :
      (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom a =
        (complexSupportInjectiveCohomologySheafIsoRelative X
          (cycleComponentAnalyticClosedSupport X x) (2 * d)).hom.hom.app
            (op (cycleComponentSmoothSupportAmbientOpen X x))
          ((cycleComponentSmoothSupportLowestSectionCohomologyComplexIso X x hx).hom
            (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x)
              (2 * (d : ℤ))
              ((rationalSupportAddEquivSupportedInjectiveHomology X
                (cycleComponentAnalyticClosedSupport X x) (2 * d)) a))) := by
    exact cycleComponentSupportedClassNormalizationIso_apply X x hx a
  rw [hnorm,
    cycleComponentSmoothSupportLowestSectionCohomologyComplexIso,
    TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso_hom,
    ha]
  exact analyticComponentPointSupportedInjectiveCoclass_section_normalization X x d z hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The supported component class equals the normalized point class. -/
theorem cycleComponentSupportedInjectiveClass_point_normalization
    (hx : Order.coheight x = d) :
    cycleComponentSupportedInjectiveClass X x hx =
      (rationalSupportAddEquivSupportedInjectiveHomology X
        (cycleComponentAnalyticClosedSupport X x) (2 * d)).symm
        (analyticComponentPointSupportedInjectiveCoclass X x d z) := by
  letI a : CycleComponentSupportedCohomology X x d :=
    (rationalSupportAddEquivSupportedInjectiveHomology X
      (cycleComponentAnalyticClosedSupport X x) (2 * d)).symm
      (analyticComponentPointSupportedInjectiveCoclass X x d z)
  symm
  apply cycleComponentSupportedInjectiveClass_unique X x hx a
  have ha :
      (rationalSupportAddEquivSupportedInjectiveHomology X
        (cycleComponentAnalyticClosedSupport X x) (2 * d)) a =
        analyticComponentPointSupportedInjectiveCoclass X x d z := by
    dsimp [a]
    exact AddEquiv.apply_symm_apply _ _
  exact cycleComponentSupportedInjectiveClass_point_normalization_aux X x d z hx a ha

/-- The cycle-component class of a point has the positive-kernel normalization. -/
theorem cycleComponentSheafClass_point_normalization
    (hx : Order.coheight x = d) :
    cycleComponentSheafClass X x hx =
      analyticComponentPointPositiveKernelClass X x d z := by
  rw [cycleComponentSheafClass_eq_forgetSupport,
    cycleComponentSupportedInjectiveClass_point_normalization X x d z hx]
  dsimp [forgetSupport]
  rw [forgetSupportToGlobalSectionsHomology_supportedInjective]
  dsimp [forgetSupport, rationalCohomologyAddEquivAmbientInjectiveHomology,
    analyticComponentPointPositiveKernelClass]
  simp [constantFieldInjectiveResolutionAugmentation_eq_ambient,
    ambientRationalInjectiveAugmentationPlus]
  rfl

end Point

variable (V : SmoothProjectiveComplexVariety) (d : ℕ)
  [SmoothOfRelativeDimension d V.structureMap]

/-- The sheaf cycle class of a point component records its integer multiplicity. -/
theorem sheafCycleClassOnCycles_single_point_normalization
    (x : V.scheme) (hx : Order.coheight x = d)
    (z : ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap)))
    (n : ℤ) :
    sheafCycleClassOnCycles V d (codimensionCycleSubgroup.single x hx n) =
      n • analyticComponentPointPositiveKernelClass V.over x d z := by
  rw [sheafCycleClassOnCycles_single,
    cycleComponentSheafClass_point_normalization V.over x d z hx]

/-- The sheaf cycle class records multiplicities in a finite integral point cycle. -/
theorem sheafCycleClassOnCycles_sum_single_point_normalization
    {ι : Type*} (t : Finset ι)
    (x : ι → V.scheme) (hx : ∀ i, Order.coheight (x i) = d)
    (z : ∀ i, ComplexPoint (Over.mk
      (cycleComponentι V.scheme (x i) ≫ V.structureMap))) (n : ι → ℤ) :
    sheafCycleClassOnCycles V d
      (∑ i ∈ t, codimensionCycleSubgroup.single (x i) (hx i) (n i)) =
      ∑ i ∈ t, n i • analyticComponentPointPositiveKernelClass
        V.over (x i) d (z i) := by
  rw [sheafCycleClassOnCycles_sum_single]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [cycleComponentSheafClass_point_normalization V.over (x i) d (z i) (hx i)]

/-- The rational sheaf cycle class of a point component records its rational multiplicity. -/
theorem rationalSheafCycleClassOnCycles_tmul_single_point_normalization
    (x : V.scheme) (hx : Order.coheight x = d)
    (z : ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap)))
    (q : ℚ) :
    rationalSheafCycleClassOnCycles V d (q ⊗ₜ[ℤ] codimensionCycleSubgroup.single x hx 1) =
      q • analyticComponentPointPositiveKernelClass V.over x d z := by
  rw [rationalSheafCycleClassOnCycles_tmul_single,
    cycleComponentSheafClass_point_normalization V.over x d z hx]

/-- The rational sheaf cycle class records multiplicities in a finite rational point cycle. -/
theorem rationalSheafCycleClassOnCycles_sum_tmul_single_point_normalization
    {ι : Type*} (t : Finset ι)
    (x : ι → V.scheme) (hx : ∀ i, Order.coheight (x i) = d)
    (z : ∀ i, ComplexPoint (Over.mk
      (cycleComponentι V.scheme (x i) ≫ V.structureMap))) (q : ι → ℚ) :
    rationalSheafCycleClassOnCycles V d
      (∑ i ∈ t, q i ⊗ₜ[ℤ] codimensionCycleSubgroup.single (x i) (hx i) 1) =
      ∑ i ∈ t, q i • analyticComponentPointPositiveKernelClass
        V.over (x i) d (z i) := by
  rw [rationalSheafCycleClassOnCycles_sum_tmul_single]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [cycleComponentSheafClass_point_normalization V.over (x i) d (z i) (hx i)]

end AlgebraicGeometry.ComplexPoint
