/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleComponentSheafClass
public import Other.AlgebraicGeometry.CycleComponentPointCoclassSectionNormalization
public import Other.AlgebraicGeometry.ComplexSupportCohomologySheafNormalization
public import Other.AlgebraicGeometry.SheafCycleClass
public import Other.AlgebraicTopology.CohomologySheafSectionRestriction
public import Other.AlgebraicTopology.OpenRestrictedLowestCohomologyNormalization

/-!
# Positive-kernel point normalization of the actual general cycle class

The comparison target is the old exactly normalized point coclass transported
through the actual relative/supported-injective comparison and the literal
positive supported-kernel inclusion. It is NOT a point branch in the cycle map.
The separate comparison with the legacy ordinary class has its own cone sign.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p)

/-- Actual restriction followed by the cohomology-sheaf comparison is the
restriction of the literal relative sheafification unit. -/
theorem complexSupportInjectiveCohomologySheafIsoRelative_restriction_section
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    {V W : Opens (ComplexPoint X)} (a : W ⟶ V) :
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ)
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

/-- The normalization isomorphism's forward map displays the actual restriction,
actual lowest-degree map, and actual cohomology-sheaf comparison. -/
theorem cycleComponentSupportedClassNormalizationIso_hom :
    (cycleComponentSupportedClassNormalizationIso X x (d := d) hx).hom =
      HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x)
        (2 * (p : ℤ)) ≫
      (cycleComponentSmoothSupportLowestSectionCohomologyIso X x (d := d) hx).hom ≫
      (complexSupportInjectiveCohomologySheafIsoRelative X
        (cycleComponentAnalyticClosedSupport X x) (2 * p)).hom.hom.app
          (op (cycleComponentSmoothSupportAmbientOpen X x)) := rfl

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
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (2 * (d : ℤ)) :=
  (complexSupportInjectiveSectionCohomologyEquiv X
    (cycleComponentAnalyticClosedSupport X x) ⊤ (2 * d)).symm
      (analyticComponentPointRelativeCoclass X x d z)

/-- The positive literal supported-kernel inclusion of the old point coclass, in
the repository's ordinary rational cohomology. No legacy cone-sign equality is claimed. -/
def analyticComponentPointPositiveKernelClass : FieldCohomology ℚ X (2 * (d : ℤ)) :=
  (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (d : ℤ))).symm
    (HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl ⊤
        (ambientRationalInjectiveComplex X)).f (2 * (d : ℤ))
      (analyticComponentPointSupportedInjectiveCoclass X x d z))

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
      cycleComponentSmoothSupportCoclassSection X x (d := d) hx := by
  have h := ConcreteCategory.congr_hom
    (complexSupportInjectiveCohomologySheafIsoRelative_restriction_section X
      (cycleComponentAnalyticClosedSupport X x) (2 * d)
      (homOfLE (show cycleComponentSmoothSupportAmbientOpen X x ≤ ⊤ from le_top)))
        (analyticComponentPointSupportedInjectiveCoclass X x d z)
  refine h.trans ?_
  change (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * d)).obj.map (homOfLE le_top).op
    ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * d)).app (op ⊤)
      (complexSupportInjectiveSectionCohomologyEquiv X
        (cycleComponentAnalyticClosedSupport X x) ⊤ (2 * d)
        (analyticComponentPointSupportedInjectiveCoclass X x d z))) = _
  rw [analyticComponentPointSupportedInjectiveCoclass_relative,
    analyticComponentPointRelativeCoclass_toSheaf]
  exact cycleComponentSmoothSupportCoclassSection_global_point_normalization X x hx z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The ACTUAL general supported component class is the old normalized point
coclass transported through the actual relative/injective comparison. This is
a uniqueness theorem about the general construction, not a point branch. -/
theorem cycleComponentSupportedInjectiveClass_point_normalization
    (hx : Order.coheight x = d) :
    cycleComponentSupportedInjectiveClass X x (d := d) hx =
      analyticComponentPointSupportedInjectiveCoclass X x d z := by
  symm
  apply cycleComponentSupportedInjectiveClass_unique X x (d := d) hx
  rw [cycleComponentSupportedClassNormalizationIso_hom,
    cycleComponentSmoothSupportLowestSectionCohomologyIso,
    TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso_hom]
  exact analyticComponentPointSupportedInjectiveCoclass_section_normalization X x d z hx

/-- Exact positive-kernel point normalization of the general ordinary class.
The separate legacy ordinary comparison retains its independently checked cone sign. -/
theorem cycleComponentSheafClass_point_normalization
    (hx : Order.coheight x = d) :
    cycleComponentSheafClass X x (d := d) hx =
      analyticComponentPointPositiveKernelClass X x d z := by
  rw [cycleComponentSheafClass,
    cycleComponentSupportedInjectiveClass_point_normalization X x d z hx]
  rfl

end Point

/-- Exact integer multiplicity at every point component in the general cycle map. -/
theorem sheafCycleClassOnCycles_single_point_normalization
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : Order.coheight x = V.dimension)
    (z : ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap)))
    (n : ℤ) :
    sheafCycleClassOnCycles V V.dimension (codimensionCycleSubgroup.single x hx n) =
      n • analyticComponentPointPositiveKernelClass V.over x V.dimension z := by
  rw [sheafCycleClassOnCycles_single,
    cycleComponentSheafClass_point_normalization V.over x V.dimension z hx]

/-- Every finite integral point cycle uses the same exact positive normalization,
including negative multiplicities and repeated points. -/
theorem sheafCycleClassOnCycles_sum_single_point_normalization
    (V : DimensionedSmoothProjectiveComplexVariety) {ι : Type*} (t : Finset ι)
    (x : ι → V.scheme) (hx : ∀ i, Order.coheight (x i) = V.dimension)
    (z : ∀ i, ComplexPoint (Over.mk
      (cycleComponentι V.scheme (x i) ≫ V.structureMap))) (n : ι → ℤ) :
    sheafCycleClassOnCycles V V.dimension
      (∑ i ∈ t, codimensionCycleSubgroup.single (x i) (hx i) (n i)) =
      ∑ i ∈ t, n i • analyticComponentPointPositiveKernelClass
        V.over (x i) V.dimension (z i) := by
  rw [sheafCycleClassOnCycles_sum_single]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [cycleComponentSheafClass_point_normalization V.over (x i) V.dimension (z i) (hx i)]

/-- Exact rational point multiplicity after scalar extension of the general map. -/
theorem rationalSheafCycleClassOnCycles_tmul_single_point_normalization
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : Order.coheight x = V.dimension)
    (z : ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap)))
    (q : ℚ) :
    rationalSheafCycleClassOnCycles V V.dimension (q ⊗ₜ[ℤ] codimensionCycleSubgroup.single x hx 1) =
      q • analyticComponentPointPositiveKernelClass V.over x V.dimension z := by
  rw [rationalSheafCycleClassOnCycles_tmul_single,
    cycleComponentSheafClass_point_normalization V.over x V.dimension z hx]

/-- The general rational map has the exact point normalization on arbitrary
finite rational combinations, with no normalization choice for each summand. -/
theorem rationalSheafCycleClassOnCycles_sum_tmul_single_point_normalization
    (V : DimensionedSmoothProjectiveComplexVariety) {ι : Type*} (t : Finset ι)
    (x : ι → V.scheme) (hx : ∀ i, Order.coheight (x i) = V.dimension)
    (z : ∀ i, ComplexPoint (Over.mk
      (cycleComponentι V.scheme (x i) ≫ V.structureMap))) (q : ι → ℚ) :
    rationalSheafCycleClassOnCycles V V.dimension
      (∑ i ∈ t, q i ⊗ₜ[ℤ] codimensionCycleSubgroup.single (x i) (hx i) 1) =
      ∑ i ∈ t, q i • analyticComponentPointPositiveKernelClass
        V.over (x i) V.dimension (z i) := by
  rw [rationalSheafCycleClassOnCycles_sum_tmul_single]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [cycleComponentSheafClass_point_normalization V.over (x i) V.dimension (z i) (hx i)]

end AlgebraicGeometry.ComplexPoint
