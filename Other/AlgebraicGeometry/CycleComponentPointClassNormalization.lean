/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CycleComponentSheafClass
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

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth s] [IsProjective s] (x : X)
  {d p : ℕ} [SmoothOfRelativeDimension d s] (hx : Order.coheight x = p)

/-- Actual restriction followed by the cohomology-sheaf comparison is the
restriction of the literal relative sheafification unit. -/
theorem complexSupportInjectiveCohomologySheafIsoRelative_restriction_section
    (S : Closeds (ComplexPoint X s)) (n : ℕ)
    {V W : Opens (ComplexPoint X s)} (a : W ⟶ V) :
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X s)) (.up ℤ)
        (complexSupportInjectiveComplex s S) a) (n : ℤ) ≫
      TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X s))
        (complexSupportInjectiveComplex s S) (n : ℤ) W ≫
      (complexSupportInjectiveCohomologySheafIsoRelative s S n).hom.hom.app (op W) =
    (complexSupportInjectiveSectionCohomologyEquiv s S V n).toAddCommGrpIso.hom ≫
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X s)) S n).app (op V) ≫
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X s)) S n).obj.map a.op := by
  rw [TopCat.Sheaf.sectionCohomologyToSheafSection_restriction_assoc,
    (complexSupportInjectiveCohomologySheafIsoRelative s S n).hom.hom.naturality,
    complexSupportInjectiveCohomologySheafIsoRelative_section_assoc]

/-- The normalization isomorphism's forward map displays the actual restriction,
actual lowest-degree map, and actual cohomology-sheaf comparison. -/
theorem cycleComponentSupportedClassNormalizationIso_hom :
    (cycleComponentSupportedClassNormalizationIso s x (d := d) hx).hom =
      HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction s x)
        (2 * (p : ℤ)) ≫
      (cycleComponentSmoothSupportLowestSectionCohomologyIso s x (d := d) hx).hom ≫
      (complexSupportInjectiveCohomologySheafIsoRelative s
        (cycleComponentAnalyticClosedSupport s x) (2 * p)).hom.hom.app
          (op (cycleComponentSmoothSupportAmbientOpen s x)) := rfl

section Point

variable (d : ℕ) [SmoothOfRelativeDimension d s]
  (z : ComplexPoint (cycleComponent X x) (cycleComponentι X x ≫ s))

/-- The OLD point coclass on the literal whole-open/full-component pair.
The pair map simply forgets all removed support except the chosen point. -/
def analyticComponentPointRelativeCoclass :
    RelativeCohomology ℚ
      (neighborhoodSupportComplementPair
        ((⊤ : Opens (ComplexPoint X s)) : Set (ComplexPoint X s))
        (cycleComponentSupport s x)) (2 * d) :=
  relativeCohomologyMap ℚ (2 * d)
    (neighborhoodSupportToPointPairMap
      ((⊤ : Opens (ComplexPoint X s)) : Set (ComplexPoint X s))
      (cycleComponentSupport s x) (cycleComponentMap s x z)
      (range_cycleComponentMap_subset s x ⟨z, rfl⟩))
    (analyticPointLocalCoclass s d (cycleComponentMap s x z))

/-- The old point coclass transported through the ACTUAL relative/supported-injective
comparison; this is an explicit comparison target, not the definition of the general class. -/
def analyticComponentPointSupportedInjectiveCoclass :
    (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex s
        (cycleComponentAnalyticClosedSupport s x))).homology (2 * (d : ℤ)) :=
  (complexSupportInjectiveSectionCohomologyEquiv s
    (cycleComponentAnalyticClosedSupport s x) ⊤ (2 * d)).symm
      (analyticComponentPointRelativeCoclass s x d z)

/-- The positive literal supported-kernel inclusion of the old point coclass, in
the repository's ordinary rational cohomology. No legacy cone-sign equality is claimed. -/
def analyticComponentPointPositiveKernelClass : FieldCohomology ℚ s (2 * (d : ℤ)) :=
  (rationalCohomologyAddEquivAmbientInjectiveHomology s (2 * (d : ℤ))).symm
    (HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X s)) (cycleComponentAnalyticClosedSupport s x).compl ⊤
        (ambientRationalInjectiveComplex s)).f (2 * (d : ℤ))
      (analyticComponentPointSupportedInjectiveCoclass s x d z))

/-- The comparison target retains exactly the old normalized relative point coclass. -/
@[simp]
theorem analyticComponentPointSupportedInjectiveCoclass_relative :
    complexSupportInjectiveSectionCohomologyEquiv s
      (cycleComponentAnalyticClosedSupport s x) ⊤ (2 * d)
      (analyticComponentPointSupportedInjectiveCoclass s x d z) =
        analyticComponentPointRelativeCoclass s x d z :=
  AddEquiv.apply_symm_apply _ _

/-- Its literal sheafification image is the old point section on the whole ambient open. -/
theorem analyticComponentPointRelativeCoclass_toSheaf :
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X s))
      (cycleComponentSupport s x) (2 * d)).app (op ⊤)
        (analyticComponentPointRelativeCoclass s x d z) =
      analyticPointCoclassSupportSection s d (cycleComponentSupport s x)
        (cycleComponentMap s x z) (range_cycleComponentMap_subset s x ⟨z, rfl⟩) ⊤ := rfl

/-- The old point candidate has the EXACT general smooth-locus section as its
canonical sheaf normalization, using actual maps throughout. -/
theorem analyticComponentPointSupportedInjectiveCoclass_section_normalization
    (hx : Order.coheight x = d) :
    (complexSupportInjectiveCohomologySheafIsoRelative s
      (cycleComponentAnalyticClosedSupport s x) (2 * d)).hom.hom.app
        (op (cycleComponentSmoothSupportAmbientOpen s x))
      (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X s))
        (complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x))
        (2 * (d : ℤ)) (cycleComponentSmoothSupportAmbientOpen s x)
        (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction s x)
          (2 * (d : ℤ)) (analyticComponentPointSupportedInjectiveCoclass s x d z))) =
      cycleComponentSmoothSupportCoclassSection s x (d := d) hx := by
  have h := ConcreteCategory.congr_hom
    (complexSupportInjectiveCohomologySheafIsoRelative_restriction_section s
      (cycleComponentAnalyticClosedSupport s x) (2 * d)
      (homOfLE (show cycleComponentSmoothSupportAmbientOpen s x ≤ ⊤ from le_top)))
        (analyticComponentPointSupportedInjectiveCoclass s x d z)
  refine h.trans ?_
  change (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X s))
      (cycleComponentSupport s x) (2 * d)).obj.map (homOfLE le_top).op
    ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X s))
      (cycleComponentSupport s x) (2 * d)).app (op ⊤)
      (complexSupportInjectiveSectionCohomologyEquiv s
        (cycleComponentAnalyticClosedSupport s x) ⊤ (2 * d)
        (analyticComponentPointSupportedInjectiveCoclass s x d z))) = _
  rw [analyticComponentPointSupportedInjectiveCoclass_relative,
    analyticComponentPointRelativeCoclass_toSheaf]
  exact cycleComponentSmoothSupportCoclassSection_global_point_normalization s x hx z

/-- The ACTUAL general supported component class is the old normalized point
coclass transported through the actual relative/injective comparison. This is
a uniqueness theorem about the general construction, not a point branch. -/
theorem cycleComponentSupportedInjectiveClass_point_normalization
    (hx : Order.coheight x = d) :
    cycleComponentSupportedInjectiveClass s x (d := d) hx =
      analyticComponentPointSupportedInjectiveCoclass s x d z := by
  symm
  apply cycleComponentSupportedInjectiveClass_unique s x (d := d) hx
  rw [cycleComponentSupportedClassNormalizationIso_hom,
    cycleComponentSmoothSupportLowestSectionCohomologyIso,
    TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso_hom]
  exact analyticComponentPointSupportedInjectiveCoclass_section_normalization s x d z hx

/-- Exact positive-kernel point normalization of the general ordinary class.
The separate legacy ordinary comparison retains its independently checked cone sign. -/
theorem cycleComponentSheafClass_point_normalization
    (hx : Order.coheight x = d) :
    cycleComponentSheafClass s x (d := d) hx =
      analyticComponentPointPositiveKernelClass s x d z := by
  rw [cycleComponentSheafClass,
    cycleComponentSupportedInjectiveClass_point_normalization s x d z hx]
  rfl

end Point

/-- Exact integer multiplicity at every point component in the general cycle map. -/
theorem sheafCycleClassOnCycles_single_point_normalization
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : Order.coheight x = V.dimension)
    (z : ComplexPoint (cycleComponent V.scheme x) (cycleComponentι V.scheme x ≫ V.structureMap))
    (n : ℤ) :
    sheafCycleClassOnCycles V V.dimension (CodimensionCycle.single x hx n) =
      n • analyticComponentPointPositiveKernelClass V.structureMap x V.dimension z := by
  rw [sheafCycleClassOnCycles_single,
    cycleComponentSheafClass_point_normalization V.structureMap x V.dimension z hx]

/-- Every finite integral point cycle uses the same exact positive normalization,
including negative multiplicities and repeated points. -/
theorem sheafCycleClassOnCycles_sum_single_point_normalization
    (V : DimensionedSmoothProjectiveComplexVariety) {ι : Type*} (t : Finset ι)
    (x : ι → V.scheme) (hx : ∀ i, Order.coheight (x i) = V.dimension)
    (z : ∀ i, ComplexPoint (cycleComponent V.scheme (x i))
      (cycleComponentι V.scheme (x i) ≫ V.structureMap)) (n : ι → ℤ) :
    sheafCycleClassOnCycles V V.dimension
      (∑ i ∈ t, CodimensionCycle.single (x i) (hx i) (n i)) =
      ∑ i ∈ t, n i • analyticComponentPointPositiveKernelClass
        V.structureMap (x i) V.dimension (z i) := by
  rw [sheafCycleClassOnCycles_sum_single]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cycleComponentSheafClass_point_normalization V.structureMap (x i) V.dimension (z i) (hx i)]

/-- Exact rational point multiplicity after scalar extension of the general map. -/
theorem rationalSheafCycleClassOnCycles_tmul_single_point_normalization
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : Order.coheight x = V.dimension)
    (z : ComplexPoint (cycleComponent V.scheme x) (cycleComponentι V.scheme x ≫ V.structureMap))
    (q : ℚ) :
    rationalSheafCycleClassOnCycles V V.dimension (q ⊗ₜ[ℤ] CodimensionCycle.single x hx 1) =
      q • analyticComponentPointPositiveKernelClass V.structureMap x V.dimension z := by
  rw [rationalSheafCycleClassOnCycles_tmul_single,
    cycleComponentSheafClass_point_normalization V.structureMap x V.dimension z hx]

/-- The general rational map has the exact point normalization on arbitrary
finite rational combinations, with no normalization choice for each summand. -/
theorem rationalSheafCycleClassOnCycles_sum_tmul_single_point_normalization
    (V : DimensionedSmoothProjectiveComplexVariety) {ι : Type*} (t : Finset ι)
    (x : ι → V.scheme) (hx : ∀ i, Order.coheight (x i) = V.dimension)
    (z : ∀ i, ComplexPoint (cycleComponent V.scheme (x i))
      (cycleComponentι V.scheme (x i) ≫ V.structureMap)) (q : ι → ℚ) :
    rationalSheafCycleClassOnCycles V V.dimension
      (∑ i ∈ t, q i ⊗ₜ[ℤ] CodimensionCycle.single (x i) (hx i) 1) =
      ∑ i ∈ t, q i • analyticComponentPointPositiveKernelClass
        V.structureMap (x i) V.dimension (z i) := by
  rw [rationalSheafCycleClassOnCycles_sum_tmul_single]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cycleComponentSheafClass_point_normalization V.structureMap (x i) V.dimension (z i) (hx i)]

end AlgebraicGeometry.ComplexPoint
