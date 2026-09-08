/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentSheafClass
public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentPointCoclassSectionNormalization
public import HodgeConjecture.Other.AlgebraicGeometry.ComplexSupportCohomologySheafNormalization
public import HodgeConjecture.Other.AlgebraicGeometry.SheafCycleClass
public import HodgeConjecture.Other.AlgebraicTopology.CohomologySheafSectionRestriction

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

end Point
end AlgebraicGeometry.ComplexPoint
