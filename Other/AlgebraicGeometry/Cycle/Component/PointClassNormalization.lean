/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

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

/-- The positive literal supported-kernel inclusion of the old point coclass, in
the repository's ordinary rational cohomology. No legacy cone-sign equality is claimed. -/
def analyticComponentPointPositiveKernelClass : H^(2 * d)(X; ℚ) :=
  (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * d)).symm
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
set_option maxHeartbeats 10000000 in
/-- The supported component class equals the normalized point class. -/
theorem cycleComponentSupportedInjectiveClass_point_normalization
    (hx : Order.coheight x = d) :
    cycleComponentSupportedInjectiveClass X x hx =
      (rationalSupportAddEquivSupportedInjectiveHomology X
        (cycleComponentAnalyticClosedSupport X x) (2 * d)).symm
        (analyticComponentPointSupportedInjectiveCoclass X x d z) := by
  let a : CycleComponentSupportedCohomology X x d :=
    (rationalSupportAddEquivSupportedInjectiveHomology X
      (cycleComponentAnalyticClosedSupport X x) (2 * d)).symm
      (analyticComponentPointSupportedInjectiveCoclass X x d z)
  symm
  apply cycleComponentSupportedInjectiveClass_unique X x hx a
  set_option maxHeartbeats 10000000 in
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
    let T := TopCat.of (ComplexPoint X)
    let Z := cycleComponentAnalyticClosedSupport X x
    let U := cycleComponentSmoothSupportAmbientOpen X x
    let hW : U ⊓ Z.compl = Z.compl := inf_eq_right.mpr
      (cycleComponentSupportComplement_le_smoothAmbientOpen X x)
    let f : Z.compl ⟶ U := homOfLE (by
      intro y hy hyS
      obtain ⟨w, _, hw⟩ := hyS
      apply hy
      change y.underlying ∈ closure ({x} : Set X.left)
      rw [← range_cycleComponentι X.left x]
      exact ⟨w, hw⟩)
    let g : U ⟶ ⊤ := homOfLE le_top
    let F := (TopCat.Sheaf.constantFunctor T).obj (AddCommGrpCat.of ℚ)
    let n : ℕ := 2 * d
    have hcycle (y : H_[Z]^n(X; ℚ)) :
        cycleComponentSupportExtensionIso X x hx y =
          CategoryTheory.Sheaf.relH.restrict F (homOfLE (show Z.compl ≤ ⊤ from le_top))
            f (homOfLE (show Z.compl ≤ Z.compl from le_rfl)) g
            (by apply Subsingleton.elim) n y := by
      rfl
    change cycleComponentSmoothSupportLowestSectionCohomologyEquiv X x hx
      (cycleComponentSupportExtensionIso X x hx a) = _
    have hcycle' : cycleComponentSupportExtensionIso X x hx a =
        CategoryTheory.Sheaf.relH.restrict F (homOfLE (show Z.compl ≤ ⊤ from le_top))
          (homOfLE (show Z.compl ≤ U from
            (cycleComponentSupportComplement_le_smoothAmbientOpen X x)))
          (homOfLE (show Z.compl ≤ Z.compl from le_rfl)) (homOfLE (show U ≤ ⊤ from le_top))
          (by apply Subsingleton.elim) n a := by
      rw [hcycle]
    rw [hcycle']
    dsimp [cycleComponentSmoothSupportLowestSectionCohomologyEquiv]
    let bridge :=
      @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology T Z.compl U Z.compl hW
        (analyticHasExt X) F (ambientRationalInjectiveComplex X)
        (ambientRationalInjectiveComplex_isKInjective X)
        (ambientRationalInjectiveSingleAugmentation X)
        (ambientRationalInjectiveSingleAugmentation_quasiIso X) n
    have hbridge :=
      @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology_restrict T Z.compl
        (⊤ : Opens T) Z.compl Z.compl U Z.compl (top_inf_eq _) hW le_rfl le_top le_rfl
        (analyticHasExt X) F (ambientRationalInjectiveComplex X)
        (ambientRationalInjectiveComplex_isKInjective X)
        (ambientRationalInjectiveSingleAugmentation X)
        (ambientRationalInjectiveSingleAugmentation_quasiIso X) n a
    let lowest :
        ((((TopCat.Sheaf.supportEvaluation T U).mapHomologicalComplex ℤᵘᵖ).obj
          (((TopCat.Sheaf.sheafSectionsSupportedOutside T Z.compl).mapHomologicalComplex ℤᵘᵖ).obj
            (ambientRationalInjectiveComplex X))).homology (n : ℤ)) ≅
          (TopCat.Sheaf.supportEvaluation T U).obj
            ((complexSupportInjectiveComplex X Z).homology (n : ℤ)) := by
      change _ ≅
        ((complexSupportInjectiveComplex X Z).homology (n : ℤ)).presheaf.obj (op U)
      exact cycleComponentSmoothSupportLowestSectionCohomologyComplexIso X x hx
    let sheaf := (TopCat.Sheaf.supportEvaluation T U).mapIso
      (complexSupportInjectiveCohomologySheafIsoRelative X Z n)
    have h := congrArg
      (fun z =>
        (lowest.addCommGroupIsoToAddEquiv.trans sheaf.addCommGroupIsoToAddEquiv) z)
      hbridge
    change
      sheaf.addCommGroupIsoToAddEquiv.toAddMonoidHom
          (lowest.addCommGroupIsoToAddEquiv.toAddMonoidHom
            (bridge ((CategoryTheory.Sheaf.relH.restrict F
              (homOfLE (show Z.compl ≤ ⊤ from le_top))
              (homOfLE (show Z.compl ≤ U from
                (cycleComponentSupportComplement_le_smoothAmbientOpen X x)))
              (homOfLE (show Z.compl ≤ Z.compl from le_rfl))
              (homOfLE (show U ≤ ⊤ from le_top))
              (by apply Subsingleton.elim) n) a))) = _
    convert h using 1 <;> simp only [AddEquiv.trans_apply]
    · rfl
    · have hsupport :
          TopCat.Sheaf.supportedSectionsRestriction T
              (show Z.compl ≤ Z.compl from le_rfl)
              (show U ≤ (⊤ : Opens T) from le_top)
              (ambientRationalInjectiveComplex X) =
            cycleComponentSupportSectionRestriction X x := by
        dsimp [TopCat.Sheaf.supportedSectionsRestriction,
          cycleComponentSupportSectionRestriction, complexSupportInjectiveComplex]
        rw [TopCat.Sheaf.sheafSectionsSupportedOutsideMap_refl]
        simp [T, Z]
      rw [hsupport]
      dsimp [lowest, sheaf, bridge,
        cycleComponentSupportSectionRestriction, cycleComponentSmoothRestrictedInjectiveComplex,
        complexSupportInjectiveComplex]
      simp [TopCat.Sheaf.supportEvaluation, T, Z, U, n]
      rfl
  rw [hnorm,
    cycleComponentSmoothSupportLowestSectionCohomologyComplexIso,
    TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso_hom]
  have ha :
      (rationalSupportAddEquivSupportedInjectiveHomology X
        (cycleComponentAnalyticClosedSupport X x) (2 * d)) a =
        analyticComponentPointSupportedInjectiveCoclass X x d z := by
    dsimp [a]
    exact AddEquiv.apply_symm_apply _ _
  rw [ha]
  exact analyticComponentPointSupportedInjectiveCoclass_section_normalization X x _ z hx

/-- Exact positive-kernel point normalization of the mapping-cone class. -/
theorem coneCycleComponentSheafClass_point_normalization
    (hx : Order.coheight x = d) :
    coneCycleComponentSheafClass X x hx =
      analyticComponentPointPositiveKernelClass X x d z := by
  rw [coneCycleComponentSheafClass_eq_injectiveModel,
    cycleComponentSupportedInjectiveClass_point_normalization X x d z hx]
  simp
  rfl

end Point

end AlgebraicGeometry.ComplexPoint
