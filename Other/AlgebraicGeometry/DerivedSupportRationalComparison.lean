/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.DerivedSupportRationalConeComparison
public import Other.AlgebraicGeometry.RationalCohomologyZero

/-!
# Actual derived supported sections and rational support hypercohomology

The comparison below starts with the actual right-derived supported-sections
functor on `D⁺`. The standard rational injective resolution is used through its
proved augmentation quasi-isomorphism and the derived unit, then through the
normalized cone comparison. No replacement functor or support comparison is
an input.

The underlying cone comparisons preserve the actual connecting morphisms,
with the standard cone triangle's negative projection corrected explicitly.
The support-forgetting square, including the actual derived-unit and ordinary
rational-cohomology comparison, is proved separately in
`DerivedSupportRationalForget`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

local instance derivedRationalComparisonSheafCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf structureMap) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf structureMap)

local instance derivedRationalComparisonGroupCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

/-- The ambient resolution as a bounded-below complex of genuinely injective
objects. Its boundedness is inherited from extension of a nonnegative
resolution, rather than supplied as a new assumption. -/
def ambientRationalInjectivePlus :
    CochainComplex.Plus (InjectiveObject (AnalyticAdditiveSheaf structureMap)) := by
  let I := HomologicalComplex.liftObjectProperty
    (Injective : AnalyticAdditiveSheaf structureMap → Prop)
    (ambientRationalInjectiveComplex structureMap) (fun _ => inferInstance)
  have hI : CochainComplex.IsStrictlyGE I 0 := by
    rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      I (InjectiveObject.ι (AnalyticAdditiveSheaf structureMap))]
    exact ambientRationalInjectiveComplex_isStrictlyGE structureMap
  exact ⟨I, 0, hI⟩

/-- The actual `D⁺` object of the standard ambient injective resolution. -/
def ambientRationalInjectiveDerivedPlus :
    DerivedCategory.Plus (AnalyticAdditiveSheaf structureMap) :=
  DerivedCategory.Plus.Qh.obj
    ((InjectiveObject.ι (AnalyticAdditiveSheaf structureMap)).mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.quotient _).obj (ambientRationalInjectivePlus structureMap)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmentation provides the canonical isomorphism from actual constant
rationals in `D⁺` to their standard injective model. -/
def constantRationalToInjectiveDerivedPlusIso :
    (DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf structureMap) 0).obj
      (constantFieldSheaf ℚ structureMap) ≅
        ambientRationalInjectiveDerivedPlus structureMap :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.singleFunctorIsoCompQ (AnalyticAdditiveSheaf structureMap) 0).app _ ≪≫
      DerivedCategory.Q.mapIso (constantRationalSheafComplexIntIsoSingleZero structureMap).symm ≪≫
      asIso (DerivedCategory.Q.map (ambientRationalInjectiveAugmentation structureMap)) ≪≫
      (DerivedCategory.quotientCompQhIso (AnalyticAdditiveSheaf structureMap)).symm.app _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual derived unit computes supported sections of rational constants
by the termwise kernel of restriction on the ambient injective resolution. -/
def derivedRationalSupportInjectiveModelIso
    (Z : Closeds (TopCat.of (ComplexPoint X structureMap))) :
    DerivedCategory.Plus.ι.obj
      ((TopCat.Sheaf.derivedClosedSupportSections
        (TopCat.of (ComplexPoint X structureMap)) Z).obj
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf structureMap) 0).obj
          (constantFieldSheaf ℚ structureMap))) ≅
    DerivedCategory.Q.obj
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X structureMap)) Z.compl ⊤
        (ambientRationalInjectiveComplex structureMap)).X₁ :=
  DerivedCategory.Plus.ι.mapIso
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X structureMap)) Z).mapIso
      (constantRationalToInjectiveDerivedPlusIso structureMap)) ≪≫
    TopCat.Sheaf.derivedClosedSupportInjectiveModelIso
      (TopCat.of (ComplexPoint X structureMap)) Z (ambientRationalInjectivePlus structureMap)

/-- The actual `D⁺` derived-support group agrees with the repository's rational
support hypercohomology. This is constructed from the constant augmentation,
derived unit, and normalized restriction-cone maps. -/
def derivedRationalSupportAddEquiv
    (Z : Closeds (TopCat.of (ComplexPoint X structureMap))) (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedClosedSupportSections
        (TopCat.of (ComplexPoint X structureMap)) Z).obj
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf structureMap) 0).obj
          (constantFieldSheaf ℚ structureMap)))) ≃+
      RationalCohomologyWithSupport structureMap Z n :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat n).mapIso
    (derivedRationalSupportInjectiveModelIso structureMap Z) ≪≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app _).addCommGroupIsoToAddEquiv).trans
    (rationalSupportAddEquivSupportedInjectiveHomology structureMap Z Z.isClosed n).symm

end AlgebraicGeometry.ComplexPoint
