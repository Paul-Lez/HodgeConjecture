/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticOpenDerivedSectionsComparison
public import Other.AlgebraicGeometry.DerivedGlobalHypercohomologyComparison
public import Other.AlgebraicTopology.SupportedSectionConeConnecting

/-!
# Localization boundary for a bounded-below analytic sheaf complex

For a nonnegative analytic sheaf complex `K`, this file computes actual derived
sections with closed support by the kernel of restriction on the repository's
fixed injective replacement.  The mapping-cone connecting map then gives an
actual boundary from complement cohomology into derived supported cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ)))
  (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsStrictlyGE 0]

local instance analyticDerivedSupportLocalizationSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance analyticDerivedSupportLocalizationGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- Actual derived closed-support cohomology of `K`. -/
def AnalyticDerivedSupportCohomology
    (Z : Closeds (TopCat.of (ComplexPoint X))) (n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).obj
      (TopCat.Sheaf.supportCoefficientPlus
        (TopCat.of (ComplexPoint X)) K 0))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual derived-support object is computed by the supported-section
kernel of the fixed injective replacement. -/
def analyticDerivedSupportInjectiveModelIso
    (Z : Closeds (TopCat.of (ComplexPoint X))) :
    DerivedCategory.Plus.ι.obj
      ((TopCat.Sheaf.derivedClosedSupportSections
        (TopCat.of (ComplexPoint X)) Z).obj
        (TopCat.Sheaf.supportCoefficientPlus
          (TopCat.of (ComplexPoint X)) K 0)) ≅
    DerivedCategory.Q.obj
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) Z.compl ⊤
        (globalHypercohomologyInjectiveComplex X K)).X₁ :=
  DerivedCategory.Plus.ι.mapIso
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).mapIso
      (globalHypercohomologyCoefficientInjectiveIso X K)) ≪≫
    TopCat.Sheaf.derivedClosedSupportInjectiveModelIso
      (TopCat.of (ComplexPoint X)) Z
      (globalHypercohomologyInjectivePlus X K)

/-- Cohomology-level version of the fixed injective support model. -/
def analyticDerivedSupportIsoInjectiveHomology
    (Z : Closeds (TopCat.of (ComplexPoint X))) (n : ℤ) :
    AnalyticDerivedSupportCohomology X K Z n ≅
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) Z.compl ⊤
        (globalHypercohomologyInjectiveComplex X K)).X₁.homology n :=
  (DerivedCategory.homologyFunctor AddCommGrpCat n).mapIso
      (analyticDerivedSupportInjectiveModelIso X K Z) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app _

/-- Actual restriction of the fixed injective model from the whole space to
its intersection with the open complement. -/
abbrev analyticDerivedComplementRestriction
    (Z : Closeds (TopCat.of (ComplexPoint X))) :=
  TopCat.Sheaf.sectionComplexRestriction
    (TopCat.of (ComplexPoint X)) (.up ℤ)
    (globalHypercohomologyInjectiveComplex X K)
    (Opens.infLELeft ⊤ Z.compl)

/-- The normalized localization boundary

`H^(n-1)(X \\ Z, I(K)) ⟶ H^n_Z(X,K)`

with the complement represented as `⊤ ⊓ Z.compl` by the literal restriction
sequence. -/
def analyticDerivedSupportLocalizationBoundary
    (Z : Closeds (TopCat.of (ComplexPoint X))) (n : ℤ) :
    (((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) (⊤ ⊓ Z.compl)).mapHomologicalComplex (.up ℤ)).obj
        (globalHypercohomologyInjectiveComplex X K)).homology (n - 1) ⟶
      AnalyticDerivedSupportCohomology X K Z n :=
  HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.triangle
        (analyticDerivedComplementRestriction X K Z)).mor₂ (n - 1) ≫
    (TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone
      (TopCat.of (ComplexPoint X)) Z.compl ⊤
      (globalHypercohomologyInjectiveComplex X K)
      (fun _ ↦ TopCat.Sheaf.injective_isFlasque _ _) n).inv ≫
    (analyticDerivedSupportIsoInjectiveHomology X K Z n).inv

end AlgebraicGeometry.ComplexPoint
