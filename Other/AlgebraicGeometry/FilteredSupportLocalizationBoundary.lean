/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.DerivedGlobalHypercohomologyComparison
public import Other.AlgebraicGeometry.FilteredDerivedSupport
public import Other.AlgebraicTopology.SupportedSectionConeConnecting

/-!
# Localization boundaries for filtered holomorphic de Rham cohomology

This file computes actual derived sections with closed support of a Hodge-filtered
de Rham complex using one fixed termwise-injective model.  It then packages the
connecting map from cohomology of the open complement as an honest morphism into
`SupportedFilteredDeRhamHypercohomology`.

Thus logarithmic classes on a punctured normal neighbourhood have the correct
supported target.  No purity or nonvanishing assertion is used in the construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance filteredSupportLocalizationSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance filteredSupportLocalizationGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- For a natural filtration index, the filtered de Rham complex is concentrated
in nonnegative degrees. -/
instance hodgeFilteredDeRhamComplex_isStrictlyGE_zero (p : ℕ) :
    (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE 0 := by
  letI : (hodgeFilteredDeRhamComplex X (p : ℤ)).IsStrictlyGE (p : ℤ) := by
    unfold hodgeFilteredDeRhamComplex
    infer_instance
  exact (hodgeFilteredDeRhamComplex X (p : ℤ)).isStrictlyGE_of_ge
    0 (p : ℤ) (by omega)

/-- The fixed termwise-injective model used for filtered localization. -/
abbrev filteredDeRhamInjectiveComplex (p : ℕ) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  globalHypercohomologyInjectiveComplex X
    (hodgeFilteredDeRhamComplex X (p : ℤ))

/-- The fixed filtered injective model bundled in the bounded-below homotopy
category. -/
abbrev filteredDeRhamInjectivePlus (p : ℕ) :
    CochainComplex.Plus (InjectiveObject (AnalyticAdditiveSheaf X)) :=
  globalHypercohomologyInjectivePlus X
    (hodgeFilteredDeRhamComplex X (p : ℤ))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual derived filtered support is computed by the supported-section kernel
of the fixed injective model. -/
def supportedFilteredDeRhamInjectiveModelIso
    (Z : Closeds (TopCat.of (ComplexPoint X))) (p : ℕ) :
    DerivedCategory.Plus.ι.obj
      ((TopCat.Sheaf.derivedClosedSupportSections
        (TopCat.of (ComplexPoint X)) Z).obj
        (hodgeFilteredDeRhamPlusObject X (p : ℤ))) ≅
    DerivedCategory.Q.obj
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) Z.compl ⊤
        (filteredDeRhamInjectiveComplex X p)).X₁ :=
  DerivedCategory.Plus.ι.mapIso
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).mapIso
      (globalHypercohomologyCoefficientInjectiveIso X
        (hodgeFilteredDeRhamComplex X (p : ℤ)))) ≪≫
    TopCat.Sheaf.derivedClosedSupportInjectiveModelIso
      (TopCat.of (ComplexPoint X)) Z (filteredDeRhamInjectivePlus X p)

/-- The categorical cohomology isomorphism from actual derived filtered support
to the termwise supported-section kernel of the fixed injective model. -/
def supportedFilteredDeRhamIsoInjectiveHomology
    (Z : Closeds (TopCat.of (ComplexPoint X))) (p : ℕ) (n : ℤ) :
    SupportedFilteredDeRhamHypercohomology X Z (p : ℤ) n ≅
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) Z.compl ⊤
        (filteredDeRhamInjectiveComplex X p)).X₁.homology n :=
  (DerivedCategory.homologyFunctor AddCommGrpCat n).mapIso
      (supportedFilteredDeRhamInjectiveModelIso X Z p) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app _

/-- The restriction of the fixed filtered injective model from the whole
analytic space to the complement of a closed set. -/
abbrev filteredDeRhamComplementRestriction
    (Z : Closeds (TopCat.of (ComplexPoint X))) (p : ℕ) :=
  TopCat.Sheaf.sectionComplexRestriction
    (TopCat.of (ComplexPoint X)) (.up ℤ)
    (filteredDeRhamInjectiveComplex X p)
    (Opens.infLELeft ⊤ Z.compl)

/-- The actual localization connecting morphism

`H^(n-1)(X \\ Z, F^p Ω^*) ⟶ H^n_Z(X, F^p Ω^*)`,

computed using the fixed injective resolution and the normalized positive
kernel-to-cone comparison. -/
def filteredDeRhamLocalizationBoundary
    (Z : Closeds (TopCat.of (ComplexPoint X))) (p : ℕ) (n : ℤ) :
    (((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) (⊤ ⊓ Z.compl)).mapHomologicalComplex (.up ℤ)).obj
        (filteredDeRhamInjectiveComplex X p)).homology (n - 1) ⟶
      SupportedFilteredDeRhamHypercohomology X Z (p : ℤ) n :=
  HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.triangle
        (filteredDeRhamComplementRestriction X Z p)).mor₂ (n - 1) ≫
    (TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone
      (TopCat.of (ComplexPoint X)) Z.compl ⊤
      (filteredDeRhamInjectiveComplex X p)
      (fun _ ↦ TopCat.Sheaf.injective_isFlasque _ _) n).inv ≫
    (supportedFilteredDeRhamIsoInjectiveHomology X Z p n).inv

end AlgebraicGeometry.ComplexPoint
