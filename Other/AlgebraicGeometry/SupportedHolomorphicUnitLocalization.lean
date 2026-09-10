/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticDerivedSupportLocalizationBoundary
public import Other.AlgebraicGeometry.SupportedExponentialClass

/-!
# Localization of a holomorphic unit

A holomorphic unit on an open `U` is a degree-one cocycle for the units
complex. After the fixed injective augmentation, the actual localization
boundary for `U.compl` gives a class in supported degree two. The supported
exponential comparison supplies its explicit first-filtered lift and its
normalized integral-period class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance supportedHolomorphicUnitSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance supportedHolomorphicUnitGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

local instance holomorphicUnitsComplexInt_isStrictlyGE_zero :
    (holomorphicUnitsComplexInt X).IsStrictlyGE 0 :=
  (holomorphicUnitsComplexInt X).isStrictlyGE_of_ge 0 1 (by omega)

/-- Changing the displayed lower bound from one to zero does not change the
underlying derived object of the units complex. -/
def holomorphicUnitsCoefficientPlusZeroIso :
    TopCat.Sheaf.supportCoefficientPlus (TopCat.of (ComplexPoint X))
        (holomorphicUnitsComplexInt X) 0 ≅
      holomorphicUnitsPlusObject X :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- The generic derived-support presentation agrees with the public supported
units hypercohomology group. -/
def analyticDerivedSupportCohomologyIsoSupportedHolomorphicUnits
    (Z : Closeds (TopCat.of (ComplexPoint X))) (n : ℤ) :
    AnalyticDerivedSupportCohomology X (holomorphicUnitsComplexInt X) Z n ≅
      SupportedHolomorphicUnitsHypercohomology X Z n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).mapIso
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).mapIso
        (holomorphicUnitsCoefficientPlusZeroIso X))

/-- The map represented by a unit section, followed by the fixed injective
augmentation of the degree-one units complex. -/
def holomorphicUnitSectionToInjectiveDegreeOne
    (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitsSheaf X (dim X.left)).obj.obj (.op U)) :
    analyticOpenFreeAbelianSheaf X U ⟶
      (globalHypercohomologyInjectiveComplex X
        (holomorphicUnitsComplexInt X)).X 1 :=
  analyticSectionSheafHom X (holomorphicUnitsSheaf X (dim X.left)) U u ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 1
      (holomorphicUnitsSheaf X (dim X.left))).inv ≫
    (globalHypercohomologyInjectiveMap X
      (holomorphicUnitsComplexInt X)).f 1

/-- The preceding degree-one morphism is closed. -/
theorem holomorphicUnitSectionToInjectiveDegreeOne_closed
    (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitsSheaf X (dim X.left)).obj.obj (.op U)) :
    holomorphicUnitSectionToInjectiveDegreeOne X U u ≫
      (globalHypercohomologyInjectiveComplex X
        (holomorphicUnitsComplexInt X)).d 1 2 = 0 := by
  have h := (globalHypercohomologyInjectiveMap X
    (holomorphicUnitsComplexInt X)).comm 1 2
  unfold holomorphicUnitSectionToInjectiveDegreeOne
  unfold holomorphicUnitsComplexInt at h ⊢
  simp only [Category.assoc]
  rw [h]
  simp

/-- The degree-one open cohomology class represented by a holomorphic unit. -/
def holomorphicUnitOpenCohomologyClass
    (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitsSheaf X (dim X.left)).obj.obj (.op U)) :
    (((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj
      (globalHypercohomologyInjectiveComplex X
        (holomorphicUnitsComplexInt X))).homology 1 :=
  openCohomologyClassOfClosedMap X U
    (globalHypercohomologyInjectiveComplex X
      (holomorphicUnitsComplexInt X)) 1
    (holomorphicUnitSectionToInjectiveDegreeOne X U u)
    (holomorphicUnitSectionToInjectiveDegreeOne_closed X U u)

/-- Localization of a unit on `U` gives an actual supported-units class for
the closed complement `U.compl`. -/
def holomorphicUnitSupportedLocalizationClass
    (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitsSheaf X (dim X.left)).obj.obj (.op U)) :
    SupportedHolomorphicUnitsHypercohomology X U.compl 2 := by
  let a := holomorphicUnitOpenCohomologyClass X U u
  exact (analyticDerivedSupportCohomologyIsoSupportedHolomorphicUnits
    X U.compl 2).hom
      (analyticDerivedSupportLocalizationBoundary X
        (holomorphicUnitsComplexInt X) U.compl 2 (by
          have hdeg : (2 : ℤ) - 1 = 1 := by omega
          simpa only [top_inf_eq, Opens.compl_compl, hdeg] using a))

/-- The supported logarithmic class of the localized unit has the explicit
first-filtered lift supplied by `dlog`. -/
def holomorphicUnitSupportedFilteredClass
    (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitsSheaf X (dim X.left)).obj.obj (.op U)) :
    SupportedFilteredDeRhamHypercohomology X U.compl 1 2 :=
  supportedFilteredLogarithmicClass X U.compl 2
    (holomorphicUnitSupportedLocalizationClass X U u)

/-- The full supported de Rham class of the localized unit. -/
def holomorphicUnitSupportedDeRhamClass
    (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitsSheaf X (dim X.left)).obj.obj (.op U)) :
    SupportedDeRhamHypercohomology X U.compl 2 :=
  supportedLogarithmicClass X U.compl 2
    (holomorphicUnitSupportedLocalizationClass X U u)

/-- Forgetting the filtration gives the full supported logarithmic class. -/
theorem holomorphicUnitSupportedFilteredClass_toDeRham
    (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitsSheaf X (dim X.left)).obj.obj (.op U)) :
    supportedFilteredToDeRhamCohomology X U.compl 1 2
        (holomorphicUnitSupportedFilteredClass X U u) =
      holomorphicUnitSupportedDeRhamClass X U u :=
  supportedFilteredLogarithmicClass_toDeRham X U.compl 2 _

/-- The full class is exactly the normalized `2πi` period image of the actual
supported integral exponential class. -/
theorem holomorphicUnitSupportedIntegralClass_period
    (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitsSheaf X (dim X.left)).obj.obj (.op U)) :
    supportedIntegerPeriodToDeRhamCohomology X U.compl 2
        (supportedIntegralExponentialClass X U.compl 2
          (holomorphicUnitSupportedLocalizationClass X U u)) =
      holomorphicUnitSupportedDeRhamClass X U u :=
  supportedIntegralExponentialClass_logarithmic_comparison X U.compl 2 _

/-- End-to-end codimension-one normalization: the integral exponential class
and the explicit filtered logarithmic lift have the same full supported de
Rham image. -/
theorem holomorphicUnitSupportedIntegralClass_eq_filtered
    (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitsSheaf X (dim X.left)).obj.obj (.op U)) :
    supportedIntegerPeriodToDeRhamCohomology X U.compl 2
        (supportedIntegralExponentialClass X U.compl 2
          (holomorphicUnitSupportedLocalizationClass X U u)) =
      supportedFilteredToDeRhamCohomology X U.compl 1 2
        (holomorphicUnitSupportedFilteredClass X U u) :=
  supportedIntegralExponentialClass_eq_filteredLogarithmicClass X U.compl 2 _

end AlgebraicGeometry.ComplexPoint
