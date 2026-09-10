/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExponentialClassHodge
public import Other.AlgebraicGeometry.FilteredCycleComponentSupport

/-!
# The exponential class with closed support

This file applies the actual right-derived closed-support functor to the
holomorphic exponential resolution.  A supported class of holomorphic units
therefore gives a supported integral class and, by `dlog`, an explicit lift to
the first filtered de Rham complex.  The comparison retains the normalized
period `2πi` at the level of coefficient complexes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance supportedExponentialSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance supportedExponentialGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

theorem holomorphicUnitsComplexInt_isGE :
    (holomorphicUnitsComplexInt X).IsGE 1 := by
  letI : (holomorphicUnitsComplexInt X).IsStrictlyGE 1 :=
    holomorphicUnitsComplexInt_isStrictlyGE X
  rw [CochainComplex.isGE_iff]
  intro i hi
  exact HomologicalComplex.ExactAt.of_isZero
    ((holomorphicUnitsComplexInt X).isZero_of_isStrictlyGE 1 i hi)

theorem holomorphicExponentialResolutionInt_isGE :
    (holomorphicExponentialResolutionInt X).IsGE 0 := by
  letI : (holomorphicExponentialResolutionInt X).IsStrictlyGE 0 := by
    unfold holomorphicExponentialResolutionInt
    infer_instance
  rw [CochainComplex.isGE_iff]
  intro i hi
  exact HomologicalComplex.ExactAt.of_isZero
    ((holomorphicExponentialResolutionInt X).isZero_of_isStrictlyGE 0 i hi)

theorem constantIntegerSheafComplexInt_isGE :
    (constantIntegerSheafComplexInt X).IsGE 0 := by
  letI : (constantIntegerSheafComplexInt X).IsStrictlyGE 0 := by
    unfold constantIntegerSheafComplexInt
    infer_instance
  rw [CochainComplex.isGE_iff]
  intro i hi
  exact HomologicalComplex.ExactAt.of_isZero
    ((constantIntegerSheafComplexInt X).isZero_of_isStrictlyGE 0 i hi)

/-- The bounded-below derived object of holomorphic units placed in degree one. -/
def holomorphicUnitsPlusObject :
    DerivedCategory.Plus (AnalyticAdditiveSheaf X) := by
  letI := holomorphicUnitsComplexInt_isGE X
  exact TopCat.Sheaf.supportCoefficientPlus
    (TopCat.of (ComplexPoint X)) (holomorphicUnitsComplexInt X) 1

/-- The bounded-below derived exponential resolution. -/
def holomorphicExponentialResolutionPlusObject :
    DerivedCategory.Plus (AnalyticAdditiveSheaf X) := by
  letI := holomorphicExponentialResolutionInt_isGE X
  exact TopCat.Sheaf.supportCoefficientPlus
    (TopCat.of (ComplexPoint X)) (holomorphicExponentialResolutionInt X) 0

/-- The bounded-below derived constant-integer object used by the exponential
resolution. -/
def constantIntegerPlusObject :
    DerivedCategory.Plus (AnalyticAdditiveSheaf X) := by
  letI := constantIntegerSheafComplexInt_isGE X
  exact TopCat.Sheaf.supportCoefficientPlus
    (TopCat.of (ComplexPoint X)) (constantIntegerSheafComplexInt X) 0

/-- Units map into the exponential resolution in `D⁺`. -/
def holomorphicUnitsToExponentialResolutionPlus :
    holomorphicUnitsPlusObject X ⟶
      holomorphicExponentialResolutionPlusObject X :=
  DerivedCategory.Plus.ι.preimage
    (DerivedCategory.Q.map (holomorphicUnitsToExponentialResolutionInt X))

/-- The normalized augmentation is an isomorphism in `D⁺`. -/
def holomorphicExponentialResolutionPlusIso :
    constantIntegerPlusObject X ≅
      holomorphicExponentialResolutionPlusObject X :=
  DerivedCategory.Plus.ι.preimageIso
    (asIso (DerivedCategory.Q.map (holomorphicExponentialResolutionIntι X)))

/-- The morphism underlying the normalized exponential-resolution
isomorphism. -/
def holomorphicExponentialResolutionPlusι :
    constantIntegerPlusObject X ⟶
      holomorphicExponentialResolutionPlusObject X :=
  DerivedCategory.Plus.ι.preimage
    (DerivedCategory.Q.map (holomorphicExponentialResolutionIntι X))

@[simp]
theorem holomorphicExponentialResolutionPlusIso_hom :
    (holomorphicExponentialResolutionPlusIso X).hom =
      holomorphicExponentialResolutionPlusι X := rfl

/-- The exponential resolution maps to full de Rham forms in `D⁺`. -/
def holomorphicExponentialResolutionToDeRhamPlus :
    holomorphicExponentialResolutionPlusObject X ⟶
      holomorphicDeRhamPlusObject X :=
  DerivedCategory.Plus.ι.preimage
    (DerivedCategory.Q.map (holomorphicExponentialResolutionToDeRhamInt X))

/-- The supported logarithmic derivative already lands in the first filtered
de Rham object before any support is forgotten. -/
def holomorphicDlogFilteredPlus :
    holomorphicUnitsPlusObject X ⟶ hodgeFilteredDeRhamPlusObject X 1 :=
  DerivedCategory.Plus.ι.preimage
    (DerivedCategory.Q.map (holomorphicDlogFilteredComplexInt X))

/-- The filtered logarithmic derivative forgets to the comparison through the
exponential resolution. -/
@[reassoc]
theorem holomorphicDlogFilteredPlus_comp_inclusion :
    holomorphicDlogFilteredPlus X ≫ hodgeFilteredDeRhamPlusInclusion X 1 =
      holomorphicUnitsToExponentialResolutionPlus X ≫
        holomorphicExponentialResolutionToDeRhamPlus X := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [holomorphicDlogFilteredPlus, hodgeFilteredDeRhamPlusInclusion,
    holomorphicUnitsToExponentialResolutionPlus,
    holomorphicExponentialResolutionToDeRhamPlus, Functor.map_preimage,
    Functor.map_comp]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
    holomorphicDlogFilteredComplexInt_comp_inclusion,
    holomorphicUnitsToExponentialResolutionInt_comp_deRham]

/-- The normalized integer-period augmentation followed by the de Rham
comparison, in `D⁺`. -/
def integerPeriodToDeRhamPlus :
    constantIntegerPlusObject X ⟶ holomorphicDeRhamPlusObject X :=
  DerivedCategory.Plus.ι.preimage
    (DerivedCategory.Q.map
      (integerToFieldConstantSheafComplexInt ℂ X
          (2 * Real.pi * Complex.I) ≫
        constantsToHolomorphicDeRhamComplexInt X))

/-- The derived exponential resolution retains the exact `2πi`
normalization. -/
@[reassoc]
theorem holomorphicExponentialResolutionPlusι_comp_deRham :
    holomorphicExponentialResolutionPlusι X ≫
        holomorphicExponentialResolutionToDeRhamPlus X =
      integerPeriodToDeRhamPlus X := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [holomorphicExponentialResolutionPlusι,
    holomorphicExponentialResolutionToDeRhamPlus, integerPeriodToDeRhamPlus,
    Functor.map_preimage, Functor.map_comp]
  rw [← DerivedCategory.Q.map_comp,
    holomorphicExponentialResolutionIntι_comp_deRham,
    Functor.map_comp]

/-- The preceding normalization, stated directly using the isomorphism. -/
@[reassoc]
theorem holomorphicExponentialResolutionPlusIso_hom_comp_deRham :
    (holomorphicExponentialResolutionPlusIso X).hom ≫
        holomorphicExponentialResolutionToDeRhamPlus X =
      integerPeriodToDeRhamPlus X := by
  rw [holomorphicExponentialResolutionPlusIso_hom]
  exact holomorphicExponentialResolutionPlusι_comp_deRham X

/-! ### The supported exponential class -/

/-- Hypercohomology with support of holomorphic units placed in degree one. -/
def SupportedHolomorphicUnitsHypercohomology
    (Z : Closeds (ComplexPoint X)) (n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).obj
        (holomorphicUnitsPlusObject X))

/-- Hypercohomology with support of the normalized exponential resolution. -/
def SupportedExponentialResolutionHypercohomology
    (Z : Closeds (ComplexPoint X)) (n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).obj
        (holomorphicExponentialResolutionPlusObject X))

/-- Hypercohomology with support of the constant integer sheaf. -/
def SupportedIntegerHypercohomology
    (Z : Closeds (ComplexPoint X)) (n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).obj
        (constantIntegerPlusObject X))

/-- The units-to-resolution map after applying derived sections with support. -/
def supportedUnitsToExponentialResolutionCohomology
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedHolomorphicUnitsHypercohomology X Z n ⟶
      SupportedExponentialResolutionHypercohomology X Z n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).map
        (holomorphicUnitsToExponentialResolutionPlus X))

/-- The normalized augmentation induces an isomorphism on supported
hypercohomology. -/
def supportedExponentialResolutionCohomologyIso
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedIntegerHypercohomology X Z n ≅
      SupportedExponentialResolutionHypercohomology X Z n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).mapIso
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).mapIso
        (holomorphicExponentialResolutionPlusIso X))

/-- The actual integral supported exponential class.  It is obtained by
mapping a supported units class to the exponential resolution and then using
the inverse normalized augmentation. -/
def supportedIntegralExponentialClassHom
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedHolomorphicUnitsHypercohomology X Z n ⟶
      SupportedIntegerHypercohomology X Z n :=
  supportedUnitsToExponentialResolutionCohomology X Z n ≫
    (supportedExponentialResolutionCohomologyIso X Z n).inv

/-- Elementwise form of `supportedIntegralExponentialClassHom`. -/
def supportedIntegralExponentialClass
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedHolomorphicUnitsHypercohomology X Z n →+
      SupportedIntegerHypercohomology X Z n :=
  (supportedIntegralExponentialClassHom X Z n).hom

/-- The normalized integer-period map to supported de Rham cohomology. -/
def supportedIntegerPeriodToDeRhamCohomology
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedIntegerHypercohomology X Z n ⟶
      SupportedDeRhamHypercohomology X Z n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).map
        (integerPeriodToDeRhamPlus X))

/-- The exponential-resolution comparison to supported de Rham
hypercohomology. -/
def supportedExponentialResolutionToDeRhamCohomology
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedExponentialResolutionHypercohomology X Z n ⟶
      SupportedDeRhamHypercohomology X Z n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).map
        (holomorphicExponentialResolutionToDeRhamPlus X))

/-- A supported units class has an explicit representative in the first
filtered de Rham hypercohomology. -/
def supportedFilteredLogarithmicClassHom
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedHolomorphicUnitsHypercohomology X Z n ⟶
      SupportedFilteredDeRhamHypercohomology X Z 1 n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).map
        (holomorphicDlogFilteredPlus X))

/-- Elementwise form of `supportedFilteredLogarithmicClassHom`. -/
def supportedFilteredLogarithmicClass
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedHolomorphicUnitsHypercohomology X Z n →+
      SupportedFilteredDeRhamHypercohomology X Z 1 n :=
  (supportedFilteredLogarithmicClassHom X Z n).hom

/-- The supported logarithmic class in full de Rham hypercohomology. -/
def supportedLogarithmicClassHom
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedHolomorphicUnitsHypercohomology X Z n ⟶
      SupportedDeRhamHypercohomology X Z n :=
  supportedUnitsToExponentialResolutionCohomology X Z n ≫
    supportedExponentialResolutionToDeRhamCohomology X Z n

/-- Elementwise form of `supportedLogarithmicClassHom`. -/
def supportedLogarithmicClass
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedHolomorphicUnitsHypercohomology X Z n →+
      SupportedDeRhamHypercohomology X Z n :=
  (supportedLogarithmicClassHom X Z n).hom

/-- Applying derived sections with support preserves the filtered `dlog`
comparison diagram. -/
@[reassoc]
theorem supportedFilteredLogarithmicClassHom_comp_deRham
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    supportedFilteredLogarithmicClassHom X Z n ≫
        supportedFilteredToDeRhamCohomology X Z 1 n =
      supportedLogarithmicClassHom X Z n := by
  unfold supportedFilteredLogarithmicClassHom
    supportedFilteredToDeRhamCohomology supportedLogarithmicClassHom
    supportedUnitsToExponentialResolutionCohomology
    supportedExponentialResolutionToDeRhamCohomology
  simpa only [Functor.mapIso_hom, Functor.map_comp] using congrArg
    (fun f =>
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
        ((TopCat.Sheaf.derivedClosedSupportSections
          (TopCat.of (ComplexPoint X)) Z).map f))
    (holomorphicDlogFilteredPlus_comp_inclusion X)

/-- The explicit filtered logarithmic lift maps to the supported logarithmic
class. -/
theorem supportedFilteredLogarithmicClass_toDeRham
    (Z : Closeds (ComplexPoint X)) (n : ℤ)
    (a : SupportedHolomorphicUnitsHypercohomology X Z n) :
    supportedFilteredToDeRhamCohomology X Z 1 n
        (supportedFilteredLogarithmicClass X Z n a) =
      supportedLogarithmicClass X Z n a :=
  ConcreteCategory.congr_hom
    (supportedFilteredLogarithmicClassHom_comp_deRham X Z n) a

/-- Applying derived sections with support preserves the normalized
integer-period comparison. -/
@[reassoc]
theorem supportedExponentialResolutionCohomologyIso_hom_comp_deRham
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    (supportedExponentialResolutionCohomologyIso X Z n).hom ≫
        supportedExponentialResolutionToDeRhamCohomology X Z n =
      supportedIntegerPeriodToDeRhamCohomology X Z n := by
  unfold supportedExponentialResolutionCohomologyIso
    supportedExponentialResolutionToDeRhamCohomology
    supportedIntegerPeriodToDeRhamCohomology
  simpa only [Functor.mapIso_hom, Functor.map_comp] using congrArg
    (fun f =>
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
        ((TopCat.Sheaf.derivedClosedSupportSections
          (TopCat.of (ComplexPoint X)) Z).map f))
    (holomorphicExponentialResolutionPlusIso_hom_comp_deRham X)

/-- The normalized integral supported exponential class maps to its
logarithmic de Rham class. -/
@[reassoc]
theorem supportedIntegralExponentialClassHom_comp_deRham
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    supportedIntegralExponentialClassHom X Z n ≫
        supportedIntegerPeriodToDeRhamCohomology X Z n =
      supportedLogarithmicClassHom X Z n := by
  unfold supportedIntegralExponentialClassHom supportedLogarithmicClassHom
  rw [Category.assoc,
    ← supportedExponentialResolutionCohomologyIso_hom_comp_deRham]
  simp

/-- Elementwise normalized comparison for the supported exponential class. -/
theorem supportedIntegralExponentialClass_logarithmic_comparison
    (Z : Closeds (ComplexPoint X)) (n : ℤ)
    (a : SupportedHolomorphicUnitsHypercohomology X Z n) :
    supportedIntegerPeriodToDeRhamCohomology X Z n
        (supportedIntegralExponentialClass X Z n a) =
      supportedLogarithmicClass X Z n a :=
  ConcreteCategory.congr_hom
    (supportedIntegralExponentialClassHom_comp_deRham X Z n) a

/-- The codimension-one supported exponential class is exactly the image of
its explicit filtered logarithmic lift. -/
theorem supportedIntegralExponentialClass_eq_filteredLogarithmicClass
    (Z : Closeds (ComplexPoint X)) (n : ℤ)
    (a : SupportedHolomorphicUnitsHypercohomology X Z n) :
    supportedIntegerPeriodToDeRhamCohomology X Z n
        (supportedIntegralExponentialClass X Z n a) =
      supportedFilteredToDeRhamCohomology X Z 1 n
        (supportedFilteredLogarithmicClass X Z n a) := by
  rw [supportedIntegralExponentialClass_logarithmic_comparison,
    supportedFilteredLogarithmicClass_toDeRham]

/-- Every normalized supported exponential class belongs to the first
supported Hodge filtration, with `supportedFilteredLogarithmicClass` as a
concrete witness. -/
theorem supportedIntegralExponentialClass_mem_supportedHodgeFiltration
    (Z : Closeds (ComplexPoint X)) (n : ℤ)
    (a : SupportedHolomorphicUnitsHypercohomology X Z n) :
    supportedIntegerPeriodToDeRhamCohomology X Z n
        (supportedIntegralExponentialClass X Z n a) ∈
      supportedHodgeFiltration X Z 1 n := by
  refine ⟨supportedFilteredLogarithmicClass X Z n a, ?_⟩
  exact (supportedIntegralExponentialClass_eq_filteredLogarithmicClass
    X Z n a).symm


end AlgebraicGeometry.ComplexPoint
