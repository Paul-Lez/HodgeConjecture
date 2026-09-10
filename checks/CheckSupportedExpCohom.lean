import Other.AlgebraicGeometry.SupportedExponentialClass

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

def SupportedHolomorphicUnitsHypercohomology
    (Z : Closeds (ComplexPoint X)) (n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).obj (holomorphicUnitsPlusObject X))

def SupportedIntegerHypercohomology
    (Z : Closeds (ComplexPoint X)) (n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).obj (constantIntegerPlusObject X))

def supportedIntegralExponentialClass
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedHolomorphicUnitsHypercohomology X Z n ⟶
      SupportedIntegerHypercohomology X Z n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).map
        (holomorphicUnitsToExponentialResolutionPlus X ≫
          (holomorphicExponentialResolutionPlusIso X).inv))

def supportedFilteredLogarithmicClass
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedHolomorphicUnitsHypercohomology X Z n ⟶
      SupportedFilteredDeRhamHypercohomology X Z 1 n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).map
        (holomorphicDlogFilteredPlus X))

def supportedIntegerPeriodToDeRhamCohomology
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedIntegerHypercohomology X Z n ⟶
      SupportedDeRhamHypercohomology X Z n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).map (integerPeriodToDeRhamPlus X))

@[reassoc]
theorem supportedExponential_filtered_normalization
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    supportedIntegralExponentialClass X Z n ≫
        supportedIntegerPeriodToDeRhamCohomology X Z n =
      supportedFilteredLogarithmicClass X Z n ≫
        supportedFilteredToDeRhamCohomology X Z 1 n := by
  unfold supportedIntegralExponentialClass
    supportedIntegerPeriodToDeRhamCohomology
    supportedFilteredLogarithmicClass
    supportedFilteredToDeRhamCohomology
  rw [← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (fun f ↦
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
      ((TopCat.Sheaf.derivedClosedSupportSections
        (TopCat.of (ComplexPoint X)) Z).map f))
  rw [Category.assoc, Iso.inv_hom_id_assoc,
    holomorphicDlogFilteredPlus_comp_inclusion]

theorem supportedIntegerPeriodClass_mem_supportedHodgeFiltration
    (Z : Closeds (ComplexPoint X)) (n : ℤ)
    (a : SupportedHolomorphicUnitsHypercohomology X Z n) :
    supportedIntegerPeriodToDeRhamCohomology X Z n
        (supportedIntegralExponentialClass X Z n a) ∈
      supportedHodgeFiltration X Z 1 n := by
  refine ⟨supportedFilteredLogarithmicClass X Z n a, ?_⟩
  exact (ConcreteCategory.congr_hom
    (supportedExponential_filtered_normalization X Z n) a).symm

end
end AlgebraicGeometry.ComplexPoint
