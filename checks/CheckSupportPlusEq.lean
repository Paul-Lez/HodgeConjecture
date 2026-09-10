import Other.AlgebraicGeometry.SupportedExponentialClass

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

noncomputable section

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance hz : (holomorphicUnitsComplexInt X).IsStrictlyGE 0 :=
  (holomorphicUnitsComplexInt X).isStrictlyGE_of_ge 0 1 (by omega)

example :
    TopCat.Sheaf.supportCoefficientPlus (TopCat.of (ComplexPoint X))
        (holomorphicUnitsComplexInt X) 0 ≅
      holomorphicUnitsPlusObject X := by
  apply ObjectProperty.isoMk _
  exact Iso.refl _

end
end AlgebraicGeometry.ComplexPoint
