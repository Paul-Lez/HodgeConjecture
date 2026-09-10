import Other.AlgebraicGeometry.BettiGlobalSectionsComparison

open CategoryTheory

open AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

example (X : Over (Spec (.of ℂ))) :
    constantComplexSheafComplexInt X = constantCoefficientSheafComplexInt X ℂ := rfl

end AlgebraicGeometry.ComplexPoint
