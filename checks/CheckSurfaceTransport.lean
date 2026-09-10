import Other.AlgebraicGeometry.ExplicitEllipticSurfacePointProduct
import Other.AlgebraicTopology.SingularProductDegreeOne

noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry

namespace AlgebraicGeometry.ExplicitEllipticCandidate

abbrev curveTop : TopCat := TopCat.of (ComplexPoint curveVariety)
abbrev surfaceTop : TopCat := TopCat.of (ComplexPoint surfaceVariety)

#check TopCat.isoOfHomeo

example : surfaceTop ≅ curveTop ⊗ curveTop :=
  TopCat.isoOfHomeo (X := surfaceTop) (Y := curveTop ⊗ curveTop)
    surfaceComplexPointHomeomorph

end AlgebraicGeometry.ExplicitEllipticCandidate
