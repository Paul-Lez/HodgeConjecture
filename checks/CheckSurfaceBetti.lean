import Other.AlgebraicGeometry.ExplicitEllipticSurfaceRationalSingularClass
import Other.AlgebraicGeometry.BettiGlobalSectionsComparison

noncomputable section
open CategoryTheory TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.ExplicitEllipticCandidate

#synth IsIntegral surfaceVariety.left
#synth Smooth surfaceVariety.hom
#synth T2Space (ComplexPoint surfaceVariety)
#synth ∀ U : Opens (ComplexPoint surfaceVariety), ParacompactSpace U

#check ComplexPoint.rationalCohomologyEquivSingularCohomology surfaceVariety 2

end AlgebraicGeometry.ExplicitEllipticCandidate

