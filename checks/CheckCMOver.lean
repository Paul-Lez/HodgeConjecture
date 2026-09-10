import Other.AlgebraicGeometry.ExplicitEllipticCMGlobal
import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ExplicitEllipticCandidate
#check curveVariety
#check curveCMEnd
#check curveCMEnd_toBase
-- theorem unavailable
example (h : curveCMEnd » curveToBase = curveToBase) : curveVariety ? curveVariety :=
  Over.homMk (U := curveVariety) (V := curveVariety) curveCMEnd h
end AlgebraicGeometry.ExplicitEllipticCandidate
