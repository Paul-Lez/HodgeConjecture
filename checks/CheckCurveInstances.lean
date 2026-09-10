import Other.AlgebraicGeometry.ExplicitEllipticCurveDeRhamClass
import Other.AlgebraicGeometry.ProjectiveAnalytificationParacompact

noncomputable section
open CategoryTheory TopologicalSpace
open AlgebraicGeometry
namespace AlgebraicGeometry.ExplicitEllipticCandidate
open ComplexPoint
#synth IsProjective curveVariety.hom
#synth T2Space (ComplexPoint curveVariety)
#synth IsIntegral curveVariety.left
#synth SmoothOfRelativeDimension 1 curveVariety.hom
local instance hsm : Smooth curveVariety.hom :=
  SmoothOfRelativeDimension.smooth 1 curveVariety.hom
example : ∀ U : Opens (ComplexPoint curveVariety), ParacompactSpace U :=
  ComplexPoint.openParacompactSpace curveVariety
end AlgebraicGeometry.ExplicitEllipticCandidate

