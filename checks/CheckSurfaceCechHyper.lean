import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCechProduct
import Other.AlgebraicGeometry.ExplicitEllipticCurveDeRhamClass
import Other.AlgebraicGeometry.ExplicitEllipticSurfaceFilteredClass

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

local instance testCurveDimSmooth :
    SmoothOfRelativeDimension (dim curve) curveVariety.hom :=
  dim_curve_eq_one.symm ▸
    (inferInstance : SmoothOfRelativeDimension 1 curveVariety.hom)

local instance testSurfaceDimSmooth :
    SmoothOfRelativeDimension (dim surface) surfaceVariety.hom :=
  dim_surface_eq_two.symm ▸
    (inferInstance : SmoothOfRelativeDimension 2 surfaceVariety.hom)

#synth IsIntegral curveVariety.left
#synth Smooth curveVariety.hom
#synth SmoothOfRelativeDimension (dim curve) curveVariety.hom
#synth IsIntegral surfaceVariety.left
#synth Smooth surfaceVariety.hom
#synth SmoothOfRelativeDimension (dim surface) surfaceVariety.hom
#check SmoothOfRelativeDimension.of_isIntegral

def testHolomorphicAdditiveFunctionSheafIsoOfDimensionEq
    (X : Over (Spec (.of ℂ))) {d e : ℕ}
    (hd : SmoothOfRelativeDimension d X.hom)
    (he : SmoothOfRelativeDimension e X.hom) (h : d = e) :
    @holomorphicAdditiveFunctionSheaf X d hd ≅
      @holomorphicAdditiveFunctionSheaf X e he := by
  subst e
  exact Iso.refl _

def testCurveCechOClass
    (a : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    HolomorphicFunctionCohomology curveVariety 1 := by
  let e := testHolomorphicAdditiveFunctionSheafIsoOfDimensionEq curveVariety
    (inferInstance : SmoothOfRelativeDimension 1 curveVariety.hom)
    (inferInstance : SmoothOfRelativeDimension (dim curve) curveVariety.hom)
    dim_curve_eq_one.symm
  exact sheafExtHypercohomologyEquiv curveVariety
    (holomorphicAdditiveFunctionSheaf curveVariety (dim curve)) 0 1
    ((curveHolomorphicCechClass a).comp (Abelian.Ext.mk₀ e.hom)
      (show 1 + 0 = 1 from rfl))

def testSurfaceCechOClass
    (a b : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    HolomorphicFunctionCohomology surfaceVariety 2 := by
  let e := testHolomorphicAdditiveFunctionSheafIsoOfDimensionEq surfaceVariety
    (inferInstance : SmoothOfRelativeDimension 2 surfaceVariety.hom)
    (inferInstance : SmoothOfRelativeDimension (dim surface) surfaceVariety.hom)
    dim_surface_eq_two.symm
  exact sheafExtHypercohomologyEquiv surfaceVariety
    (holomorphicAdditiveFunctionSheaf surfaceVariety (dim surface)) 0 2
    ((surfaceHolomorphicCechExternalProductClass a b).comp
      (Abelian.Ext.mk₀ e.hom) (show 2 + 0 = 2 from rfl))

end AlgebraicGeometry.ExplicitEllipticCandidate
