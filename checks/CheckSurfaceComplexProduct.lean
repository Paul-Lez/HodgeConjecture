import Other.AlgebraicGeometry.ExplicitEllipticSurfaceRationalSingularClass
import Other.AlgebraicTopology.SingularProductCoefficientChange

open CategoryTheory MonoidalCategory TopologicalSpace
open AlgebraicTopology

namespace AlgebraicGeometry.ExplicitEllipticCandidate

noncomputable section

theorem curveProductRationalExternalTwoClass_toComplex
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    Singular.rationalToComplexCohomologyMap
        (curveAnalyticSpace ⊗ curveAnalyticSpace) 2
        (curveProductRationalExternalTwoClass alpha halpha) =
      let a := curveRationalOneRepresentativePairing alpha halpha
      Singular.degreeOneExternalCohomologyClass ℂ
        (Singular.qToCSingularCochain curveAnalyticSpace 1 a.cochain)
        (Singular.qToCSingularCochain curveAnalyticSpace 1 a.cochain)
        (by rw [← Singular.qToCSingularCochain_coboundary, a.coboundary_eq_zero,
          map_zero])
        (by rw [← Singular.qToCSingularCochain_coboundary, a.coboundary_eq_zero,
          map_zero]) := by
  let a := curveRationalOneRepresentativePairing alpha halpha
  change Singular.rationalToComplexCohomologyMap
      (curveAnalyticSpace ⊗ curveAnalyticSpace) 2
      (Singular.degreeOneExternalCohomologyClass ℚ a.cochain a.cochain
        a.coboundary_eq_zero a.coboundary_eq_zero) = _
  exact Singular.rationalToComplexCohomologyMap_degreeOneExternalCohomologyClass
    a.cochain a.cochain a.coboundary_eq_zero a.coboundary_eq_zero

theorem surfaceRationalExternalTwoClass_toComplex
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    Singular.rationalToComplexCohomologyMap surfaceAnalyticSpace 2
        (surfaceRationalExternalTwoClass alpha halpha) =
      (Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2).symm
        (let a := curveRationalOneRepresentativePairing alpha halpha
        Singular.degreeOneExternalCohomologyClass ℂ
          (Singular.qToCSingularCochain curveAnalyticSpace 1 a.cochain)
          (Singular.qToCSingularCochain curveAnalyticSpace 1 a.cochain)
          (by rw [← Singular.qToCSingularCochain_coboundary, a.coboundary_eq_zero,
            map_zero])
          (by rw [← Singular.qToCSingularCochain_coboundary, a.coboundary_eq_zero,
            map_zero])) := by
  rw [show surfaceRationalExternalTwoClass alpha halpha =
      Singular.cohomologyMap ℚ 2 surfaceAnalyticProductIso.hom
        (curveProductRationalExternalTwoClass alpha halpha) from rfl]
  rw [Singular.rationalToComplexCohomologyMap_naturality_degreeTwo]
  change Singular.cohomologyMap ℂ 2 surfaceAnalyticProductIso.hom
      (Singular.rationalToComplexCohomologyMap
        (curveAnalyticSpace ⊗ curveAnalyticSpace) 2
        (curveProductRationalExternalTwoClass alpha halpha)) = _
  rw [curveProductRationalExternalTwoClass_toComplex]
  rfl

end

end AlgebraicGeometry.ExplicitEllipticCandidate
