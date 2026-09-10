import Other.AlgebraicGeometry.ExplicitEllipticCMHolomorphicDifferential
import Other.AlgebraicGeometry.TopHodgeFilteredScalarNaturality

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

example :
    curveCMTopFilteredClass =
      hypercohomologyMap curveVariety
        (hodgeFilteredDeRhamComplexScalar curveVariety 1 Complex.I) 1
        curveTopFilteredClass := by
  unfold curveCMTopFilteredClass curveTopFilteredClass
  unfold topHolomorphicFormFilteredEquivOfDimension
  rw [curveCMGlobalHolomorphicDifferential_eq_i_smul]
  exact topHolomorphicFormFilteredEquiv_scalar curveVariety Complex.I
    curveGlobalHolomorphicDifferential

example :
    curveCMDeRhamClass =
      Complex.I •
        filteredToDeRhamCohomology curveVariety 1 1 curveTopFilteredClass := by
  unfold curveCMDeRhamClass
  rw [show curveCMTopFilteredClass =
      hypercohomologyMap curveVariety
        (hodgeFilteredDeRhamComplexScalar curveVariety 1 Complex.I) 1
        curveTopFilteredClass by
    exact topHolomorphicFormFilteredEquiv_scalar curveVariety Complex.I
      curveGlobalHolomorphicDifferential]
  rw [deRham_complex_smul_eq]
  unfold filteredToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  rw [hodgeFilteredDeRhamComplexScalar_comp_inclusion]

end AlgebraicGeometry.ExplicitEllipticCandidate
