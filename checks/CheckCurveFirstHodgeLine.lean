import Other.AlgebraicGeometry.ExplicitEllipticCMDeRhamEigen
import Other.AlgebraicGeometry.ExplicitEllipticCurveConnectivity

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance curveSmoothForFirstHodgeLine : Smooth curveVariety.hom :=
  SmoothOfRelativeDimension.smooth 1 curveVariety.hom

/-- Every class in the first Hodge filtration of the explicit curve is a
complex multiple of the invariant differential's de Rham class. -/
theorem curve_firstHodge_class_eq_smul
    (x : DeRhamHypercohomology curveVariety 1)
    (hx : x ∈ hodgeFiltration curveVariety 1 1) :
    ∃ c : ℂ, x = c •
      filteredToDeRhamCohomology curveVariety 1 1 curveTopFilteredClass := by
  rcases hx with ⟨beta, rfl⟩
  let e := topHolomorphicFormFilteredEquivOfDimension
    curveVariety 1 dim_curve_eq_one
  let w := e.symm beta
  obtain ⟨c, hc⟩ := exists_curveGlobalOneForm_eq_smul w
  refine ⟨c, ?_⟩
  have hbeta : beta = hypercohomologyMap curveVariety
      (hodgeFilteredDeRhamComplexScalar curveVariety 1 c) 1
      curveTopFilteredClass := by
    apply e.injective
    rw [show e.symm beta = w from rfl]
    rw [topHolomorphicFormFilteredEquivOfDimension_scalar]
    exact hc
  rw [hbeta]
  rw [deRham_complex_smul_eq]
  unfold filteredToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  rw [hodgeFilteredDeRhamComplexScalar_comp_inclusion]

end AlgebraicGeometry.ExplicitEllipticCandidate
