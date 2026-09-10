import Other.AlgebraicGeometry.ExplicitEllipticCMHolomorphicDifferential
import Other.AlgebraicGeometry.TopHodgeFilteredScalarNaturality

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

def topHolomorphicFormScalarSheafMapOfDimension (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (c : ℂ) :
    holomorphicDeRhamSheaf X d d ⟶ holomorphicDeRhamSheaf X d d :=
  (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
    (scalarHolomorphicDeRhamPresheaf X d d c)

theorem testOfDimension (d : ℕ) (hd : dim X.left = d)
    [SmoothOfRelativeDimension d X.hom] (c : ℂ)
    (w : (holomorphicDeRhamSheaf X d d).obj.obj (.op ⊤)) :
    topHolomorphicFormFilteredEquivOfDimension X d hd
        ((topHolomorphicFormScalarSheafMapOfDimension X d c).hom.app (.op ⊤) w) =
      hypercohomologyMap X (hodgeFilteredDeRhamComplexScalar X d c) d
        (topHolomorphicFormFilteredEquivOfDimension X d hd w) := by
  subst d
  exact topHolomorphicFormFilteredEquiv_scalar X c w

end
end AlgebraicGeometry.ComplexPoint

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

example :
    curveCMTopFilteredClass =
      hypercohomologyMap curveVariety
        (hodgeFilteredDeRhamComplexScalar curveVariety 1 Complex.I) 1
        curveTopFilteredClass := by
  exact testOfDimension curveVariety 1 dim_curve_eq_one Complex.I
    curveGlobalHolomorphicDifferential

end AlgebraicGeometry.ExplicitEllipticCandidate
