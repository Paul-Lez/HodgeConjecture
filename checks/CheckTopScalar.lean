import checks.CheckConcentratedNat

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

theorem check_topHodgeFilteredComplexIsoSingle_scalar (c : ℂ) :
    hodgeFilteredDeRhamComplexScalar X (dim X.left) c ≫
        (topHodgeFilteredComplexIsoSingle X).hom =
      (topHodgeFilteredComplexIsoSingle X).hom ≫
        (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
          (dim X.left)).map
            ((scalarHolomorphicDeRhamComplex X (dim X.left) c).f
              (dim X.left)) := by
  unfold topHodgeFilteredComplexIsoSingle
  rw [Category.assoc, check_concentrated_naturality]
  rw [← Functor.map_comp]
  rw [check_topHodgeFilteredTermIso_scalar]
  simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.ComplexPoint
