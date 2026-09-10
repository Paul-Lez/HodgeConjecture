import Other.AlgebraicTopology.SingularProductDegreeOne

noncomputable section

open CategoryTheory Limits Simplicial MonoidalCategory
open scoped Simplicial

universe u

namespace AlgebraicTopology.Simplicial

variable (R : Type u) [Field R]

example {X : SSet.{u}}
    (eta : LinearMap.ker
      (((X.chainComplex (ModuleCat.of R R)).sc 1).linearDual.g.hom)) :
    cochainClassOfOneCocycle R
        (cohomologyCycleToCocycle R 1 eta).1
        (cohomologyCycleToCocycle R 1 eta).2 =
      ((X.chainComplex (ModuleCat.of R R)).sc 1).linearDual.moduleCatHomologyClass eta := by
  rfl

end AlgebraicTopology.Simplicial
