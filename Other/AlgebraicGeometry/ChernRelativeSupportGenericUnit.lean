/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernRelativeSupportUnit
public import Other.AlgebraicGeometry.ChernWindingGenericChartData
public import Other.AlgebraicGeometry.CartierWindingChartUnit
public import Other.AlgebraicGeometry.CartierWindingChartCoefficient

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open HomologicalComplex
open AlgebraicTopology.Singular
open AlgebraicGeometry
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
local instance genericUnitTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
attribute [local instance] isNoetherian_of_isProjective
variable {X d}

namespace GenericWindingChartData

variable {c : Scheme.CartierData X.left} {x : X.left}
  [SmoothOfRelativeDimension d X.hom] {q : ComplexPoint X}

set_option maxHeartbeats 1000000 in
lemma normalizedCartierUnit_supportMap
    (G : GenericWindingChartData X c x d q)
    (hx : c.divisor x ≠ 0) :
    let ch := G.toChart
    let S := cycleComponentAnalyticClosedSupport X x
    let T := analyticClosedSupport X (badLocus c)
    let hST : S ≤ T := fun _ hy => closure_subset_badLocus c x hx hy
    let Ω := T.compl
    let hEq : ch.carrier ⊓ Ω = ch.punctured :=
      ch.inf_goodComplement_eq_punctured hx
    let uT := (holomorphicUnitSheaf X d).obj.map (homOfLE hEq.le).op ch.cartierUnit
    (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) (2 : ℤ)).hom.app
        (op ch.carrier)
        ((complexSupportInjectiveCohomologySheafIsoRelative X S 2).inv.hom.app (op ch.carrier)
          (ch.winding ch.cartierUnit)) =
      (complexSupportInjectiveCohomologySheafIsoRelative X T 2).inv.hom.app (op ch.carrier)
        (windingSheafHom (hasWindingPeriods X d ch.carrier T) uT) := by
  dsimp only
  let ch := G.toChart
  let S := cycleComponentAnalyticClosedSupport X x
  let T := analyticClosedSupport X (badLocus c)
  let hST : S ≤ T := fun _ hy => closure_subset_badLocus c x hx hy
  let Ω := T.compl
  let hEq : ch.carrier ⊓ Ω = ch.punctured := ch.inf_goodComplement_eq_punctured hx
  let uT := (holomorphicUnitSheaf X d).obj.map (homOfLE hEq.le).op ch.cartierUnit
  apply normalizedWindingUnit_supportMap (X := X) hST ch.carrier
    ch.cartierUnit uT
  rfl

end GenericWindingChartData

end AlgebraicGeometry.ComplexPoint
