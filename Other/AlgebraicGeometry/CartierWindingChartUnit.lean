/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CartierLocalFormUnit
public import Other.AlgebraicGeometry.CartierFrameLift
public import Other.AlgebraicGeometry.ChernWindingChartPeriods

/-!
# The Cartier unit on a winding chart

The Cartier function on a punctured winding chart is the analytification of the algebraic
unit constructed on the basic open of the prime equation. In the additive unit sheaf it is
the sum of an extendable coefficient unit and the divisor multiplicity times the chart's
prime coordinate. Consequently its winding class has the required integer multiplicity.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
open CategoryTheory TopologicalSpace Opposite Order
open scoped Manifold ContDiff
namespace AlgebraicGeometry.ComplexPoint
variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]
local instance cartierWindingChartUnitTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- Analytification on additive groups of units. -/
def analyticUnitHom (U : X.left.Opens) :
    Additive (Γ(X.left, U)ˣ) →+
      (holomorphicUnitSheaf X d).obj.obj (op (analyticOpen X U)) :=
  (Units.map ((regularToHolomorphicRingSheaf X d).hom.app (op U)).hom.toMonoidHom).toAdditive

lemma analyticUnitHom_val (U : X.left.Opens) (u : Γ(X.left, U)ˣ) :
    unitSection (unitOf (analyticUnitHom (X := X) (d := d) U (Additive.ofMul u))) =
      analyticFunction X d U u := rfl

lemma analyticUnitHom_restrict {U V : X.left.Opens} (hVU : V ≤ U)
    (u : Γ(X.left, U)ˣ) :
    analyticUnitHom (X := X) (d := d) V
        (Additive.ofMul (Units.map (X.left.presheaf.map (homOfLE hVU).op).hom u)) =
      sres (holomorphicUnitSheaf X d) (analyticOpen_mono X hVU)
        (analyticUnitHom (X := X) (d := d) U (Additive.ofMul u)) := by
  apply Additive.toMul.injective
  apply Units.ext
  exact analyticFunction_res hVU (u : Γ(X.left, U))

variable [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
attribute [local instance] isNoetherian_of_isProjective
variable {c : Scheme.CartierData X.left} {x : X.left} {p : ℕ} {q : ComplexPoint X}
  (ch : ChernWindingChart X c x d p q)

lemma ChernWindingChart.punctured_le_basicOpen :
    ch.punctured ≤ analyticOpen X (X.left.basicOpen ch.localForm.equation) := by
  intro y hy
  have hyU : Point.underlying y ∈ ch.localForm.opens := ch.le_analytic hy.1
  by_contra h
  exact hy.2 (ch.localForm.mem_closure_of_notMem_basicOpen _ hyU h)

/-- The full Cartier function, as a unit on the punctured chart. -/
def ChernWindingChart.cartierUnit :
    (holomorphicUnitSheaf X d).obj.obj (op ch.punctured) :=
  sres (holomorphicUnitSheaf X d) ch.punctured_le_basicOpen
    (analyticUnitHom (X := X) (d := d) _ (Additive.ofMul ch.localForm.cartierUnit))

/-- The unit coefficient of the algebraic local form extends across the component. -/
def ChernWindingChart.coefficientUnit :
    (holomorphicUnitSheaf X d).obj.obj (op ch.carrier) :=
  sres (holomorphicUnitSheaf X d) ch.le_analytic
    (analyticUnitHom (X := X) (d := d) _ (Additive.ofMul ch.localForm.unit))

lemma ChernWindingChart.equationUnit_eq_coord :
    sres (holomorphicUnitSheaf X d) ch.punctured_le_basicOpen
      (analyticUnitHom (X := X) (d := d) _ (Additive.ofMul ch.localForm.equationUnit)) =
        ch.coord := by
  apply Additive.toMul.injective
  apply Units.ext
  change ringRes ch.punctured_le_basicOpen
    (analyticFunction X d _ ch.localForm.equationUnit) = (Additive.toMul ch.coord).val
  rw [ch.localForm.equationUnit_val, analyticFunction_res, ch.coord_eq]
  rfl

/-- The full Cartier function is the extendable unit plus the multiplicity times the prime
coordinate in the additive unit sheaf. -/
lemma ChernWindingChart.cartierUnit_eq :
    ch.cartierUnit = ch.restrictUnit ch.coefficientUnit + (c.divisor x) • ch.coord := by
  have h : Additive.ofMul ch.localForm.cartierUnit =
      Additive.ofMul (Units.map
        (X.left.presheaf.map (homOfLE (X.left.basicOpen_le ch.localForm.equation)).op).hom
          ch.localForm.unit) + (c.divisor x) • Additive.ofMul ch.localForm.equationUnit := rfl
  unfold ChernWindingChart.cartierUnit
  rw [h, map_add, map_zsmul, sres_add, sres_zsmul, ch.equationUnit_eq_coord,
    analyticUnitHom_restrict, sres_sres]
  rfl

lemma ChernWindingChart.winding_cartierUnit
    (h : ch.HasTrivialUnitWinding) :
    ch.winding ch.cartierUnit = (c.divisor x) • ch.winding ch.coord := by
  rw [ch.cartierUnit_eq, map_add, h, map_zsmul, zero_add]

end AlgebraicGeometry.ComplexPoint
