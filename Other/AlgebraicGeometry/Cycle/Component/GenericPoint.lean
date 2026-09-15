/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Mathlib.AlgebraicGeometry.PointClosure

/-!
# The generic point of a cycle component

`Scheme.pointClosureι_genericPoint` says that the generic point of `X.pointClosure x` lies over
`x`. This file records the order-theoretic consequences: the generic point is the top of the
specialisation order of the component, its height there is the height of `x`, and its coheight
there is zero.

The dimension statements the conjecture is stated with use
`Scheme.topologicalKrullDim_pointClosure` directly, so none of this is needed to state it.
-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (X : Scheme) (x : X)

/-- The generic point of the closure of `{x}` corresponds to the top of `Set.Iic x`. -/
@[simp]
lemma pointClosureOrderIsoIic_genericPoint :
    X.pointClosureOrderIsoIic x (genericPoint (X.pointClosure x)) = ⟨x, Set.mem_Iic.mpr le_rfl⟩ :=
  Subtype.ext (X.pointClosureι_genericPoint x)

/-- The height of the generic point of the closure of `{x}` is the height of `x`. -/
lemma height_genericPoint_pointClosure :
    Order.height (genericPoint (X.pointClosure x)) = Order.height x := by
  apply WithBot.coe_eq_coe.mp
  rw [← X.orderKrullDim_pointClosure x, ← Order.height_top_eq_krullDim]
  rfl

/-- The generic point of the closure of `{x}` has coheight zero there. -/
@[simp]
lemma coheight_genericPoint_pointClosure :
    Order.coheight (genericPoint (X.pointClosure x)) = 0 :=
  Order.coheight_top (X.pointClosure x)

end AlgebraicGeometry.Scheme
