/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Mathlib.AlgebraicGeometry.ReducedClosedSubscheme
import HodgeConjecture.Mathlib.Topology.KrullDimension

/-!
# The closure of a point as an integral closed subscheme

`X.pointClosure x` is the closure of `{x}` with its reduced scheme structure: the integral closed
subscheme of `X` with generic point `x`. Its points are the specializations of `x`, so its
dimension is `Order.height x`.

## Main definitions

* `AlgebraicGeometry.Scheme.pointClosure`: the closure of `{x}` as an integral closed subscheme.
* `AlgebraicGeometry.Scheme.pointClosureOrderIsoIic`: the points of `X.pointClosure x`, as an
  order isomorphism onto the specializations `Set.Iic x` of `x`.

## Main results

* `AlgebraicGeometry.Scheme.pointClosureι_genericPoint`: `x` is the generic point of
  `X.pointClosure x`.
* `AlgebraicGeometry.Scheme.topologicalKrullDim_pointClosure`: the dimension of `X.pointClosure x`
  is `Order.height x`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme

variable (X : Scheme.{u}) (x : X)

/-- The closure of `{x}` with its reduced scheme structure: the integral closed subscheme of `X`
with generic point `x`. -/
abbrev pointClosure : Scheme :=
  X.reducedClosedSubscheme (Closeds.closure {x})

/-- The closed immersion of the closure of `{x}`. On points it is the inclusion of `closure {x}`
into `X` (`reducedClosedSubschemeι_apply`). -/
abbrev pointClosureι : X.pointClosure x ⟶ X :=
  X.reducedClosedSubschemeι (Closeds.closure {x})

instance : IsIntegral (X.pointClosure x) :=
  X.isIntegral_reducedClosedSubscheme isIrreducible_singleton.closure

@[simp]
lemma range_pointClosureι : Set.range (X.pointClosureι x) = closure {x} :=
  X.range_reducedClosedSubschemeι _

/-- The points of the closure of `{x}` are the specialisations of `x`. -/
def pointClosureOrderIsoIic : X.pointClosure x ≃o Set.Iic x :=
  have key (z : X) : z ∈ closure {x} ↔ z ≤ x := by
    rw [Scheme.le_iff_specializes, specializes_iff_mem_closure]
  let e : X.pointClosure x ≃ Set.Iic x :=
    { toFun := fun y ↦ ⟨X.pointClosureι x y, (key _).1 y.2⟩
      invFun := fun y ↦ ⟨y.1, (key _).2 y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  ⟨e, by
    intro a b
    change X.pointClosureι x a ≤ X.pointClosureι x b ↔ a ≤ b
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact (X.pointClosureι x).isClosedEmbedding.isInducing.specializes_iff⟩

@[simp]
lemma coe_pointClosureOrderIsoIic_apply (y : X.pointClosure x) :
    (X.pointClosureOrderIsoIic x y : X) = X.pointClosureι x y :=
  rfl

@[simp]
lemma pointClosureι_pointClosureOrderIsoIic_symm_apply (y : Set.Iic x) :
    X.pointClosureι x ((X.pointClosureOrderIsoIic x).symm y) = y :=
  rfl

/-- The point `x` is the generic point of the closure of `{x}`. -/
@[simp]
lemma pointClosureι_genericPoint : X.pointClosureι x (genericPoint (X.pointClosure x)) = x := by
  let z : X.pointClosure x := ⟨x, subset_closure (Set.mem_singleton x)⟩
  have hz : IsGenericPoint z Set.univ := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    rw [← Scheme.le_iff_specializes, ← (X.pointClosureOrderIsoIic x).le_iff_le]
    exact (X.pointClosureOrderIsoIic x y).2
  rw [← hz.eq (genericPoint_spec _)]
  rfl

/-- The Krull dimension of the specialisation order of the closure of `{x}` is the height of
`x`. -/
lemma krullDim_pointClosure : Order.krullDim (X.pointClosure x) = Order.height x := by
  rw [Order.krullDim_eq_of_orderIso (X.pointClosureOrderIsoIic x)]
  exact (Order.height_eq_krullDim_Iic x).symm

/-- The topological Krull dimension of the closure of `{x}` is the height of `x`. -/
lemma topologicalKrullDim_pointClosure :
    topologicalKrullDim (X.pointClosure x) = Order.height x := by
  rw [topologicalKrullDim_eq_krullDim, krullDim_pointClosure]

end Scheme

end AlgebraicGeometry
