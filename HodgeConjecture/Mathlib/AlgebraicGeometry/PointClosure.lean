/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Mathlib.AlgebraicGeometry.ReducedClosedSubscheme
public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.KrullDimension

/-!
# The closure of a point as an integral closed subscheme

`X.pointClosure x` is the closure of `{x}` with its reduced scheme structure: the integral closed
subscheme of `X` with generic point `x`. Its points are the specialisations of `x`, so its
dimension is `Order.height x`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The topological Krull dimension of a scheme is the Krull dimension of its specialisation
order. -/
lemma Scheme.topologicalKrullDim_eq_orderKrullDim (X : Scheme.{u}) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

namespace Scheme

variable (X : Scheme.{u}) (x : X)

/-- The closure of `{x}` with its reduced scheme structure: the integral closed subscheme of `X`
with generic point `x`. -/
abbrev pointClosure : Scheme :=
  X.reducedClosedSubscheme (Closeds.closure {x})

/-- The closed immersion of the closure of `{x}`. -/
abbrev pointClosureι : X.pointClosure x ⟶ X :=
  X.reducedClosedSubschemeι (Closeds.closure {x})

instance : IsIntegral (X.pointClosure x) :=
  X.isIntegral_reducedClosedSubscheme isIrreducible_singleton.closure

@[simp]
lemma range_pointClosureι : Set.range (X.pointClosureι x) = closure {x} :=
  X.range_reducedClosedSubschemeι _

/-- The points of the closure of `{x}` are the specialisations of `x`. -/
def pointClosureOrderIsoIic : X.pointClosure x ≃o Set.Iic x :=
  let e : X.pointClosure x ≃ Set.Iic x :=
    { toFun := fun y ↦ ⟨X.pointClosureι x y, show X.pointClosureι x y ≤ x by
        rw [Scheme.le_iff_specializes, specializes_iff_mem_closure]
        exact y.2⟩
      invFun := fun y ↦ ⟨y.1, show y.1 ∈ closure {x} by
        rw [← specializes_iff_mem_closure, ← Scheme.le_iff_specializes]
        exact y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  ⟨e, by
    intro a b
    change X.pointClosureι x a ≤ X.pointClosureι x b ↔ a ≤ b
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact (X.pointClosureι x).isClosedEmbedding.isInducing.specializes_iff⟩

@[simp]
lemma pointClosureOrderIsoIic_apply (y : X.pointClosure x) :
    (X.pointClosureOrderIsoIic x y : X) = X.pointClosureι x y :=
  rfl

@[simp]
lemma pointClosureι_symm_pointClosureOrderIsoIic (y : Set.Iic x) :
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
lemma orderKrullDim_pointClosure : Order.krullDim (X.pointClosure x) = Order.height x := by
  rw [Order.krullDim_eq_of_orderIso (X.pointClosureOrderIsoIic x)]
  exact (Order.height_eq_krullDim_Iic x).symm

/-- The topological Krull dimension of the closure of `{x}` is the height of `x`. -/
lemma topologicalKrullDim_pointClosure :
    topologicalKrullDim (X.pointClosure x) = Order.height x := by
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim, orderKrullDim_pointClosure]

end Scheme

end AlgebraicGeometry
