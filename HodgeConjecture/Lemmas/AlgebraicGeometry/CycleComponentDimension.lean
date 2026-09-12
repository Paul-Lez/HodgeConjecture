/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.AlgebraicCycleSupport
/-!
# Dimension of a reduced cycle component

This file relates the order-theoretic dimension of the reduced closure of a scheme point to the
specialization order in the ambient scheme.  These facts separate the purely topological part of
the component dimension calculation from the catenary dimension formula needed for a smooth
variety.

Mathlib currently has no catenary or equidimensional scheme API, and its
`SmoothOfRelativeDimension` API does not relate relative dimension to `Order.height` or
`Order.coheight`.  Consequently this file proves the unconditional identity
`dim(closure {x}) = height(x)`, but does not claim the further smooth-variety formula
`height(x) + coheight(x) = dim(X)`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

/-- Membership in a reduced cycle component is membership in the closure that defines it. -/
lemma mem_cycleComponent_support_iff (X : Scheme) (x y : X) :
    y ∈ (Scheme.IdealSheafData.vanishingIdeal
        (X := X) ⟨closure {x}, isClosed_closure⟩).support ↔
      y ∈ closure {x} :=
  Set.ext_iff.mp
    (Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨closure {x}, isClosed_closure⟩) y

/-- The points of the reduced closure of `x` are exactly the specializations below `x`.

This is an order isomorphism for the specialization preorders. It is the order-theoretic core of
the dimension calculation for a cycle component. -/
def cycleComponentOrderIsoIic (X : Scheme) (x : X) :
    cycleComponent X x ≃o Set.Iic x := by
  let e : cycleComponent X x ≃ Set.Iic x :=
    { toFun := fun y ↦ ⟨cycleComponentι X x y, show cycleComponentι X x y ≤ x by
        rw [Scheme.le_iff_specializes, specializes_iff_mem_closure]
        exact (mem_cycleComponent_support_iff X x (cycleComponentι X x y)).mp y.2⟩
      invFun := fun y ↦ ⟨y.1, by
        apply (mem_cycleComponent_support_iff X x y.1).mpr
        rw [← specializes_iff_mem_closure, ← Scheme.le_iff_specializes]
        exact y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine ⟨e, ?_⟩
  intro a b
  change (cycleComponentι X x a ≤ cycleComponentι X x b) ↔ a ≤ b
  rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
  exact (cycleComponentι X x).isClosedEmbedding.isInducing.specializes_iff

@[simp]
lemma cycleComponentOrderIsoIic_apply (X : Scheme) (x : X) (y : cycleComponent X x) :
    (cycleComponentOrderIsoIic X x y : X) = cycleComponentι X x y :=
  rfl

@[simp]
lemma cycleComponentOrderIsoIic_symm_apply_coe
    (X : Scheme) (x : X) (y : Set.Iic x) :
    cycleComponentι X x ((cycleComponentOrderIsoIic X x).symm y) = y :=
  rfl

/-- For a scheme, topological Krull dimension is the Krull dimension of its specialization
preorder. -/
lemma Scheme.topologicalKrullDim_eq_orderKrullDim (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso
    (irreducibleSetEquivPoints (α := X))

/-- The order-theoretic Krull dimension of the reduced closure of `x` is exactly the height of
`x` in the ambient scheme. -/
lemma orderKrullDim_cycleComponent (X : Scheme) (x : X) :
    Order.krullDim (cycleComponent X x) = Order.height x := by
  rw [Order.krullDim_eq_of_orderIso (cycleComponentOrderIsoIic X x)]
  exact (Order.height_eq_krullDim_Iic x).symm

/-- The topological Krull dimension of the reduced closure of `x` is exactly the order-theoretic
height of `x` in the ambient scheme. -/
lemma topologicalKrullDim_cycleComponent (X : Scheme) (x : X) :
    topologicalKrullDim (cycleComponent X x) = Order.height x := by
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim]
  exact orderKrullDim_cycleComponent X x

end AlgebraicGeometry
