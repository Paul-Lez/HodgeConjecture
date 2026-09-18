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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support
/-!
# Dimension of a closed subvariety

This file relates the order-theoretic dimension of the source of a closed embedding with
irreducible source to the specialization order in the ambient scheme. These facts separate the
purely topological part of the dimension calculation from the catenary dimension formula needed
for a smooth variety.

Mathlib currently has no catenary or equidimensional scheme API, and its
`SmoothOfRelativeDimension` API does not relate relative dimension to `Order.height` or
`Order.coheight`. Consequently this file proves the unconditional identity
`dim Y = height (i (genericPoint Y))`, but does not claim the further smooth-variety formula
`height(x) + coheight(x) = dim(X)`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Scheme} (f : Y ⟶ X) [IsClosedImmersion f] [IrreducibleSpace Y]

/-- A point below the image of the generic point is in the image. -/
lemma mem_range_of_le_image_genericPoint (y : X) (hy : y ≤ f (genericPoint Y)) :
    y ∈ Set.range f := by
  rw [range_eq_closure_image_genericPoint f, ← specializes_iff_mem_closure,
    ← Scheme.le_iff_specializes]
  exact hy

/-- Every point of the source of a closed immersion with irreducible source lies below the image
of the generic point. -/
lemma le_image_genericPoint (y : Y) : f y ≤ f (genericPoint Y) := by
  rw [Scheme.le_iff_specializes, specializes_iff_mem_closure,
    ← range_eq_closure_image_genericPoint f]
  exact ⟨y, rfl⟩

/-- The points of the source of a closed immersion with irreducible source are exactly the
specializations below the image of the generic point.

This is an order isomorphism for the specialization preorders. It is the order-theoretic core of
the dimension calculation for a closed subvariety. -/
def closedImmersionOrderIsoIic : Y ≃o Set.Iic (f (genericPoint Y)) :=
  let e : Y ≃ Set.Iic (f (genericPoint Y)) :=
    { toFun := fun y ↦ ⟨f y, le_image_genericPoint f y⟩
      invFun := fun y ↦ (mem_range_of_le_image_genericPoint f y.1 y.2).choose
      left_inv := fun y ↦ f.isClosedEmbedding.injective
        (mem_range_of_le_image_genericPoint f (f y) (le_image_genericPoint f y)).choose_spec
      right_inv := fun y ↦ Subtype.ext
        (mem_range_of_le_image_genericPoint f y.1 y.2).choose_spec }
  ⟨e, by
    intro a b
    change (f a ≤ f b) ↔ a ≤ b
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact f.isClosedEmbedding.isInducing.specializes_iff⟩

/-- For a scheme, topological Krull dimension is the Krull dimension of its specialization
preorder. -/
lemma Scheme.topologicalKrullDim_eq_orderKrullDim (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso
    (irreducibleSetEquivPoints (α := X))

/-- The order-theoretic Krull dimension of the source of a closed immersion with irreducible
source is the height of the image of its generic point. -/
lemma orderKrullDim_eq_height_image_genericPoint :
    Order.krullDim Y = Order.height (f (genericPoint Y)) := by
  rw [Order.krullDim_eq_of_orderIso (closedImmersionOrderIsoIic f)]
  exact (Order.height_eq_krullDim_Iic _).symm

/-- The topological Krull dimension of the source of a closed immersion with irreducible source
is the height of the image of its generic point. -/
lemma topologicalKrullDim_eq_height_image_genericPoint :
    topologicalKrullDim Y = Order.height (f (genericPoint Y)) := by
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim]
  exact orderKrullDim_eq_height_image_genericPoint f

end AlgebraicGeometry
