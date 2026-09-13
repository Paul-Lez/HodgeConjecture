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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.Dimension

/-!
# The generic point of a reduced cycle component

The ambient point of a cycle component is a point of that component, and it is its generic point:
it is the top of the component's specialization order, it agrees with the canonical generic point
supplied by integrality, its height inside the component is the ambient height, and its coheight
there is zero.

The dimension statements the conjecture is stated with use `topologicalKrullDim_cycleComponent`
directly, so none of this is needed to state it.
-/


@[expose] public section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

/-- The ambient point, regarded as a point of its reduced closure. -/
def cycleComponentGenericPoint (X : Scheme) (x : X) : cycleComponent X x :=
  ⟨x, (mem_cycleComponent_support_iff X x x).mpr (subset_closure (Set.mem_singleton x))⟩

@[simp]
lemma cycleComponentι_genericPoint (X : Scheme) (x : X) :
    cycleComponentι X x (cycleComponentGenericPoint X x) = x :=
  rfl

/-- The distinguished point of the reduced component corresponds to the top of the ambient
specialization interval. -/
lemma cycleComponentOrderIsoIic_genericPoint (X : Scheme) (x : X) :
    cycleComponentOrderIsoIic X x (cycleComponentGenericPoint X x) =
      ⟨x, show x ≤ x from le_rfl⟩ :=
  rfl

/-- The distinguished point is a generic point of the reduced component. -/
lemma cycleComponentGenericPoint_isGeneric (X : Scheme) (x : X) :
    IsGenericPoint (cycleComponentGenericPoint X x) Set.univ := by
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.mem_univ, iff_true]
  rw [← Scheme.le_iff_specializes, ← (cycleComponentOrderIsoIic X x).le_iff_le,
    cycleComponentOrderIsoIic_genericPoint]
  exact (cycleComponentOrderIsoIic X x y).2

/-- The explicitly constructed point agrees with the canonical generic point supplied by
integrality. -/
lemma cycleComponentGenericPoint_eq_genericPoint (X : Scheme) (x : X) :
    cycleComponentGenericPoint X x = genericPoint (cycleComponent X x) :=
  (cycleComponentGenericPoint_isGeneric X x).eq
    (genericPoint_spec (cycleComponent X x))

/-- The distinguished generic point is the top element of the component's specialization
preorder. -/
@[simp]
lemma cycleComponentGenericPoint_eq_top (X : Scheme) (x : X) :
    cycleComponentGenericPoint X x = ⊤ :=
  cycleComponentGenericPoint_eq_genericPoint X x

/-- The distinguished generic point is maximal in the component's specialization preorder. -/
lemma cycleComponentGenericPoint_isMax (X : Scheme) (x : X) :
    IsMax (cycleComponentGenericPoint X x) := by
  rw [cycleComponentGenericPoint_eq_top]
  exact isMax_top

/-- The height of the distinguished generic point inside the component equals the ambient height
of the point defining the component. -/
lemma height_cycleComponentGenericPoint (X : Scheme) (x : X) :
    Order.height (cycleComponentGenericPoint X x) = Order.height x := by
  rw [cycleComponentGenericPoint_eq_top]
  apply WithBot.coe_eq_coe.mp
  rw [Order.height_top_eq_krullDim]
  exact orderKrullDim_cycleComponent X x

/-- The coheight of the distinguished generic point inside its component is zero. -/
@[simp]
lemma coheight_cycleComponentGenericPoint (X : Scheme) (x : X) :
    Order.coheight (cycleComponentGenericPoint X x) = 0 := by
  rw [cycleComponentGenericPoint_eq_top]
  exact Order.coheight_top _

/-- A codimension hypothesis records the ambient coheight of the generic point of the reduced
component, without changing or supplementing that hypothesis. -/
lemma cycleComponentGenericPoint_ambient_coheight
    (X : Scheme) (x : X) {p : ℕ} (hx : Order.coheight x = p) :
    Order.coheight (cycleComponentι X x (cycleComponentGenericPoint X x)) = p := by
  simpa only [cycleComponentι_genericPoint] using hx

end AlgebraicGeometry
