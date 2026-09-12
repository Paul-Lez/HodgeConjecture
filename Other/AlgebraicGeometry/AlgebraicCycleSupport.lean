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

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The support of an algebraic cycle

The support of an algebraic cycle is the union of the closures of the generic points carrying a
nonzero coefficient, and its preimage in the analytic complex-point space is the union of the
supports of the individual components, hence closed on a projective variety.

The conjecture is stated through the span of the classes of the individual components, so it
never names the support of a cycle as a whole.
-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ))

/-- The underlying closed support of an algebraic cycle: the union of the closures of all generic
points having nonzero coefficient. -/
def algebraicCycleSupport {R : Type*} [Zero R] (X : Scheme)
    (c : AlgebraicCycle X R) : Set X :=
  ⋃ x ∈ c.support, closure {x}

/-- The complex points lying over the geometric support of an algebraic cycle. -/
def analyticCycleSupport {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (c : AlgebraicCycle X.left R) : Set (ComplexPoint X) :=
  Point.underlying ⁻¹' algebraicCycleSupport X.left c

/-- The analytic support of a cycle is the union of the analytic supports of its nonzero
components. -/
lemma analyticCycleSupport_eq_iUnion {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R) :
    analyticCycleSupport X c =
      ⋃ x ∈ c.support, cycleComponentSupport X x := by
  ext z
  simp [analyticCycleSupport, algebraicCycleSupport, cycleComponentSupport]

/-- The analytic support of an algebraic cycle on a projective variety is closed. -/
lemma isClosed_analyticCycleSupport {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R) :
    IsClosed (analyticCycleSupport X c) := by
  rw [analyticCycleSupport_eq_iUnion]
  exact (algebraicCycle_support_finite X c).isClosed_biUnion fun x _ =>
    isClosed_cycleComponentSupport X x

lemma cycleComponentSupport_subset_analyticCycleSupport {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R)
    (x : X.left) (hx : c x ≠ 0) :
    cycleComponentSupport X x ⊆ analyticCycleSupport X c :=
  fun _ hz => Set.mem_iUnion₂.mpr ⟨x, Function.mem_support.mpr hx, hz⟩

@[simp]
lemma algebraicCycleSupport_zero {R : Type*} [Zero R] (X : Scheme) :
    algebraicCycleSupport X (0 : AlgebraicCycle X R) = ∅ := by
  simp [algebraicCycleSupport]
  exact fun _ => rfl

@[simp]
lemma analyticCycleSupport_zero {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    analyticCycleSupport X (0 : AlgebraicCycle X.left R) = ∅ := by
  simp [analyticCycleSupport]

end AlgebraicGeometry
