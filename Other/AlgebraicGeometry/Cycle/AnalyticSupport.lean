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
public import Other.Mathlib.AlgebraicGeometry.AlgebraicCycle.Support

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
public import Other.AlgebraicGeometry.Cycle.Support

/-!
# The analytic support of an algebraic cycle

The complex points over the support of an algebraic cycle form a closed subset of the analytic
complex-point space, the union of the supports of the components with a nonzero coefficient.

The conjecture is stated through the span of the classes of the individual components, so it
never names the support of a cycle as a whole.
-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

open CycleComponent

open ComplexPoint

variable (X : Over (Spec ↧ℂ))

namespace CycleComponent

/-- The inclusion of a cycle component on complex points, bundled as a continuous map. -/
noncomputable def continuousMap
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    @ContinuousMap
      (ComplexPoint (over X x))
      (ComplexPoint X) Point.analyticTopology Point.analyticTopology :=
  Point.continuousMap (Over.homMk (X.left.pointClosureι x) rfl)

end CycleComponent

variable {R : Type*} [Zero R] (c : AlgebraicCycle X.left R)

/-- The complex points over the support of an algebraic cycle. -/
noncomputable def analyticCycleSupport : Closeds (ComplexPoint X) :=
  c.closedSupport.preimage Point.continuous_underlying

/-- Unfold the analytic support of `c` to the preimage of its topological support in `X.left`. -/
@[simp]
lemma coe_analyticCycleSupport :
    (analyticCycleSupport X c : Set (ComplexPoint X)) = Point.underlying ⁻¹' tsupport c :=
  rfl

/-- Membership in the analytic support of `c`, tested on the underlying scheme point. -/
@[simp]
lemma mem_analyticCycleSupport {z : ComplexPoint X} :
    z ∈ analyticCycleSupport X c ↔ z.underlying ∈ tsupport c :=
  Iff.rfl

/-- The analytic support of a cycle is the union of the supports of its components with a nonzero
coefficient. -/
lemma coe_analyticCycleSupport_eq_iUnion :
    (analyticCycleSupport X c : Set (ComplexPoint X)) =
      ⋃ x ∈ c.support, x‾(ℂ) :=
  (congrArg (Point.underlying ⁻¹' ·) c.coe_closedSupport_eq_iUnion).trans Set.preimage_iUnion₂

/-- The support of a component with a nonzero coefficient lies in the analytic support of the
cycle. -/
lemma CycleComponent.support_le_analyticCycleSupport {x : X.left} (hx : c x ≠ 0) :
    x‾(ℂ) ≤ analyticCycleSupport X c :=
  fun _ hz ↦ c.closure_singleton_le_closedSupport hx hz

/-- The zero cycle has empty analytic support. -/
@[simp]
lemma analyticCycleSupport_zero : analyticCycleSupport X (0 : AlgebraicCycle X.left R) = ⊥ :=
  congrArg (Closeds.preimage · Point.continuous_underlying) AlgebraicCycle.closedSupport_zero

end AlgebraicGeometry
