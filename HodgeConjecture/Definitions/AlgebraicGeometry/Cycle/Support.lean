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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
public import HodgeConjecture.Mathlib.AlgebraicGeometry.PointClosure

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Cycle components and their support

A cycle on `X` is indexed by the points of `X.left`. The component at `x` is the integral closed
subscheme `Z = X.left.pointClosure x`. `CycleComponent.over X x` bundles `Z` over `ℂ`, and
`CycleComponent.ι X x` is its closed immersion into `X`. The complex points of `X` that lie on `Z`
form the closed set `CycleComponent.support X x`, written `x‾(ℂ)` for `Z(ℂ)`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.CycleComponent

variable (X : Over (Spec ↧ℂ)) (x : X.left)

/-- The cycle component at `x`, the integral closed subscheme `X.left.pointClosure x`, as a scheme
over `ℂ`. -/
abbrev over : Over (Spec ↧ℂ) :=
  ComplexPoint.overMk X (X.left.pointClosureι x)

/-- The closed immersion of the cycle component at `x`, as a morphism over `ℂ`. -/
abbrev ι : over X x ⟶ X :=
  ComplexPoint.overHomMk X (X.left.pointClosureι x)

instance [LocallyOfFiniteType X.hom] : JacobsonSpace (X.left.pointClosure x) :=
  LocallyOfFiniteType.jacobsonSpace (X.left.pointClosureι x ≫ X.hom)

/-- `Z(ℂ)`: the complex points of `X` on the cycle component `Z` at `x`. -/
def support : Closeds (ComplexPoint X) :=
  (Closeds.closure {x}).preimage Point.continuous_underlying

@[inherit_doc support]
scoped notation3:max x:max "‾(ℂ)" => support _ x

@[simp]
lemma coe_support :
    (x‾(ℂ) : Set (ComplexPoint X)) = Point.underlying ⁻¹' closure {x} :=
  rfl

@[simp]
lemma mem_support {z : ComplexPoint X} :
    z ∈ x‾(ℂ) ↔ z.underlying ∈ closure {x} :=
  Iff.rfl

end AlgebraicGeometry.CycleComponent
