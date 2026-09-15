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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
public import HodgeConjecture.Mathlib.AlgebraicGeometry.PointClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Cycle components and their support

A cycle on `X` is indexed by the points of `X.left`; the component at `x` is the integral closed
subscheme `X.left.pointClosure x`. This file bundles it over `ℂ` and defines its support, the
closed set of complex points of `X` that lie on it.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ)) (x : X.left)

/-- The cycle component at `x`, over `ℂ`. -/
abbrev cycleComponentOver : Over (Spec ↧ℂ) :=
  Over.mk (X.left.pointClosureι x ≫ X.hom)

/-- The closed immersion of the cycle component at `x`, as a morphism over `ℂ`. -/
abbrev cycleComponentOverι : cycleComponentOver X x ⟶ X :=
  Over.homMk (X.left.pointClosureι x) rfl

instance : IsClosedImmersion (cycleComponentOverι X x).left :=
  inferInstanceAs (IsClosedImmersion (X.left.pointClosureι x))

instance [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (cycleComponentOver X x).hom :=
  inferInstanceAs (LocallyOfFiniteType (X.left.pointClosureι x ≫ X.hom))

instance [LocallyOfFinitePresentation (X.left.pointClosureι x ≫ X.hom)] :
    LocallyOfFinitePresentation (cycleComponentOver X x).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (X.left.pointClosureι x ≫ X.hom))

instance [IsProjective X.hom] : IsProjective (cycleComponentOver X x).hom :=
  inferInstanceAs (IsProjective (X.left.pointClosureι x ≫ X.hom))

namespace ComplexPoint

/-- The complex points of `X` on the cycle component at `x`. -/
def cycleComponentSupport : Closeds (ComplexPoint X) :=
  (Closeds.closure {x}).preimage Point.continuous_underlying

@[simp]
lemma coe_cycleComponentSupport :
    (cycleComponentSupport X x : Set (ComplexPoint X)) = Point.underlying ⁻¹' closure {x} :=
  rfl

@[simp]
lemma mem_cycleComponentSupport {z : ComplexPoint X} :
    z ∈ cycleComponentSupport X x ↔ z.underlying ∈ closure {x} :=
  Iff.rfl

end ComplexPoint

end AlgebraicGeometry
