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

public import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Complex points and closed points

For a complex scheme locally of finite type, its complex points are equivalent to its closed
scheme points. The second construction packages the same fact for any point model whose map to
the underlying scheme is injective with image the closed points.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.ComplexPoint

/-- Complex points of a scheme locally of finite type over `ℂ` are equivalent to its closed
scheme points. -/
def complexPointEquivClosedPoint
    (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom] :
    ComplexPoint X ≃ closedPoints X.left :=
  { toFun := fun z ↦ pointEquivClosedPoint X.hom ⟨z.left, Over.w z⟩
    invFun := fun x ↦ Over.homMk ((pointEquivClosedPoint X.hom).symm x).1
      ((pointEquivClosedPoint X.hom).symm x).2
    left_inv := fun z ↦ by
      apply Over.OverMorphism.ext
      exact congrArg Subtype.val
        ((pointEquivClosedPoint X.hom).symm_apply_apply ⟨z.left, Over.w z⟩)
    right_inv := fun x ↦ (pointEquivClosedPoint X.hom).apply_symm_apply x }

/-- A point model mapping injectively to a complex scheme with image its closed points is
equivalent to the scheme's complex points. -/
def pointEquivOfRangeClosedPoints
    (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom]
    (A : Type*) (p : A → X.left) (hp_inj : Function.Injective p)
    (hp_range : Set.range p = closedPoints X.left) : A ≃ ComplexPoint X := by
  let q : A → closedPoints X.left :=
    fun a ↦ ⟨p a, by rw [← hp_range]; exact Set.mem_range_self a⟩
  exact (Equiv.ofBijective q
    ⟨fun a b h ↦ hp_inj (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨a, ha⟩ : x.1 ∈ Set.range p := by rw [hp_range]; exact x.2
      exact ⟨a, Subtype.ext ha⟩⟩).trans
    (complexPointEquivClosedPoint X).symm

end AlgebraicGeometry.ComplexPoint
