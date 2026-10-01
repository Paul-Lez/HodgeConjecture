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
scheme points.
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

end AlgebraicGeometry.ComplexPoint
