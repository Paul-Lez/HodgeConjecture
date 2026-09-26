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
import Other.AlgebraicGeometry.LefschetzOneOneStatement

/-! # Check the explicit rational Lefschetz (1, 1) specification -/

open CategoryTheory AlgebraicGeometry ComplexPoint

/-- This check fails if the explicit-cycle specification changes. -/
example :
    RationalLefschetzOneOne ↔
      ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
        [IsProjective X.hom] (α : H^2(X; ℚ)),
        α ∈ Hdg^1(X; ℚ) →
          ∃ D : TensorProduct ℤ ℚ (codimensionCycleSubgroup X.left 1),
            rationalSheafCycleClassOnCycles
              { scheme := X.left, structureMap := X.hom } 1 D = α :=
  Iff.rfl
