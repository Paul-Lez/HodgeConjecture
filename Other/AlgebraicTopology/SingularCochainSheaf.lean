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

public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Sheaf.Cochain

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- The canonical augmentation from the constant presheaf complex to singular cochains. -/
def constantsToSingularCochainPresheafComplex :
    (CochainComplex.single₀ (TopCat.Presheaf AddCommGrpCat X)).obj
        (constantCoefficientPresheaf R X) ⟶ singularCochainPresheafComplex R X :=
  HomologicalComplex.mkHomFromSingle (constantsToSingularCochainZero R X) <| by
    intro k hk
    obtain rfl : k = 1 := by simpa using hk.symm
    change constantsToSingularCochainZero R X ≫
      (singularCochainPresheafComplex R X).d 0 1 = 0
    rw [singularCochainPresheafComplex_d]
    exact constantsToSingularCochainZero_comp_coboundary R X

end AlgebraicTopology.Singular
