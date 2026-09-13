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

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicDeRham

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- The inclusion of the constant presheaf into the holomorphic de Rham complex. -/
def constantsToHolomorphicDeRhamPresheafComplex
    [SmoothOfRelativeDimension d X.hom] :
    (CochainComplex.single₀
      (TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
        (constantComplexAddCommGrpPresheaf X) ⟶
      holomorphicDeRhamPresheafComplex X d :=
  HomologicalComplex.mkHomFromSingle
    (constantsToHolomorphicDeRhamZero X d) <| by
      intro k hk
      obtain rfl : k = 1 := by simpa using hk.symm
      change constantsToHolomorphicDeRhamZero X d ≫
        (holomorphicDeRhamPresheafComplex X d).d 0 1 = 0
      rw [holomorphicDeRhamPresheafComplex_d]
      exact constantsToHolomorphicDeRhamZero_comp_differential X d

/-- Multiplication by a complex scalar as an endomorphism of the presheaf de Rham complex. -/
def scalarHolomorphicDeRhamPresheafComplex
    [SmoothOfRelativeDimension d X.hom] (c : ℂ) :
    holomorphicDeRhamPresheafComplex X d ⟶
      holomorphicDeRhamPresheafComplex X d := by
  unfold holomorphicDeRhamPresheafComplex
  exact CochainComplex.ofHom
    (fun p => scalarHolomorphicDeRhamPresheaf X d p c)
    (fun p => by
      simpa [CochainComplex.of_d] using
        scalarHolomorphicDeRhamPresheaf_d X d p c)

end AlgebraicGeometry.ComplexPoint
