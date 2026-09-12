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

public import HodgeConjecture.Definitions.Algebra.FieldToComplex

/-!
# A coefficient field inside the complex numbers

Lemmas about the definitions in
`HodgeConjecture.Definitions.Algebra.FieldToComplex`.
-/

@[expose] public noncomputable section

variable (K : Type) [Field K] [Algebra K ℂ]

/-- The chosen rational-linear retraction is a left inverse to `K → ℂ`. -/
lemma complexToFieldLinear_comp_algebraMap :
    complexToFieldLinear K ∘ₗ Algebra.linearMap K ℂ = LinearMap.id :=
  Classical.choose_spec <| (Algebra.linearMap K ℂ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)

@[simp] lemma complexToFieldLinear_algebraMap (q : K) :
    complexToFieldLinear K (algebraMap K ℂ q) = q :=
  LinearMap.congr_fun (complexToFieldLinear_comp_algebraMap K) q

