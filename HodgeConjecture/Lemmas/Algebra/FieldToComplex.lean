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

public import HodgeConjecture.Mathlib.Algebra.Ring.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# A coefficient field inside the complex numbers

The definitions in this file, and the lemmas about them, are reached from the statement of the
conjecture only through proofs, so the statement never inspects them: by proof irrelevance
nothing about how they were built can change what it asserts.
-/

@[expose] public noncomputable section

variable (K : Type) [Field K] [Algebra K ℂ]

/-- A rational-linear retraction of the inclusion `K → ℂ`. Such a retraction exists because an
injective linear map of vector spaces over a field splits. -/
noncomputable def complexToFieldLinear : ℂ →ₗ[K] K :=
  Classical.choose <| (Algebra.linearMap K ℂ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)

end

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
