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

public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Complex periods of a rational vector space

A period of a rational vector space is a complex-valued rational-linear functional on it. This
file records the two structures such functionals carry: complex conjugation acts on them, and the
rational functionals embed among them as the conjugation-invariant ones coming from scalars.

Extending a functional along a field extension is the general construction behind the embedding,
so it is proved for an arbitrary algebra of fields.
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicTopology.Singular

/-- Extend the values of a linear functional along a field extension. -/
def extendFunctional (K L : Type u) [Field K] [Field L] [Algebra K L]
    (M : Type u) [AddCommGroup M] [Module K M] :
    Module.Dual K M →ₗ[K] (M →ₗ[K] L) where
  toFun φ := (Algebra.linearMap K L).comp φ
  map_add' φ ψ := by
    ext x
    simp
  map_smul' a φ := by
    ext x
    simp [Algebra.smul_def]

@[simp]
lemma extendFunctional_apply (K L : Type u) [Field K] [Field L] [Algebra K L]
    (M : Type u) [AddCommGroup M] [Module K M] (φ : Module.Dual K M) (x : M) :
    extendFunctional K L M φ x = algebraMap K L (φ x) :=
  rfl

lemma extendFunctional_injective (K L : Type u) [Field K] [Field L] [Algebra K L]
    (M : Type u) [AddCommGroup M] [Module K M] :
    Function.Injective (extendFunctional K L M) := by
  intro φ ψ h
  ext x
  apply FaithfulSMul.algebraMap_injective K L
  exact LinearMap.congr_fun h x

/-- Complex-valued rational-linear periods on a rational vector space. -/
abbrev ComplexPeriodSpace (M : Type) [AddCommGroup M] [Module ℚ M] :=
  M →ₗ[ℚ] ℂ

/-- Complex conjugation of a complex-valued rational-linear period functional. -/
def conjugatePeriod (M : Type) [AddCommGroup M] [Module ℚ M] :
    ComplexPeriodSpace M →ₗ[ℚ] ComplexPeriodSpace M where
  toFun φ := (Complex.conjAe.restrictScalars ℚ).toLinearMap.comp φ
  map_add' φ ψ := by ext; simp
  map_smul' q φ := by ext; simp

@[simp]
lemma conjugatePeriod_apply (M : Type) [AddCommGroup M] [Module ℚ M]
    (φ : ComplexPeriodSpace M) (x : M) :
    conjugatePeriod M φ x = Complex.conjAe (φ x) :=
  rfl

@[simp]
lemma conjugatePeriod_involutive (M : Type) [AddCommGroup M] [Module ℚ M]
    (φ : ComplexPeriodSpace M) :
    conjugatePeriod M (conjugatePeriod M φ) = φ := by
  ext
  simp

/-- A rational functional, viewed as a complex-valued period functional. -/
abbrev rationalPeriod (M : Type) [AddCommGroup M] [Module ℚ M] :
    Module.Dual ℚ M →ₗ[ℚ] ComplexPeriodSpace M :=
  extendFunctional ℚ ℂ M

lemma rationalPeriod_injective (M : Type) [AddCommGroup M] [Module ℚ M] :
    Function.Injective (rationalPeriod M) :=
  extendFunctional_injective ℚ ℂ M

@[simp]
lemma conjugatePeriod_rationalPeriod (M : Type) [AddCommGroup M] [Module ℚ M]
    (φ : Module.Dual ℚ M) :
    conjugatePeriod M (rationalPeriod M φ) = rationalPeriod M φ := by
  ext x
  simp

end AlgebraicTopology.Singular
