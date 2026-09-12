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

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Rational linear equivalences from additive equivalences

The equivalence counterpart of `AddMonoidHom.toRatLinearMap`.
-/

@[expose] public noncomputable section

variable {M M₂ : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂] [Module ℚ M₂]

/-- An additive equivalence of rational vector spaces as a rational linear equivalence. -/
def AddEquiv.toRatLinearEquiv (e : M ≃+ M₂) : M ≃ₗ[ℚ] M₂ :=
  e.toLinearEquiv (map_rat_smul e)

@[simp]
lemma AddEquiv.coe_toRatLinearEquiv (e : M ≃+ M₂) : ⇑e.toRatLinearEquiv = e := rfl

end
