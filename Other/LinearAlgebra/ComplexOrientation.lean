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

public import HodgeConjecture.Lemmas.LinearAlgebra.ComplexOrientation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.Orientation
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity


@[expose] public noncomputable section

/-- A complex-linear automorphism has positive real determinant after restriction of scalars.

This is stated for an arbitrary finite free complex module.  The real freeness needed to form the
determinant is supplied by the scalar-tower instance behind `LinearMap.det_restrictScalars`.
-/
theorem LinearEquiv.det_restrictScalars_complex_pos
    {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E]
    [IsScalarTower ℝ ℂ E] [Module.Free ℂ E]
    (f : E ≃ₗ[ℂ] E) :
    0 < LinearMap.det ((f.restrictScalars ℝ).toLinearMap) := by
  change 0 < LinearMap.det (f.toLinearMap.restrictScalars ℝ)
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  exact Complex.normSq_pos.mpr f.isUnit_det'.ne_zero

end

@[expose] public noncomputable section

namespace Complex

/-- The canonical complex orientation of `Fin n → ℂ`, regarded as a real vector space. -/
def piOrientation (n : ℕ) : Orientation ℝ (Fin n → ℂ) (Fin (n * 2)) :=
  (piBasisOneI n).orientation

/-- Complex-linear automorphisms of `Fin n → ℂ` preserve its canonical complex orientation. -/
theorem map_piOrientation (n : ℕ) (f : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    Orientation.map (Fin (n * 2)) (f.restrictScalars ℝ) (piOrientation n) =
      piOrientation n :=
  (Orientation.map_eq_iff_det_pos _ _
    (by rw [Module.finrank_eq_card_basis (piBasisOneI n)])).2
    f.det_restrictScalars_complex_pos

end Complex
