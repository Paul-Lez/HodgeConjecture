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
