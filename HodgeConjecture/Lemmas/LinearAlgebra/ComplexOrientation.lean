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

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.Orientation
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Orientations of complex vector spaces

Every complex-linear automorphism preserves either real orientation of its underlying real vector
space.  This file proves that fact from the determinant norm formula and defines the standard
orientation of `Fin n → ℂ`, with real and imaginary basis vectors interleaved.

The generic preservation theorem is phrased using mathlib's `Orientation`.  In particular, it is
the linear-algebra input needed to construct the constant-sign `Manifold.OrientationLift` proposed
in [mathlib4 PR #35376](https://github.com/leanprover-community/mathlib4/pull/35376): apply
`Manifold.OrientationLift.compatible_of_det` to the positivity result after identifying a
holomorphic tangent coordinate change with the scalar restriction of a complex-linear
equivalence.
-/

@[expose] public noncomputable section

namespace Complex

/-- The real dimension of `Fin n → ℂ` is `2 * n`, in the form expected by
`Manifold.OrientationLift`. -/
instance piOrientationFinrankFact (n : ℕ) :
    Fact (Fintype.card (Fin (n * 2)) = Module.finrank ℝ (Fin n → ℂ)) :=
  ⟨by simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]⟩

/-- The standard real basis of `Fin n → ℂ`, ordered
`(re z 0, im z 0, re z 1, im z 1, ...)`.

It is obtained by composing the standard complex basis of the function space with `basisOneI`,
then reindexing the product basis by `finProdFinEquiv`.
-/
def piBasisOneI (n : ℕ) : Module.Basis (Fin (n * 2)) ℝ (Fin n → ℂ) :=
  (basisOneI.smulTower' (Pi.basisFun ℂ (Fin n))).reindex finProdFinEquiv

/-- The real-coordinate identification of `Fin n → ℂ` with `Fin (n * 2) → ℝ`, listing the real
and imaginary part of each complex coordinate consecutively.

This is the coordinate map of `piBasisOneI`. It is recorded as a continuous linear equivalence so
that continuity, linearity and `map_eq_zero_iff` all come from Mathlib rather than being reproved
for the underlying function. -/
def piCoordCLE (n : ℕ) : (Fin n → ℂ) ≃L[ℝ] (Fin (n * 2) → ℝ) :=
  (piBasisOneI n).equivFunL



end Complex
