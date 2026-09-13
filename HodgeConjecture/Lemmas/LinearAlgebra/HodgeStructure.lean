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

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Rational Hodge structures

The definitions in this file, and the lemmas about them, are reached from the statement of the
conjecture only through proofs, so the statement never inspects them: by proof irrelevance
nothing about how they were built can change what it asserts.
-/

@[expose] public noncomputable section

open scoped DirectSum TensorProduct

universe u

namespace HodgeStructure

/-- The canonical map from a `K`-vector space to its complexification. -/
def ofBase (K : Type) [Field K] [Algebra K ℂ] (V : Type u) [AddCommGroup V] [Module K V] :
    V →ₗ[K] ℂ ⊗[K] V :=
  TensorProduct.mk K ℂ V 1

variable (V : Type u) [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on a complexified rational vector space. It conjugates the scalar factor
and fixes every rational vector. -/
def conjugate : ℂ ⊗[ℚ] V →ₗ[ℚ] ℂ ⊗[ℚ] V :=
  TensorProduct.map (Complex.conjAe.restrictScalars ℚ).toLinearMap LinearMap.id

/-- A pure decomposition of weight `n` with natural-number bidegrees on a rational vector
space `V` of arbitrary dimension.

The pieces are indexed by pairs `(p,q)`. They form an internal direct sum, only pieces with
`p + q = n` can be nonzero, and complex conjugation exchanges the `(p,q)` and `(q,p)` pieces. -/
structure Pure (n : ℕ) where
  /-- The Hodge piece `V^{p,q}` inside `V_ℂ`. -/
  piece : ℕ → ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- Hodge pieces off the prescribed weight are zero. -/
  piece_eq_bot_of_add_ne : ∀ p q, p + q ≠ n → piece p q = ⊥
  /-- Every complexified vector has a unique finite decomposition into Hodge pieces. -/
  isInternal : DirectSum.IsInternal (fun pq : ℕ × ℕ ↦ piece pq.1 pq.2)
  /-- The complex conjugation exchanges bidegrees. -/
  conjugate_mem_iff : ∀ p q x, conjugate V x ∈ piece p q ↔ x ∈ piece q p

namespace Pure

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {n : ℕ}

/-- Rational Hodge classes of codimension `p`: rational vectors whose complexifications lie in
the middle Hodge piece `V^{p,p}`. -/
def hodgeClasses (p : ℕ) (H : Pure V (2 * p)) : Submodule ℚ V :=
  Submodule.comap (ofBase ℚ V) ((H.piece p p).restrictScalars ℚ)

end Pure

end HodgeStructure

end

@[expose] public noncomputable section

open scoped DirectSum TensorProduct

universe u

namespace HodgeStructure

@[simp]
lemma ofBase_apply (K : Type) [Field K] [Algebra K ℂ] (V : Type u) [AddCommGroup V] [Module K V]
    (v : V) : ofBase K V v = 1 ⊗ₜ[K] v := rfl

variable (V : Type u) [AddCommGroup V] [Module ℚ V]

@[simp]
lemma conjugate_tmul (z : ℂ) (v : V) :
    conjugate V (z ⊗ₜ[ℚ] v) = Complex.conjAe z ⊗ₜ[ℚ] v := rfl

@[simp]
lemma conjugate_ofBase (v : V) : conjugate V (ofBase ℚ V v) = ofBase ℚ V v := by
  simp

@[simp]
lemma conjugate_conjugate (x : ℂ ⊗[ℚ] V) : conjugate V (conjugate V x) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z v
    simp
  · intro x y hx hy
    simp [hx, hy]

namespace Pure

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {n : ℕ}

end Pure

end HodgeStructure
