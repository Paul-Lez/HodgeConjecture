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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Points
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Algebraic idempotents and subsets of complex points

An idempotent global regular function on an integral scheme is zero or one. Consequently,
a subset whose characteristic function is the evaluation of such a section is empty or full.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Point

variable {X : Over (Spec (CommRingCat.of ℂ))} [IsIntegral X.left]

/-- An idempotent global regular function has the same value, zero or one, at every
complex point. -/
theorem evaluate_top_idempotent_eq_zero_or_one (s : Γ(X.left, ⊤))
    (hs : IsIdempotentElem s) :
    (∀ z : Point ℂ X, evaluate ⊤ s z = 0) ∨
      (∀ z : Point ℂ X, evaluate ⊤ s z = 1) := by
  rcases (IsIdempotentElem.iff_eq_zero_or_one.mp hs) with rfl | rfl
  · left
    intro z
    rw [← evaluationHom_hom_apply ⊤ ⟨z, trivial⟩]
    exact map_zero _
  · right
    intro z
    rw [← evaluationHom_hom_apply ⊤ ⟨z, trivial⟩]
    exact map_one _

/-- A subset whose characteristic function algebraizes to an idempotent global section
of an integral scheme is empty or full. -/
theorem eq_empty_or_univ_of_indicator_eq_evaluate
    (U : Set (Point ℂ X)) (s : Γ(X.left, ⊤)) (hs : IsIdempotentElem s)
    (heval : ∀ z, evaluate ⊤ s z = U.indicator (fun _ ↦ (1 : ℂ)) z) :
    U = ∅ ∨ U = Set.univ := by
  classical
  rcases evaluate_top_idempotent_eq_zero_or_one s hs with hzero | hone
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have := heval z
    simp [hzero z, hz] at this
  · right
    apply Set.eq_univ_of_forall
    intro z
    by_contra hz
    have := heval z
    simp [hone z, hz] at this

end AlgebraicGeometry.Point
