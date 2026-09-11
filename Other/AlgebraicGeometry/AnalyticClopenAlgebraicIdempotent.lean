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
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Algebraic idempotents and subsets of complex points

An idempotent global regular function on an integral scheme is zero or one. Consequently,
a subset whose characteristic function is the evaluation of such a section is empty or full.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Point

/-- A regular function on a reduced complex scheme locally of finite type is determined by
its values at complex points. -/
theorem section_eq_zero_of_evaluate_eq_zero
    {X : Over (Spec (CommRingCat.of ℂ))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] {U : X.left.Opens} (s : Γ(X.left, U))
    (hs : ∀ z : Point ℂ X, z ∈ overOpen U → evaluate U s z = 0) : s = 0 := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply eq_zero_of_basicOpen_eq_bot s
  apply TopologicalSpace.Opens.ext
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (X := X.left) (Z := (X.left.basicOpen s : Set X.left)) ⟨x, hx⟩
    (X.left.basicOpen s).isOpen.isLocallyClosed
  let p := (pointEquivClosedPoint X.hom).symm ⟨y, hyclosed⟩
  let z : Point ℂ X := Over.homMk p.1 p.2
  have hz : z.underlying = y := congrArg Subtype.val
    ((pointEquivClosedPoint X.hom).apply_symm_apply ⟨y, hyclosed⟩)
  have hzbasic : z ∈ overOpen (X.left.basicOpen s) := by
    change z.underlying ∈ X.left.basicOpen s
    rwa [hz]
  have hzU : z ∈ overOpen U := X.left.basicOpen_le s hzbasic
  exact (mem_overOpen_basicOpen_iff_evaluate_ne_zero s z hzU).mp hzbasic (hs z hzU)

/-- Evaluation on complex points detects equality of regular functions on a reduced scheme
locally of finite type. -/
theorem evaluateOnOpen_injective
    {X : Over (Spec (CommRingCat.of ℂ))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] (U : X.left.Opens) :
    Function.Injective (fun s : Γ(X.left, U) => evaluateOnOpen U s) := by
  intro s t h
  apply sub_eq_zero.mp
  apply section_eq_zero_of_evaluate_eq_zero (s - t)
  intro z hz
  rw [← evaluationHom_hom_apply U ⟨z, hz⟩, map_sub]
  apply sub_eq_zero.mpr
  exact congrFun h ⟨z, hz⟩

/-- Pointwise idempotence of a regular function implies algebraic idempotence. -/
theorem isIdempotentElem_of_evaluate
    {X : Over (Spec (CommRingCat.of ℂ))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] {U : X.left.Opens} (s : Γ(X.left, U))
    (hs : ∀ z : Point ℂ X, z ∈ overOpen U →
      evaluate U s z * evaluate U s z = evaluate U s z) : IsIdempotentElem s := by
  apply evaluateOnOpen_injective U
  funext z
  change (evaluationHom U z).hom (s * s) = (evaluationHom U z).hom s
  rw [map_mul]
  rw [show (evaluationHom U z).hom s = evaluate U s z.1 from
    evaluationHom_hom_apply U z s]
  exact hs z.1 z.2

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

/-- An indicator represented by a global regular function on an integral complex scheme
locally of finite type is trivial; algebraic idempotence follows from its pointwise values. -/
theorem eq_empty_or_univ_of_indicator_eq_regular
    [LocallyOfFiniteType X.hom] (U : Set (Point ℂ X)) (s : Γ(X.left, ⊤))
    (heval : ∀ z, evaluate ⊤ s z = U.indicator (fun _ ↦ (1 : ℂ)) z) :
    U = ∅ ∨ U = Set.univ := by
  classical
  apply eq_empty_or_univ_of_indicator_eq_evaluate U s ?_ heval
  apply isIdempotentElem_of_evaluate
  intro z _
  rw [heval]
  by_cases hz : z ∈ U <;> simp [hz]

end AlgebraicGeometry.Point
