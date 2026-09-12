/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import HodgeConjecture.Mathlib.AlgebraicGeometry.GenericPoint
public import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-! # Codimension cycles

Integral cycles with support in a fixed codimension, before imposing any relations.
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The additive group of codimension-`p` algebraic cycles on `X`: the subgroup of algebraic cycles
whose points with nonzero coefficient all have coheight `p`. -/
def codimensionCycleSubgroup (X : Scheme.{u}) (p : ℕ) : AddSubgroup (AlgebraicCycle X ℤ) where
  carrier c := ∀ x, c x ≠ 0 → coheight x = p
  zero_mem' x hx := (hx rfl).elim
  add_mem' := by
    intro a b ha hb x hx
    by_cases hax : a x = 0
    · exact hb x (by simpa [hax] using hx)
    · exact ha x hax
  neg_mem' := by
    intro a ha x hx
    refine ha x fun h ↦ hx ?_
    change -(a x) = 0
    simp [h]

instance (X : Scheme.{u}) (p : ℕ) : CoeFun (codimensionCycleSubgroup X p) (fun _ ↦ X → ℤ) where
  coe c := c.1

namespace codimensionCycleSubgroup

variable {X : Scheme.{u}} {p : ℕ}

@[ext]
lemma ext {a b : codimensionCycleSubgroup X p} (h : ∀ x, a.1 x = b.1 x) : a = b :=
  Subtype.ext (Function.locallyFinsuppWithin.ext h)

/-- The cycle with coefficient `n` at one point and zero elsewhere. -/
noncomputable def single (x : X) (hx : coheight x = p) (n : ℤ) : codimensionCycleSubgroup X p :=
  by
    classical
    exact ⟨Function.locallyFinsuppWithin.single x n, by
      intro y hy
      by_cases h : y = x
      · simpa [h] using hx
      · simp [Function.locallyFinsuppWithin.single_apply, h] at hy⟩

@[simp]
lemma single_apply [DecidableEq X] (x : X) (hx : coheight x = p) (n : ℤ) (y : X) :
    single x hx n y = if y = x then n else 0 := by
  simp [single, Function.locallyFinsuppWithin.single_apply]

@[simp]
lemma single_same (x : X) (hx : coheight x = p) (n : ℤ) : single x hx n x = n := by
  classical
  simp

@[simp]
lemma single_zero (x : X) (hx : coheight x = p) : single x hx 0 = 0 := by
  classical
  ext
  simp

/-- Every point of the spectrum of a field has codimension zero. -/
lemma specField_coheight (K : Type u) [Field K] (x : Spec ↧K) : coheight x = 0 := by
  refine Order.IsMax.coheight_eq_zero fun y _ ↦ ?_
  rw [Subsingleton.elim y x]

end codimensionCycleSubgroup

/-- The inclusion of pure codimension cycles into all algebraic cycles. -/
def codimensionCycleInclusion (X : Scheme.{u}) (p : ℕ) :
    codimensionCycleSubgroup X p →+ AlgebraicCycle X ℤ :=
  (codimensionCycleSubgroup X p).subtype

end AlgebraicGeometry
