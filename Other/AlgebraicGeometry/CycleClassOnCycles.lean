/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CodimensionCycle
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Additive extension of component classes to cycles -/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- On a compact scheme, regard a locally finite integral algebraic cycle as a finitely supported
function. -/
def compactCycleToFinsupp {X : Scheme.{u}} [CompactSpace X] :
    AlgebraicCycle X ℤ →+ X →₀ ℤ where
  toFun c := Finsupp.ofSupportFinite c
    (by
      simpa using c.locallyFiniteSupport.finite_inter_support_of_isCompact
        (W := Set.univ) isCompact_univ)
  map_zero' := by
    ext
    rfl
  map_add' _ _ := by
    ext
    rfl

@[simp] lemma compactCycleToFinsupp_apply {X : Scheme.{u}} [CompactSpace X]
    (c : AlgebraicCycle X ℤ) (x : X) : compactCycleToFinsupp c x = c x :=
  rfl

/-- Extend prescribed classes of irreducible codimension-`p` components additively to integral
codimension-`p` cycles. Values away from codimension `p` are set to zero; the support condition on
a `codimensionCycleSubgroup` ensures that this branch is never used by a nonzero coefficient. -/
def cycleClassOnCyclesOfComponents {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M) :
    codimensionCycleSubgroup X p →+ M := by
  classical
  let componentValue : X → M := fun x ↦
    if hx : coheight x = p then componentClass x hx else 0
  exact (Finsupp.linearCombination ℤ componentValue).toAddMonoidHom.comp
    ((compactCycleToFinsupp (X := X)).comp (codimensionCycleInclusion X p))

/-- The additive extension sends a one-component cycle to its coefficient times the prescribed
component class. -/
@[simp] lemma cycleClassOnCyclesOfComponents_single
    {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (x : X) (hx : coheight x = p) (n : ℤ) :
    cycleClassOnCyclesOfComponents componentClass
        (codimensionCycleSubgroup.single x hx n) =
      n • componentClass x hx := by
  classical
  change (Finsupp.linearCombination ℤ (fun y ↦
      if hy : coheight y = p then componentClass y hy else 0))
    (compactCycleToFinsupp ((codimensionCycleInclusion X p)
      (codimensionCycleSubgroup.single x hx n))) = n • componentClass x hx
  have hsingle : compactCycleToFinsupp
      ((codimensionCycleInclusion X p) (codimensionCycleSubgroup.single x hx n)) =
      Finsupp.single x n := by
    ext y
    change codimensionCycleSubgroup.single x hx n y = Finsupp.single x n y
    rw [codimensionCycleSubgroup.single_apply, Finsupp.single_apply]
    by_cases h : y = x
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hsingle, Finsupp.linearCombination_single, dif_pos hx]

end AlgebraicGeometry
