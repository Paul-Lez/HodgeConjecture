/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Mathlib.AlgebraicGeometry.AlgebraicCycle.Weight
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Additive extension of component classes to cycles -/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace Function.locallyFinsupp

namespace AlgebraicGeometry

universe u

/-- Extend prescribed classes of irreducible codimension-`p` components additively to integral
codimension-`p` cycles. Values away from codimension `p` are set to zero; the support condition on
`AlgebraicCycle.codimSubgroup` ensures that this branch is never used by a nonzero coefficient. -/
def cycleClassOnCyclesOfComponents {X : Scheme.{u}} [CompactSpace X] {p : ℕ} {M : Type*}
    [AddCommGroup M] (componentClass : ∀ (x : X), coheight x = p → M) :
    AlgebraicCycle.codimSubgroup X ℤ p →+ M :=
  let componentValue : X → M := fun x ↦
    if hx : coheight x = p then componentClass x hx else 0
  (Finsupp.linearCombination ℤ componentValue).toAddMonoidHom.comp
    (toFinsuppAddMonoidHom.comp (AlgebraicCycle.codimSubgroup X ℤ p).subtype)

/-- The additive extension sends a one-component cycle to its coefficient times the prescribed
component class. -/
@[simp] lemma cycleClassOnCyclesOfComponents_single {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M] (componentClass : ∀ (x : X), coheight x = p → M) (x : X)
    (hx : coheight x = p) (n : ℤ) :
    cycleClassOnCyclesOfComponents componentClass (supported.single x hx n) =
      n • componentClass x hx := by
  simp [cycleClassOnCyclesOfComponents, supported.single, hx]

end AlgebraicGeometry
