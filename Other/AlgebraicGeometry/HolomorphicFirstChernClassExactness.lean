/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicFirstChernClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The image of the holomorphic first Chern class
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- An integral cohomology class lifts through the analytic Chern-class connecting map exactly
when its image in the second cohomology of holomorphic functions vanishes. -/
theorem exists_holomorphicFirstChernClass_iff
    (α : H^2(X; ℤ)) :
    (∃ β, holomorphicFirstChernClass X d β = α) ↔
      integerToHolomorphicSecondCohomology X d α = 0 := by
  constructor
  · rintro ⟨β, rfl⟩
    change (β.comp (holomorphicExponentialSequence_shortExact X d).extClass rfl).comp
      (Abelian.Ext.mk₀ (holomorphicExponentialSequence X d).f) (add_zero 2) = 0
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
      ShortComplex.ShortExact.extClass_comp, Abelian.Ext.comp_zero]
  · intro hα
    exact Abelian.Ext.covariant_sequence_exact₁
      _ (holomorphicExponentialSequence_shortExact X d) α hα rfl

end AlgebraicGeometry.ComplexPoint
