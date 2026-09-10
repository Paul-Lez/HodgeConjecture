/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponentialSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The connecting map of the holomorphic exponential sequence

We construct the map `H¹(𝒪ˣ) → H²(ℤ)` and characterize its image as the kernel of
`H²(ℤ) → H²(𝒪)`. Cohomology here is expressed as Ext from the constant integer sheaf.
This is the analytic lifting step in the exponential-sequence proof of Lefschetz `(1, 1)`.
Identifying `H¹(𝒪ˣ)` with line bundles and comparing with divisor cycle classes are separate steps.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- The analytic first Chern-class connecting map of the holomorphic exponential sequence. -/
def holomorphicFirstChernClass :
    Abelian.Ext.{1} (constantIntegerSheaf X) (holomorphicUnitSheaf X d) 1 →+
      Abelian.Ext.{1} (constantIntegerSheaf X) (constantIntegerSheaf X) 2 :=
  (holomorphicExponentialSequence_shortExact X d).extClass.postcomp
    (constantIntegerSheaf X) rfl

/-- The map on second cohomology induced by the inclusion of integers into holomorphic functions. -/
def integerToHolomorphicSecondCohomology :
    Abelian.Ext.{1} (constantIntegerSheaf X) (constantIntegerSheaf X) 2 →+
      Abelian.Ext.{1} (constantIntegerSheaf X) (holomorphicAdditiveSheaf X d) 2 :=
  (Abelian.Ext.mk₀ (integerConstantsToHolomorphicSheaf X d)).postcomp
    (constantIntegerSheaf X) (add_zero 2)

set_option backward.isDefEq.respectTransparency false in
/-- An integral cohomology class lifts through the analytic Chern-class connecting map exactly
when its image in the second cohomology of holomorphic functions vanishes. -/
theorem exists_holomorphicFirstChernClass_iff
    (α : Abelian.Ext.{1} (constantIntegerSheaf X) (constantIntegerSheaf X) 2) :
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
      (constantIntegerSheaf X) (holomorphicExponentialSequence_shortExact X d) α hα rfl

end AlgebraicGeometry.ComplexPoint
