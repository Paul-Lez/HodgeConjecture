/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponentialSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# The connecting map of the holomorphic exponential sequence
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- The analytic first Chern-class connecting map of the holomorphic exponential sequence. -/
def holomorphicFirstChernClass :
    Abelian.Ext.{1} (𝓒(↧(ComplexPoint X); ℤ)) (holomorphicUnitSheaf X d) 1 →+
      Abelian.Ext.{1} (𝓒(↧(ComplexPoint X); ℤ)) (𝓒(↧(ComplexPoint X); ℤ)) 2 :=
  (holomorphicExponentialSequence_shortExact X d).extClass.postcomp
    (𝓒(↧(ComplexPoint X); ℤ)) rfl

/-- The map on second cohomology induced by the inclusion of integers into holomorphic functions. -/
def integerToHolomorphicSecondCohomology :
    Abelian.Ext.{1} (𝓒(↧(ComplexPoint X); ℤ)) (𝓒(↧(ComplexPoint X); ℤ)) 2 →+
      Abelian.Ext.{1} (𝓒(↧(ComplexPoint X); ℤ)) (holomorphicAdditiveSheaf X d) 2 :=
  (Abelian.Ext.mk₀ (integerConstantsToHolomorphicSheaf X d)).postcomp
    (𝓒(↧(ComplexPoint X); ℤ)) (add_zero 2)


end AlgebraicGeometry.ComplexPoint
