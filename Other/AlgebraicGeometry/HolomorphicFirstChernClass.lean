/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponentialSequence
public import Other.AlgebraicGeometry.IntegralCohomology
public import Other.CategoryTheory.Sites.SheafCohomology.Connecting

/-!
# The connecting map of the holomorphic exponential sequence
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.ComplexPoint

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- The analytic first Chern-class connecting map of the holomorphic exponential sequence. -/
def holomorphicFirstChernClass :
    Sheaf.H.{0} (holomorphicUnitSheaf X d) 1 →+ H^2(X; ℤ) :=
  Sheaf.H.δ (holomorphicExponentialSequence_shortExact X d) 1

/-- The map on second cohomology induced by the inclusion of integers into holomorphic functions. -/
def integerToHolomorphicSecondCohomology :
    H^2(X; ℤ) →+ Sheaf.H.{0} (holomorphicAdditiveSheaf X d) 2 :=
  Sheaf.H.map (integerConstantsToHolomorphicSheaf X d) 2


end AlgebraicGeometry.ComplexPoint
