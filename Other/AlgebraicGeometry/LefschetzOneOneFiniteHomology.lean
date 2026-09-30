/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.LefschetzOneOneReduction
public import Other.AlgebraicGeometry.ProjectiveFiniteHomology

/-!
# Lefschetz reduction using finite integral homology
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

/-- The rational Lefschetz `(1, 1)` theorem follows from finite generation of the second
integral homology of all analytic spaces together with the divisor representation of
unit-sheaf extensions. -/
theorem _root_.RationalLefschetzOneOne.of_finiteSecondHomology_of_divisor
    (hfin : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasFiniteSecondHomology X)
    (hdivisor : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasDivisorOfUnitExtension X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_obligations
    (fun X _ _ _ ↦ hasIntegralDenominatorClearing_of_hasFiniteSecondHomology X (hfin X)) hdivisor

/-- The rational Lefschetz `(1, 1)` theorem follows from finite good covers of all analytic
spaces together with the divisor representation of unit-sheaf extensions. Integral denominator
clearing is no longer an independent obligation. -/
theorem _root_.RationalLefschetzOneOne.of_finiteGoodCover_of_divisor
    (hcover : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasFiniteGoodCover X)
    (hdivisor : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasDivisorOfUnitExtension X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_obligations
    (fun X _ _ _ ↦ hasIntegralDenominatorClearing_of_hasFiniteGoodCover X (hcover X)) hdivisor

/-- The rational Lefschetz `(1, 1)` theorem follows from the divisor representation of unit-sheaf
extensions alone. -/
theorem _root_.RationalLefschetzOneOne.of_divisor
    (hdivisor : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasDivisorOfUnitExtension X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_obligations (fun X _ _ _ ↦ hasIntegralDenominatorClearing X) hdivisor

end AlgebraicGeometry.ComplexPoint
