/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Statement
public import Other.AlgebraicGeometry.ChernRelativeFinalAssembly
public import Other.AlgebraicGeometry.DivisorObligations
public import Other.AlgebraicGeometry.GAGAProper
public import Other.AlgebraicGeometry.GAGAtoLefschetz
public import Other.AlgebraicGeometry.LefschetzOneOneReduction
public import Other.AlgebraicGeometry.ProjectiveFiniteHomology

/-!
# Rational Lefschetz (1, 1)

This file states and proves the rational Lefschetz `(1, 1)` theorem for smooth projective
integral schemes over `ℂ`. It does not assert the stronger integral identification with the
image of the first Chern class map from the Picard group, the reverse inclusion, or the theorem
for compact Kähler manifolds.

## Reference

* [P. Deligne, *The Hodge Conjecture*, §2(iii)]
  (https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint

/-- Every rational degree-two Hodge class on a smooth projective integral complex scheme lies
in the span of codimension-one algebraic cycle classes. -/
theorem lefschetzOneOne
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Hdg^1(X; ℚ) ≤ algebraicCycleClassSpan X 1 := by
  intro α hα
  obtain ⟨D, rfl⟩ :=
    exists_rationalSheafCycleClassOnCycles_eq_of_obligations X
      (hasIntegralDenominatorClearing X)
      (hasDivisorOfUnitExtension_of_algebraicModel X
        (hasAlgebraicModel_of_analyticLineBundlesAlgebraize X
          (analyticLineBundlesAlgebraize X))
        (hasDivisorOfAlgebraicModel_of_divisorClass X
          (hasDivisorClassOfSomeCartierData_of_cartierData X
            (hasDivisorClassOfCartierData (X := X))))) α hα
  exact rationalSheafCycleClassOnCycles_mem_algebraicCycleClassSpan X 1 D

end
