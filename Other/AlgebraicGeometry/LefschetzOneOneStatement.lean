/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.LefschetzOneOne
public import Other.AlgebraicGeometry.Cycle.SheafClass

/-!
# Rational Lefschetz (1, 1): explicit-cycle statement

This file contains the stronger specification used by the proof. Unlike `LefschetzOneOne`, which
asserts membership in the span of algebraic cycle classes, `RationalLefschetzOneOne` returns an
explicit rational codimension-one cycle whose constructed cycle class is the given Hodge class.

No implication from the Hodge conjecture and no GAGA, exponential-sequence, or divisor argument is
defined here.
-/

open CategoryTheory AlgebraicGeometry ComplexPoint

/-- The explicit-cycle rational Lefschetz `(1, 1)` statement for smooth projective integral
complex schemes. -/
@[expose] public def RationalLefschetzOneOne : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (α : H^2(X; ℚ)),
    α ∈ Hdg^1(X; ℚ) →
      ∃ D : TensorProduct ℤ ℚ (codimensionCycleSubgroup X.left 1),
        rationalSheafCycleClassOnCycles
          { scheme := X.left, structureMap := X.hom } 1 D = α
