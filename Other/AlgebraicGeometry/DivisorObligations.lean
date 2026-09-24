/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.LefschetzOneOneReduction
public import Other.AlgebraicGeometry.DivisorClassComparison

/-!
# Divisor–Chern compatibility in the Lefschetz reduction
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] isNoetherian_of_isProjective

/-- The third obligation of the Lefschetz `(1, 1)` reduction follows from the cycle-class
comparison for the divisor of a rational section alone: the existence of that divisor is
proved. -/
theorem hasDivisorOfAlgebraicModel_of_divisorClass
    (hclass : HasDivisorClassOfSomeCartierData X) : HasDivisorOfAlgebraicModel X := by
  intro E L hL e
  obtain ⟨c, _, hc⟩ := hclass E L hL e
  exact ⟨c.divisor, hc⟩

end AlgebraicGeometry.ComplexPoint
