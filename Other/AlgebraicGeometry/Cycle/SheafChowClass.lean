/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cycle.ChowClass
public import Other.AlgebraicGeometry.Cycle.SheafClass

/-!
# Sheaf cycle classes on Chow groups

This file begins the descent of the constructed sheaf cycle-class map through rational
equivalence. Codimension zero is unconditional; positive codimension requires principal-divisor
vanishing on closed carriers.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ComplexPoint

/-- The sheaf cycle-class map kills rational equivalences in codimension zero. -/
theorem rationalEquivalenceSubgroup_le_sheafCycleClassOnCycles_zero_ker
    (V : SmoothProjectiveComplexVariety) :
    rationalEquivalenceSubgroup V.scheme 0 ≤
      (sheafCycleClassOnCycles V 0).ker := by
  rw [rationalEquivalenceSubgroup_zero]
  exact bot_le

/-- The integral codimension-zero sheaf cycle-class map on the Chow group. -/
def codimensionZeroSheafCycleClassOnChow (V : SmoothProjectiveComplexVariety) :
    ChowGroup V.scheme 0 →+ H^0(V.over; ℚ) :=
  ChowGroup.lift (sheafCycleClassOnCycles V 0)
    (rationalEquivalenceSubgroup_le_sheafCycleClassOnCycles_zero_ker V)

@[simp]
lemma codimensionZeroSheafCycleClassOnChow_mk
    (V : SmoothProjectiveComplexVariety)
    (z : codimensionCycleSubgroup V.scheme 0) :
    codimensionZeroSheafCycleClassOnChow V (ChowGroup.mk z) =
      sheafCycleClassOnCycles V 0 z :=
  ChowGroup.lift_mk _ _ _

/-- The rational codimension-zero sheaf cycle-class map on the Chow group. -/
def rationalCodimensionZeroSheafCycleClassOnChow
    (V : SmoothProjectiveComplexVariety) :
    RationalChowGroup V.scheme 0 →ₗ[ℚ] H^0(V.over; ℚ) :=
  ChowGroup.rationalExtension (codimensionZeroSheafCycleClassOnChow V)

end AlgebraicGeometry.ComplexPoint
