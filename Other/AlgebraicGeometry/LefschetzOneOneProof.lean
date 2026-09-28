/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.GAGAProper

/-!
# Proof of the rational Lefschetz (1, 1) theorem

This file is the final proof boundary. It proves the explicit-cycle proposition
`RationalLefschetzOneOne`, then derives the canonical proposition `LefschetzOneOne`.
-/

open CategoryTheory AlgebraicGeometry

@[expose] public noncomputable section

namespace AlgebraicGeometry.ComplexPoint

/-- The rational Lefschetz `(1, 1)` theorem in explicit-cycle form. -/
theorem _root_.rationalLefschetzOneOne : RationalLefschetzOneOne := by
  exact RationalLefschetzOneOne.of_analyticLineBundlesAlgebraize fun X ↦
    analyticLineBundlesAlgebraize X

/-- The rational Lefschetz `(1, 1)` theorem in the repository's canonical formulation. -/
theorem _root_.lefschetzOneOne : LefschetzOneOne :=
  rationalLefschetzOneOne.to_lefschetzOneOne

end AlgebraicGeometry.ComplexPoint

end
