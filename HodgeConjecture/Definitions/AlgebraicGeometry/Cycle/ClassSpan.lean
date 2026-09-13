/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.FundamentalClass

/-! # The span of normalized algebraic component classes -/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- The rational span of the normalized classes of the integral components of codimension `p`,
inside `H^(2p)(X; ℚ)`. -/
def algebraicCycleClassSpan
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) :
    Submodule ℚ (H^(2 * (p : ℤ))(X; ℚ)) :=
  ⨆ (x : X.left) (hx : coheight x = p),
    Submodule.span ℚ {cycleComponentSheafClass X x hx}

end AlgebraicGeometry.ComplexPoint
