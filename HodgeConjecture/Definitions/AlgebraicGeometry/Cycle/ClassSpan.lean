/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SheafClass

/-! # The span of normalized algebraic component classes -/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- The rational span of the actually constructed codimension-`p` component classes.

The relative dimension is the canonical `dim X`, whose certificate is proved from smoothness and
integrality. This definition spans explicit normalized component classes. -/
def algebraicCycleClassSpan
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) :
    Submodule ℚ (H^(2 * (p : ℤ))(X; ℚ)) :=
  ⨆ (x : X.left) (hx : coheight x = p),
    Submodule.span ℚ {cycleComponentSheafClass X x hx}

end AlgebraicGeometry.ComplexPoint
