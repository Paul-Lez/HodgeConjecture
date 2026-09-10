/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfacePointProduct
public import Other.AlgebraicGeometry.HolomorphicFunctionPullback

/-!
# Holomorphic pullback along the explicit elliptic-surface projections

This specializes functorial pullback of holomorphic functions to the two projections from the
explicit self-product surface to the elliptic curve.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

/-- Pullback of holomorphic functions along the first surface projection. -/
def surfaceFstHolomorphicFunctionPullback :
    ComplexPoint.holomorphicFunctionSheaf curveVariety 1 ⟶
      (TopCat.Sheaf.pushforward CommRingCat
        (ComplexPoint.analyticMapTopCat surfaceVariety curveVariety surfaceVarietyFst)).obj
        (ComplexPoint.holomorphicFunctionSheaf surfaceVariety 2) :=
  ComplexPoint.holomorphicFunctionSheafToPushforward
    surfaceVariety curveVariety surfaceVarietyFst 2 1

/-- Pullback of holomorphic functions along the second surface projection. -/
def surfaceSndHolomorphicFunctionPullback :
    ComplexPoint.holomorphicFunctionSheaf curveVariety 1 ⟶
      (TopCat.Sheaf.pushforward CommRingCat
        (ComplexPoint.analyticMapTopCat surfaceVariety curveVariety surfaceVarietySnd)).obj
        (ComplexPoint.holomorphicFunctionSheaf surfaceVariety 2) :=
  ComplexPoint.holomorphicFunctionSheafToPushforward
    surfaceVariety curveVariety surfaceVarietySnd 2 1

/-- Additive pullback along the first surface projection. -/
def surfaceFstHolomorphicAdditivePullback :
    ComplexPoint.holomorphicAdditiveFunctionSheaf curveVariety 1 ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat
        (ComplexPoint.analyticMapTopCat surfaceVariety curveVariety surfaceVarietyFst)).obj
        (ComplexPoint.holomorphicAdditiveFunctionSheaf surfaceVariety 2) :=
  ComplexPoint.holomorphicAdditiveFunctionSheafToPushforward
    surfaceVariety curveVariety surfaceVarietyFst 2 1

/-- Additive pullback along the second surface projection. -/
def surfaceSndHolomorphicAdditivePullback :
    ComplexPoint.holomorphicAdditiveFunctionSheaf curveVariety 1 ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat
        (ComplexPoint.analyticMapTopCat surfaceVariety curveVariety surfaceVarietySnd)).obj
        (ComplexPoint.holomorphicAdditiveFunctionSheaf surfaceVariety 2) :=
  ComplexPoint.holomorphicAdditiveFunctionSheafToPushforward
    surfaceVariety curveVariety surfaceVarietySnd 2 1

end AlgebraicGeometry.ExplicitEllipticCandidate
