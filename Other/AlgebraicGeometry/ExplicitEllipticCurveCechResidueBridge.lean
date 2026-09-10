/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCurveCechRepresentative

/-!
# A residue detector for the explicit elliptic Cech class

This file isolates all Mayer--Vietoris and Ext bookkeeping from the analytic
residue calculation.  An additive functional on the overlap which kills the
two-chart coboundaries and is nonzero on the adjusted representative proves
the corresponding actual sheaf extension nonzero.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

/-- The residue-friendly algebraic representative `(x²+1)/y`, regarded as an
actual holomorphic function on the analytic overlap. -/
def curveCechAdjustedHolomorphicRepresentative :
    OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap) :=
  curveCechOpenFunctionAddEquiv
    (regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
      curveCechAdjustedRegularRepresentative)

/-- An additive overlap functional which kills every two-chart coboundary
detects a nonzero curve Mayer--Vietoris extension. -/
theorem curveHolomorphicCechClass_ne_zero_of_addHom
    (c : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap))
    (residue :
      OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap) →+ ℂ)
    (residue_coboundary : ∀
      (a : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen 0)))
      (b : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen 1))),
      residue (curveCechCoboundary a b) = 0)
    (residue_c : residue c ≠ 0) :
    curveHolomorphicCechClass c ≠ 0 := by
  intro hc
  obtain ⟨a, b, hab⟩ :=
    (analyticTransitionExtClass_eq_zero_iff curveVariety
      (holomorphicAdditiveFunctionSheaf curveVariety 1)
      (curveCechOpen 0) (curveCechOpen 1) curveCechOpen_cover c).mp hc
  apply residue_c
  rw [← hab]
  exact residue_coboundary a b

/-- Exact analytic interface for proving the adjusted representative's
degree-one Cech class nonzero. -/
theorem curveAdjustedHolomorphicCechClass_ne_zero_of_residue
    (residue :
      OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap) →+ ℂ)
    (residue_coboundary : ∀
      (a : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen 0)))
      (b : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen 1))),
      residue (curveCechCoboundary a b) = 0)
    (residue_adjusted : residue curveCechAdjustedHolomorphicRepresentative ≠ 0) :
    curveHolomorphicCechClass curveCechAdjustedHolomorphicRepresentative ≠ 0 :=
  curveHolomorphicCechClass_ne_zero_of_addHom
    curveCechAdjustedHolomorphicRepresentative residue
    residue_coboundary residue_adjusted

end AlgebraicGeometry.ExplicitEllipticCandidate
