module

public import KirovDolbeault.HodgeBridgeProbe
public import Other.AlgebraicGeometry.ExplicitEllipticCurveCechRepresentative

@[expose] public noncomputable section

/-!
# Residue detector interface for the explicit elliptic Cech class

This scratch module states the exact interface between a local residue
construction and the project's Mayer--Vietoris extension class.  All sheaf
and Ext bookkeeping is discharged here; the remaining hypotheses are the two
analytic residue facts for the selected curve charts.
-/

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

/-- Exact final interface for the adjusted representative.  A construction
of this `residue` and the two displayed properties proves the desired
degree-one analytic Cech class nonzero. -/
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
