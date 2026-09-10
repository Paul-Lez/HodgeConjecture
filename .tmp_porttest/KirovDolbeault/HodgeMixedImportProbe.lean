module

public import KirovDolbeault.HodgeBridgeProbe
public import Other.AlgebraicGeometry.ExplicitEllipticCurveCechRepresentative

@[expose] public noncomputable section

/-!
# Mixed residue/elliptic bridge probe

This scratch module verifies that the module-converted local residue kernel can
coexist with the project's analytic elliptic Cech construction under Lean 4.33.
It deliberately stays outside the production import graph while the remaining
global residue input is evaluated.
-/

open Complex

namespace AlgebraicGeometry.ExplicitEllipticCandidate

/-- The scalar local residue evaluator which the elliptic Cech detector will
use after reading an overlap form in the coordinate `u = X/Y` at infinity. -/
abbrev curveLocalResidueAtInfinity :=
  Jacobians.Dolbeault.puncturedResidue 0

/-- The local normal form of the adjusted representative has the required
nonzero residue. -/
theorem curveLocalResidue_neg_inv :
    Jacobians.Dolbeault.resAt (fun z : ℂ => -(z⁻¹)) 0 = -1 :=
  Jacobians.Dolbeault.puncturedResidue_neg_inv

end AlgebraicGeometry.ExplicitEllipticCandidate
