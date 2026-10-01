/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothClosedLift

/-!
# Purity along the smooth locus of an integral cycle component

The local relative-cohomology sheaves with support in the cycle component vanish away from degree
`2p` on the complement of its canonical singular boundary. This follows from normal
neighborhoods of the smooth-locus closed lift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is the analytic open subset `X(ℂ) \ Z_sing(ℂ)`, on which the
remaining support is the complex manifold `Z_reg(ℂ)`. -/
abbrev cycleComponentSmoothSupportAmbientOpen : Opens (ComplexPoint X) :=
  -- `X(ℂ) \ Z_sing(ℂ)`.
  (cycleComponentSingularAnalyticClosedFiltration X x 0).compl

end AlgebraicGeometry.ComplexPoint
