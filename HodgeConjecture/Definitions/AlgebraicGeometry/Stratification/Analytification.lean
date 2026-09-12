/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.SingularLocusDimension
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Complex points of the constructed smooth decomposition

The finite algebraic decomposition induces an actual partition of complex-point sets into
the images of smooth complex schemes. The images are analytically locally closed. The
lifting assertion follows from the existing equivalence between complex points and closed
scheme points; it is not a supplied parametrization of a stratum.

No analytic triangulation, homology-dimension theorem, or frontier condition is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ))) {Y : Over (Spec (.of ℂ))}

local instance smoothStratificationAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

variable [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]

instance reducedClosedSmoothPiece_locallyOfFiniteType (T : Closeds X.left) :
    LocallyOfFiniteType (Over.mk (reducedClosedSmoothPieceι X.hom T ≫ X.hom)).hom := by
  change LocallyOfFiniteType (reducedClosedSmoothPieceι X.hom T ≫ X.hom)
  infer_instance

end AlgebraicGeometry.ComplexPoint
