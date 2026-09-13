/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Topology.Dimension.ClosedSubset
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.Basic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.Dimension

/-!
# The singular locus has smaller algebraic dimension

Over a perfect field the complement of the smooth locus of a reduced irreducible scheme is
a proper closed subset. This file constructs that reduced closed subscheme and proves its
strict Krull-dimension bound, including the `d - p` bound for cycle components. The bounds
are on algebraic dimension throughout.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- The closed complement of the actual smooth locus. -/
def singularLocusClosed : Closeds X := f.smoothLocus.compl

variable (Y : Over (Spec (.of ℂ)))
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

end AlgebraicGeometry
