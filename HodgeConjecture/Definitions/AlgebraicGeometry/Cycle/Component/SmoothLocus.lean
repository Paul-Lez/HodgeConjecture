/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Support
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Locus

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The smooth locus of a cycle component

The smooth locus of the cycle component at `x` is an open subscheme of `X.left.pointClosure x`,
smooth over `ℂ`. This file bundles it over `ℂ` as an open subscheme of `cycleComponentOver X x`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ)) (x : X.left)
  [LocallyOfFinitePresentation (X.left.pointClosureι x ≫ X.hom)]

/-- The smooth locus of the cycle component at `x`. -/
abbrev cycleComponentSmoothLocus : (X.left.pointClosure x).Opens :=
  (X.left.pointClosureι x ≫ X.hom).smoothLocus

/-- The smooth locus of the cycle component at `x`, over `ℂ`. -/
abbrev cycleComponentSmoothLocusOver : Over (Spec ↧ℂ) :=
  ComplexPoint.openScheme (cycleComponentOver X x) (cycleComponentSmoothLocus X x)

instance : Smooth (cycleComponentSmoothLocusOver X x).hom :=
  inferInstanceAs (Smooth ((cycleComponentSmoothLocus X x).ι ≫ X.left.pointClosureι x ≫ X.hom))

end AlgebraicGeometry
