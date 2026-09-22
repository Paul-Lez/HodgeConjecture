/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Support
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Locus

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The smooth locus of a cycle component

The smooth locus of the cycle component at `x` is an open subscheme of `X.left.pointClosure x`,
smooth over `ℂ`. This file bundles it over `ℂ` as an open subscheme of `over X x`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.CycleComponent

variable (X : Over (Spec ↧ℂ)) (x : X.left)
  [LocallyOfFinitePresentation (X.left.pointClosureι x ≫ X.hom)]

/-- The smooth locus of the cycle component at `x`. -/
abbrev smoothLocus : (X.left.pointClosure x).Opens :=
  (X.left.pointClosureι x ≫ X.hom).smoothLocus

/-- The smooth locus of the cycle component at `x`, over `ℂ`. -/
abbrev smoothLocusOver : Over (Spec ↧ℂ) :=
  ComplexPoint.openScheme (over X x) (smoothLocus X x)

instance : Smooth (smoothLocusOver X x).hom :=
  inferInstanceAs (Smooth ((smoothLocus X x).ι ≫ X.left.pointClosureι x ≫ X.hom))

end AlgebraicGeometry.CycleComponent
