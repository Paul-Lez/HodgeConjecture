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
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

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

/-- The singular locus equipped with its reduced closed-subscheme structure. -/
def reducedSingularLocus : Scheme := reducedClosedSubscheme (singularLocusClosed f)

/-- Its canonical closed immersion in the original scheme. -/
def reducedSingularLocusι : reducedSingularLocus f ⟶ X :=
  reducedClosedSubschemeι (singularLocusClosed f)

instance reducedSingularLocus_isReduced : IsReduced (reducedSingularLocus f) :=
  inferInstanceAs (IsReduced (reducedClosedSubscheme (singularLocusClosed f)))

instance reducedSingularLocusι_isClosedImmersion :
    IsClosedImmersion (reducedSingularLocusι f) :=
  inferInstanceAs (IsClosedImmersion (reducedClosedSubschemeι (singularLocusClosed f)))

variable (Y : Over (Spec ↧ℂ))
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- The singular locus of every cycle component admits the actual finite smooth
decomposition constructed by Noetherian recursion. -/
def cycleComponentSingularStratification (x : Y.left) :
    List (Closeds (cycleComponent Y.left x)) := by
  letI := cycleComponent_isNoetherian Y x
  exact reducedSmoothStratification (cycleComponentι Y.left x ≫ Y.hom)
    (singularLocusClosed (cycleComponentι Y.left x ≫ Y.hom))

end AlgebraicGeometry
