/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SingularClosedFiltration
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothLocus
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.SourceOpen
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.ClosedPointDimension

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The smooth locus of a cycle component as a closed subscheme

The smooth locus of the cycle component at `x` is closed in the open subscheme of `X.left`
obtained by deleting the image of the singular locus. This file records that open, the closed
immersion of the smooth locus into it, and the complex points of `X` in it.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (x : X.left)

/-- The open subscheme of `X.left` in which the smooth locus of the cycle component at `x` is
closed: the complement of the image of the singular locus. -/
def cycleComponentSmoothLocusAmbientOpen : X.left.Opens :=
  closedImmersionSourceOpenTarget (X.left.pointClosureι x) (cycleComponentSmoothLocus X x)

/-- The open `cycleComponentSmoothLocusAmbientOpen X x`, over `ℂ`. -/
abbrev cycleComponentSmoothLocusAmbientOpenOver : Over (Spec ↧ℂ) :=
  ComplexPoint.openScheme X (cycleComponentSmoothLocusAmbientOpen X x)

/-- The smooth locus of the cycle component at `x` as a closed subscheme of
`cycleComponentSmoothLocusAmbientOpen X x`, over `ℂ`. -/
def cycleComponentSmoothLocusClosedLiftOver :
    cycleComponentSmoothLocusOver X x ⟶ cycleComponentSmoothLocusAmbientOpenOver X x :=
  Over.homMk
    (closedImmersionSourceOpenLift (X.left.pointClosureι x) (cycleComponentSmoothLocus X x)) (by
      change closedImmersionSourceOpenLift _ _ ≫
        (closedImmersionSourceOpenTarget (X.left.pointClosureι x)
          (cycleComponentSmoothLocus X x)).ι ≫ X.hom =
            (cycleComponentSmoothLocus X x).ι ≫ X.left.pointClosureι x ≫ X.hom
      rw [← Category.assoc, closedImmersionSourceOpenLift_ι, Category.assoc])

instance : IsClosedImmersion (cycleComponentSmoothLocusClosedLiftOver X x).left :=
  inferInstanceAs (IsClosedImmersion (closedImmersionSourceOpenLift _ _))

@[reassoc (attr := simp)]
theorem cycleComponentSmoothLocusClosedLiftOver_openInclusion :
    cycleComponentSmoothLocusClosedLiftOver X x ≫
        ComplexPoint.openInclusion X (cycleComponentSmoothLocusAmbientOpen X x) =
      ComplexPoint.openInclusion (cycleComponentOver X x) (cycleComponentSmoothLocus X x) ≫
        cycleComponentOverι X x :=
  Over.OverMorphism.ext (closedImmersionSourceOpenLift_ι _ _)

namespace ComplexPoint

/-- The open `X(ℂ) \ Z_sing(ℂ)`, where `Z` is the closure of `x` and `Z_sing` its singular
locus. -/
def cycleComponentSmoothSupportAmbientOpen : Opens (ComplexPoint X) :=
  ⟨Point.overOpen (cycleComponentSmoothLocusAmbientOpen X x), Point.isOpen_overOpen _⟩

@[simp]
lemma coe_cycleComponentSmoothSupportAmbientOpen :
    (cycleComponentSmoothSupportAmbientOpen X x : Set (ComplexPoint X)) =
      Point.overOpen (cycleComponentSmoothLocusAmbientOpen X x) :=
  rfl

@[simp]
lemma mem_cycleComponentSmoothSupportAmbientOpen {z : ComplexPoint X} :
    z ∈ cycleComponentSmoothSupportAmbientOpen X x ↔
      z.underlying ∈ cycleComponentSmoothLocusAmbientOpen X x :=
  Iff.rfl

end ComplexPoint

end AlgebraicGeometry
