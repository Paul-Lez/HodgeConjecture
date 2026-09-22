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

namespace AlgebraicGeometry.CycleComponent

variable (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (x : X.left)

/-- The open subscheme of `X.left` in which the smooth locus of the cycle component at `x` is
closed: the complement of the image of the singular locus. -/
def smoothAmbientOpen : X.left.Opens :=
  closedImmersionSourceOpenTarget (X.left.pointClosureι x) (smoothLocus X x)

/-- The open `smoothAmbientOpen X x`, over `ℂ`. -/
abbrev smoothAmbientOpenOver : Over (Spec ↧ℂ) :=
  ComplexPoint.openScheme X (smoothAmbientOpen X x)

/-- The smooth locus of the cycle component at `x` as a closed subscheme of
`smoothAmbientOpen X x`, over `ℂ`. -/
def smoothClosedLift :
    smoothLocusOver X x ⟶ smoothAmbientOpenOver X x :=
  Over.homMk
    (closedImmersionSourceOpenLift (X.left.pointClosureι x) (smoothLocus X x)) (by
      change closedImmersionSourceOpenLift _ _ ≫
        (closedImmersionSourceOpenTarget (X.left.pointClosureι x)
          (smoothLocus X x)).ι ≫ X.hom =
            (smoothLocus X x).ι ≫ X.left.pointClosureι x ≫ X.hom
      rw [← Category.assoc, closedImmersionSourceOpenLift_ι, Category.assoc])

instance : IsClosedImmersion (smoothClosedLift X x).left :=
  inferInstanceAs (IsClosedImmersion (closedImmersionSourceOpenLift _ _))

@[reassoc (attr := simp)]
theorem smoothClosedLift_openInclusion :
    smoothClosedLift X x ≫
        ComplexPoint.openInclusion X (smoothAmbientOpen X x) =
      ComplexPoint.openInclusion (over X x) (smoothLocus X x) ≫
        ι X x :=
  Over.OverMorphism.ext (closedImmersionSourceOpenLift_ι _ _)

/-- The open `X(ℂ) \ Z_sing(ℂ)`, where `Z` is the closure of `x` and `Z_sing` its singular
locus. -/
def analyticSmoothAmbientOpen : Opens (ComplexPoint X) :=
  ⟨Point.overOpen (smoothAmbientOpen X x), Point.isOpen_overOpen _⟩

@[inherit_doc analyticSmoothAmbientOpen]
scoped notation3:max x:max "‾ˢⁱⁿᵍ(ℂ)ᶜ" => analyticSmoothAmbientOpen _ x

@[simp]
lemma coe_analyticSmoothAmbientOpen :
    (x‾ˢⁱⁿᵍ(ℂ)ᶜ : Set (ComplexPoint X)) =
      Point.overOpen (smoothAmbientOpen X x) :=
  rfl

@[simp]
lemma mem_analyticSmoothAmbientOpen {z : ComplexPoint X} :
    z ∈ x‾ˢⁱⁿᵍ(ℂ)ᶜ ↔
      z.underlying ∈ smoothAmbientOpen X x :=
  Iff.rfl

end AlgebraicGeometry.CycleComponent
