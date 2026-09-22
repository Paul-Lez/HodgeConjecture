/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.WindingRelativeCocycle
public import HodgeConjecture.Lemmas.AlgebraicTopology.EuclideanLocalHomology
public import HodgeConjecture.Definitions.AlgebraicTopology.FlattenedSupportLocalHomology

/-!
# The relative singular class of a winding cocycle

For a support `S` in a neighbourhood `W`, a nowhere-zero function on `W \\ S` has an
explicit integer singular `1`-cocycle, `ChernWinding.windingIntegerCochain`.  Precomposing its
cohomology class with the connecting map of `(W, W \\ S)` gives the degree-two relative class
of the support.  Thus this definition uses the displayed singular cochain, rather than a Chern
class or a cycle-class comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology.Singular

namespace ChernWinding

variable {M : Type} [TopologicalSpace M] (W S : Set M)

/-- The pair consisting of a neighbourhood and its complement of the specified support. -/
abbrev supportPair : TopPair := neighborhoodSupportComplementPair W S

/-- The punctured neighbourhood on which the winding cochain is evaluated. -/
abbrev puncturedSpace : TopCat := (supportPair W S).snd

/-- The degree-two singular relative class defined by the explicit winding-index cochain.

Its value on a relative two-cycle is the winding-index cocycle evaluated on that cycle's
connecting boundary in the punctured neighbourhood. -/
def windingRelativeClass (g : C(puncturedSpace W S, ℂ)) (hg : ∀ y, g y ≠ 0) :
    RelativeCohomology ℚ (supportPair W S) 2 :=
  (windingRationalPeriod g hg).comp (relativeSingularBoundary (supportPair W S) 1).hom

@[simp]
lemma windingRelativeClass_apply (g : C(puncturedSpace W S, ℂ)) (hg : ∀ y, g y ≠ 0)
    (z : RelativeHomology ℚ (supportPair W S) 2) :
    windingRelativeClass W S g hg z =
      windingRationalPeriod g hg ((relativeSingularBoundary (supportPair W S) 1).hom z) :=
  rfl

set_option maxHeartbeats 2000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a support-complement pair, the literal mapping-cone cocycle `(0, windingIndex)` is
exactly the boundary-period relative class. -/
theorem windingRelativeCochainClass_eq_windingRelativeClass
    (g : C(puncturedSpace W S, ℂ)) (hg : ∀ y, g y ≠ 0) :
    windingRelativeCochainClass (X := supportPair W S) g hg =
      windingRelativeClass W S g hg := by
  rw [windingRelativeCochainClass_eq_boundaryPeriod]
  rfl

end ChernWinding
