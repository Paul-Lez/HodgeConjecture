/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothLocus
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Support, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

open ComplexPoint

variable (X : Over (Spec ↧ℂ)) (x : X.left)

/-- Map the complex points of a cycle component into its support. -/
def cycleComponentSupportMap : ComplexPoint (cycleComponentOver X x) → cycleComponentSupport X x :=
  fun z => ⟨Point.map (cycleComponentOverι X x) z, (range_map_cycleComponentOverι X x).le ⟨z, rfl⟩⟩

/-- The complex points of a cycle component are the complex points of `X` in its support. -/
def cycleComponentPointEquivSupport :
    ComplexPoint (cycleComponentOver X x) ≃ cycleComponentSupport X x :=
  Equiv.ofBijective (cycleComponentSupportMap X x)
    ⟨fun _ _ h => map_injective_of_mono (cycleComponentOverι X x) (congrArg Subtype.val h),
      fun z => by
        obtain ⟨w, hw⟩ := (range_map_cycleComponentOverι X x).ge z.2
        exact ⟨w, Subtype.ext hw⟩⟩

/-- The complex points of a cycle component that lie in its smooth locus. -/
def cycleComponentSmoothAnalyticLocus [LocallyOfFiniteType X.hom] :
    Set (ComplexPoint (cycleComponentOver X x)) :=
  Point.overOpen (cycleComponentSmoothLocus X x)

/-- An algebraic cycle on a projective complex variety has finite support. Algebraic cycles are
locally finite by definition, and the underlying Zariski space is compact. -/
lemma algebraicCycle_support_finite {R : Type*} [Zero R] [IsProjective X.hom]
    (c : AlgebraicCycle X.left R) :
    c.support.Finite := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  simpa using c.locallyFiniteSupport.finite_inter_support_of_isCompact
    (W := Set.univ) isCompact_univ

/-- Every cycle component has a complex point in its smooth locus. The smooth locus is dense
over the perfect field `ℂ`, and it contains a closed point. -/
theorem exists_cycleComponent_smooth_complexPoint [LocallyOfFiniteType X.hom] :
    ∃ z : ComplexPoint (cycleComponentOver X x), z.underlying ∈ cycleComponentSmoothLocus X x := by
  let f := X.left.pointClosureι x ≫ X.hom
  let : JacobsonSpace (X.left.pointClosure x) := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyClosed⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.2.isLocallyClosed
  let p := (pointEquivClosedPoint f).symm ⟨y, hyClosed⟩
  refine ⟨Over.homMk p.1 p.2, ?_⟩
  have hp := (pointEquivClosedPoint f).apply_symm_apply ⟨y, hyClosed⟩
  have hp' : p.1 (IsLocalRing.closedPoint ℂ) = y := congrArg Subtype.val hp
  change p.1 (IsLocalRing.closedPoint ℂ) ∈ f.smoothLocus
  rw [hp']
  exact hy

end AlgebraicGeometry
