/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothLocus
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support

import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion

/-!
# Support, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.CycleComponent

open ComplexPoint

variable (X : Over (Spec ↧ℂ)) (x : X.left)

/-- Map the complex points of a cycle component into its support. -/
def supportMap : ComplexPoint (over X x) → x‾(ℂ) :=
  fun z => ⟨Point.map (ι X x) z, (range_map_ι X x).le ⟨z, rfl⟩⟩

/-- The complex points of a cycle component are the complex points of `X` in its support. -/
def pointEquivSupport :
    ComplexPoint (over X x) ≃ x‾(ℂ) :=
  (Equiv.ofInjective _ (map_injective_of_mono (ι X x))).trans
    (Equiv.setCongr (range_map_ι X x))

/-- The complex points of a cycle component that lie in its smooth locus. -/
def smoothAnalyticLocus [LocallyOfFiniteType X.hom] :
    Set (ComplexPoint (over X x)) :=
  Point.overOpen (smoothLocus X x)

/-- Every cycle component has a complex point in its smooth locus. The smooth locus is dense
over the perfect field `ℂ`, and it contains a closed point. -/
theorem exists_smooth_complexPoint [LocallyOfFiniteType X.hom] :
    ∃ z : ComplexPoint (over X x), z.underlying ∈ smoothLocus X x := by
  obtain ⟨y, hy, hyClosed⟩ := (dense_smoothLocus_closedPoints X x).nonempty
  let f := X.left.pointClosureι x ≫ X.hom
  let p := (pointEquivClosedPoint f).symm ⟨y, hyClosed⟩
  refine ⟨Over.homMk p.1 p.2, ?_⟩
  have hp' : p.1 (IsLocalRing.closedPoint ℂ) = y :=
    congrArg Subtype.val ((pointEquivClosedPoint f).apply_symm_apply ⟨y, hyClosed⟩)
  change p.1 (IsLocalRing.closedPoint ℂ) ∈ f.smoothLocus
  rw [hp']
  exact hy

end AlgebraicGeometry.CycleComponent
