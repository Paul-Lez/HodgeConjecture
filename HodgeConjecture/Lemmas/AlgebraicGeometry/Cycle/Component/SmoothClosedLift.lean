/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothClosedLift

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion

/-!
# The smooth locus of a cycle component as a closed subscheme

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothClosedLift`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.CycleComponent

open ComplexPoint

variable (X : Over (Spec ↧ℂ)) (x : X.left)

section FiniteType

variable [LocallyOfFiniteType X.hom]

@[simp]
theorem coe_smoothAmbientOpen :
    (smoothAmbientOpen X x : Set X.left) =
      (X.left.pointClosureι x ''
        (singularLocusClosed (X.left.pointClosureι x ≫ X.hom) : Set _))ᶜ :=
  rfl

/-- The ambient open of the smooth locus is the complement of the first stage of the ambient
singular filtration. -/
theorem smoothAmbientOpen_eq_compl :
    smoothAmbientOpen X x =
      (ambientSingularFiltration X x 0).compl :=
  rfl

@[reassoc (attr := simp)]
theorem smoothClosedLift_left_ι :
    (smoothClosedLift X x).left ≫
        (smoothAmbientOpen X x).ι =
      (smoothLocus X x).ι ≫ X.left.pointClosureι x :=
  closedImmersionSourceOpenLift_ι _ _

/-- The closed lift of the smooth locus has image the cycle component, restricted to the ambient
open. -/
theorem range_smoothClosedLift_left :
    Set.range (smoothClosedLift X x).left =
      (smoothAmbientOpen X x).ι ⁻¹' closure ({x} : Set X.left) := by
  rw [← X.left.range_pointClosureι x]
  exact range_closedImmersionSourceOpenLift _ _

/-- The complex points of the ambient open of the smooth locus are the complement of the first
stage of the analytic singular filtration. -/
theorem analyticSmoothAmbientOpen_eq_compl :
    x‾ˢⁱⁿᵍ(ℂ)ᶜ =
      (x‾ˢⁱⁿᵍ(ℂ)).compl :=
  rfl

/-- Inside the ambient open, the complex points of the closed lift of the smooth locus are the
complex points on the cycle component. -/
theorem range_map_smoothClosedLift :
    Set.range (Point.map (smoothClosedLift X x)) =
      Point.map (openInclusion X (smoothAmbientOpen X x)) ⁻¹'
          (x‾(ℂ)) := by
  rw [range_map_of_closedImmersion]
  ext z
  change z.underlying ∈ Set.range (smoothClosedLift X x).left ↔ _
  rw [range_smoothClosedLift_left]
  rfl

end FiniteType

section Dimension

variable [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {p : ℕ}

/-- The smooth locus of a codimension-`p` cycle component is smooth of relative dimension
`dim X - p` over `ℂ`. -/
theorem smoothLocusOver_smoothOfRelativeDimension (hx : Order.coheight x = p) :
    SmoothOfRelativeDimension (dim X.left - p) (smoothLocusOver X x).hom := by
  let A := smoothLocus X x
  let g := A.ι ≫ X.left.pointClosureι x ≫ X.hom
  let : Smooth g := (X.left.pointClosureι x ≫ X.hom).smooth_restrict_smoothLocus
  obtain ⟨m, hm⟩ := Smooth.exists_smoothOfRelativeDimension g
  obtain ⟨z, hzA, hzClosed⟩ := (dense_smoothLocus_closedPoints X x).nonempty
  let zA : A.toScheme := ⟨z, hzA⟩
  have hzAClosed : IsClosed ({zA} : Set A) := by
    have he : A.ι ⁻¹' ({z} : Set (X.left.pointClosure x)) = {zA} := by
      ext a
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    exact he ▸ hzClosed.preimage A.ι.continuous
  have hmEq : m = dim X.left - p := by
    exact_mod_cast calc
      (m : ℕ∞) = Order.coheight zA :=
        (SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
          (f := g) (d := m) zA hzAClosed).symm
      _ = Order.coheight z := (coheight_eq_of_isOpenImmersion (x := zA) A.ι).symm
      _ = dim X.left - p := closedPoint_coheight_eq_sub X x z hx hzClosed
  subst m
  exact hm

end Dimension

end AlgebraicGeometry.CycleComponent
