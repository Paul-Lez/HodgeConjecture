/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothClosedLift

/-!
# The smooth-locus closed lift of a closed subvariety

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothClosedLift`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
/-- `X ∖ Y_sing` is the complement of the image of the singular locus of the source: the
filtration index `0` in the definition contributes nothing. -/
@[simp] theorem coe_closedEmbeddingSmoothLocusAmbientOpen :
    (closedEmbeddingSmoothLocusAmbientOpen i : Set X.left) =
      (i.left ''
        (singularLocusClosed (i.left ≫ X.hom) : Set _))ᶜ := rfl

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
/-- The exact image of the lift is the restriction of the full support. -/
theorem range_closedEmbeddingSmoothLocusClosedLift :
    Set.range (closedEmbeddingSmoothLocusClosedLift i) =
      (closedEmbeddingSmoothLocusAmbientOpen i).ι ⁻¹' Set.range i.left :=
  range_closedImmersionSourceOpenLift _ _

variable {p : ℕ}

/-- The smooth locus has the constant relative dimension of the integral source. -/
theorem closedEmbeddingSmoothLocus_smoothOfRelativeDimension
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = p) :
    SmoothOfRelativeDimension (dim X.left - p)
      ((i.left ≫ X.hom).smoothLocus.ι ≫ i.left ≫ X.hom) := by
  let A := (i.left ≫ X.hom).smoothLocus
  let g := A.ι ≫ i.left ≫ X.hom
  let : Smooth g := (i.left ≫ X.hom).smooth_restrict_smoothLocus
  obtain ⟨m, hm⟩ := Smooth.exists_smoothOfRelativeDimension g
  obtain ⟨z, hzA, hzClosed⟩ := (dense_closedEmbedding_smooth_closedPoints i).nonempty
  let zA : A.toScheme := ⟨z, hzA⟩
  have hzAClosed : IsClosed ({zA} : Set A) := by
    have he : A.ι ⁻¹' ({z} : Set (Y.left)) = {zA} := by
      ext a
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    exact he ▸ hzClosed.preimage A.ι.continuous
  have hmEq : m = dim X.left - p := by
    exact_mod_cast calc
      (m : ℕ∞) = Order.coheight zA :=
        (SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
          (f := g) (d := m) zA hzAClosed).symm
      _ = Order.coheight z := (coheight_eq_of_isOpenImmersion (x := zA) A.ι).symm
      _ = dim X.left - p := closedEmbedding_closedPoint_coheight_eq_sub i z hi hzClosed
  subst m
  exact hm

namespace ComplexPoint

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
/-- The analytic image of the algebraic boundary complement is the exact open used by
the original ambient supported resolution. -/
theorem closedEmbeddingSmoothLocusAmbientOpen_analytic_image :
    Set.range (Point.map (openInclusion X (closedEmbeddingSmoothLocusAmbientOpen i))) =
      ((closedEmbeddingSingularAnalyticClosedFiltration i 0).compl : Set (ComplexPoint X)) := by
  rw [range_map_of_isImmersion X]
  change (Point.underlying : ComplexPoint X → X.left) ⁻¹'
      Set.range (closedEmbeddingSmoothLocusAmbientOpen i).ι = _
  rw [Scheme.Opens.range_ι]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
/-- The complex-point image of the closed lift is precisely the restricted full support. -/
theorem closedEmbeddingSmoothLocusClosedLift_complexPoints_range :
    Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)) =
      Point.map (openInclusion X (closedEmbeddingSmoothLocusAmbientOpen i)) ⁻¹'
          (closedEmbeddingSupport i) := by
  rw [range_map_of_isImmersion]
  change (Point.underlying : ComplexPoint (closedEmbeddingSmoothLocusAmbientOpenOver i) →
    (closedEmbeddingSmoothLocusAmbientOpenOver i).left) ⁻¹'
      Set.range (closedEmbeddingSmoothLocusClosedLift i) = _
  rw [range_closedEmbeddingSmoothLocusClosedLift]
  rfl

end ComplexPoint
end AlgebraicGeometry
