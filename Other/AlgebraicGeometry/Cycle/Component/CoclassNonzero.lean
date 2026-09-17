/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
public import Other.AlgebraicGeometry.Cycle.Support

/-! # Nonvanishing through the component's open transport -/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]
  {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)

/-- The smooth locus of the source of a closed embedding has a complex point. -/
theorem closedEmbeddingSmoothLocusOver_nonempty :
    Nonempty (ComplexPoint (closedEmbeddingSmoothLocusOver i)) := by
  obtain ⟨z, hz⟩ := exists_closedEmbedding_smooth_complexPoint i
  exact ⟨asOpenPoint Y (i.left ≫ X.hom).smoothLocus z hz⟩

set_option backward.isDefEq.respectTransparency false in
/-- Open transport of the normalized section preserves nonvanishing. -/
theorem closedEmbeddingSmoothSupportCoclassSection_ne_zero_of_lift_ne_zero
    (hne : closedEmbeddingSmoothClosedLiftCoclassSection i hi ≠ 0) :
    closedEmbeddingSmoothSupportCoclassSection i hi ≠ 0 := by
  intro hzero
  have h := closedEmbeddingSmoothSupportCoclassSection_restrict i hi ⊤
    (le_of_eq (closedEmbeddingSmoothClosedLiftAmbientMap_imageOpen i))
  rw [hzero, map_zero] at h
  simp only [homOfLE_refl, op_id] at h
  apply hne
  let e := (sheafToPresheaf (Opens.grothendieckTopology
    (ComplexPoint (closedEmbeddingSmoothLocusAmbientOpenOver i))) AddCommGrpCat).mapIso
    (supportRelativeCohomologySheafOpenIso (closedEmbeddingSmoothClosedLiftAmbientMap i)
      (closedEmbeddingSmoothClosedLiftAmbientMap_isOpenEmbedding i)
      (closedEmbeddingSupport i)
      (Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)))
      (closedEmbeddingSmoothClosedLiftAmbientMap_support i) (2 * p))
  apply (ConcreteCategory.bijective_of_isIso (e.app (op ⊤)).hom).1
  rw [map_zero]
  simpa [e] using h.symm

/-- The degree identification does not change whether the auxiliary section vanishes. -/
theorem closedEmbeddingSmoothClosedLiftCoclassSection_ne_zero_iff :
    closedEmbeddingSmoothClosedLiftCoclassSection i hi ≠ 0 ↔
      letI := closedEmbeddingSmoothLocusOver_hom_smoothOfRelativeDimension i hi
      smoothClosedSupportCoclassSection (closedEmbeddingSmoothLocusAmbientOpenOver i)
        (closedEmbeddingSmoothLocusOver i) (closedEmbeddingSmoothLocusClosedLiftOver i)
        (dim X.left - p) (dim X.left) ≠ 0 := by
  let := closedEmbeddingSmoothLocusOver_hom_smoothOfRelativeDimension i hi
  have transport (a b : ℕ) (h : a = b)
      (s : (supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint (closedEmbeddingSmoothLocusAmbientOpenOver i)))
        (Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)))
        (2 * a)).obj.obj (op ⊤)) : (h ▸ s) ≠ 0 ↔ s ≠ 0 := by
    subst b
    rfl
  exact transport _ _ (closedEmbeddingSmoothClosedLift_codimension i hi) _

end AlgebraicGeometry.ComplexPoint
