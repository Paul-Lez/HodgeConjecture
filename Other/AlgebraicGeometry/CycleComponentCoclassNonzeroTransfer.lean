/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection

/-! # Nonvanishing through the component's open transport -/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p)

/-- The actual smooth locus of each reduced component has a complex point. -/
theorem cycleComponentSmoothLocusOver_nonempty :
    Nonempty (ComplexPoint (cycleComponentSmoothLocusOver X x)) := by
  obtain ⟨z, hz⟩ := exists_cycleComponent_smooth_complexPoint X x
  exact ⟨asOpenPoint (Over.mk (cycleComponentι X.left x ≫ X.hom))
    (cycleComponentι X.left x ≫ X.hom).smoothLocus z hz⟩

set_option backward.isDefEq.respectTransparency false in
/-- Open transport of the normalized component section preserves nonvanishing. -/
theorem cycleComponentSmoothSupportCoclassSection_ne_zero_of_lift_ne_zero
    (hne : cycleComponentSmoothClosedLiftCoclassSection X x (d := d) hx ≠ 0) :
    cycleComponentSmoothSupportCoclassSection X x (d := d) hx ≠ 0 := by
  intro hzero
  have h := cycleComponentSmoothSupportCoclassSection_restrict X x (d := d) hx ⊤
    (le_of_eq (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x))
  rw [hzero, map_zero] at h
  simp only [homOfLE_refl, op_id] at h
  apply hne
  let e := (sheafToPresheaf (Opens.grothendieckTopology
    (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x))) AddCommGrpCat).mapIso
    (supportRelativeCohomologySheafOpenIso (cycleComponentSmoothClosedLiftAmbientMap X x)
      (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
      (cycleComponentSupport X x)
      (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
      (cycleComponentSmoothClosedLiftAmbientMap_support X x) (2 * p))
  apply (ConcreteCategory.bijective_of_isIso (e.app (op ⊤)).hom).1
  rw [map_zero]
  simpa [e] using h.symm

/-- The degree identification does not change whether the auxiliary section vanishes. -/
theorem cycleComponentSmoothClosedLiftCoclassSection_ne_zero_iff :
    cycleComponentSmoothClosedLiftCoclassSection X x (d := d) hx ≠ 0 ↔
      letI := cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension X x
        (d := d) hx
      smoothClosedSupportCoclassSection (cycleComponentSmoothLocusAmbientOpenOver X x)
        (cycleComponentSmoothLocusOver X x) (cycleComponentSmoothLocusClosedLiftOver X x)
        (d - p) d ≠ 0 := by
  let := cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension X x
    (d := d) hx
  have transport (a b : ℕ) (h : a = b)
      (s : (supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
        (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
        (2 * a)).obj.obj (op ⊤)) : (h ▸ s) ≠ 0 ↔ s ≠ 0 := by
    subst b
    rfl
  exact transport _ _ (cycleComponentSmoothClosedLift_codimension X x (d := d) hx) _

end AlgebraicGeometry.ComplexPoint
