/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.SmoothClosedSupportCoclassSection

/-!
# The actual global exactly normalized smooth-support coclass section

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.SmoothClosedSupportCoclassSection`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
open TopCat.Presheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

@[simp] theorem smoothClosedSupportCoclassSection_germ (x : ComplexPoint X) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection X Y i m d) =
        smoothClosedSupportCoclassStalk X Y i m d x :=
  TopCat.Sheaf.sectionOfLocallyRepresentable_germ
    (smoothClosedSupportCoclassSheaf X Y i m d)
    (smoothClosedSupportCoclassStalk X Y i m d)
    (smoothClosedSupportCoclassStalk_locallyRepresentable X Y i m d) x

/-- Exact stalk normalization in every actual normal chart. -/
theorem smoothClosedSupportCoclassSection_germ_eq_chart
    (z : ComplexPoint Y) (x : ComplexPoint X)
    (hx : x ∈ smoothClosedSupportChartOpen X Y i m d z) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection X Y i m d) =
        smoothClosedSupportChartCoclassGerm X Y i m d z x hx := by
  rw [smoothClosedSupportCoclassSection_germ,
    smoothClosedSupportCoclassStalk_eq_chartGerm X Y i m d z x hx]

/-- The global section restricts to the actual normalized section on a full normal chart. -/
theorem smoothClosedSupportCoclassSection_restrict_chart (z : ComplexPoint Y) :
    (smoothClosedSupportCoclassSheaf X Y i m d).obj.map
      (homOfLE (show smoothClosedSupportChartOpen X Y i m d z ≤ ⊤ from le_top)).op
      (smoothClosedSupportCoclassSection X Y i m d) =
        smoothClosedSupportChartSheafSection X Y i m d z := by
  apply TopCat.Presheaf.section_ext (smoothClosedSupportCoclassSheaf X Y i m d)
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply]
  exact smoothClosedSupportCoclassSection_germ_eq_chart X Y i m d z x hx

/-- Outside the actual image, the global section has zero germ. -/
theorem smoothClosedSupportCoclassSection_germ_eq_zero
    (x : ComplexPoint X) (hxS : x ∉ Set.range (Point.map i)) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection X Y i m d) = 0 := by
  rw [smoothClosedSupportCoclassSection_germ,
    smoothClosedSupportCoclassStalk_eq_zero X Y i m d x hxS]

/-- Uniqueness of the actual gluing, expressed by its exact stalk normalization. -/
theorem smoothClosedSupportCoclassSection_unique
    (s : (smoothClosedSupportCoclassSheaf X Y i m d).obj.obj (op ⊤))
    (hs : ∀ x : ComplexPoint X,
      (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x s =
        smoothClosedSupportCoclassStalk X Y i m d x) :
    s = smoothClosedSupportCoclassSection X Y i m d := by
  apply TopCat.Presheaf.section_ext (smoothClosedSupportCoclassSheaf X Y i m d)
  exact fun x _ ↦ (hs x).trans (smoothClosedSupportCoclassSection_germ X Y i m d x).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- At every center, the global section has exactly the germ of the previously
constructed normal-slice coclass, on any prescribed local model neighborhood. -/
theorem smoothClosedSupportCoclassSection_germ_eq_normalCoclass
    (z : ComplexPoint Y) (V : Opens (ComplexPoint X))
    (hzV : Point.map i z ∈ V) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm
      (Point.map i z) (smoothClosedSupportCoclassSection X Y i m d) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (Set.range (Point.map i)) (2 * (d - m))
      (smoothClosedSupportNeighborhood X Y i m d z V hzV)
      (Point.map i z) (mem_smoothClosedSupportNeighborhood X Y i m d z V hzV)
      (smoothClosedSupportNormalCoclass X Y i m d z V hzV) := by
  let C := smoothClosedSupportChartOpen X Y i m d z
  let U := smoothClosedSupportNeighborhood X Y i m d z V hzV
  let W := C ⊓ U
  have hWC : W ≤ C := inf_le_left
  have hWU : W ≤ U := inf_le_right
  have hzW : Point.map i z ∈ W :=
    ⟨mem_smoothClosedSupportChartOpen X Y i m d z,
      mem_smoothClosedSupportNeighborhood X Y i m d z V hzV⟩
  rw [smoothClosedSupportCoclassSection_germ_eq_chart X Y i m d z
    (Point.map i z) (mem_smoothClosedSupportChartOpen X Y i m d z)]
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq
    (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
    hWC hWU (Point.map i z) hzW
  rw [smoothClosedSupportChartCoclass_restrict,
    smoothClosedSupportNormalCoclass_restrict_eq_chart X Y i m d z V hzV W hWU hWC]

/-- The fixed chart normalization at support centers and zero germs off support
uniquely characterize the global section, independently of preimage choices. -/
theorem smoothClosedSupportCoclassSection_unique_of_normalization
    (s : (smoothClosedSupportCoclassSheaf X Y i m d).obj.obj (op ⊤))
    (hs : ∀ z : ComplexPoint Y,
      (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm (Point.map i z) s =
        smoothClosedSupportChartCoclassGerm X Y i m d z (Point.map i z)
          (mem_smoothClosedSupportChartOpen X Y i m d z))
    (hzero : ∀ (x : ComplexPoint X), x ∉ Set.range (Point.map i) →
      (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x s = 0) :
    s = smoothClosedSupportCoclassSection X Y i m d := by
  apply smoothClosedSupportCoclassSection_unique
  intro x
  by_cases hxS : x ∈ Set.range (Point.map i)
  · obtain ⟨z, rfl⟩ := hxS
    exact (hs z).trans (smoothClosedSupportCoclassStalk_eq_chartGerm
      X Y i m d z (Point.map i z)
      (mem_smoothClosedSupportChartOpen X Y i m d z)).symm
  · rw [hzero x hxS, smoothClosedSupportCoclassStalk_eq_zero X Y i m d x hxS]

section CrossPresentation

variable (Y' : Over (Spec (.of ℂ))) (i' : Y' ⟶ X)
  [SmoothOfRelativeDimension m Y'.hom] [IsClosedImmersion i'.left]

/-- Two smooth closed-immersion presentations with the same analytic image give the
same globally normalized support coclass.  The support equality is the only transport
in the statement; compatibility of the normal orientations is a theorem of the
holomorphic transition maps, not an extra hypothesis. -/
theorem smoothClosedSupportCoclassSection_eq_cross
    (hS : Set.range (Point.map i') = Set.range (Point.map i)) :
    smoothClosedSupportCoclassSection X Y i m d =
      supportRelativeCohomologySectionTransport
        (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
        hS ⊤ (smoothClosedSupportCoclassSection X Y' i' m d) := by
  apply TopCat.Presheaf.section_ext (smoothClosedSupportCoclassSheaf X Y i m d)
  intro x hx
  change (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection X Y i m d) =
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x
      (supportRelativeCohomologySectionTransport
        (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
        hS ⊤ (smoothClosedSupportCoclassSection X Y' i' m d))
  by_cases hxS : x ∈ Set.range (Point.map i)
  · have hxS0 := hxS
    obtain ⟨z, hz⟩ := hxS
    obtain ⟨z', hz'⟩ : x ∈ Set.range (Point.map i') := by
      rwa [hS]
    have hxz : x ∈ smoothClosedSupportChartOpen X Y i m d z := by
      simpa only [hz] using mem_smoothClosedSupportChartOpen X Y i m d z
    have hxz' : x ∈ smoothClosedSupportChartOpen X Y' i' m d z' := by
      simpa only [hz'] using mem_smoothClosedSupportChartOpen X Y' i' m d z'
    rw [supportRelativeCohomologySectionTransport_Γgerm]
    obtain ⟨W, hW, hW', hxW, heq⟩ :=
      exists_open_smoothClosedSupportChartCoclass_eq_cross
        X Y i m d z Y' i' z' hS x hxS0 hxz hxz'
    have hWU : (W : Set (ComplexPoint X)) ⊆
        (smoothClosedSupportChartOpen X Y i m d z : Set (ComplexPoint X)) := hW
    have hWV : (W : Set (ComplexPoint X)) ⊆
        (smoothClosedSupportChartOpen X Y' i' m d z' : Set (ComplexPoint X)) := hW'
    calc
      _ = smoothClosedSupportChartCoclassGerm X Y i m d z x hxz :=
        smoothClosedSupportCoclassSection_germ_eq_chart X Y i m d z x hxz
      _ = supportRelativeCohomologyStalkTransport
          (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
          hS x (smoothClosedSupportChartCoclassGerm X Y' i' m d z' x hxz') := by
        unfold smoothClosedSupportChartCoclassGerm
        rw [supportRelativeCohomologyStalkTransport_germ]
        apply supportRelativeCohomologyGerm_eq_of_restrict_eq
          (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
          (U := smoothClosedSupportChartOpen X Y i m d z)
          (V := smoothClosedSupportChartOpen X Y' i' m d z')
          hWU hWV x hxW
        rw [smoothClosedSupportChartCoclass_restrict X Y i m d z hWU (le_refl _)]
        rw [neighborhoodSupportRelativeCohomologyMap_transport_support
          (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
          hS hWV (smoothClosedSupportChartCoclass X Y' i' m d z'
            (smoothClosedSupportChartOpen X Y' i' m d z') (le_refl _))]
        rw [smoothClosedSupportChartCoclass_restrict X Y' i' m d z' hWV (le_refl _)]
        exact heq
      _ = supportRelativeCohomologyStalkTransport
          (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
          hS x ((smoothClosedSupportCoclassSheaf X Y' i' m d).presheaf.Γgerm x
            (smoothClosedSupportCoclassSection X Y' i' m d)) := by
        congr 1
        exact (smoothClosedSupportCoclassSection_germ_eq_chart
          X Y' i' m d z' x hxz').symm
  · rw [smoothClosedSupportCoclassSection_germ_eq_zero X Y i m d x hxS]
    have hxS' : x ∉ Set.range (Point.map i') := by
      rwa [hS]
    rw [supportRelativeCohomologySectionTransport_Γgerm,
      smoothClosedSupportCoclassSection_germ_eq_zero X Y' i' m d x hxS']
    simp only [supportRelativeCohomologyStalkTransport_zero]

end CrossPresentation

end AlgebraicGeometry.ComplexPoint
