/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedSupportCoclassOverlap
public import HodgeConjecture.Other.AlgebraicTopology.SupportRelativeCohomologySheaf

/-!
# The actual global exactly normalized smooth-support coclass section

The actual holomorphic normal charts supply local relative coclasses. Their
proved ambient overlap agreement identifies their sheaf germs. Off the closed
image the actual relative complexes vanish, so those same chart germs are zero.
Unique sheaf gluing therefore constructs the global section, retaining its exact
complex normalization. No local representability or overlap coherence is supplied.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
open TopCat.Presheaf

namespace AlgebraicGeometry.ComplexPoint

variable {X Y : Scheme}
  (structureMapX : X ⟶ Spec (.of ℂ)) (structureMapY : Y ⟶ Spec (.of ℂ))
  (i : Y ⟶ X) (hi : i ≫ structureMapX = structureMapY) (m d : ℕ)
  [SmoothOfRelativeDimension m structureMapY] [SmoothOfRelativeDimension d structureMapX]
  [IsClosedImmersion i]

/-- The actual source open of a constructed holomorphic normal chart. -/
def smoothClosedSupportChartOpen (z : ComplexPoint Y structureMapY) :
    Opens (ComplexPoint X structureMapX) :=
  ⟨(closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source,
    (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).open_source⟩

theorem mem_smoothClosedSupportChartOpen (z : ComplexPoint Y structureMapY) :
    Point.map i hi z ∈ smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z :=
  closedImmersionHolomorphicFlatteningChart_mem_source structureMapX structureMapY i hi m d z

/-- The target is the sheafification of the literal relative-cohomology presheaf. -/
abbrev smoothClosedSupportCoclassSheaf : TopCat.Sheaf AddCommGrpCat
    (TopCat.of (ComplexPoint X structureMapX)) :=
  supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X structureMapX))
    (Set.range (Point.map i hi)) (2 * (d - m))

/-- The exact normal coclass determines an actual section on its full chart source. -/
def smoothClosedSupportChartSheafSection (z : ComplexPoint Y structureMapY) :
    (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).obj.obj
      (op (smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z)) :=
  (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X structureMapX))
    (Set.range (Point.map i hi)) (2 * (d - m))).app _
      (smoothClosedSupportChartCoclass structureMapX structureMapY i hi m d z
        (smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z) (le_refl _))

/-- Its germ is, by definition, the germ of the fixed normal-projection coclass. -/
def smoothClosedSupportChartCoclassGerm (z : ComplexPoint Y structureMapY)
    (x : ComplexPoint X structureMapX)
    (hx : x ∈ smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z) :
    (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).presheaf.stalk x :=
  supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X structureMapX))
    (Set.range (Point.map i hi)) (2 * (d - m))
    (smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z) x hx
    (smoothClosedSupportChartCoclass structureMapX structureMapY i hi m d z
      (smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z) (le_refl _))

/-- The actual ambient overlap theorem proves equality of chart germs on support. -/
theorem smoothClosedSupportChartCoclassGerm_eq
    (z z' : ComplexPoint Y structureMapY) (x : ComplexPoint X structureMapX)
    (hxS : x ∈ Set.range (Point.map i hi))
    (hx : x ∈ smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z)
    (hx' : x ∈ smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z') :
    smoothClosedSupportChartCoclassGerm structureMapX structureMapY i hi m d z x hx =
      smoothClosedSupportChartCoclassGerm structureMapX structureMapY i hi m d z' x hx' := by
  obtain ⟨W, hW, hW', hxW, heq⟩ := exists_open_smoothClosedSupportChartCoclass_eq
    structureMapX structureMapY i hi m d z z' x hxS hx hx'
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq
    (TopCat.of (ComplexPoint X structureMapX)) (Set.range (Point.map i hi)) (2 * (d - m))
    (U := smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z)
    (V := smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z')
    hW hW' x hxW
  simpa only [smoothClosedSupportChartCoclass_restrict] using heq

/-- Away from the actual closed image, the actual chart coclass germ is zero. -/
theorem smoothClosedSupportChartCoclassGerm_eq_zero
    (z : ComplexPoint Y structureMapY) (x : ComplexPoint X structureMapX)
    (hx : x ∈ smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z)
    (hxS : x ∉ Set.range (Point.map i hi)) :
    smoothClosedSupportChartCoclassGerm structureMapX structureMapY i hi m d z x hx = 0 :=
  supportRelativeCohomologyGerm_eq_zero_of_not_mem
    (TopCat.of (ComplexPoint X structureMapX)) (Set.range (Point.map i hi)) (2 * (d - m))
    (isClosed_range_map_of_closedImmersion hi)
    (smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z) x hx hxS
    (smoothClosedSupportChartCoclass structureMapX structureMapY i hi m d z
      (smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z) (le_refl _))

/-- A pointwise normalized germ family. Choice selects a preimage point only;
the proved chart-overlap theorem below proves independence of that selection. -/
def smoothClosedSupportCoclassStalk (x : ComplexPoint X structureMapX) :
    (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).presheaf.stalk x := by
  classical
  exact if hxS : x ∈ Set.range (Point.map i hi) then
    smoothClosedSupportChartCoclassGerm structureMapX structureMapY i hi m d hxS.choose x
      (by simpa only [hxS.choose_spec] using
        mem_smoothClosedSupportChartOpen structureMapX structureMapY i hi m d hxS.choose)
  else 0

/-- The normalized germ family agrees with every actual chart, including at points
outside the support. This supplies local coherence as a theorem, not as data. -/
theorem smoothClosedSupportCoclassStalk_eq_chartGerm
    (z : ComplexPoint Y structureMapY) (x : ComplexPoint X structureMapX)
    (hx : x ∈ smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z) :
    smoothClosedSupportCoclassStalk structureMapX structureMapY i hi m d x =
      smoothClosedSupportChartCoclassGerm structureMapX structureMapY i hi m d z x hx := by
  by_cases hxS : x ∈ Set.range (Point.map i hi)
  · rw [smoothClosedSupportCoclassStalk, dif_pos hxS]
    exact smoothClosedSupportChartCoclassGerm_eq structureMapX structureMapY i hi m d
      hxS.choose z x hxS _ hx
  · rw [smoothClosedSupportCoclassStalk, dif_neg hxS]
    exact (smoothClosedSupportChartCoclassGerm_eq_zero structureMapX structureMapY i hi m d z x hx hxS).symm

@[simp] theorem smoothClosedSupportCoclassStalk_eq_zero
    (x : ComplexPoint X structureMapX) (hxS : x ∉ Set.range (Point.map i hi)) :
    smoothClosedSupportCoclassStalk structureMapX structureMapY i hi m d x = 0 := by
  rw [smoothClosedSupportCoclassStalk, dif_neg hxS]

/-- Actual charts and the open support complement prove local representability
of the entire normalized stalk family. -/
theorem smoothClosedSupportCoclassStalk_locallyRepresentable :
    ∀ x : ComplexPoint X structureMapX,
      ∃ (U : Opens (ComplexPoint X structureMapX)) (_ : x ∈ U)
        (s : (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).obj.obj (op U)),
        ∀ (y : ComplexPoint X structureMapX) (hy : y ∈ U),
          (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).presheaf.germ U y hy s =
            smoothClosedSupportCoclassStalk structureMapX structureMapY i hi m d y := by
  intro x
  by_cases hxS : x ∈ Set.range (Point.map i hi)
  · obtain ⟨z, rfl⟩ := hxS
    refine ⟨smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z,
      mem_smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z,
      smoothClosedSupportChartSheafSection structureMapX structureMapY i hi m d z, ?_⟩
    intro y hy
    exact (smoothClosedSupportCoclassStalk_eq_chartGerm structureMapX structureMapY i hi m d z y hy).symm
  · let U : Opens (ComplexPoint X structureMapX) :=
      ⟨(Set.range (Point.map i hi))ᶜ, (isClosed_range_map_of_closedImmersion hi).isOpen_compl⟩
    refine ⟨U, hxS, 0, ?_⟩
    intro y hy
    rw [map_zero, smoothClosedSupportCoclassStalk_eq_zero structureMapX structureMapY i hi m d y hy]

/-- The actual unique global gluing of exactly normalized smooth normal coclasses. -/
def smoothClosedSupportCoclassSection :
    (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).obj.obj (op ⊤) :=
  TopCat.Sheaf.sectionOfLocallyRepresentable _
    (smoothClosedSupportCoclassStalk structureMapX structureMapY i hi m d)
    (smoothClosedSupportCoclassStalk_locallyRepresentable structureMapX structureMapY i hi m d)

@[simp] theorem smoothClosedSupportCoclassSection_germ (x : ComplexPoint X structureMapX) :
    (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection structureMapX structureMapY i hi m d) =
        smoothClosedSupportCoclassStalk structureMapX structureMapY i hi m d x :=
  TopCat.Sheaf.sectionOfLocallyRepresentable_germ
    (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d)
    (smoothClosedSupportCoclassStalk structureMapX structureMapY i hi m d)
    (smoothClosedSupportCoclassStalk_locallyRepresentable structureMapX structureMapY i hi m d) x

/-- Exact stalk normalization in every actual normal chart. -/
theorem smoothClosedSupportCoclassSection_germ_eq_chart
    (z : ComplexPoint Y structureMapY) (x : ComplexPoint X structureMapX)
    (hx : x ∈ smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z) :
    (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection structureMapX structureMapY i hi m d) =
        smoothClosedSupportChartCoclassGerm structureMapX structureMapY i hi m d z x hx := by
  rw [smoothClosedSupportCoclassSection_germ,
    smoothClosedSupportCoclassStalk_eq_chartGerm structureMapX structureMapY i hi m d z x hx]

/-- The global section restricts to the actual normalized section on a full normal chart. -/
theorem smoothClosedSupportCoclassSection_restrict_chart (z : ComplexPoint Y structureMapY) :
    (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).obj.map
      (homOfLE (show smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z ≤ ⊤ from le_top)).op
      (smoothClosedSupportCoclassSection structureMapX structureMapY i hi m d) =
        smoothClosedSupportChartSheafSection structureMapX structureMapY i hi m d z := by
  apply TopCat.Presheaf.section_ext (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d)
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply]
  exact smoothClosedSupportCoclassSection_germ_eq_chart structureMapX structureMapY i hi m d z x hx

/-- Outside the actual image, the global section has zero germ. -/
theorem smoothClosedSupportCoclassSection_germ_eq_zero
    (x : ComplexPoint X structureMapX) (hxS : x ∉ Set.range (Point.map i hi)) :
    (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection structureMapX structureMapY i hi m d) = 0 := by
  rw [smoothClosedSupportCoclassSection_germ,
    smoothClosedSupportCoclassStalk_eq_zero structureMapX structureMapY i hi m d x hxS]

/-- Uniqueness of the actual gluing, expressed by its exact stalk normalization. -/
theorem smoothClosedSupportCoclassSection_unique
    (s : (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).obj.obj (op ⊤))
    (hs : ∀ x : ComplexPoint X structureMapX,
      (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).presheaf.Γgerm x s =
        smoothClosedSupportCoclassStalk structureMapX structureMapY i hi m d x) :
    s = smoothClosedSupportCoclassSection structureMapX structureMapY i hi m d := by
  apply TopCat.Presheaf.section_ext (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d)
  intro x _
  exact (hs x).trans (smoothClosedSupportCoclassSection_germ structureMapX structureMapY i hi m d x).symm

/-- At every center, the global section has exactly the germ of the previously
constructed normal-slice coclass, on any prescribed local model neighborhood. -/
theorem smoothClosedSupportCoclassSection_germ_eq_normalCoclass
    (z : ComplexPoint Y structureMapY) (V : Opens (ComplexPoint X structureMapX))
    (hzV : Point.map i hi z ∈ V) :
    (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).presheaf.Γgerm
      (Point.map i hi z) (smoothClosedSupportCoclassSection structureMapX structureMapY i hi m d) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X structureMapX))
      (Set.range (Point.map i hi)) (2 * (d - m))
      (smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z V hzV)
      (Point.map i hi z) (mem_smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z V hzV)
      (smoothClosedSupportNormalCoclass structureMapX structureMapY i hi m d z V hzV) := by
  let C := smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z
  let U := smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z V hzV
  let W := C ⊓ U
  have hWC : W ≤ C := inf_le_left
  have hWU : W ≤ U := inf_le_right
  have hzW : Point.map i hi z ∈ W :=
    ⟨mem_smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z,
      mem_smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z V hzV⟩
  rw [smoothClosedSupportCoclassSection_germ_eq_chart structureMapX structureMapY i hi m d z
    (Point.map i hi z) (mem_smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z)]
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq
    (TopCat.of (ComplexPoint X structureMapX)) (Set.range (Point.map i hi)) (2 * (d - m))
    hWC hWU (Point.map i hi z) hzW
  rw [smoothClosedSupportChartCoclass_restrict,
    smoothClosedSupportNormalCoclass_restrict_eq_chart structureMapX structureMapY i hi m d z V hzV W hWU hWC]

/-- The fixed chart normalization at support centers and zero germs off support
uniquely characterize the global section, independently of preimage choices. -/
theorem smoothClosedSupportCoclassSection_unique_of_normalization
    (s : (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).obj.obj (op ⊤))
    (hs : ∀ z : ComplexPoint Y structureMapY,
      (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).presheaf.Γgerm (Point.map i hi z) s =
        smoothClosedSupportChartCoclassGerm structureMapX structureMapY i hi m d z (Point.map i hi z)
          (mem_smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z))
    (hzero : ∀ (x : ComplexPoint X structureMapX), x ∉ Set.range (Point.map i hi) →
      (smoothClosedSupportCoclassSheaf structureMapX structureMapY i hi m d).presheaf.Γgerm x s = 0) :
    s = smoothClosedSupportCoclassSection structureMapX structureMapY i hi m d := by
  apply smoothClosedSupportCoclassSection_unique
  intro x
  by_cases hxS : x ∈ Set.range (Point.map i hi)
  · obtain ⟨z, rfl⟩ := hxS
    exact (hs z).trans (smoothClosedSupportCoclassStalk_eq_chartGerm
      structureMapX structureMapY i hi m d z (Point.map i hi z)
      (mem_smoothClosedSupportChartOpen structureMapX structureMapY i hi m d z)).symm
  · rw [hzero x hxS, smoothClosedSupportCoclassStalk_eq_zero structureMapX structureMapY i hi m d x hxS]

end AlgebraicGeometry.ComplexPoint
