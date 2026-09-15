/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.CoclassOverlap
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologySheaf
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.SupportDescent
/-!
# The global normalized smooth-support coclass section

Normal charts supply normalized Thom sections. They agree on support overlaps and vanish
off the closed image. Sheaf descent gives the unique global section with these restrictions.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
open TopCat.Presheaf

namespace AlgebraicGeometry.ComplexPoint

variable {X Y : Over (Spec ↧ℂ)}
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- The source open of a constructed holomorphic normal chart. -/
def smoothClosedSupportChartOpen (z : ComplexPoint Y) :
    Opens (ComplexPoint X) :=
  ⟨(closedImmersionHolomorphicFlatteningChart X Y i m d z).source,
    (closedImmersionHolomorphicFlatteningChart X Y i m d z).open_source⟩

theorem mem_smoothClosedSupportChartOpen (z : ComplexPoint Y) :
    Point.map i z ∈ smoothClosedSupportChartOpen i m d z :=
  closedImmersionHolomorphicFlatteningChart_mem_source X Y i m d z

/-- The target is the sheafification of the literal relative-cohomology presheaf. -/
abbrev smoothClosedSupportCoclassSheaf : TopCat.Sheaf AddCommGrpCat
    (TopCat.of (ComplexPoint X)) :=
  supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
    (Set.range (Point.map i)) (2 * (d - m))

/-- The exact normal coclass determines a section on its full chart source. -/
def smoothClosedSupportChartSheafSection (z : ComplexPoint Y) :
    (smoothClosedSupportCoclassSheaf i m d).obj.obj
      (op (smoothClosedSupportChartOpen i m d z)) :=
  (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
    (Set.range (Point.map i)) (2 * (d - m))).app _
      (smoothClosedSupportChartCoclass i m d z
        (smoothClosedSupportChartOpen i m d z) (le_refl _))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The chart sections descend uniquely with zero on the support complement. -/
theorem existsUnique_smoothClosedSupportCoclassSection :
    ∃! t : (smoothClosedSupportCoclassSheaf i m d).obj.obj (op ⊤),
      (∀ z : ComplexPoint Y,
        (smoothClosedSupportCoclassSheaf i m d).obj.map
          (homOfLE (show smoothClosedSupportChartOpen i m d z ≤ ⊤ from le_top)).op t =
            smoothClosedSupportChartSheafSection i m d z) ∧
      (smoothClosedSupportCoclassSheaf i m d).obj.map
        (homOfLE (show
          (⟨(Set.range (Point.map i))ᶜ,
            (isClosed_range_map_of_closedImmersion i).isOpen_compl⟩ :
              Opens (ComplexPoint X)) ≤ ⊤ from le_top)).op t = 0 := by
  apply TopCat.Sheaf.existsUnique_section_of_isClosed_cover
    (smoothClosedSupportCoclassSheaf i m d)
    (isClosed_range_map_of_closedImmersion i)
    (fun z => smoothClosedSupportChartOpen i m d z)
    (fun z => smoothClosedSupportChartSheafSection i m d z)
  · intro q hq
    obtain ⟨z, rfl⟩ := hq
    exact ⟨z, mem_smoothClosedSupportChartOpen i m d z⟩
  · intro z z' q hqS hq hq'
    change @supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (Set.range (Point.map i)) (2 * (d - m))
        (smoothClosedSupportChartOpen i m d z) q hq
        (smoothClosedSupportChartCoclass i m d z
          (smoothClosedSupportChartOpen i m d z) (le_refl _)) =
      @supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (Set.range (Point.map i)) (2 * (d - m))
        (smoothClosedSupportChartOpen i m d z') q hq'
        (smoothClosedSupportChartCoclass i m d z'
          (smoothClosedSupportChartOpen i m d z') (le_refl _))
    obtain ⟨W, hW, hW', hqW, heq⟩ :=
      exists_open_smoothClosedSupportChartCoclass_eq
        i m d z z' q hqS hq hq'
    apply supportRelativeCohomologyGerm_eq_of_restrict_eq
      (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
      hW hW' q hqW
    simpa only [smoothClosedSupportChartCoclass_restrict] using heq
  · intro z q hq hqS
    change @supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (Set.range (Point.map i)) (2 * (d - m))
      (smoothClosedSupportChartOpen i m d z) q hq
      (smoothClosedSupportChartCoclass i m d z
        (smoothClosedSupportChartOpen i m d z) (le_refl _)) = 0
    exact supportRelativeCohomologyGerm_eq_zero_of_not_mem
      (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
      (isClosed_range_map_of_closedImmersion i)
      (smoothClosedSupportChartOpen i m d z) q hq hqS _

/-- The global normalized section obtained by descent from the normal charts. -/
def smoothClosedSupportCoclassSection :
    (smoothClosedSupportCoclassSheaf i m d).obj.obj (op ⊤) :=
  (existsUnique_smoothClosedSupportCoclassSection i m d).choose

end AlgebraicGeometry.ComplexPoint
