/-
  Every finite cover of a compact Riemann surface is refined by a chart-disk cover.

  ## What this file proves

  The Dolbeault/Čech ladder repeatedly needs to replace an *arbitrary* finite cover `𝔘` by a
  `ChartDiskCover` (each set a coordinate disk, where `∂̄` is solvable) that *refines* `𝔘`.
  `LerayCoverExists.chartDiskCover` builds a canonical chart-disk cover from scratch, but it refines
  nothing in particular.  This file builds the refinement version:

      `exists_chartDiskCover_refinement (𝔘 : FiniteCover X) :
         ∃ (𝔇 : ChartDiskCover X) (r : 𝔇.ι → 𝔘.ι), 𝔇.toFiniteCover.IsRefinement 𝔘 r`

  ## Construction (standard compactness / shrinking)

  For each `x : X`, pick an index `coverIdx x` with `x ∈ 𝔘.U (coverIdx x)` (from `𝔘.covers`).  The
  chart `extChartAt 𝓘(ℝ,ℂ) x` is continuous at `x`, `extChartAt … x x` lies in the (open) target, and
  `𝔘.U (coverIdx x)` is an open neighborhood of `x`.  So there is a radius `refRadius x > 0` with both
  `closedBall (extChartAt … x x) (refRadius x) ⊆ (extChartAt … x).target` and the coordinate disk
  `(extChartAt … x) ⁻¹' ball (extChartAt … x x) (refRadius x) ∩ source ⊆ 𝔘.U (coverIdx x)`.  These
  disks are an open cover of compact `X`; extract a finite subcover indexed by a `Finset`, assemble the
  `ChartDiskCover`, and read off `IsRefinement` from the per-point disk-inside-cover-set containment.

  All declarations are complete; `#print axioms exists_chartDiskCover_refinement` is
  `[propext, Classical.choice, Quot.sound]`.
-/
import KirovDolbeault.Dolbeault.ChartDiskCover
import KirovDolbeault.Dolbeault.CechRefinement

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The per-point shrinking lemma

For each `x` and open neighborhood `V ∋ x`, a small coordinate disk around `x` fits inside both the
chart target (closed ball) and `V` (open disk). -/

/-- For each `x` and open neighborhood `V` of `x`, there is a radius `ρ > 0` whose *closed* coordinate
ball lies in the chart target and whose coordinate disk lands inside `V`.

`(extChartAt … x).symm` is continuous at `c := extChartAt … x x` and sends `c ↦ x ∈ V`, so
`(extChartAt … x).symm ⁻¹' V` is a neighborhood of `c`; intersecting with the (open) target and
extracting a metric ball `ball c ρ₁` gives the radius (halved for the closed-ball clause).  Membership
in `V` follows since `(extChartAt … x).symm` left-inverts `extChartAt … x` on the source. -/
theorem exists_radius_disk_subset (x : X) (V : Set X) (hVopen : IsOpen V) (hxV : x ∈ V) :
    ∃ ρ > 0,
      Metric.closedBall (extChartAt 𝓘(ℝ, ℂ) x x) ρ ⊆ (extChartAt 𝓘(ℝ, ℂ) x).target ∧
      (extChartAt 𝓘(ℝ, ℂ) x) ⁻¹' Metric.ball (extChartAt 𝓘(ℝ, ℂ) x x) ρ
          ∩ (extChartAt 𝓘(ℝ, ℂ) x).source ⊆ V := by
  set e := extChartAt 𝓘(ℝ, ℂ) x with he
  set c := e x with hc
  have hsymmnhd : e.symm ⁻¹' V ∈ nhds c := by
    have hVnhd : V ∈ nhds (e.symm c) := by
      rw [hc, he, extChartAt_to_inv (I := 𝓘(ℝ, ℂ)) x]; exact hVopen.mem_nhds hxV
    have := (continuousAt_extChartAt_symm x).preimage_mem_nhds hVnhd
    simpa [he, hc] using this
  have htgtnhd : e.target ∈ nhds c := (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hsymmnhd htgtnhd)
  refine ⟨ρ₁ / 2, half_pos hρ₁pos, ?_, ?_⟩
  · exact (Metric.closedBall_subset_ball (half_lt_self hρ₁pos)).trans
      (hρ₁sub.trans Set.inter_subset_right)
  · rintro y ⟨hyball, hysrc⟩
    have hyball' : e y ∈ Metric.ball c ρ₁ := Metric.ball_subset_ball (by linarith) hyball
    have hmem : e y ∈ e.symm ⁻¹' V := (hρ₁sub hyball').1
    rwa [Set.mem_preimage, e.left_inv hysrc] at hmem

namespace exists_chartDiskCover_refinement

variable (𝔘 : FiniteCover X)

/-! ### Per-point data: a chosen cover index and a chart-disk inside that cover set. -/

/-- For each `x`, an index `i` of the cover with `x ∈ 𝔘.U i` (exists by `𝔘.covers`). -/
theorem exists_coverIdx (x : X) : ∃ i, x ∈ ((𝔘.U i : Opens X) : Set X) := by
  have hx : x ∈ ((⨆ i, 𝔘.U i : Opens X) : Set X) := by rw [𝔘.covers]; trivial
  rwa [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at hx

/-- The chosen cover index containing `x`. -/
noncomputable def coverIdx (x : X) : 𝔘.ι := (exists_coverIdx 𝔘 x).choose

theorem coverIdx_mem (x : X) : x ∈ ((𝔘.U (coverIdx 𝔘 x) : Opens X) : Set X) :=
  (exists_coverIdx 𝔘 x).choose_spec

/-- The shrinking-lemma data applied to `V = 𝔘.U (coverIdx x)`. -/
theorem exists_refRadius (x : X) :
    ∃ ρ > 0,
      Metric.closedBall (extChartAt 𝓘(ℝ, ℂ) x x) ρ ⊆ (extChartAt 𝓘(ℝ, ℂ) x).target ∧
      (extChartAt 𝓘(ℝ, ℂ) x) ⁻¹' Metric.ball (extChartAt 𝓘(ℝ, ℂ) x x) ρ
          ∩ (extChartAt 𝓘(ℝ, ℂ) x).source ⊆ ((𝔘.U (coverIdx 𝔘 x) : Opens X) : Set X) :=
  exists_radius_disk_subset x _ (𝔘.U (coverIdx 𝔘 x)).isOpen (coverIdx_mem 𝔘 x)

/-- The chosen disk radius around `x`. -/
noncomputable def refRadius (x : X) : ℝ := (exists_refRadius 𝔘 x).choose

theorem refRadius_pos (x : X) : 0 < refRadius 𝔘 x := (exists_refRadius 𝔘 x).choose_spec.1

theorem closedBall_refRadius_subset_target (x : X) :
    Metric.closedBall (extChartAt 𝓘(ℝ, ℂ) x x) (refRadius 𝔘 x) ⊆ (extChartAt 𝓘(ℝ, ℂ) x).target :=
  (exists_refRadius 𝔘 x).choose_spec.2.1

/-- The chart-disk neighborhood of `x` whose chart-preimage ball sits inside `𝔘.U (coverIdx x)`.
Written with the chart-preimage first to match the `ChartDiskCover.isDisk` field directly. -/
def refDiskNbhd (x : X) : Set X :=
  (extChartAt 𝓘(ℝ, ℂ) x) ⁻¹' Metric.ball (extChartAt 𝓘(ℝ, ℂ) x x) (refRadius 𝔘 x)
    ∩ (extChartAt 𝓘(ℝ, ℂ) x).source

theorem refDiskNbhd_subset_cover (x : X) :
    refDiskNbhd 𝔘 x ⊆ ((𝔘.U (coverIdx 𝔘 x) : Opens X) : Set X) :=
  (exists_refRadius 𝔘 x).choose_spec.2.2

theorem refDiskNbhd_isOpen (x : X) : IsOpen (refDiskNbhd 𝔘 x) := by
  rw [refDiskNbhd, Set.inter_comm]
  exact (continuousOn_extChartAt x).isOpen_inter_preimage (isOpen_extChartAt_source x)
    Metric.isOpen_ball

theorem mem_refDiskNbhd (x : X) : x ∈ refDiskNbhd 𝔘 x :=
  ⟨by simp only [Set.mem_preimage]; exact Metric.mem_ball_self (refRadius_pos 𝔘 x),
    mem_extChartAt_source x⟩

/-! ### Finite subcover and assembly into a `ChartDiskCover`. -/

theorem exists_finite_refDiskNbhd_cover :
    ∃ s : Finset X, (⋃ x ∈ s, refDiskNbhd 𝔘 x) = Set.univ := by
  have hcov : Set.univ ⊆ ⋃ x : X, refDiskNbhd 𝔘 x := fun y _ =>
    Set.mem_iUnion.mpr ⟨y, mem_refDiskNbhd 𝔘 y⟩
  obtain ⟨s, hs⟩ := IsCompact.elim_finite_subcover isCompact_univ
    (fun x : X => refDiskNbhd 𝔘 x) (fun x => refDiskNbhd_isOpen 𝔘 x) hcov
  exact ⟨s, Set.eq_univ_of_univ_subset hs⟩

/-- The finite set of centres of the refining chart-disk cover. -/
noncomputable def centers : Finset X := (exists_finite_refDiskNbhd_cover 𝔘).choose

theorem centers_cover : (⋃ x ∈ centers 𝔘, refDiskNbhd 𝔘 x) = Set.univ :=
  (exists_finite_refDiskNbhd_cover 𝔘).choose_spec

/-- The centre of `X` indexed by `Fin (centers.card)`. -/
noncomputable def center (i : Fin (centers 𝔘).card) : X := ((centers 𝔘).equivFin.symm i : X)

/-- The refining chart-disk cover of `X` whose every set sits inside some `𝔘.U`. -/
noncomputable def cover : ChartDiskCover X where
  ι := Fin (centers 𝔘).card
  U := fun i => ⟨refDiskNbhd 𝔘 (center 𝔘 i), refDiskNbhd_isOpen 𝔘 _⟩
  covers := by
    rw [← TopologicalSpace.Opens.coe_inj, TopologicalSpace.Opens.coe_iSup]
    show (⋃ i : Fin (centers 𝔘).card, refDiskNbhd 𝔘 (center 𝔘 i)) = _
    have hreindex :
        (⋃ i : Fin (centers 𝔘).card, refDiskNbhd 𝔘 (center 𝔘 i))
          = ⋃ j : {x // x ∈ centers 𝔘}, refDiskNbhd 𝔘 j.1 :=
      ((centers 𝔘).equivFin.symm.surjective).iUnion_comp
        (fun j : {x // x ∈ centers 𝔘} => refDiskNbhd 𝔘 j.1)
    rw [hreindex, Set.iUnion_subtype, centers_cover]
    rfl
  center := center 𝔘
  radius := fun i => refRadius 𝔘 (center 𝔘 i)
  radius_pos := fun i => refRadius_pos 𝔘 _
  closedBall_subset_target := fun i => closedBall_refRadius_subset_target 𝔘 _
  isDisk := fun i => rfl

@[simp] theorem cover_U (i : (cover 𝔘).ι) :
    ((cover 𝔘).U i : Set X) = refDiskNbhd 𝔘 (center 𝔘 i) := rfl

/-- The refinement index map: each disk's centre lies in the cover set `𝔘.U (coverIdx center)`. -/
noncomputable def refMap (i : (cover 𝔘).ι) : 𝔘.ι := coverIdx 𝔘 (center 𝔘 i)

theorem isRefinement : (cover 𝔘).toFiniteCover.IsRefinement 𝔘 (refMap 𝔘) := fun i =>
  show ((cover 𝔘).U i : Set X) ⊆ _ from by
    rw [cover_U]; exact refDiskNbhd_subset_cover 𝔘 (center 𝔘 i)

end exists_chartDiskCover_refinement

/-- **Every finite cover of compact `X` is refined by a chart-disk cover.**  For each point pick a
cover set containing it (`coverIdx`), shrink a coordinate disk around the point to fit inside that
cover set and the chart target (`exists_radius_disk_subset`), extract a finite subcover by compactness,
and assemble the `ChartDiskCover`; the refinement map sends each disk's centre to its chosen cover
index. -/
theorem exists_chartDiskCover_refinement (𝔘 : FiniteCover X) :
    ∃ (𝔇 : ChartDiskCover X) (r : 𝔇.ι → 𝔘.ι),
      FiniteCover.IsRefinement 𝔇.toFiniteCover 𝔘 r :=
  ⟨exists_chartDiskCover_refinement.cover 𝔘, exists_chartDiskCover_refinement.refMap 𝔘,
    exists_chartDiskCover_refinement.isRefinement 𝔘⟩

end Jacobians.Dolbeault
