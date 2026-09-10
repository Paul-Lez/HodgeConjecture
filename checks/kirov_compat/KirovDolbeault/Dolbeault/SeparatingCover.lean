/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.ChartDiskRefinement

/-!
# The separating chart-disk cover with a reserved privately-covered disk

The fine-sheaf residue lane (FineResidue) needs a chart-disk cover `𝔇` with two pieces of
geometric discipline that the canonical `chartDiskCover` does not provide:

1. **Point separation** (`SeparatesPoles`): each point of a prescribed finite set `S`
   (the support of `K = div ω₀`) lies in NO overlap of two distinct cover sets.
2. **A reserved privately-covered disk**: one distinguished index `j₀` and a nonempty open
   `W ⊆ U j₀` meeting no other cover set — so every `a ∈ W` is `MLIsolated`, which is what the
   `CupMLWitnessR` construction needs: a freely chosen isolated point per `(D, v)`, avoiding a
   finite bad set inside the (infinite) `W`.

This file builds both at once, refining an arbitrary finite cover `𝔘` (so the proven Čech
refinement *injectivity* can compare `H¹` at the new cover against the canonical one):

## Construction

Pick a reserved point `p ∉ S` (`X` is infinite).  Shrink a coordinate disk `U₀` around `p`
inside `𝔘.U (idx p) ∩ Sᶜ` (`exists_radius_disk_subset`), and let `W`/`resCore` be the
half-radius open disk and *closed* (compact) half-radius disk inside it.  Every other point
`x ∉ resCore` gets a coordinate disk inside

  `𝔘.U (idx x) ∩ resCoreᶜ ∩ (S.erase x)ᶜ`

— avoiding the private core and every `S`-point except possibly `x` itself.  `X ∖ U₀` is
compact and covered by these disks (it misses `resCore ⊆ U₀`); a finite subcover plus `U₀`
assembles into a `ChartDiskCover` indexed by `Option (Fin n)` (`none` = the reserved disk).

* Separation: an overlap of two distinct sets contains an `S`-point `z` only if both sets are
  good disks with centers `= z` — but distinct indices have distinct centers.
* Privacy: `W ⊆ resCore` while every good disk avoids `resCore`.

## Main declarations

* `exists_separatingChartDiskCover` — the headline package: the refining cover, the
  separation property for `S`, and the reserved nonempty open `W` with the privacy property.
-/

open scoped Manifold ContDiff Topology Classical
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace SeparatingCover

/-! ### Generic point-picking: nonempty opens of a complex 1-manifold are infinite -/

/-- A nonempty open subset of `X` is infinite (local copy of the `TracePullback` /
`DegreeOneSphere` lemma, kept here to avoid importing those heavy files). -/
private theorem infinite_of_isOpen_nonempty {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) :
    W.Infinite := by
  obtain ⟨y₀, hy₀⟩ := hne
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ y₀ with hc
  set U : Set X := c.source ∩ W with hU
  have hUopen : IsOpen U := c.open_source.inter hW
  have hy₀U : y₀ ∈ U := ⟨mem_chart_source ℂ y₀, hy₀⟩
  have hcU_open : IsOpen (c '' U) := c.isOpen_image_of_subset_source hUopen Set.inter_subset_left
  have hcy₀ : c y₀ ∈ c '' U := ⟨y₀, hy₀U, rfl⟩
  haveI : Filter.NeBot (𝓝[≠] (c y₀)) := Module.punctured_nhds_neBot ℂ ℂ (c y₀)
  have hcU_inf : (c '' U).Infinite := infinite_of_mem_nhds (c y₀) (hcU_open.mem_nhds hcy₀)
  have hsub : c '' U ⊆ c.target := by rintro _ ⟨x, hx, rfl⟩; exact c.map_source hx.1
  have himg : (c.symm '' (c '' U)).Infinite := hcU_inf.image (c.symm.injOn.mono hsub)
  refine himg.mono ?_
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  rw [c.left_inv hx.1]; exact hx.2

/-- Removing a finite set from a nonempty open subset of `X` leaves a point. -/
theorem exists_mem_open_notMem_finite {W C : Set X} (hW : IsOpen W) (hne : W.Nonempty)
    (hC : C.Finite) : ∃ y ∈ W, y ∉ C := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  exact (infinite_of_isOpen_nonempty hW hne) (hC.subset fun y hy => h y hy)

variable (𝔘 : FiniteCover X) (S : Finset X)

/-- The chosen cover index containing `x` (reuse of the `ChartDiskRefinement` chooser). -/
noncomputable def idx (x : X) : 𝔘.ι := exists_chartDiskCover_refinement.coverIdx 𝔘 x

theorem idx_mem (x : X) : x ∈ ((𝔘.U (idx 𝔘 x) : Opens X) : Set X) :=
  exists_chartDiskCover_refinement.coverIdx_mem 𝔘 x

/-! ### The reserved point and its private disk -/

theorem exists_reservedPoint : ∃ p : X, p ∉ (S : Set X) := by
  haveI : Nonempty X := inferInstance
  obtain ⟨p, _, hp⟩ :=
    exists_mem_open_notMem_finite isOpen_univ Set.univ_nonempty S.finite_toSet
  exact ⟨p, hp⟩

/-- The reserved point `p ∉ S` around which the privately-covered disk is built. -/
noncomputable def resPt : X := (exists_reservedPoint (X := X) S).choose

theorem resPt_notMem : resPt (X := X) S ∉ (S : Set X) :=
  (exists_reservedPoint (X := X) S).choose_spec

/-- The open neighborhood of the reserved point that the reserved disk must fit in: the chosen
`𝔘`-set minus the whole of `S`. -/
def resNbhd : Set X := ((𝔘.U (idx 𝔘 (resPt S)) : Opens X) : Set X) ∩ (↑S : Set X)ᶜ

theorem resNbhd_isOpen : IsOpen (resNbhd 𝔘 S) :=
  (𝔘.U (idx 𝔘 (resPt S))).isOpen.inter S.finite_toSet.isClosed.isOpen_compl

theorem resPt_mem_resNbhd : resPt S ∈ resNbhd 𝔘 S :=
  ⟨idx_mem 𝔘 (resPt S), resPt_notMem S⟩

theorem exists_resRadius :
    ∃ ρ > 0,
      Metric.closedBall (extChartAt 𝓘(ℝ, ℂ) (resPt S) (resPt S)) ρ
          ⊆ (extChartAt 𝓘(ℝ, ℂ) (resPt S)).target ∧
      (extChartAt 𝓘(ℝ, ℂ) (resPt S)) ⁻¹' Metric.ball (extChartAt 𝓘(ℝ, ℂ) (resPt S) (resPt S)) ρ
          ∩ (extChartAt 𝓘(ℝ, ℂ) (resPt S)).source ⊆ resNbhd 𝔘 S :=
  exists_radius_disk_subset (resPt S) _ (resNbhd_isOpen 𝔘 S) (resPt_mem_resNbhd 𝔘 S)

/-- The radius of the reserved disk. -/
noncomputable def resRadius : ℝ := (exists_resRadius 𝔘 S).choose

theorem resRadius_pos : 0 < resRadius 𝔘 S := (exists_resRadius 𝔘 S).choose_spec.1

theorem closedBall_resRadius_subset_target :
    Metric.closedBall (extChartAt 𝓘(ℝ, ℂ) (resPt S) (resPt S)) (resRadius 𝔘 S)
      ⊆ (extChartAt 𝓘(ℝ, ℂ) (resPt S)).target :=
  (exists_resRadius 𝔘 S).choose_spec.2.1

/-- **The reserved disk** `U₀` (the distinguished cover set, written in the
`ChartDiskCover.isDisk` shape). -/
def resDisk : Set X :=
  (extChartAt 𝓘(ℝ, ℂ) (resPt S)) ⁻¹'
      Metric.ball (extChartAt 𝓘(ℝ, ℂ) (resPt S) (resPt S)) (resRadius 𝔘 S)
    ∩ (extChartAt 𝓘(ℝ, ℂ) (resPt S)).source

theorem resDisk_subset_resNbhd : resDisk 𝔘 S ⊆ resNbhd 𝔘 S :=
  (exists_resRadius 𝔘 S).choose_spec.2.2

theorem resDisk_isOpen : IsOpen (resDisk 𝔘 S) := by
  rw [resDisk, Set.inter_comm]
  exact (continuousOn_extChartAt (resPt S)).isOpen_inter_preimage
    (isOpen_extChartAt_source (resPt S)) Metric.isOpen_ball

theorem resDisk_disjoint_S : ∀ z ∈ resDisk 𝔘 S, z ∉ (S : Set X) := fun _ hz =>
  (resDisk_subset_resNbhd 𝔘 S hz).2

/-- **The private compact core**: the `chart⁻¹`-image of the *closed* half-radius ball.  Good
disks avoid it; the open zone `resZone` sits inside it. -/
def resCore : Set X :=
  (extChartAt 𝓘(ℝ, ℂ) (resPt S)).symm ''
    Metric.closedBall (extChartAt 𝓘(ℝ, ℂ) (resPt S) (resPt S)) (resRadius 𝔘 S / 2)

theorem closedBall_half_subset_target :
    Metric.closedBall (extChartAt 𝓘(ℝ, ℂ) (resPt S) (resPt S)) (resRadius 𝔘 S / 2)
      ⊆ (extChartAt 𝓘(ℝ, ℂ) (resPt S)).target :=
  (Metric.closedBall_subset_closedBall (half_le_self (resRadius_pos 𝔘 S).le)).trans
    (closedBall_resRadius_subset_target 𝔘 S)

theorem resCore_isCompact : IsCompact (resCore 𝔘 S) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((continuousOn_extChartAt_symm (resPt S)).mono (closedBall_half_subset_target 𝔘 S))

theorem resCore_isClosed : IsClosed (resCore 𝔘 S) := (resCore_isCompact 𝔘 S).isClosed

theorem resCore_subset_resDisk : resCore 𝔘 S ⊆ resDisk 𝔘 S := by
  rintro _ ⟨w, hw, rfl⟩
  have hwt : w ∈ (extChartAt 𝓘(ℝ, ℂ) (resPt S)).target := closedBall_half_subset_target 𝔘 S hw
  refine ⟨?_, (extChartAt 𝓘(ℝ, ℂ) (resPt S)).map_target hwt⟩
  rw [Set.mem_preimage, (extChartAt 𝓘(ℝ, ℂ) (resPt S)).right_inv hwt]
  exact lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (half_lt_self (resRadius_pos 𝔘 S))

/-- **The reserved open zone** `W`: the open half-radius disk.  Nonempty (contains `p`), inside
the reserved disk, inside the private core — so it meets no good disk. -/
def resZone : Set X :=
  (extChartAt 𝓘(ℝ, ℂ) (resPt S)) ⁻¹'
      Metric.ball (extChartAt 𝓘(ℝ, ℂ) (resPt S) (resPt S)) (resRadius 𝔘 S / 2)
    ∩ (extChartAt 𝓘(ℝ, ℂ) (resPt S)).source

theorem resZone_isOpen : IsOpen (resZone 𝔘 S) := by
  rw [resZone, Set.inter_comm]
  exact (continuousOn_extChartAt (resPt S)).isOpen_inter_preimage
    (isOpen_extChartAt_source (resPt S)) Metric.isOpen_ball

theorem resPt_mem_resZone : resPt S ∈ resZone 𝔘 S :=
  ⟨by simp only [Set.mem_preimage]
      exact Metric.mem_ball_self (half_pos (resRadius_pos 𝔘 S)),
    mem_extChartAt_source (resPt S)⟩

theorem resZone_subset_resCore : resZone 𝔘 S ⊆ resCore 𝔘 S := fun y ⟨hyb, hysrc⟩ =>
  ⟨extChartAt 𝓘(ℝ, ℂ) (resPt S) y, Metric.ball_subset_closedBall hyb,
    (extChartAt 𝓘(ℝ, ℂ) (resPt S)).left_inv hysrc⟩

theorem resZone_subset_resDisk : resZone 𝔘 S ⊆ resDisk 𝔘 S :=
  (resZone_subset_resCore 𝔘 S).trans (resCore_subset_resDisk 𝔘 S)

/-! ### The good disks: coordinate disks avoiding the core and (almost all of) `S` -/

/-- A **good point**: one outside the private core (every point the good disks must cover). -/
def Good : Type _ := {x : X // x ∉ resCore 𝔘 S}

/-- The open neighborhood a good disk must fit in: the chosen `𝔘`-set, minus the private core,
minus every `S`-point except possibly the center itself. -/
def goodNbhd (x : Good 𝔘 S) : Set X :=
  ((𝔘.U (idx 𝔘 x.1) : Opens X) : Set X) ∩ (resCore 𝔘 S)ᶜ ∩ (↑(S.erase x.1) : Set X)ᶜ

theorem goodNbhd_isOpen (x : Good 𝔘 S) : IsOpen (goodNbhd 𝔘 S x) :=
  (((𝔘.U (idx 𝔘 x.1)).isOpen.inter (resCore_isClosed 𝔘 S).isOpen_compl).inter
    (S.erase x.1).finite_toSet.isClosed.isOpen_compl)

theorem mem_goodNbhd (x : Good 𝔘 S) : x.1 ∈ goodNbhd 𝔘 S x :=
  ⟨⟨idx_mem 𝔘 x.1, x.2⟩, fun h => (Finset.mem_erase.mp h).1 rfl⟩

theorem exists_goodRadius (x : Good 𝔘 S) :
    ∃ ρ > 0,
      Metric.closedBall (extChartAt 𝓘(ℝ, ℂ) x.1 x.1) ρ ⊆ (extChartAt 𝓘(ℝ, ℂ) x.1).target ∧
      (extChartAt 𝓘(ℝ, ℂ) x.1) ⁻¹' Metric.ball (extChartAt 𝓘(ℝ, ℂ) x.1 x.1) ρ
          ∩ (extChartAt 𝓘(ℝ, ℂ) x.1).source ⊆ goodNbhd 𝔘 S x :=
  exists_radius_disk_subset x.1 _ (goodNbhd_isOpen 𝔘 S x) (mem_goodNbhd 𝔘 S x)

/-- The radius of the good disk at `x`. -/
noncomputable def goodRadius (x : Good 𝔘 S) : ℝ := (exists_goodRadius 𝔘 S x).choose

theorem goodRadius_pos (x : Good 𝔘 S) : 0 < goodRadius 𝔘 S x :=
  (exists_goodRadius 𝔘 S x).choose_spec.1

theorem closedBall_goodRadius_subset_target (x : Good 𝔘 S) :
    Metric.closedBall (extChartAt 𝓘(ℝ, ℂ) x.1 x.1) (goodRadius 𝔘 S x)
      ⊆ (extChartAt 𝓘(ℝ, ℂ) x.1).target :=
  (exists_goodRadius 𝔘 S x).choose_spec.2.1

/-- The good disk at `x` (in the `ChartDiskCover.isDisk` shape). -/
def goodDisk (x : Good 𝔘 S) : Set X :=
  (extChartAt 𝓘(ℝ, ℂ) x.1) ⁻¹' Metric.ball (extChartAt 𝓘(ℝ, ℂ) x.1 x.1) (goodRadius 𝔘 S x)
    ∩ (extChartAt 𝓘(ℝ, ℂ) x.1).source

theorem goodDisk_subset_goodNbhd (x : Good 𝔘 S) : goodDisk 𝔘 S x ⊆ goodNbhd 𝔘 S x :=
  (exists_goodRadius 𝔘 S x).choose_spec.2.2

theorem goodDisk_isOpen (x : Good 𝔘 S) : IsOpen (goodDisk 𝔘 S x) := by
  rw [goodDisk, Set.inter_comm]
  exact (continuousOn_extChartAt x.1).isOpen_inter_preimage
    (isOpen_extChartAt_source x.1) Metric.isOpen_ball

theorem mem_goodDisk_self (x : Good 𝔘 S) : x.1 ∈ goodDisk 𝔘 S x :=
  ⟨by simp only [Set.mem_preimage]; exact Metric.mem_ball_self (goodRadius_pos 𝔘 S x),
    mem_extChartAt_source x.1⟩

theorem goodDisk_disjoint_core (x : Good 𝔘 S) : ∀ z ∈ goodDisk 𝔘 S x, z ∉ resCore 𝔘 S :=
  fun _ hz => (goodDisk_subset_goodNbhd 𝔘 S x hz).1.2

/-- A point of `S` inside a good disk must be the disk's center. -/
theorem eq_center_of_mem_goodDisk_of_mem_S (x : Good 𝔘 S) {z : X} (hz : z ∈ goodDisk 𝔘 S x)
    (hzS : z ∈ (S : Set X)) : z = x.1 := by
  have h := (goodDisk_subset_goodNbhd 𝔘 S x hz).2
  by_contra hne
  exact h (Finset.mem_erase.mpr ⟨hne, hzS⟩)

/-! ### The finite subcover and the assembled cover -/

theorem exists_goodFinset :
    ∃ F : Finset (Good 𝔘 S), (resDisk 𝔘 S)ᶜ ⊆ ⋃ x ∈ F, goodDisk 𝔘 S x := by
  have hcompact : IsCompact (resDisk 𝔘 S)ᶜ := (resDisk_isOpen 𝔘 S).isClosed_compl.isCompact
  have hcov : (resDisk 𝔘 S)ᶜ ⊆ ⋃ x : Good 𝔘 S, goodDisk 𝔘 S x := by
    intro y hy
    have hyc : y ∉ resCore 𝔘 S := fun hc => hy (resCore_subset_resDisk 𝔘 S hc)
    exact Set.mem_iUnion.mpr ⟨⟨y, hyc⟩, mem_goodDisk_self 𝔘 S ⟨y, hyc⟩⟩
  exact hcompact.elim_finite_subcover _ (goodDisk_isOpen 𝔘 S) hcov

/-- The finite set of good centers. -/
noncomputable def goodCenters : Finset (Good 𝔘 S) := (exists_goodFinset 𝔘 S).choose

theorem goodCenters_cover : (resDisk 𝔘 S)ᶜ ⊆ ⋃ x ∈ goodCenters 𝔘 S, goodDisk 𝔘 S x :=
  (exists_goodFinset 𝔘 S).choose_spec

/-- The good center indexed by `Fin (goodCenters.card)`. -/
noncomputable def goodIdx (i : Fin (goodCenters 𝔘 S).card) : Good 𝔘 S :=
  ((goodCenters 𝔘 S).equivFin.symm i).1

theorem goodIdx_injective : Function.Injective (goodIdx 𝔘 S) := fun _ _ h =>
  (goodCenters 𝔘 S).equivFin.symm.injective (Subtype.ext h)

/-- The index type of the separating cover: `none` is the reserved disk, `some i` the good
disks. -/
abbrev Index : Type := Option (Fin (goodCenters 𝔘 S).card)

/-- The centers of the separating cover. -/
noncomputable def center : Index 𝔘 S → X
  | none => resPt S
  | some i => (goodIdx 𝔘 S i).1

/-- The radii of the separating cover. -/
noncomputable def radius : Index 𝔘 S → ℝ
  | none => resRadius 𝔘 S
  | some i => goodRadius 𝔘 S (goodIdx 𝔘 S i)

/-- The sets of the separating cover. -/
noncomputable def coverSet : Index 𝔘 S → Set X
  | none => resDisk 𝔘 S
  | some i => goodDisk 𝔘 S (goodIdx 𝔘 S i)

theorem coverSet_isOpen : ∀ i, IsOpen (coverSet 𝔘 S i)
  | none => resDisk_isOpen 𝔘 S
  | some i => goodDisk_isOpen 𝔘 S (goodIdx 𝔘 S i)

/-- **The separating chart-disk cover.** -/
noncomputable def cover : ChartDiskCover X where
  ι := Index 𝔘 S
  U := fun i => ⟨coverSet 𝔘 S i, coverSet_isOpen 𝔘 S i⟩
  covers := by
    rw [← TopologicalSpace.Opens.coe_inj, TopologicalSpace.Opens.coe_iSup,
      TopologicalSpace.Opens.coe_top]
    apply Set.eq_univ_of_forall
    intro y
    rw [Set.mem_iUnion]
    by_cases hy : y ∈ resDisk 𝔘 S
    · exact ⟨none, hy⟩
    · have hy' := goodCenters_cover 𝔘 S hy
      rw [Set.mem_iUnion₂] at hy'
      obtain ⟨x, hxF, hyx⟩ := hy'
      refine ⟨some ((goodCenters 𝔘 S).equivFin ⟨x, hxF⟩), ?_⟩
      show y ∈ goodDisk 𝔘 S (goodIdx 𝔘 S ((goodCenters 𝔘 S).equivFin ⟨x, hxF⟩))
      rw [goodIdx, Equiv.symm_apply_apply]
      exact hyx
  center := center 𝔘 S
  radius := radius 𝔘 S
  radius_pos := fun i => by
    cases i with
    | none => exact resRadius_pos 𝔘 S
    | some i => exact goodRadius_pos 𝔘 S (goodIdx 𝔘 S i)
  closedBall_subset_target := fun i => by
    cases i with
    | none => exact closedBall_resRadius_subset_target 𝔘 S
    | some i => exact closedBall_goodRadius_subset_target 𝔘 S (goodIdx 𝔘 S i)
  isDisk := fun i => by cases i <;> rfl

@[simp] theorem cover_U_none : (((cover 𝔘 S).U none : Opens X) : Set X) = resDisk 𝔘 S := rfl

@[simp] theorem cover_U_some (i : Fin (goodCenters 𝔘 S).card) :
    (((cover 𝔘 S).U (some i) : Opens X) : Set X) = goodDisk 𝔘 S (goodIdx 𝔘 S i) := rfl

/-! ### The three output properties -/

/-- The refinement map into `𝔘`. -/
noncomputable def refMap : (cover 𝔘 S).ι → 𝔘.ι
  | none => idx 𝔘 (resPt S)
  | some i => idx 𝔘 (goodIdx 𝔘 S i).1

/-- **Refinement**: every set of the separating cover sits inside its chosen `𝔘`-set. -/
theorem cover_isRefinement :
    FiniteCover.IsRefinement (cover 𝔘 S).toFiniteCover 𝔘 (refMap 𝔘 S) := by
  intro j
  cases j with
  | none =>
    intro z hz
    exact (resDisk_subset_resNbhd 𝔘 S hz).1
  | some i =>
    intro z hz
    exact (goodDisk_subset_goodNbhd 𝔘 S (goodIdx 𝔘 S i) hz).1.1

/-- **Separation**: no point of `S` lies in the overlap of two distinct cover sets. -/
theorem cover_separates :
    ∀ i j : (cover 𝔘 S).ι, i ≠ j →
      ∀ z ∈ (((cover 𝔘 S).U i : Opens X) : Set X) ∩ (((cover 𝔘 S).U j : Opens X) : Set X),
        z ∉ (S : Set X) := by
  intro i j hij z hz hzS
  cases i with
  | none => exact resDisk_disjoint_S 𝔘 S z hz.1 hzS
  | some k =>
    cases j with
    | none => exact resDisk_disjoint_S 𝔘 S z hz.2 hzS
    | some l =>
      have hk : z = (goodIdx 𝔘 S k).1 :=
        eq_center_of_mem_goodDisk_of_mem_S 𝔘 S (goodIdx 𝔘 S k) hz.1 hzS
      have hl : z = (goodIdx 𝔘 S l).1 :=
        eq_center_of_mem_goodDisk_of_mem_S 𝔘 S (goodIdx 𝔘 S l) hz.2 hzS
      apply hij
      have : goodIdx 𝔘 S k = goodIdx 𝔘 S l := Subtype.ext (hk ▸ hl)
      exact congrArg some (goodIdx_injective 𝔘 S this)

/-- **Privacy**: the reserved zone meets no cover set other than the reserved disk. -/
theorem cover_resZone_private :
    ∀ w ∈ resZone 𝔘 S, ∀ i : (cover 𝔘 S).ι, i ≠ none →
      w ∉ (((cover 𝔘 S).U i : Opens X) : Set X) := by
  intro w hw i hi
  cases i with
  | none => exact absurd rfl hi
  | some k =>
    intro hwk
    exact goodDisk_disjoint_core 𝔘 S (goodIdx 𝔘 S k) w hwk (resZone_subset_resCore 𝔘 S hw)

end SeparatingCover

/-- **The separating chart-disk cover with a reserved privately-covered disk** (the cover-lane
bill of materials, item 1).  For every finite cover `𝔘` and finite point set `S` there is a
chart-disk cover `𝔇` refining `𝔘`, together with a distinguished index `j₀` and a nonempty
open `W`, such that:

* no point of `S` lies in an overlap of two distinct cover sets (so `SeparatesPoles 𝔇 K`
  holds for every divisor `K` with `K.support ⊆ S`);
* `W ⊆ U j₀` and `W` meets **no other** cover set — every `a ∈ W` is isolated in the cover
  (`MLIsolated`), the input of the `CupMLWitnessR` one-point-cocycle construction;
* `W` avoids `S` entirely (so the `ω₀`-slot is nonvanishing on all of `W` when
  `S = (div ω₀).support`). -/
theorem exists_separatingChartDiskCover (𝔘 : FiniteCover X) (S : Finset X) :
    ∃ (𝔇 : ChartDiskCover X) (r : 𝔇.ι → 𝔘.ι) (j₀ : 𝔇.ι) (W : Opens X),
      FiniteCover.IsRefinement 𝔇.toFiniteCover 𝔘 r ∧
      (∀ i j : 𝔇.ι, i ≠ j →
        ∀ z ∈ ((𝔇.U i : Opens X) : Set X) ∩ ((𝔇.U j : Opens X) : Set X), z ∉ (S : Set X)) ∧
      (W : Set X).Nonempty ∧
      (W : Set X) ⊆ ((𝔇.U j₀ : Opens X) : Set X) ∧
      (∀ w ∈ (W : Set X), ∀ i : 𝔇.ι, i ≠ j₀ → w ∉ ((𝔇.U i : Opens X) : Set X)) ∧
      (∀ w ∈ (W : Set X), w ∉ (S : Set X)) := by
  refine ⟨SeparatingCover.cover 𝔘 S, SeparatingCover.refMap 𝔘 S, none,
    ⟨SeparatingCover.resZone 𝔘 S, SeparatingCover.resZone_isOpen 𝔘 S⟩,
    SeparatingCover.cover_isRefinement 𝔘 S, SeparatingCover.cover_separates 𝔘 S,
    ⟨SeparatingCover.resPt S, SeparatingCover.resPt_mem_resZone 𝔘 S⟩,
    SeparatingCover.resZone_subset_resDisk 𝔘 S, ?_, ?_⟩
  · intro w hw i hi
    exact SeparatingCover.cover_resZone_private 𝔘 S w hw i hi
  · intro w hw
    exact SeparatingCover.resDisk_disjoint_S 𝔘 S w (SeparatingCover.resZone_subset_resDisk 𝔘 S hw)

end Jacobians.Dolbeault
