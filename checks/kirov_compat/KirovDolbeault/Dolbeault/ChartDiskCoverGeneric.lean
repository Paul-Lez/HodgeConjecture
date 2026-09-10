/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.LerayCoverExists
import KirovDolbeault.Dolbeault.SkyscraperProductWitness

/-!
# Every chart-disk cover is Leray and locally realizable

`LerayCoverExists` and `SkyscraperProductWitness` prove `IsLeray` and `LocallyRealizable` for the
one *canonical* cover `chartDiskCover`.  But both proofs are chart-generic: a cover set of ANY
`ChartDiskCover` is a chart-ball preimage (`isDisk`), so it is simply connected
(`simplyConnectedSpace_chartBallPreimage`), and it sits inside a single chart source
(`subset_chart_source`), so the factorized-rational product witness gives local Mittag–Leffler on
it verbatim.  This file generalizes both — needed because the Serre-duality lane replaces the
canonical cover by the *separating* cover (`SeparatingCover.lean`: pole separation + the reserved
privately-covered disk), which must still feed the Leray/realizability legs of the ladder.

## Main declarations

* `ChartDiskCover.isLeray` — every chart-disk cover is a Leray cover (simply connected sets).
* `ChartDiskCover.exists_orderExact_witness` — the exact-order product witness on any chart-disk
  cover-set (generalizing `exists_orderExact_witness_chartDisk`).
* `ChartDiskCover.locallyRealizable` — every chart-disk cover is locally realizable.
-/

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Filter Function

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace ChartDiskCover

variable (𝔇 : ChartDiskCover X)

/-- A cover set of a chart-disk cover sits in the chart source of its center (the `chartAt ℂ`
form of `subset_chart_source`). -/
theorem subset_chartAt_source (j : 𝔇.ι) :
    ((𝔇.U j : Opens X) : Set X) ⊆ (chartAt ℂ (𝔇.center j)).source := by
  intro x hx
  have h := 𝔇.subset_chart_source j hx
  rwa [extChartAt_source] at h

/-- The cover set of a chart-disk cover, written in the `chartAt ℂ` chart (source-first, the
shape `simplyConnectedSpace_chartBallPreimage` consumes). -/
theorem coe_U_eq_chartBallPreimage (j : 𝔇.ι) :
    ((𝔇.U j : Opens X) : Set X)
      = (chartAt ℂ (𝔇.center j)).source ∩ (chartAt ℂ (𝔇.center j)) ⁻¹'
          Metric.ball ((chartAt ℂ (𝔇.center j)) (𝔇.center j)) (𝔇.radius j) := by
  rw [𝔇.isDisk j, Set.inter_comm]
  simp only [mfld_simps]

/-- The coordinate ball of a chart-disk cover set sits inside the `chartAt ℂ` chart target. -/
theorem ball_subset_chartAt_target (j : 𝔇.ι) :
    Metric.ball ((chartAt ℂ (𝔇.center j)) (𝔇.center j)) (𝔇.radius j)
      ⊆ (chartAt ℂ (𝔇.center j)).target := by
  intro z hz
  have h := 𝔇.closedBall_subset_target j (Metric.ball_subset_closedBall hz)
  rw [extChartAt_target] at h
  simpa [mfld_simps] using h

/-- **Every chart-disk cover is a Leray cover**: each cover set is a chart-ball preimage
(`isDisk`), hence simply connected (`simplyConnectedSpace_chartBallPreimage`).  Generalizes
`chartDiskCover_simplyConnected` from the canonical cover to all of them. -/
theorem isLeray : 𝔇.toFiniteCover.IsLeray := by
  intro i
  have h := simplyConnectedSpace_chartBallPreimage (chartAt ℂ (𝔇.center i))
    ((chartAt ℂ (𝔇.center i)) (𝔇.center i)) (𝔇.radius i) (𝔇.radius_pos i)
    (ball_subset_chartAt_target 𝔇 i)
  rw [← coe_U_eq_chartBallPreimage] at h
  exact h

/-- **The exact-order product witness on any chart-disk cover-set** (generalizing
`exists_orderExact_witness_chartDisk` from the canonical cover): for each cover-set `U j ∋ P` and
divisor `D`, a section `g ∈ 𝒪_{D+P}(U j)` of order *exactly* `−(D P)−1` at `P`.  Same factorized
rational witness `g = (∏ᶠ u, (· − u)^{dz u}) ∘ φ` through the center chart; the only cover-specific
input is `U j ⊆ φ.source` (`subset_chartAt_source`). -/
theorem exists_orderExact_witness (D : Divisor X) (j : 𝔇.ι) (P : X)
    (hP : P ∈ 𝔇.U j) :
    ∃ g : ↥(𝔇.U j) → ℂ,
      ∃ _ : g ∈ OmegaD (D + Finsupp.single P 1) (𝔇.U j),
      ordU g ⟨P, hP⟩ = ((-(D P) - 1 : ℤ) : WithTop ℤ) := by
  classical
  set U := (𝔇.U j : Opens X) with hU
  set c := 𝔇.center j with hc
  set φ := chartAt (H := ℂ) c with hφ
  have hUsrc : (U : Set X) ⊆ φ.source := subset_chartAt_source 𝔇 j
  set DP : Divisor X := D + Finsupp.single P 1 with hDP
  -- The exponent function `dz` realising the prescribed pole/zero orders, with finite support.
  set dz : ℂ → ℤ := fun w => if w ∈ φ.target then -(DP (φ.symm w)) else 0 with hdz
  have hdz_fin : Function.HasFiniteSupport dz := by
    apply Set.Finite.subset (DP.support.finite_toSet.image φ)
    intro w hw
    simp only [Function.mem_support, ne_eq, hdz] at hw
    by_cases hwt : w ∈ φ.target
    · have hne : DP (φ.symm w) ≠ 0 := by intro h; apply hw; simp [hwt, h]
      exact ⟨φ.symm w, by simpa [Finsupp.mem_support_iff] using hne, φ.right_inv hwt⟩
    · exact absurd (by simp [hwt]) hw
  have hdz_eval : ∀ {x : X}, x ∈ φ.source → dz (φ x) = -(DP x) := fun {x} hx => by
    simp only [hdz, φ.map_source hx, if_true, φ.left_inv hx]
  -- The factorized-rational witness `F` and its planar meromorphy/order.
  set F : ℂ → ℂ := ∏ᶠ u, (· - u) ^ dz u with hF
  have hFmer : ∀ z : ℂ, MeromorphicAt F z := fun z =>
    (FactorizedRational.meromorphicNFOn_univ dz).meromorphicOn z (Set.mem_univ z)
  have hForder : ∀ z : ℂ, meromorphicOrderAt F z = (dz z : WithTop ℤ) := fun _ =>
    FactorizedRational.meromorphicOrderAt_eq dz hdz_fin
  set g : U → ℂ := fun w => F (φ w.1) with hg
  -- `ordU g ⟨x⟩ = −DP(x)` for every `x ∈ U` (exact equality everywhere).
  have hgord : ∀ {x : X} (hx : x ∈ U), ordU g ⟨x, hx⟩ = ((-(DP x) : ℤ) : WithTop ℤ) :=
    fun {x} hx => by
      rw [ordU_comp_chart_eq hUsrc F hx, hForder, hdz_eval (hUsrc hx)]
  refine ⟨g, ?_, ?_⟩
  · rw [mem_OmegaD]
    refine ⟨isMeromorphic_comp_chart hUsrc hFmer, fun x => ?_⟩
    rw [hgord x.2]; norm_cast
  · rw [hgord hP]
    congr 1
    show -(DP P) = -(D P) - 1
    rw [hDP, Finsupp.add_apply, Finsupp.single_eq_same]; ring

/-- **Every chart-disk cover is locally realizable** (local Mittag–Leffler): generalizes
`locallyRealizable_chartDiskCover` from the canonical cover, via the chart-generic exact-order
product witness. -/
theorem locallyRealizable : 𝔇.toFiniteCover.LocallyRealizable := by
  intro D P j hP
  exact coeffGermLin_surjective_of_exists_witness hP
    (exists_orderExact_witness 𝔇 D j P hP)

end ChartDiskCover

end Jacobians.Dolbeault
