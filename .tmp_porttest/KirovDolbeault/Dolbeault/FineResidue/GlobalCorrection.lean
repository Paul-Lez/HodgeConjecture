/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.MeroVanish

/-!
# R6c — the global-correction evaluation engine (non-isolated marked point)

The W1 piece of the Čech↔tail dictionary route (`docs/planning/DICT_ROUTE.md`): the
evaluation of the fine-sheaf residue functional on a coboundary whose marked simple-pole
point `b` may lie in SEVERAL cover sets — the case the marked engine
(`resFunctional_eq_neg_residue_of_mero_coboundary`) excludes via `MLIsolated`.

## The global-cutoff-subtraction mechanism (discovery D3)

A presentation `h` of the cocycle `w` (`w i j = h j − h i` on overlaps) is replaced by
`h̃ := h − (H, H, …, H)` for a GLOBAL scalar `H` (the cutoff `θ·h_{j₀}` in the
application): constant cochains have zero coboundary, so `w` is unchanged, while at `b`
the matching principal parts cancel and `h̃` is SMOOTH there.  The price: `h̃` is no
longer holomorphic where `dθ ≠ 0`; the discrepancy `∂̄h̃_i = −∂̄H` is COMMON to all
charts.  Consequences for the R5/R6 engine skeleton:

* curvature relocation + reinsertion kill: UNCHANGED (they consume only smoothness);
* the per-chart Stokes term dies for EVERY chart (vanish-engine style — the marked-chart
  R0 evaluation disappears, and with it the isolation requirement);
* the Leibniz split gains ONE explicit term per chart, `−∫ ρ̃_j·(∂̄H̃_j)·g̃_j`
  (`corrFam`, with the junk value at the marked coordinate repaired to `0`);
* the correction terms form a `(1,1)` family (`isOneOneCoeff_corrFam`), collapse by the
  R4 relocation lemma + `∑ρ ≡ 1` to a single chart-`j₀` integral (`corrC`), and are
  evaluated by the GENERAL R0 atom `integral_dbar_smearedSimplePole` (no local constancy
  of the weight is needed — discovery D1) to `−π·r`.

## Main declarations

* `corrFam` / `corrC` — the repaired correction family and its chart-`j₀` planar cut.
* `isOneOneCoeff_corrFam` — the correction family is `(1,1)`.
* `integral_pouCoeff_glueCoeff_corr_split` — the Leibniz split with the explicit
  correction term.
* `sum_integral_pouCoeff_corrFam` — the relocation collapse `∑_j ∫ρ̃_j·corr_j = ∫corrC`.
* `integral_corrC_eq_neg_pi_residue` — the final R0 evaluation `∫corrC = −π·r`.
* `resFunctional_eq_neg_residue_of_global_correction` — **the headline**:
  `resFunctional 𝔇 t = −r` with NO isolation hypothesis on the marked point.
-/

open Complex Filter MeasureTheory
open scoped Manifold ContDiff Topology Classical Real
open TopologicalSpace (Opens)

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

variable {𝔇 : ChartDiskCover X}

/-! ### The repaired correction family -/

/-- **The repaired correction family** `∂̄H̃·g`: the chart-`i` read of `∂̄H` against the
`dz`-slot, with the junk value at the marked coordinate `chartMap i b` replaced by `0`
(`∂̄` of the singular read is undefined there; on a punctured neighbourhood it vanishes
honestly when `H` is holomorphic near `b` off `b`). -/
noncomputable def corrFam (𝔇 : ChartDiskCover X) (H : X → ℂ)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (b : X) : 𝔇.toFiniteCover.ι → ℂ → ℂ :=
  fun i z =>
    if b ∈ (𝔇.U i : Set X) ∧ z = chartMap 𝔇 i b then 0
    else DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ)) z * g i z

theorem corrFam_apply (H : X → ℂ) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (b : X)
    (i : 𝔇.toFiniteCover.ι) (z : ℂ) :
    corrFam 𝔇 H g b i z
      = if b ∈ (𝔇.U i : Set X) ∧ z = chartMap 𝔇 i b then 0
        else DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ)) z * g i z := rfl

section Clearances

variable {H : X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} {j₀ : 𝔇.toFiniteCover.ι} {b : X}

/-- A global scalar vanishing near `x` has chart-`i` read vanishing near the coordinate. -/
theorem hread_eventually_zero {i : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i : Set X)) (h0 : ∀ᶠ y in 𝓝 x, H y = 0) :
    ∀ᶠ ζ in 𝓝 (chartMap 𝔇 i x), H ((chartAt ℂ (𝔇.center i)).symm ζ) = 0 := by
  have hsrc : x ∈ (chartAt ℂ (𝔇.center i)).source := mem_chartSource_of_mem_U 𝔇 hx
  have hzt : chartMap 𝔇 i x ∈ (chartAt ℂ (𝔇.center i)).target :=
    (chartAt ℂ (𝔇.center i)).map_source hsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) :=
    (chartAt ℂ (𝔇.center i)).continuousAt_symm hzt
  have hli : (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) = x :=
    (chartAt ℂ (𝔇.center i)).left_inv hsrc
  have h0' : ∀ᶠ y in 𝓝 ((chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x)), H y = 0 := by
    rw [hli]
    exact h0
  exact hcont.eventually h0'

/-- `∂̄` of the chart read vanishes near the coordinate of a point where `H` locally
vanishes. -/
theorem dbar_hread_eventually_zero {i : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i : Set X)) (h0 : ∀ᶠ y in 𝓝 x, H y = 0) :
    ∀ᶠ ζ in 𝓝 (chartMap 𝔇 i x),
      DbarDisk.dbar (fun ξ => H ((chartAt ℂ (𝔇.center i)).symm ξ)) ζ = 0 := by
  filter_upwards [(hread_eventually_zero hx h0).eventually_nhds] with ζ hζ
  exact dbar_eq_zero_of_eventuallyEq_zero hζ

/-- **The cross-chart holomorphy transport**: if the chart-`j₀` read of `H` is
ℂ-differentiable at the coordinates of punctured-neighbourhood points of `b`, then in
EVERY chart containing `b` the read's `∂̄` vanishes on a punctured neighbourhood of the
marked coordinate (relocate through the analytic transition). -/
theorem dbar_hread_eventually_zero_near_marked (hb : b ∈ (𝔇.U j₀ : Set X))
    {i : 𝔇.toFiniteCover.ι} (hbi : b ∈ (𝔇.U i : Set X))
    (hH0 : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℂ
      (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) (chartMap 𝔇 j₀ x)) :
    ∀ᶠ z in 𝓝[≠] (chartMap 𝔇 i b),
      DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ)) z = 0 := by
  have hbsrc : b ∈ (chartAt ℂ (𝔇.center i)).source := mem_chartSource_of_mem_U 𝔇 hbi
  have hzt : chartMap 𝔇 i b ∈ (chartAt ℂ (𝔇.center i)).target :=
    (chartAt ℂ (𝔇.center i)).map_source hbsrc
  have hli : (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i b) = b :=
    (chartAt ℂ (𝔇.center i)).left_inv hbsrc
  have hctend : Tendsto (chartAt ℂ (𝔇.center i)).symm
      (𝓝[≠] (chartMap 𝔇 i b)) (𝓝[≠] b) := by
    have h := (chartAt ℂ (𝔇.center i)).symm.tendsto_nhdsNE (x := chartMap 𝔇 i b)
      (by simpa using hzt)
    rwa [hli] at h
  have hov : ∀ᶠ x in 𝓝[≠] b, x ∈ ((𝔇.U i ⊓ 𝔇.U j₀ : Opens X) : Set X) :=
    eventually_nhdsWithin_of_eventually_nhds
      ((𝔇.U i ⊓ 𝔇.U j₀ : Opens X).isOpen.mem_nhds ⟨hbi, hb⟩)
  have hri : ∀ᶠ z in 𝓝[≠] (chartMap 𝔇 i b),
      chartMap 𝔇 i ((chartAt ℂ (𝔇.center i)).symm z) = z := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    filter_upwards [(chartAt ℂ (𝔇.center i)).open_target.mem_nhds hzt] with z hz
    exact (chartAt ℂ (𝔇.center i)).right_inv hz
  filter_upwards [hctend.eventually hH0, hctend.eventually hov, hri] with z hdiff hxov hzri
  set x := (chartAt ℂ (𝔇.center i)).symm z with hxdef
  -- the chart-`i` read agrees near `z` with the chart-`j₀` read through the transition
  have hev : (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ))
      =ᶠ[𝓝 z] fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm (transitionMap 𝔇 i j₀ ζ)) := by
    have h1 := symm_transitionMap_eventuallyEq 𝔇 (j := i) (k := j₀) (x := x) hxov
    rw [hzri] at h1
    filter_upwards [h1] with ζ hζ
    rw [hζ]
  have htr : AnalyticAt ℂ (transitionMap 𝔇 i j₀) z := by
    have h1 := transitionMap_analyticAt 𝔇 (x := x) hxov.1 hxov.2
    rwa [hzri] at h1
  have htc : transitionMap 𝔇 i j₀ z = chartMap 𝔇 j₀ x := by
    have h1 := transitionMap_chartMap 𝔇 (x := x) (k := j₀) hxov.1
    rwa [hzri] at h1
  have hcomp : DifferentiableAt ℂ
      (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm (transitionMap 𝔇 i j₀ ζ))) z := by
    have hbase : DifferentiableAt ℂ (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ))
        (transitionMap 𝔇 i j₀ z) := by
      rw [htc]
      exact hdiff
    exact hbase.comp z htr.differentiableAt
  have hdz : DifferentiableAt ℂ (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ)) z :=
    hcomp.congr_of_eventuallyEq hev
  exact DbarDisk.dbar_eq_zero_of_differentiableAt hdz

/-- The correction family vanishes on a FULL neighbourhood of the marked coordinate
(punctured holomorphy + the repair at the point). -/
theorem corrFam_eventually_zero_near_marked (hb : b ∈ (𝔇.U j₀ : Set X))
    {i : 𝔇.toFiniteCover.ι} (hbi : b ∈ (𝔇.U i : Set X))
    (hH0 : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℂ
      (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) (chartMap 𝔇 j₀ x)) :
    ∀ᶠ z in 𝓝 (chartMap 𝔇 i b), corrFam 𝔇 H g b i z = 0 := by
  have h1 := dbar_hread_eventually_zero_near_marked hb hbi hH0
  rw [eventually_nhdsWithin_iff] at h1
  filter_upwards [h1] with z hz
  by_cases hzα : z = chartMap 𝔇 i b
  · rw [corrFam_apply, if_pos ⟨hbi, hzα⟩]
  · rw [corrFam_apply, if_neg (fun hc => hzα hc.2), hz (by simpa using hzα), zero_mul]

/-- The correction family vanishes near the coordinates of points off `tsupport H`. -/
theorem corrFam_eventually_zero_of_notMem_tsupport {i : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i : Set X)) (hxs : x ∉ tsupport H) :
    ∀ᶠ z in 𝓝 (chartMap 𝔇 i x), corrFam 𝔇 H g b i z = 0 := by
  have h0 : ∀ᶠ y in 𝓝 x, H y = 0 := by
    filter_upwards [(isClosed_tsupport H).isOpen_compl.mem_nhds hxs] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  filter_upwards [dbar_hread_eventually_zero hx h0] with z hz
  rw [corrFam_apply]
  split_ifs with hc
  · rfl
  · rw [hz, zero_mul]

/-- **The correction family is a `(1,1)` chart-coefficient family**: smooth at chart
points (locally zero near the marked coordinate; `∂̄` of a smooth read times the analytic
slot elsewhere) and satisfying the `normSq φ′` overlap law (`∂̄` contributes `conj φ′` by
the chain rule, the slot contributes `φ′`). -/
theorem isOneOneCoeff_corrFam (hb : b ∈ (𝔇.U j₀ : Set X))
    (hHsm : ∀ x : X, x ≠ b → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) H x)
    (hH0 : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℂ
      (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) (chartMap 𝔇 j₀ x))
    (hg : IsOneZeroCoeff 𝔇 g) :
    IsOneOneCoeff 𝔇 (corrFam 𝔇 H g b) := by
  have hreadCD : ∀ (i : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U i : Set X) → x ≠ b →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ))
        (chartMap 𝔇 i x) := by
    intro i x hx hxb
    have hsrc : x ∈ (chartAt ℂ (𝔇.center i)).source := mem_chartSource_of_mem_U 𝔇 hx
    have hli : (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) = x :=
      (chartAt ℂ (𝔇.center i)).left_inv hsrc
    refine contDiffAt_chartSymmRead_of_contMDiffAt
      ((chartAt ℂ (𝔇.center i)).map_source hsrc) ?_
    rw [hli]
    exact hHsm x hxb
  constructor
  · -- smoothness at chart points
    intro i x hx
    by_cases hxb : x = b
    · subst hxb
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        (corrFam_eventually_zero_near_marked hb hx hH0)
    · have hdb : ContDiffAt ℝ (⊤ : ℕ∞)
          (DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ)))
          (chartMap 𝔇 i x) :=
        ChartDiskCover.contDiffAt_dbar_chartDisk (hreadCD i x hx hxb)
      have hgc : ContDiffAt ℝ (⊤ : ℕ∞) (g i) (chartMap 𝔇 i x) :=
        ((hg.1 i x hx).restrictScalars (𝕜 := ℝ)).contDiffAt
      refine (hdb.mul hgc).congr_of_eventuallyEq ?_
      by_cases hbi : b ∈ (𝔇.U i : Set X)
      · have hne : chartMap 𝔇 i x ≠ chartMap 𝔇 i b := fun hc =>
          hxb ((chartAt ℂ (𝔇.center i)).injOn (mem_chartSource_of_mem_U 𝔇 hx)
            (mem_chartSource_of_mem_U 𝔇 hbi) hc)
        filter_upwards [isOpen_compl_singleton.mem_nhds
          (by simpa using hne : chartMap 𝔇 i x ∈ ({chartMap 𝔇 i b}ᶜ : Set ℂ))] with z hz
        rw [corrFam_apply, if_neg (fun hc => (by simpa using hz : z ≠ chartMap 𝔇 i b) hc.2)]
      · filter_upwards with z
        rw [corrFam_apply, if_neg (fun hc => hbi hc.1)]
  · -- the overlap law
    intro p q x hx
    have hxp : x ∈ (𝔇.U p : Set X) := hx.1
    have hxq : x ∈ (𝔇.U q : Set X) := hx.2
    have htend : Tendsto (transitionMap 𝔇 p q) (𝓝 (chartMap 𝔇 p x))
        (𝓝 (chartMap 𝔇 q x)) := by
      have hc := (transitionMap_analyticAt 𝔇 hxp hxq).continuousAt
      rwa [ContinuousAt, transitionMap_chartMap 𝔇 hxp] at hc
    by_cases hxb : x = b
    · -- both sides vanish near the respective marked coordinates
      subst hxb
      have h1 := corrFam_eventually_zero_near_marked (g := g) hb hxp hH0
      have h2 := corrFam_eventually_zero_near_marked (g := g) hb hxq hH0
      unfold OneOneLawAt
      filter_upwards [h1, htend.eventually h2] with z hz1 hz2
      rw [hz1, hz2, zero_mul]
    · -- generic law via the `∂̄` chain rule and the slot law
      have hzqt : chartMap 𝔇 q x ∈ (chartAt ℂ (𝔇.center q)).target :=
        (chartAt ℂ (𝔇.center q)).map_source (mem_chartSource_of_mem_U 𝔇 hxq)
      have hsrcp : x ∈ (chartAt ℂ (𝔇.center p)).source := mem_chartSource_of_mem_U 𝔇 hxp
      have hlip : (chartAt ℂ (𝔇.center p)).symm (chartMap 𝔇 p x) = x :=
        (chartAt ℂ (𝔇.center p)).left_inv hsrcp
      have hcontp : ContinuousAt (chartAt ℂ (𝔇.center p)).symm (chartMap 𝔇 p x) :=
        (chartAt ℂ (𝔇.center p)).continuousAt_symm
          ((chartAt ℂ (𝔇.center p)).map_source hsrcp)
      -- the symm-read point stays near `x`, hence off `b`, eventually
      have hxnb : ∀ᶠ z in 𝓝 (chartMap 𝔇 p x),
          (chartAt ℂ (𝔇.center p)).symm z ≠ b := by
        have hxmem : x ∈ ({b}ᶜ : Set X) := by simpa using hxb
        have h0 : ∀ᶠ y in 𝓝 ((chartAt ℂ (𝔇.center p)).symm (chartMap 𝔇 p x)),
            y ∈ ({b}ᶜ : Set X) := by
          rw [hlip]
          exact isOpen_compl_singleton.mem_nhds hxmem
        filter_upwards [hcontp.eventually h0] with z hz
        simpa using hz
      -- read agreement through the transition, smoothness of the `q`-read, target
      -- membership, the slot law, and `≠`-marked-coordinate guards
      have hFev : (fun ζ => H ((chartAt ℂ (𝔇.center p)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 p x)]
            fun ζ => H ((chartAt ℂ (𝔇.center q)).symm (transitionMap 𝔇 p q ζ)) := by
        filter_upwards [symm_transitionMap_eventuallyEq 𝔇 hx] with ζ hζ
        rw [hζ]
      have hguardp : ∀ᶠ z in 𝓝 (chartMap 𝔇 p x),
          ¬ (b ∈ (𝔇.U p : Set X) ∧ z = chartMap 𝔇 p b) := by
        by_cases hbp : b ∈ (𝔇.U p : Set X)
        · have hne : chartMap 𝔇 p x ≠ chartMap 𝔇 p b := fun hc =>
            hxb ((chartAt ℂ (𝔇.center p)).injOn hsrcp
              (mem_chartSource_of_mem_U 𝔇 hbp) hc)
          filter_upwards [isOpen_compl_singleton.mem_nhds
            (by simpa using hne : chartMap 𝔇 p x ∈ ({chartMap 𝔇 p b}ᶜ : Set ℂ))] with z hz
          exact fun hc => (by simpa using hz : z ≠ chartMap 𝔇 p b) hc.2
        · filter_upwards with z
          exact fun hc => hbp hc.1
      have hguardq : ∀ᶠ z in 𝓝 (chartMap 𝔇 p x),
          ¬ (b ∈ (𝔇.U q : Set X) ∧ transitionMap 𝔇 p q z = chartMap 𝔇 q b) := by
        by_cases hbq : b ∈ (𝔇.U q : Set X)
        · have hne : chartMap 𝔇 q x ≠ chartMap 𝔇 q b := fun hc =>
            hxb ((chartAt ℂ (𝔇.center q)).injOn (mem_chartSource_of_mem_U 𝔇 hxq)
              (mem_chartSource_of_mem_U 𝔇 hbq) hc)
          filter_upwards [htend.eventually (isOpen_compl_singleton.mem_nhds
            (by simpa using hne : chartMap 𝔇 q x ∈ ({chartMap 𝔇 q b}ᶜ : Set ℂ)))] with z hz
          exact fun hc => (by simpa using hz : transitionMap 𝔇 p q z ≠ chartMap 𝔇 q b) hc.2
        · filter_upwards with z
          exact fun hc => hbq hc.1
      -- smoothness of the `q`-read near the relocated coordinate, as an eventual fact
      have hqsm : ∀ᶠ z in 𝓝 (chartMap 𝔇 p x), DifferentiableAt ℝ
          (fun ζ => H ((chartAt ℂ (𝔇.center q)).symm ζ)) (transitionMap 𝔇 p q z) := by
        have hCD : ContDiffAt ℝ (⊤ : ℕ∞)
            (fun ζ => H ((chartAt ℂ (𝔇.center q)).symm ζ)) (chartMap 𝔇 q x) :=
          hreadCD q x hxq hxb
        have hCD1 : ContDiffAt ℝ 1
            (fun ζ => H ((chartAt ℂ (𝔇.center q)).symm ζ)) (chartMap 𝔇 q x) :=
          hCD.of_le (by exact_mod_cast le_top)
        have h1 : ∀ᶠ w in 𝓝 (chartMap 𝔇 q x), DifferentiableAt ℝ
            (fun ζ => H ((chartAt ℂ (𝔇.center q)).symm ζ)) w := by
          filter_upwards [hCD1.eventually (by simp)] with w hw
          exact hw.differentiableAt one_ne_zero
        exact htend.eventually h1
      unfold OneOneLawAt
      filter_upwards [hFev.eventuallyEq_nhds, hguardp, hguardq, hqsm,
        (transitionMap_analyticAt 𝔇 hxp hxq).eventually_analyticAt,
        hg.2 p q x hx] with z hzF hgp hgq hqd hzan hzg
      rw [corrFam_apply, corrFam_apply, if_neg hgp, if_neg hgq]
      have h1 : DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center p)).symm ζ)) z
          = DbarDisk.dbar
              (fun ζ => H ((chartAt ℂ (𝔇.center q)).symm (transitionMap 𝔇 p q ζ))) z :=
        dbar_congr_of_eventuallyEq hzF
      have h2 := dbar_comp (f := fun ζ => H ((chartAt ℂ (𝔇.center q)).symm ζ))
        (φ := transitionMap 𝔇 p q) hqd hzan.differentiableAt
      rw [Function.comp_def] at h2
      have hns : ((normSq (deriv (transitionMap 𝔇 p q) z) : ℝ) : ℂ)
          = deriv (transitionMap 𝔇 p q) z
              * (starRingEnd ℂ) (deriv (transitionMap 𝔇 p q) z) :=
        (Complex.mul_conj _).symm
      rw [h1, h2, hzg, hns]
      ring

end Clearances

/-! ### The Leibniz split with the explicit correction term -/

section CorrSplit

variable {S : Finset X} {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    {H : X → ℂ} {b : X}

/-- **The Leibniz step with the common `∂̄`-discrepancy kept explicit** (per chart): for a
presentation `h` whose chart reads satisfy `∂̄h̃_i = −∂̄H̃_i` off `S ∪ {b}` (the
`h + H`-holomorphy hypothesis `hhol'`), the `j`-th summand of the residue integral equals
the PoU-reinserted curvature terms MINUS the Stokes term MINUS the correction term
`∫ ρ̃_j·(∂̄H̃_j·g̃_j)`.  This is `integral_pouCoeff_glueCoeff_mero_split` with the
holomorphy of `h` replaced by the global-correction shape. -/
theorem integral_pouCoeff_glueCoeff_corr_split
    (hiso : ∀ a ∈ S, ∃ j₁, MLIsolated 𝔇 j₁ a)
    (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h) (hδ : IsCoboundaryOn 𝔇 w h)
    (hg : IsOneZeroCoeff 𝔇 g)
    (htmem : IsOneOneCoeff 𝔇 (glueCoeff 𝔇 w g))
    (hcorr : IsOneOneCoeff 𝔇 (corrFam 𝔇 H g b))
    (hsmH : ∀ x : X, x ≠ b → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) H x)
    (hhol' : ∀ i, ∀ x ∈ (𝔇.U i : Set X), x ∉ (S : Set X) → x ≠ b →
      DifferentiableAt ℂ (fun z => h i ((chartAt ℂ (𝔇.center i)).symm z)
        + H ((chartAt ℂ (𝔇.center i)).symm z)) (chartMap 𝔇 i x))
    (j : 𝔇.toFiniteCover.ι) :
    ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z
      = (∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)))
        - (∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z)
        - ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z := by
  -- the a.e. pointwise Leibniz identity (off the bad coordinates of `insert b S`)
  have hpt : ∀ z : ℂ, z ∉ badCoords 𝔇 (insert b S) j →
      pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z
        = DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
          - DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
          - pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z := by
    intro z hzT
    by_cases hzU : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      have hxbS : x ∉ insert b S := fun hx =>
        hzT ((chartMap_mem_badCoords_iff 𝔇 hxU).mpr hx)
      have hxb : x ≠ b := fun hc => hxbS (hc ▸ Finset.mem_insert_self b S)
      have hxS : x ∉ (S : Set X) := fun hx =>
        hxbS (Finset.mem_insert_of_mem hx)
      have hxsrc : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hxU
      have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
        (chartAt ℂ (𝔇.center j)).map_source hxsrc
      have hcont : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
        (chartAt ℂ (𝔇.center j)).symm.continuousAt
          (by rwa [(chartAt ℂ (𝔇.center j)).symm_source])
      have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
        (chartAt ℂ (𝔇.center j)).left_inv hxsrc
      have hovU : ((𝔇.U j : Opens X) : Set X)
          ∈ 𝓝 ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) := by
        rw [hli]
        exact (𝔇.U j).isOpen.mem_nhds hxU
      -- the Forster collapse, read in chart-`j` coordinates
      have hsplit_ev : splitCoeff 𝔇 w j =ᶠ[𝓝 (chartMap 𝔇 j x)]
          fun ζ => h j ((chartAt ℂ (𝔇.center j)).symm ζ)
            - pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) := by
        filter_upwards [hcont.preimage_mem_nhds hovU] with ζ hζ
        rw [splitCoeff_apply, pouSplit_eq_of_coboundary 𝔇 hδ hζ]
      have hBd : DifferentiableAt ℝ
          (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) :=
        (contDiffAt_pouAverageRead_off hsm hxU hxS).differentiableAt (by simp)
      have hgd : DifferentiableAt ℝ (g j) (chartMap 𝔇 j x) :=
        ((hg.1 j x hxU).restrictScalars (𝕜 := ℝ)).differentiableAt
      -- the chart reads of `h j` and `H`
      have hHrd : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun ζ => H ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) := by
        refine contDiffAt_chartSymmRead_of_contMDiffAt hzt ?_
        rw [hli]
        exact hsmH x hxb
      have hhd : DifferentiableAt ℝ
          (fun ζ => h j ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) := by
        have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
            (fun ζ => h j ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) := by
          refine contDiffAt_chartSymmRead_of_contMDiffAt hzt ?_
          rw [hli]
          exact hsm j x hxU hxS
        exact h1.differentiableAt (by simp)
      -- the common-discrepancy law `∂̄h̃_j = −∂̄H̃_j` at the good point
      have hdbar_h : DbarDisk.dbar
            (fun ζ => h j ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x)
          = - DbarDisk.dbar
              (fun ζ => H ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) := by
        have hsplit : (fun ζ => h j ((chartAt ℂ (𝔇.center j)).symm ζ))
            = fun ζ => (h j ((chartAt ℂ (𝔇.center j)).symm ζ)
                + H ((chartAt ℂ (𝔇.center j)).symm ζ))
              - H ((chartAt ℂ (𝔇.center j)).symm ζ) := by
          funext ζ
          ring
        rw [hsplit, DbarOpenDisk.dbar_sub
            ((hhol' j x hxU hxS hxb).restrictScalars ℝ)
            (hHrd.differentiableAt (by simp)),
          DbarDisk.dbar_eq_zero_of_differentiableAt (hhol' j x hxU hxS hxb), zero_sub]
      have hdbar_split : DbarDisk.dbar (splitCoeff 𝔇 w j) (chartMap 𝔇 j x)
          = - DbarDisk.dbar
              (fun ζ => H ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x)
            - DbarDisk.dbar
              (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ))
              (chartMap 𝔇 j x) := by
        rw [dbar_congr_of_eventuallyEq hsplit_ev, DbarOpenDisk.dbar_sub hhd hBd, hdbar_h]
      have hdbarB : DbarDisk.dbar
            (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)
            (chartMap 𝔇 j x)
          = DbarDisk.dbar (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ))
              (chartMap 𝔇 j x) * g j (chartMap 𝔇 j x) := by
        rw [dbar_mul hBd hgd,
          DbarDisk.dbar_eq_zero_of_differentiableAt (hg.1 j x hxU).differentiableAt,
          mul_zero, add_zero]
      have hdbarPB : DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) (chartMap 𝔇 j x)
          = DbarDisk.dbar (pouCoeff 𝔇 j) (chartMap 𝔇 j x)
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x))
                  * g j (chartMap 𝔇 j x))
            + pouCoeff 𝔇 j (chartMap 𝔇 j x)
              * DbarDisk.dbar
                  (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)
                  (chartMap 𝔇 j x) :=
        dbar_mul ((contDiff_pouCoeff 𝔇 j).differentiable (by simp) _)
          ((contDiffAt_pouAverageRead_mul_off hsm hg hxU hxS).differentiableAt (by simp))
      -- the repaired correction value at the good point
      have hcorrv : corrFam 𝔇 H g b j (chartMap 𝔇 j x)
          = DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x)
              * g j (chartMap 𝔇 j x) := by
        rw [corrFam_apply]
        refine if_neg ?_
        rintro ⟨hbU, hzb⟩
        exact hzT (hzb ▸ (chartMap_mem_badCoords_iff 𝔇 hbU).mpr (Finset.mem_insert_self b S))
      rw [glueCoeff_apply, hdbar_split, hdbarPB, hdbarB, hcorrv]
      ring
    · have hzs : z ∉ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j) := fun hc =>
        hzU (Set.image_mono (fun y hy => cechPoU_subordinate 𝔇 j hy) hc)
      have hP0 : pouCoeff 𝔇 j z = 0 := Set.indicator_of_notMem hzU _
      have hD0 : DbarDisk.dbar (pouCoeff 𝔇 j) z = 0 :=
        dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hzs
      have hPB0 : DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z = 0 := by
        refine dbar_eq_zero_of_eventuallyEq_zero ?_
        filter_upwards [(isCompact_image_tsupport_cechPoU 𝔇
          j).isClosed.isOpen_compl.mem_nhds hzs] with ζ hζ
        rw [pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hζ, zero_mul]
      rw [hP0, hD0, hPB0, zero_mul, zero_mul, zero_mul]
      ring
  -- integrability bookkeeping
  have hIt : Integrable fun z => pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z :=
    integrable_pouCoeff_mul 𝔇 htmem j
  have hIcorr : Integrable fun z => pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z :=
    integrable_pouCoeff_mul 𝔇 hcorr j
  have hYcd : ContDiff ℝ (⊤ : ℕ∞) fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) := by
    refine contDiff_of_chartImage_clearance 𝔇 (j := j) ?_ ?_
    · rintro z ⟨x, hxU, rfl⟩
      by_cases hxS : x ∈ (S : Set X)
      · obtain ⟨j₁, hj₁⟩ := hiso x hxS
        have hj : j = j₁ := eq_isolated_index hj₁ hxU
        subst hj
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [eventually_dbar_pouCoeff_zero_near_iso hj₁] with w' hw'
        rw [hw', zero_mul]
      · exact (ChartDiskCover.contDiffAt_dbar_chartDisk
          (contDiff_pouCoeff 𝔇 j).contDiffAt).mul
          (contDiffAt_pouAverageRead_mul_off hsm hg hxU hxS)
    · intro z hz
      rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul]
  have hYcs : HasCompactSupport fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    (DbarDisk.hasCompactSupport_dbar (hasCompactSupport_pouCoeff 𝔇 j)).mul_right
  have hIY : Integrable fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    hYcd.continuous.integrable_of_hasCompactSupport hYcs
  -- the bad coordinates are volume-negligible
  have hane : ∀ᵐ z : ℂ ∂volume, z ∉ badCoords 𝔇 (insert b S) j := by
    refine ae_iff.mpr ?_
    have hset : {z : ℂ | ¬ z ∉ badCoords 𝔇 (insert b S) j}
        = ((badCoords 𝔇 (insert b S) j : Finset ℂ) : Set ℂ) := by
      ext z
      simp
    rw [hset]
    exact (badCoords 𝔇 (insert b S) j).finite_toSet.measure_zero _
  have hF : Integrable fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
      - pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z := hIY.sub hIt
  have e2 : (∫ z, (DbarDisk.dbar (pouCoeff 𝔇 j) z
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
        - pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z))
      = (∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
        - ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z := integral_sub hIY hIt
  have hkey : ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
      = ((∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
        - ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z)
        - ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z := by
    calc ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
        = ∫ z, ((DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
              - pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z)
            - pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z) := by
          refine integral_congr_ae ?_
          filter_upwards [hane] with z hz
          linear_combination hpt z hz
      _ = (∫ z, (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
              - pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z))
            - ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z := integral_sub hF hIcorr
      _ = ((∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
            - ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z)
            - ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z := by rw [e2]
  -- PoU reinsertion of the curvature term
  have hreins : (∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
      = ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
    calc ∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
        = ∫ z, ∑ k, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
            * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          simp only [← Finset.sum_mul, sum_rhoC_apply, one_mul]
      _ = ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
            * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
          refine integral_finsetSum Finset.univ fun k _ => ?_
          have hcd : ContDiff ℝ (⊤ : ℕ∞) fun z =>
              rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
                * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                    * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) :=
            contDiff_of_chartImage_clearance 𝔇
              (fun z hz => (contDiffAt_chartSymmRead (rhoC 𝔇 k).contMDiff
                (chartMap_image_U_subset_target 𝔇 j hz)).mul hYcd.contDiffAt)
              (fun z hz => by
                rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul, mul_zero])
          exact hcd.continuous.integrable_of_hasCompactSupport hYcs.mul_left
  rw [← hreins]
  linear_combination hkey

end CorrSplit

/-! ### The relocation collapse to the distinguished chart -/

section Collapse

variable {H : X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} {j₀ : 𝔇.toFiniteCover.ι} {b : X}

/-- The **chart-`j₀` planar cut** of the correction family: the `corrFam` component of the
distinguished chart, cut off by the indicator of the chart image of `U j₀` (the `pouCoeff`
pattern — junk values of the chart inverse outside the target are removed where the honest
family vanishes anyway). -/
noncomputable def corrC (𝔇 : ChartDiskCover X) (H : X → ℂ)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (b : X) (j₀ : 𝔇.toFiniteCover.ι) : ℂ → ℂ :=
  (chartMap 𝔇 j₀ '' (𝔇.U j₀ : Set X)).indicator (corrFam 𝔇 H g b j₀)

/-- The chart image of `tsupport H` is compact (for `tsupport H ⊆ U j₀`). -/
theorem isCompact_chartMap_image_tsupport (hHsupp : tsupport H ⊆ (𝔇.U j₀ : Set X)) :
    IsCompact (chartMap 𝔇 j₀ '' tsupport H) := by
  have hts : IsCompact (tsupport H) := (isClosed_tsupport H).isCompact
  refine hts.image_of_continuousOn ?_
  refine (chartAt ℂ (𝔇.center j₀)).continuousOn.mono fun x hx => ?_
  exact mem_chartSource_of_mem_U 𝔇 (hHsupp hx)

/-- The planar cut vanishes off the chart image of `tsupport H`. -/
theorem corrC_eq_zero_of_notMem_image_tsupport {z : ℂ} (hz : z ∉ chartMap 𝔇 j₀ '' tsupport H) : corrC 𝔇 H g b j₀ z = 0 := by
  by_cases hzU : z ∈ chartMap 𝔇 j₀ '' (𝔇.U j₀ : Set X)
  · obtain ⟨x, hxU, rfl⟩ := hzU
    have hxs : x ∉ tsupport H := fun hs => hz (Set.mem_image_of_mem _ hs)
    have hmem : chartMap 𝔇 j₀ x ∈ chartMap 𝔇 j₀ '' (𝔇.U j₀ : Set X) := ⟨x, hxU, rfl⟩
    rw [corrC, Set.indicator_of_mem hmem]
    exact (corrFam_eventually_zero_of_notMem_tsupport hxU hxs).self_of_nhds
  · exact Set.indicator_of_notMem hzU _

/-- The planar cut is continuous (locally the smooth `corrFam` component on the open chart
image; locally `0` off the compact image of `tsupport H`). -/
theorem continuous_corrC (hHsupp : tsupport H ⊆ (𝔇.U j₀ : Set X))
    (hcorr : IsOneOneCoeff 𝔇 (corrFam 𝔇 H g b)) : Continuous (corrC 𝔇 H g b j₀) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ chartMap 𝔇 j₀ '' (𝔇.U j₀ : Set X)
  · obtain ⟨x, hxU, rfl⟩ := hz
    have h1 : ContinuousAt (corrFam 𝔇 H g b j₀) (chartMap 𝔇 j₀ x) :=
      (hcorr.1 j₀ x hxU).continuousAt
    refine h1.congr ?_
    filter_upwards [(isOpen_chartMap_image 𝔇 j₀ (𝔇.U j₀).isOpen
      (subset_refl _)).mem_nhds ⟨x, hxU, rfl⟩] with w hw
    exact (Set.indicator_of_mem hw _).symm
  · have hzs : z ∉ chartMap 𝔇 j₀ '' tsupport H := fun hc =>
      hz (Set.image_mono hHsupp hc)
    have hev : corrC 𝔇 H g b j₀ =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [(isCompact_chartMap_image_tsupport
        hHsupp).isClosed.isOpen_compl.mem_nhds hzs] with w hw
      exact corrC_eq_zero_of_notMem_image_tsupport hw
    exact continuousAt_const.congr hev.symm

/-- The planar cut has compact support (inside the chart image of `tsupport H`). -/
theorem hasCompactSupport_corrC (hHsupp : tsupport H ⊆ (𝔇.U j₀ : Set X)) :
    HasCompactSupport (corrC 𝔇 H g b j₀) :=
  HasCompactSupport.intro (isCompact_chartMap_image_tsupport hHsupp) fun _ hz =>
    corrC_eq_zero_of_notMem_image_tsupport hz

/-- **The per-chart relocation of the correction term** (R4): the chart-`j` correction
integral reads entirely inside `U j ⊓ U j₀` (the support of `H`), where the R4 relocation
lemma re-routes it to the distinguished chart against the global weight `ρ_j`. -/
theorem integral_pouCoeff_corrFam_eq (hHsupp : tsupport H ⊆ (𝔇.U j₀ : Set X))
    (hcorr : IsOneOneCoeff 𝔇 (corrFam 𝔇 H g b)) (j : 𝔇.toFiniteCover.ι) :
    ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z
      = ∫ z, rhoC 𝔇 j ((chartAt ℂ (𝔇.center j₀)).symm z) * corrC 𝔇 H g b j₀ z := by
  -- step 1: the chart-`j` integrand vanishes off the overlap image
  have hvan1 : ∀ z, z ∉ overlapImage 𝔇 j j₀ →
      pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z = 0 := by
    intro z hz
    by_cases hzU : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      have hxj₀ : x ∉ (𝔇.U j₀ : Set X) := fun hk => hz ⟨x, ⟨hxU, hk⟩, rfl⟩
      have hxs : x ∉ tsupport H := fun hs => hxj₀ (hHsupp hs)
      rw [(corrFam_eventually_zero_of_notMem_tsupport hxU hxs).self_of_nhds, mul_zero]
    · rw [show pouCoeff 𝔇 j z = 0 from Set.indicator_of_notMem hzU _, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan1]
  -- step 2: on the overlap image, the `pouCoeff` weight is the `ρ_j` read
  have hcongr1 : ∀ z ∈ overlapImage 𝔇 j j₀,
      pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z
        = rhoC 𝔇 j ((chartAt ℂ (𝔇.center j)).symm z) * corrFam 𝔇 H g b j z := by
    rintro z ⟨x, hx, rfl⟩
    have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (chartAt ℂ (𝔇.center j)).left_inv (mem_chartSource_of_mem_U 𝔇 hx.1)
    rw [pouCoeff_chartMap 𝔇 hx.1, hli]
  rw [MeasureTheory.setIntegral_congr_fun (isOpen_overlapImage 𝔇 j j₀).measurableSet hcongr1]
  -- step 3: relocate to the distinguished chart (R4, weight `ρ_j`)
  have hrel := setIntegral_overlap_relocate 𝔇 hcorr j j₀ fun y => rhoC 𝔇 j y
  simp only [] at hrel
  rw [hrel]
  -- step 4: on the chart-`j₀` overlap image, the component is the planar cut
  have hcongr2 : ∀ z ∈ overlapImage 𝔇 j₀ j,
      rhoC 𝔇 j ((chartAt ℂ (𝔇.center j₀)).symm z) * corrFam 𝔇 H g b j₀ z
        = rhoC 𝔇 j ((chartAt ℂ (𝔇.center j₀)).symm z) * corrC 𝔇 H g b j₀ z := by
    rintro z ⟨x, hx, rfl⟩
    have hmem : chartMap 𝔇 j₀ x ∈ chartMap 𝔇 j₀ '' (𝔇.U j₀ : Set X) := ⟨x, hx.1, rfl⟩
    rw [corrC, Set.indicator_of_mem hmem]
  rw [MeasureTheory.setIntegral_congr_fun (isOpen_overlapImage 𝔇 j₀ j).measurableSet hcongr2]
  -- step 5: the chart-`j₀` integrand vanishes off the overlap image, re-extend to `ℂ`
  have hvan2 : ∀ z, z ∉ overlapImage 𝔇 j₀ j →
      rhoC 𝔇 j ((chartAt ℂ (𝔇.center j₀)).symm z) * corrC 𝔇 H g b j₀ z = 0 := by
    intro z hz
    by_cases hzU : z ∈ chartMap 𝔇 j₀ '' (𝔇.U j₀ : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      have hxj : x ∉ (𝔇.U j : Set X) := fun hj => hz ⟨x, ⟨hxU, hj⟩, rfl⟩
      have hxsupp : x ∉ tsupport (cechPoU 𝔇 j) := fun hs => hxj (cechPoU_subordinate 𝔇 j hs)
      have hli : (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ x) = x :=
        (chartAt ℂ (𝔇.center j₀)).left_inv (mem_chartSource_of_mem_U 𝔇 hxU)
      rw [hli, rhoC_eq_zero_of_notMem_tsupport hxsupp, zero_mul]
    · rw [show corrC 𝔇 H g b j₀ z = 0 from Set.indicator_of_notMem hzU _, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvan2]

/-- **The relocation collapse**: the PoU-weighted correction terms sum to the single
distinguished-chart integral of the planar cut (`∑ρ ≡ 1`). -/
theorem sum_integral_pouCoeff_corrFam (hHsupp : tsupport H ⊆ (𝔇.U j₀ : Set X))
    (hcorr : IsOneOneCoeff 𝔇 (corrFam 𝔇 H g b)) :
    ∑ j, ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z = ∫ z, corrC 𝔇 H g b j₀ z := by
  -- the relocated integrands are continuous with compact support, hence integrable
  have hcont : ∀ j : 𝔇.toFiniteCover.ι, Continuous fun z =>
      rhoC 𝔇 j ((chartAt ℂ (𝔇.center j₀)).symm z) * corrC 𝔇 H g b j₀ z := by
    intro j
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ chartMap 𝔇 j₀ '' (𝔇.U j₀ : Set X)
    · have hzt : z ∈ (chartAt ℂ (𝔇.center j₀)).target :=
        chartMap_image_U_subset_target 𝔇 j₀ hz
      have h1 : ContinuousAt (chartAt ℂ (𝔇.center j₀)).symm z :=
        (chartAt ℂ (𝔇.center j₀)).continuousAt_symm hzt
      exact ((((rhoC 𝔇 j).contMDiff).continuous.continuousAt).comp h1).mul
        ((continuous_corrC hHsupp hcorr).continuousAt)
    · have hzs : z ∉ chartMap 𝔇 j₀ '' tsupport H := fun hc =>
        hz (Set.image_mono hHsupp hc)
      have hev : (fun w => rhoC 𝔇 j ((chartAt ℂ (𝔇.center j₀)).symm w)
          * corrC 𝔇 H g b j₀ w) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [(isCompact_chartMap_image_tsupport
          hHsupp).isClosed.isOpen_compl.mem_nhds hzs] with w hw
        rw [corrC_eq_zero_of_notMem_image_tsupport hw, mul_zero]
      exact continuousAt_const.congr hev.symm
  have hint : ∀ j ∈ (Finset.univ : Finset 𝔇.toFiniteCover.ι), Integrable fun z =>
      rhoC 𝔇 j ((chartAt ℂ (𝔇.center j₀)).symm z) * corrC 𝔇 H g b j₀ z := fun j _ =>
    (hcont j).integrable_of_hasCompactSupport (hasCompactSupport_corrC hHsupp).mul_left
  calc ∑ j, ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z
      = ∑ j, ∫ z, rhoC 𝔇 j ((chartAt ℂ (𝔇.center j₀)).symm z) * corrC 𝔇 H g b j₀ z :=
        Finset.sum_congr rfl fun j _ => integral_pouCoeff_corrFam_eq hHsupp hcorr j
    _ = ∫ z, ∑ j, rhoC 𝔇 j ((chartAt ℂ (𝔇.center j₀)).symm z) * corrC 𝔇 H g b j₀ z :=
        (integral_finsetSum Finset.univ hint).symm
    _ = ∫ z, corrC 𝔇 H g b j₀ z := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [← Finset.sum_mul, sum_rhoC_apply, one_mul]

end Collapse

/-! ### The final R0 evaluation of the planar cut -/

section FinalAtom

variable {H : X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} {j₀ : 𝔇.toFiniteCover.ι} {b : X}

/-- **The R0 evaluation of the correction cut**: if the chart-`j₀` slot product `H̃·g̃` has
the simple-pole shape `r·(ζ−α)⁻¹ + q` at the marked coordinate, then `∫ corrC = −π·r` —
split off a bump-smeared simple pole (the GENERAL R0 atom, no local constancy), repair the
remainder, and Stokes-kill it. -/
theorem integral_corrC_eq_neg_pi_residue (hb : b ∈ (𝔇.U j₀ : Set X))
    (hHsupp : tsupport H ⊆ (𝔇.U j₀ : Set X))
    (hHsm : ∀ x : X, x ≠ b → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) H x)
    (hg : IsOneZeroCoeff 𝔇 g) {r : ℂ} {q : ℂ → ℂ}
    (hq : AnalyticAt ℂ q (chartMap 𝔇 j₀ b))
    (hpe : (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)
      =ᶠ[𝓝[≠] (chartMap 𝔇 j₀ b)] fun ζ => r * (ζ - chartMap 𝔇 j₀ b)⁻¹ + q ζ) :
    ∫ z, corrC 𝔇 H g b j₀ z = -π * r := by
  classical
  set α := chartMap 𝔇 j₀ b with hαdef
  set U' : Set ℂ := chartMap 𝔇 j₀ '' (𝔇.U j₀ : Set X) with hU'def
  set K' : Set ℂ := chartMap 𝔇 j₀ '' tsupport H with hK'def
  have hU'open : IsOpen U' := isOpen_chartMap_image 𝔇 j₀ (𝔇.U j₀).isOpen (subset_refl _)
  have hK'cpt : IsCompact K' := isCompact_chartMap_image_tsupport hHsupp
  have hK'U' : K' ⊆ U' := Set.image_mono hHsupp
  have hαU : α ∈ U' := ⟨b, hb, rfl⟩
  set Φ : ℂ → ℂ := U'.indicator
    (fun w => H ((chartAt ℂ (𝔇.center j₀)).symm w) * g j₀ w) with hΦdef
  -- the indicator is inactive near interior points
  have hΦev : ∀ w ∈ U', Φ =ᶠ[𝓝 w]
      fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ := by
    intro w hw
    filter_upwards [hU'open.mem_nhds hw] with ζ hζ
    exact Set.indicator_of_mem hζ _
  have hΦsing : Φ =ᶠ[𝓝[≠] α] fun ζ => r * (ζ - α)⁻¹ + q ζ :=
    ((hΦev α hαU).filter_mono nhdsWithin_le_nhds).trans hpe
  -- Φ vanishes off the compact K'
  have hΦ0 : ∀ w ∉ K', Φ w = 0 := by
    intro w hw
    by_cases hwU : w ∈ U'
    · obtain ⟨x, hxU, rfl⟩ := hwU
      have hxs : x ∉ tsupport H := fun hs => hw (Set.mem_image_of_mem _ hs)
      have hli : (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ x) = x :=
        (chartAt ℂ (𝔇.center j₀)).left_inv (mem_chartSource_of_mem_U 𝔇 hxU)
      have hmem : chartMap 𝔇 j₀ x ∈ U' := ⟨x, hxU, rfl⟩
      rw [hΦdef, Set.indicator_of_mem hmem, hli,
        image_eq_zero_of_notMem_tsupport hxs, zero_mul]
    · exact Set.indicator_of_notMem hwU _
  have hΦcs : HasCompactSupport Φ := HasCompactSupport.intro hK'cpt hΦ0
  -- Φ is smooth off α
  have hΦsmall : ∀ w : ℂ, w ≠ α → ContDiffAt ℝ (⊤ : ℕ∞) Φ w := by
    intro w hwα
    by_cases hwU : w ∈ U'
    · obtain ⟨x, hxU, rfl⟩ := hwU
      have hxb : x ≠ b := fun hc => hwα (by rw [hc])
      have hzt : chartMap 𝔇 j₀ x ∈ (chartAt ℂ (𝔇.center j₀)).target :=
        chartMap_image_U_subset_target 𝔇 j₀ ⟨x, hxU, rfl⟩
      have hli : (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ x) = x :=
        (chartAt ℂ (𝔇.center j₀)).left_inv (mem_chartSource_of_mem_U 𝔇 hxU)
      have hH : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) (chartMap 𝔇 j₀ x) := by
        refine contDiffAt_chartSymmRead_of_contMDiffAt hzt ?_
        rw [hli]
        exact hHsm x hxb
      have hgc : ContDiffAt ℝ (⊤ : ℕ∞) (g j₀) (chartMap 𝔇 j₀ x) :=
        ((hg.1 j₀ x hxU).restrictScalars (𝕜 := ℝ)).contDiffAt
      exact (hH.mul hgc).congr_of_eventuallyEq (hΦev (chartMap 𝔇 j₀ x) ⟨x, hxU, rfl⟩)
    · have hwK : w ∉ K' := fun hc => hwU (hK'U' hc)
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hK'cpt.isClosed.isOpen_compl.mem_nhds hwK] with ζ hζ
      exact hΦ0 ζ hζ
  -- the bump and the smeared simple pole
  set ψb : ContDiffBump α :=
    { rIn := 1, rOut := 2, rIn_pos := one_pos, rIn_lt_rOut := one_lt_two } with hψbdef
  obtain ⟨hψsm, hψcs⟩ := DbarLocal.contDiff_hasCompactSupport_ofReal_contDiffBump ψb
  set ψ : ℂ → ℂ := fun w => ((ψb w : ℝ) : ℂ) with hψdef
  have hψ1 : ∀ᶠ w in 𝓝 α, ψ w = 1 := by
    filter_upwards [Metric.closedBall_mem_nhds α one_pos] with w hw
    show ((ψb w : ℝ) : ℂ) = 1
    rw [show ψb w = 1 from ψb.one_of_mem_closedBall hw, Complex.ofReal_one]
  set χ : ℂ → ℂ := fun w => r * ψ w with hχdef
  have hχcd : ContDiff ℝ (⊤ : ℕ∞) χ := contDiff_const.mul hψsm
  have hχcs : HasCompactSupport χ := hψcs.mul_left
  have hχα : χ α = r := by
    show r * ((ψb α : ℝ) : ℂ) = r
    rw [show ψb α = 1 from ψb.one_of_mem_closedBall
      (Metric.mem_closedBall_self one_pos.le), Complex.ofReal_one, mul_one]
  set sing : ℂ → ℂ := fun w => χ w * (w - α)⁻¹ with hsingdef
  -- the repaired remainder
  set Φ₁ : ℂ → ℂ := fun w => Φ w - sing w with hΦ₁def
  set u' : ℂ → ℂ := pointRepair Φ₁ ({α} : Finset ℂ) with hu'def
  have hΦ₁ext : Φ₁ =ᶠ[𝓝[≠] α] q := by
    filter_upwards [hΦsing, hψ1.filter_mono nhdsWithin_le_nhds] with ζ hζ hζψ
    show Φ ζ - sing ζ = q ζ
    rw [hζ]
    show r * (ζ - α)⁻¹ + q ζ - χ ζ * (ζ - α)⁻¹ = q ζ
    rw [show χ ζ = r * ψ ζ from rfl, hζψ]
    ring
  have hu'cd : ContDiff ℝ (⊤ : ℕ∞) u' := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hzα : z = α
    · subst hzα
      exact ((hq.restrictScalars (𝕜 := ℝ)).contDiffAt).congr_of_eventuallyEq
        (pointRepair_eventuallyEq_of_extends (Finset.mem_singleton_self α) hq hΦ₁ext)
    · have hsingcd : ContDiffAt ℝ (⊤ : ℕ∞) sing z := by
        refine hχcd.contDiffAt.mul ?_
        exact (contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hzα)
      exact ((hΦsmall z hzα).sub hsingcd).congr_of_eventuallyEq
        (pointRepair_eventuallyEq_off (by simpa using hzα))
  have hu'cs : HasCompactSupport u' := by
    refine HasCompactSupport.intro (K := (K' ∪ tsupport ψ) ∪ ({α} : Set ℂ))
      ((hK'cpt.union hψcs).union isCompact_singleton) fun w hw => ?_
    have hwK : w ∉ K' := fun hc => hw (Set.mem_union_left _ (Set.mem_union_left _ hc))
    have hwψ : w ∉ tsupport ψ := fun hc =>
      hw (Set.mem_union_left _ (Set.mem_union_right _ hc))
    have hwα : w ≠ α := fun hc => hw (Set.mem_union_right _ (by simpa using hc))
    rw [hu'def, pointRepair_eq_off (by simpa using hwα)]
    show Φ w - sing w = 0
    rw [hΦ0 w hwK]
    show (0 : ℂ) - χ w * (w - α)⁻¹ = 0
    rw [show χ w = r * ψ w from rfl, image_eq_zero_of_notMem_tsupport hwψ]
    ring
  -- the singular piece: the GENERAL R0 atom
  have hval : ∫ ζ, DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) ζ = -π * r := by
    rw [integral_dbar_smearedSimplePole hχcd hχcs α, hχα]
  -- the continuous a.e. representative of `∂̄(χ·(·−α)⁻¹)`
  have hχconst : χ =ᶠ[𝓝 α] fun _ => r := by
    filter_upwards [hψ1] with ζ hζ
    show r * ψ ζ = r
    rw [hζ, mul_one]
  have hdχ0 : ∀ᶠ ζ in 𝓝 α, DbarDisk.dbar χ ζ = 0 := by
    filter_upwards [hχconst.eventuallyEq_nhds] with ζ hζ
    rw [dbar_congr_of_eventuallyEq hζ]
    exact DbarDisk.dbar_const r ζ
  set Gf : ℂ → ℂ := fun ζ => DbarDisk.dbar χ ζ * (ζ - α)⁻¹ with hGdef
  have hGzero : Gf =ᶠ[𝓝 α] fun _ => (0 : ℂ) := by
    filter_upwards [hdχ0] with ζ hζ
    show DbarDisk.dbar χ ζ * (ζ - α)⁻¹ = 0
    rw [hζ, zero_mul]
  have hGcont : Continuous Gf := by
    rw [continuous_iff_continuousAt]
    intro ζ
    by_cases hζα : ζ = α
    · subst hζα
      exact continuousAt_const.congr hGzero.symm
    · exact ((DbarDisk.continuous_dbar hχcd).continuousAt).mul
        ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hζα))
  have hGcs : HasCompactSupport Gf := (DbarDisk.hasCompactSupport_dbar hχcs).mul_right
  have hane : ∀ᵐ z : ℂ ∂volume, z ≠ α := by
    refine ae_iff.mpr ?_
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton _
  have hGae : (fun ζ => DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) ζ) =ᵐ[volume] Gf := by
    filter_upwards [hane] with ζ hζ
    show DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) ζ = DbarDisk.dbar χ ζ * (ζ - α)⁻¹
    rw [dbar_smul_inv_sub hχcd α hζ, div_eq_mul_inv]
  have hIsing : Integrable fun ζ => DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) ζ :=
    (hGcont.integrable_of_hasCompactSupport hGcs).congr hGae.symm
  have hI1 : Integrable (DbarDisk.dbar u') :=
    (DbarDisk.continuous_dbar hu'cd).integrable_of_hasCompactSupport
      (DbarDisk.hasCompactSupport_dbar hu'cs)
  -- the a.e. identification `corrC = ∂̄u' + ∂̄(smeared pole)`
  have hsplit : (fun z => corrC 𝔇 H g b j₀ z) =ᵐ[volume]
      fun z => DbarDisk.dbar u' z + DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) z := by
    filter_upwards [hane] with z hzα
    -- `corrC z = ∂̄Φ z` off `α`
    have hcorrΦ : corrC 𝔇 H g b j₀ z = DbarDisk.dbar Φ z := by
      by_cases hzU : z ∈ U'
      · obtain ⟨x, hxU, hxz⟩ := hzU
        have hxb : x ≠ b := by
          intro hc
          subst hc
          exact hzα hxz.symm
        have hzt : z ∈ (chartAt ℂ (𝔇.center j₀)).target := by
          rw [← hxz]
          exact chartMap_image_U_subset_target 𝔇 j₀ ⟨x, hxU, rfl⟩
        have hli : (chartAt ℂ (𝔇.center j₀)).symm z = x := by
          rw [← hxz]
          exact (chartAt ℂ (𝔇.center j₀)).left_inv (mem_chartSource_of_mem_U 𝔇 hxU)
        have hHd : DifferentiableAt ℝ
            (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) z := by
          have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
              (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) z := by
            refine contDiffAt_chartSymmRead_of_contMDiffAt hzt ?_
            rw [hli]
            exact hHsm x hxb
          exact h1.differentiableAt (by simp)
        have hgdC : DifferentiableAt ℂ (g j₀) z := by
          rw [← hxz]
          exact (hg.1 j₀ x hxU).differentiableAt
        have hΦd : DbarDisk.dbar Φ z = DbarDisk.dbar
            (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ) z :=
          dbar_congr_of_eventuallyEq (hΦev z ⟨x, hxU, hxz⟩)
        have hmul : DbarDisk.dbar
            (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ) z
            = DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) z
                * g j₀ z := by
          rw [dbar_mul hHd (hgdC.restrictScalars ℝ),
            DbarDisk.dbar_eq_zero_of_differentiableAt hgdC, mul_zero, add_zero]
        have hcv : corrC 𝔇 H g b j₀ z
            = DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) z
                * g j₀ z := by
          have hmem : z ∈ U' := ⟨x, hxU, hxz⟩
          rw [corrC, Set.indicator_of_mem hmem, corrFam_apply]
          refine if_neg ?_
          rintro ⟨_, hzb⟩
          exact hzα hzb
        rw [hcv, hΦd, hmul]
      · have hzK : z ∉ K' := fun hc => hzU (hK'U' hc)
        have hΦz : DbarDisk.dbar Φ z = 0 := by
          refine dbar_eq_zero_of_eventuallyEq_zero ?_
          filter_upwards [hK'cpt.isClosed.isOpen_compl.mem_nhds hzK] with ζ hζ
          exact hΦ0 ζ hζ
        rw [show corrC 𝔇 H g b j₀ z = 0 from Set.indicator_of_notMem hzU _, hΦz]
    -- `∂̄Φ = ∂̄u' + ∂̄(smeared pole)` off `α`
    have hsingd : DifferentiableAt ℝ sing z := by
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) sing z := by
        refine hχcd.contDiffAt.mul ?_
        exact (contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hzα)
      exact h1.differentiableAt (by simp)
    have hu'ev : u' =ᶠ[𝓝 z] Φ₁ := pointRepair_eventuallyEq_off (by simpa using hzα)
    have hΦeq : Φ =ᶠ[𝓝 z] fun w => u' w + sing w := by
      filter_upwards [hu'ev] with w hw
      rw [hw]
      show Φ w = Φ w - sing w + sing w
      ring
    have hu'd : DifferentiableAt ℝ u' z :=
      hu'cd.contDiffAt.differentiableAt (by simp)
    rw [hcorrΦ, dbar_congr_of_eventuallyEq hΦeq, DbarOpenDisk.dbar_add hu'd hsingd]
  calc ∫ z, corrC 𝔇 H g b j₀ z
      = ∫ z, (DbarDisk.dbar u' z + DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) z) :=
        integral_congr_ae hsplit
    _ = (∫ z, DbarDisk.dbar u' z) + ∫ z, DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) z :=
        integral_add hI1 hIsing
    _ = -π * r := by
        rw [integral_dbar_eq_zero hu'cd hu'cs, hval, zero_add]

end FinalAtom

/-! ### The headline -/

section Headline

variable {S : Finset X} {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    {H : X → ℂ} {j₀ : 𝔇.toFiniteCover.ι} {b : X}

/-- **THE GLOBAL-CORRECTION EVALUATION HEADLINE — the residue functional evaluates
coboundaries with a marked simple-pole point WITHOUT any cover-isolation of the marked
point.**  Data shape: `w i j = h j − h i` on overlaps with `h` smooth off the isolated bad
set `S` AND smooth at the marked point `b ∉ S` (the global-cutoff-subtracted presentation);
the original holomorphy is recorded as `∂̄(h + H) = 0` off `S ∪ {b}` for a global scalar
`H` supported in the distinguished chart `U j₀ ∋ b`, holomorphic near `b` off `b`, whose
slot product `H̃·g̃_{j₀}` has the simple-pole shape `r·(ζ−α)⁻¹ + q`.  Then

  `resFunctional 𝔇 t = −r`.

Same conclusion and sign convention as the isolated marked engine
(`resFunctional_eq_neg_residue_of_mero_coboundary`); the proof routes the entire residue
through the single distinguished-chart correction integral (`DICT_ROUTE.md`, D1–D3). -/
theorem resFunctional_eq_neg_residue_of_global_correction (t : oneOneCoeff 𝔇)
    (ht : (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) = glueCoeff 𝔇 w g)
    (hg : IsOneZeroCoeff 𝔇 g) (hiso : ∀ a ∈ S, ∃ i₀, MLIsolated 𝔇 i₀ a)
    (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h) (hδ : IsCoboundaryOn 𝔇 w h)
    (hext : ∀ a ∈ S, ∀ i₀, MLIsolated 𝔇 i₀ a → SlotProductExtendsAt 𝔇 h g i₀ a)
    (hb : b ∈ (𝔇.U j₀ : Set X))
    (hHsupp : tsupport H ⊆ (𝔇.U j₀ : Set X))
    (hHsm : ∀ x : X, x ≠ b → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) H x)
    (hH0 : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℂ
      (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) (chartMap 𝔇 j₀ x))
    (hhol' : ∀ i, ∀ x ∈ (𝔇.U i : Set X), x ∉ (S : Set X) → x ≠ b →
      DifferentiableAt ℂ (fun z => h i ((chartAt ℂ (𝔇.center i)).symm z)
        + H ((chartAt ℂ (𝔇.center i)).symm z)) (chartMap 𝔇 i x))
    {r : ℂ} {q : ℂ → ℂ} (hq : AnalyticAt ℂ q (chartMap 𝔇 j₀ b))
    (hpe : (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)
      =ᶠ[𝓝[≠] (chartMap 𝔇 j₀ b)] fun ζ => r * (ζ - chartMap 𝔇 j₀ b)⁻¹ + q ζ) :
    resFunctional 𝔇 t = -r := by
  have hcorr : IsOneOneCoeff 𝔇 (corrFam 𝔇 H g b) := isOneOneCoeff_corrFam hb hHsm hH0 hg
  have htmem : IsOneOneCoeff 𝔇 (glueCoeff 𝔇 w g) := ht ▸ t.2
  -- the relocated curvature double sum dies (the R5 mechanism, verbatim)
  have hcurv : ∑ j, ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
      * (DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) = 0 := by
    calc ∑ j, ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
        = ∑ j, ∑ k, ∫ z, pouCoeff 𝔇 k z
            * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
            integral_overlapTerm_relocate_mero hiso hsm hg j k
      _ = ∑ k, ∑ j, ∫ z, pouCoeff 𝔇 k z
            * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) :=
          Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun k _ =>
            sum_integral_relocated_eq_zero_mero hiso hsm hg k
  -- the Stokes sum dies chart by chart (the vanish-engine kill — no marked evaluation)
  have hstokes : ∀ j : 𝔇.toFiniteCover.ι, ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z = 0 := fun j =>
    integral_dbar_pouCoeff_pouAverage_eq_zero hiso hsm hg hext j
  -- the correction sum is the distinguished-chart R0 evaluation
  have hcorrsum : ∑ j, ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z = -π * r := by
    rw [sum_integral_pouCoeff_corrFam hHsupp hcorr]
    exact integral_corrC_eq_neg_pi_residue hb hHsupp hHsm hg hq hpe
  have hIfun : resIntegralFun 𝔇 (glueCoeff 𝔇 w g) = (π : ℂ) * r := by
    calc resIntegralFun 𝔇 (glueCoeff 𝔇 w g)
        = ∑ j, ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z := rfl
      _ = ∑ j, ((∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
              * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                  * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)))
            - (∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z)
            - ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z) :=
          Finset.sum_congr rfl fun j _ =>
            integral_pouCoeff_glueCoeff_corr_split hiso hsm hδ hg htmem hcorr hHsm hhol' j
      _ = ((∑ j, ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
              * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                  * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)))
            - ∑ j, ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z)
            - ∑ j, ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      _ = (π : ℂ) * r := by
          rw [hcurv, Finset.sum_congr rfl fun j _ => hstokes j, hcorrsum]
          simp
  have hI : resIntegral 𝔇 t = (π : ℂ) * r := by
    have hfun : resIntegral 𝔇 t = resIntegralFun 𝔇 (glueCoeff 𝔇 w g) := by
      rw [← ht]
      rfl
    rw [hfun, hIfun]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [resFunctional_apply, hI, resNormalization]
  field_simp

end Headline

end Jacobians.Dolbeault.FineResidue
