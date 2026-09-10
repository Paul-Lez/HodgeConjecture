/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedClusterSplit
import KirovDolbeault.ProperMapDegreeSheets

/-!
# The ramification-multiplicity bridge `localDeg ↔ analyticOrderAt(holoRepr − c)`

The Forster §5 cluster split (`exists_clusterSplit`, `SerreResidueRamifiedClusterSplit.lean`) consumes,
at a ramification preimage `p` of a finite value-centre `c`, the **analytic-order hypothesis**
`analyticOrderAt (F − c) (chart_p p) = m`, where `F = f.holoRepr ∘ chart_p.symm` is the *geometric*
value of the cover read in the `p`-chart (the limit-repair `holoRepr`, whose value matches
`f.toRiemannSphere` and whose value fibre `F⁻¹(coe c)` is the genuine sphere fibre).  This file supplies
that hypothesis from the intrinsic local degree `localDeg f (coe c) p` — the *genuine* ramification
multiplicity (= number of regular sheets clustering at `p` over a nearby value, by the
conservation-of-number engine `LocalMultiplicitySheets`/`exists_properMapDegree`).

This is the **multiplicity bridge**: the single reusable lemma turning the intrinsic `localDeg`
multiplicity into the `analyticOrderAt = m` input the per-preimage cluster atom needs.  It is the
multiplicity half of the cluster-reindexing wall (TARGET 1 of Gate A's `∑Res = 0`); it mirrors the
proven `exists_sheetDatum_coe` (`ProperMapDegreeSheets.lean`), extracting its per-point order
computation as a standalone bridge.

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `analyticOrderAt_holoRepr_sub_eq_mult` — at a *non-pole* fibre preimage `p` over `coe c` of a
  non-constant cover (`f.div ≠ 0`), with `m := (localDeg f (coe c) p).toNat`:
  - `1 ≤ m` (positivity);
  - `analyticOrderAt (fun z => f.holoRepr (chart_p.symm z) − c) (chart_p p) = m`;
  - `localDeg f (coe c) p = m`.
  This is *exactly* the `hm`/`hord` pair `exists_clusterSplit` / `exists_wpow_normalForm` consume.

* `exists_clusterSplit_at_fibrePoint` — the genuine §5 cluster split at a non-pole fibre preimage,
  driven by the intrinsic multiplicity: from the multiplicity bridge it produces the normal-form
  coordinate `η`, its local inverse `s = η⁻¹`, and the cluster sheet preimage property, at the genuine
  `m = (localDeg f (coe c) p).toNat`.

## ⚠ Soundness

The multiplicity is the *genuine* intrinsic local degree `localDeg` (the §17.9 conservation-of-number
multiplicity, the one `exists_properMapDegree` is built from), **not** an ad-hoc number.  The geometric
value `F = holoRepr ∘ chart.symm` is the genuine limit-repair value of the cover (its value fibre is the
sphere fibre, `holoRepr_pullback_eventuallyEq_toFun`), so the order is the genuine ramification index.
No false/junk field; no custom axiom; no gaps.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §5 (the normal form `z = wᵐ`, `m` = ramification
  index), §4 (the degree).
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §II.4 (the local degree / argument principle).
* `Jacobians/ProperMapDegreeSheets.lean` (`exists_sheetDatum_coe`, `meromorphicOrderAt_holoRepr_sub_eq`,
  `localDeg_coe_eq_chartPullback_order`, `fibre_finite_of_div_ne_zero`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace Jacobians

open Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct
  Jacobians.ProperMapDegreeSheets Jacobians.MultiplicityPatchingConstruct

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The geometric value `holoRepr p = c` at a non-pole fibre point -/

/-- **The geometric value `holoRepr p = c` at a non-pole fibre point.**  If `p` is a non-pole
(`0 ≤ f.orderAtPoint p`) lying in the fibre `F⁻¹(coe c)` (`f.toRiemannSphere p = coe c`), then the
limit-repair value `f.holoRepr p = c` (since `F p = coe (holoRepr p)` for a non-pole, and `coe` is
injective). -/
theorem holoRepr_eq_of_fibre_nonpole (f : MeromorphicFunction X) {c : ℂ} {p : X}
    (hp_fib : f.toRiemannSphere p = ((c : ℂ) : RiemannSphere)) (hp_np : 0 ≤ f.orderAtPoint p) :
    f.holoRepr p = c := by
  have := f.toRiemannSphere_of_nonneg hp_np
  rw [this] at hp_fib
  exact OnePoint.coe_injective hp_fib

/-! ## The multiplicity bridge -/

/-- **The multiplicity bridge.**  At a non-pole fibre preimage `p` over `coe c` of a non-constant cover
(`f.div ≠ 0`), set `m := (localDeg f (coe c) p).toNat` (the genuine ramification multiplicity).  Then:

* `1 ≤ m` (positivity);
* `analyticOrderAt (fun z => f.holoRepr (chart_p.symm z) − c) (chart_p p) = m`;
* `localDeg f (coe c) p = m` (the local degree is exactly that natural).

This is **exactly** the `hm`/`hord` pair `exists_clusterSplit` / `exists_wpow_normalForm` consume: the
ramified normal form `F = c + ηᵐ` at the genuine multiplicity `m`.  The proof mirrors the per-point order
computation inside `exists_sheetDatum_coe` (`ProperMapDegreeSheets.lean`): the geometric chart-pullback
`g = holoRepr ∘ chart.symm` is analytic at the non-pole, its order at the chart centre is `≠ 0`
(it vanishes there, `holoRepr p = c`) and `≠ ⊤` (else the fibre `F⁻¹(coe c)` would be infinite,
contradicting finiteness), and `localDeg = (meromorphicOrderAt of the toFun pullback) = (analyticOrderAt
of the holoRepr pullback)`. -/
theorem analyticOrderAt_holoRepr_sub_eq_mult (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ} {p : X}
    (hp_fib : f.toRiemannSphere p = ((c : ℂ) : RiemannSphere)) (hp_np : 0 ≤ f.orderAtPoint p) :
    1 ≤ (localDeg f ((c : ℂ) : RiemannSphere) p).toNat ∧
      analyticOrderAt (fun z => f.holoRepr ((chartAt (H := ℂ) p).symm z) - c)
          ((chartAt (H := ℂ) p) p)
        = ((localDeg f ((c : ℂ) : RiemannSphere) p).toNat : ℕ∞) ∧
      localDeg f ((c : ℂ) : RiemannSphere) p
        = ((localDeg f ((c : ℂ) : RiemannSphere) p).toNat : ℤ) := by
  classical
  set e := chartAt (H := ℂ) p with he
  have hfib_fin := fibre_finite_of_div_ne_zero f hdiv (((c : ℂ) : RiemannSphere))
  have hrepr : f.holoRepr p = c := holoRepr_eq_of_fibre_nonpole f hp_fib hp_np
  set g := f.holoRepr ∘ e.symm with hg
  have hg_an : AnalyticAt ℂ g (e p) := f.analyticAt_holoRepr_chartPullback_of_orderNonneg hp_np
  have hg_val : g (e p) = c := by
    show f.holoRepr (e.symm (e p)) = c; rw [e.left_inv (mem_chart_source ℂ p), hrepr]
  have hgc_an : AnalyticAt ℂ (fun z => g z - c) (e p) := hg_an.sub analyticAt_const
  -- Order `≠ 0` (vanishing at `e p`) and `≠ ⊤` (finite fibre).
  have hval0 : (fun z => g z - c) (e p) = 0 := by show g (e p) - c = 0; rw [hg_val]; ring
  have hne_zero : analyticOrderAt (fun z => g z - c) (e p) ≠ 0 :=
    (hgc_an.analyticOrderAt_ne_zero).mpr hval0
  have hne_top : analyticOrderAt (fun z => g z - c) (e p) ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hge : ∀ᶠ y in 𝓝 p, f.holoRepr y = c := by
      have hpre : e ⁻¹' {z | g z - c = 0} ∈ 𝓝 p :=
        (e.continuousAt (mem_chart_source ℂ p)).preimage_mem_nhds htop
      have hsrc : ∀ᶠ y in 𝓝 p, y ∈ e.source := e.open_source.mem_nhds (mem_chart_source ℂ p)
      filter_upwards [hpre, hsrc] with y hy hysrc
      simp only [Set.mem_preimage, Set.mem_setOf_eq, sub_eq_zero] at hy
      rw [show f.holoRepr y = g (e y) from
        (by show _ = f.holoRepr (e.symm (e y)); rw [e.left_inv hysrc]), hy]
    have hFe : ∀ᶠ y in 𝓝 p, f.toRiemannSphere y = ((c : ℂ) : RiemannSphere) := by
      filter_upwards [f.toRiemannSphere_eventuallyEq_coe_holoRepr hp_np, hge] with y hy1 hy2
      rw [hy1]; show ((f.holoRepr y : ℂ) : RiemannSphere) = _; rw [hy2]
    rw [Filter.eventually_iff, _root_.mem_nhds_iff] at hFe
    obtain ⟨U0, hU0sub, hU0open, hpU0⟩ := hFe
    exact (Jacobians.infinite_of_isOpen_nonempty hU0open ⟨p, hpU0⟩)
      (hfib_fin.subset (fun y hy => hU0sub hy))
  -- `m := order.toNat`, `1 ≤ m`, `analyticOrderAt = m`.
  set m : ℕ := (analyticOrderAt (fun z => g z - c) (e p)).toNat with hm_def
  have hm_eq : analyticOrderAt (fun z => g z - c) (e p) = (m : ℕ∞) := (ENat.coe_toNat hne_top).symm
  have hm1 : 1 ≤ m := by
    rw [Nat.one_le_iff_ne_zero]; intro h0; apply hne_zero; rw [hm_eq, h0]; rfl
  -- `localDeg f (coe c) p = m`: chart-pullback order via `holoRepr` (junk-free) = analytic order.
  have hlocalDeg : localDeg f ((c : ℂ) : RiemannSphere) p = (m : ℤ) := by
    rw [localDeg_coe_eq_chartPullback_order f c e (chart_mem_atlas ℂ p) (mem_chart_source ℂ p),
      ← meromorphicOrderAt_holoRepr_sub_eq f p c (e.map_source (mem_chart_source ℂ p)),
      show (fun w => f.holoRepr (e.symm w) - c) = (fun w => g w - c) from rfl,
      hgc_an.meromorphicOrderAt_eq, hm_eq]
    simp
  -- Repackage: `(localDeg).toNat = m`, the analytic order is over the `holoRepr` pullback.
  have htoNat : (localDeg f ((c : ℂ) : RiemannSphere) p).toNat = m := by
    rw [hlocalDeg]; simp
  refine ⟨by rw [htoNat]; exact hm1, ?_, by rw [htoNat, hlocalDeg]⟩
  rw [htoNat, show (fun z => f.holoRepr (e.symm z) - c) = (fun z => g z - c) from rfl, hm_eq]

/-! ## The genuine cluster split at a non-pole fibre point, driven by the intrinsic multiplicity -/

/-- **The Forster §5 cluster split at a non-pole fibre preimage.**  At a non-pole fibre preimage `p`
over `coe c` of a non-constant cover (`f.div ≠ 0`), with `m := (localDeg f (coe c) p).toNat` the genuine
multiplicity and `ζ` a primitive `m`-th root, the geometric chart-pullback `F = f.holoRepr ∘ chart_p.symm`
has the §5 normal form `F = c + ηᵐ`, with local inverse `s = η⁻¹` (`s 0 = chart_p p`), and the cluster
sheet points `clusterSheet s ζ w₀ j z = s(ζʲ w₀ z)` are genuine preimages of `z` under `F`.

This composes the multiplicity bridge `analyticOrderAt_holoRepr_sub_eq_mult` (the genuine intrinsic
multiplicity) with `exists_clusterSplit` (the §5 atom).  It is the geometric per-preimage datum the
full-fibre cluster identity `hgeom_fibre` consumes, *with the multiplicity verified to be the genuine
local degree* (not asserted). -/
theorem exists_clusterSplit_at_fibrePoint (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ} {p : X}
    (hp_fib : f.toRiemannSphere p = ((c : ℂ) : RiemannSphere)) (hp_np : 0 ≤ f.orderAtPoint p)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (localDeg f ((c : ℂ) : RiemannSphere) p).toNat) :
    ∃ (η s : ℂ → ℂ),
      AnalyticAt ℂ η ((chartAt (H := ℂ) p) p) ∧ η ((chartAt (H := ℂ) p) p) = 0 ∧
      deriv η ((chartAt (H := ℂ) p) p) ≠ 0 ∧
      (∀ᶠ w in 𝓝 ((chartAt (H := ℂ) p) p),
        f.holoRepr ((chartAt (H := ℂ) p).symm w)
          = c + η w ^ (localDeg f ((c : ℂ) : RiemannSphere) p).toNat) ∧
      AnalyticAt ℂ s 0 ∧ s 0 = (chartAt (H := ℂ) p) p ∧ deriv s 0 ≠ 0 ∧
      (∀ᶠ a in 𝓝 0, η (s a) = a) ∧
      (∀ (w₀ : ℂ → ℂ) (z : ℂ) (j : ℕ),
        η (s (ζ ^ j * w₀ z)) = ζ ^ j * w₀ z →
        f.holoRepr ((chartAt (H := ℂ) p).symm (s (ζ ^ j * w₀ z)))
          = c + η (s (ζ ^ j * w₀ z)) ^ (localDeg f ((c : ℂ) : RiemannSphere) p).toNat →
        w₀ z ^ ((localDeg f ((c : ℂ) : RiemannSphere) p).toNat : ℤ) = z - c →
        f.holoRepr ((chartAt (H := ℂ) p).symm (clusterSheet s ζ w₀ j z)) = z) := by
  obtain ⟨hm1, hord, _⟩ := analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np
  set F : ℂ → ℂ := fun z => f.holoRepr ((chartAt (H := ℂ) p).symm z) with hF
  have hF_an : AnalyticAt ℂ F ((chartAt (H := ℂ) p) p) := by
    show AnalyticAt ℂ (fun z => f.holoRepr ((chartAt (H := ℂ) p).symm z)) _
    exact f.analyticAt_holoRepr_chartPullback_of_orderNonneg hp_np
  have hFc : F ((chartAt (H := ℂ) p) p) = c := by
    show f.holoRepr ((chartAt (H := ℂ) p).symm ((chartAt (H := ℂ) p) p)) = c
    rw [(chartAt (H := ℂ) p).left_inv (mem_chart_source ℂ p),
      holoRepr_eq_of_fibre_nonpole f hp_fib hp_np]
  exact exists_clusterSplit hm1 hF_an hFc hord hζ

end Jacobians
