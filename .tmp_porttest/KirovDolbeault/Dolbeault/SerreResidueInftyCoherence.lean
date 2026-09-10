/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueDirectGenus0GermDischarge
import KirovDolbeault.Discharge.Manifold.CriticalSetDerivBridge

/-!
# Gate A `∑Res = 0` — the `∞`-coherence engine (§VIII.3 at `∞`, reciprocal chart)

`Jacobians.Dolbeault.SerreResidueTheorem.residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg`
(`SerreResidueDirectGenus0GermDischarge.lean`) reduced Gate A `∑Res = 0` (kirovGenus `0`, simple `∞`-poles,
canonical full-fibre selection) to *exactly* the genericity bookkeeping, the branch-value boundedness
`hbnd`, and the **`∞`-coherence** `hcoh_geom`:

> `recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0]
>    recipCoeff (inftyMovingSumNF ω₀ f (inftyFibreDataNF_full g f hsimpleInf hmeroInf))`,

the §VIII.3 `∞`-single-valuedness (the value-trace's reciprocal-chart germ at `∞` equals the
`∞`-moving-fibre-sum's germ).  This is the `∞`-analogue of the *finite* moving coherence `Cfull`, which
was discharged via the symmetric-invariance lever
(`MovingCoherenceDatum.ofSphereSheetSystemCanon` / `…coherent`), and has — unlike `Cfull` — **no
engine** yet in the repo (only the *reduction* `hcoh_inf_of_inftyMovingCoherenceNF`).

This file builds the `∞`-sheet-system engine, the reciprocal-chart analogue of the proven finite engine.

## Step (1) — `∞` is off the branch locus when all `∞`-poles are simple

`exists_sphereSheetSystem` (the off-branch sheet system) requires the value `∞` to be off the branch
locus.  A pole `a` with `orderAtPoint a = −1` (a **simple** pole) is a *regular point* of
`F = f.toRiemannSphere`: reading `F` near `a` in the `∞`-chart `chartInfty`, the chart pullback is the
reciprocal `1/f`, a zero of order `= the pole order = 1`, so its derivative is nonzero
(`deriv_ne_zero_of_analyticOrderAt_eq_one`), hence `F` is locally injective at `a`
(`injOn_nhds_of_deriv_ne_zero`, transported through the charts).  The fibre `F⁻¹{∞}` is exactly the
pole set; if *every* pole is simple, *no* pole is critical, so `∞ ∉ branchLocus F = F '' criticalSet F`.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `notMem_criticalSet_of_orderAtPoint_eq_neg_one` — a simple pole is off the critical set of
  `F = f.toRiemannSphere` (the analytic core: reciprocal chart-pullback derivative `≠ 0` ⟹ locally
  injective).
* `infty_notMem_branchLocus_of_simpleInfty` — `∞ ∉ branchLocus f.toRiemannSphere`, given that every pole
  is simple (`hsimpleInf`, via `inftyFibreEnum` enumerating all poles).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (the trace `Tr`; single-valued by
  symmetry; the trace = symmetric moving fibre-sum near each value, including `∞`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22 (local sheet systems), §5/§4.22 (the local
  normal form, reciprocal chart), §17.
* `Jacobians/ToSphereGeneral.lean` (`contMDiffAt_toRiemannSphere_at_pole`: the reciprocal chart pullback
  `chartInfty ∘ F ∘ chart⁻¹ =ᶠ N⁻¹`, order `−orderAtPoint`).
* `Jacobians/Discharge/Manifold/CriticalSetDerivBridge.lean` (`injOn_nhds_of_deriv_ne_zero`,
  `deriv_ne_zero_of_analyticOrderAt_eq_one`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22, §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTraceFullFibre
  Jacobians.Dolbeault.FormTraceMovingFibre RiemannSphere

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ## Step (1): `∞` is off the branch locus when all `∞`-poles are simple -/

/-- **The reciprocal chart pullback at a pole is analytic of order `−orderAtPoint`.**  At a pole `P`
(`orderAtPoint P < 0`), the chart pullback of `F = f.toRiemannSphere` in the `∞`-chart `chartInfty`,
`G := chartInfty ∘ F ∘ (chart P).symm`, is analytic at `chart P P` with analytic order equal to the
*natural number* `(−orderAtPoint P).toNat ≥ 1` — the reciprocal `1/f` has a zero of order `= the pole
order`.  This is the analytic local normal form at `∞`, extracted from the proof of
`contMDiffAt_toRiemannSphere_at_pole` (the punctured/centre germ-match `G =ᶠ N⁻¹`). -/
theorem analyticAt_chartInfty_toRiemannSphere_pullback_of_pole (f : MeromorphicFunction X) {P : X}
    (hP : f.orderAtPoint P < 0) :
    AnalyticAt ℂ (chartInfty ∘ (f.toRiemannSphere) ∘ (chartAt (H := ℂ) P).symm)
        ((chartAt (H := ℂ) P) P) ∧
      analyticOrderAt (chartInfty ∘ (f.toRiemannSphere) ∘ (chartAt (H := ℂ) P).symm)
        ((chartAt (H := ℂ) P) P) = (((-f.orderAtPoint P).toNat : ℕ) : ℕ∞) := by
  set φ := chartAt (H := ℂ) P with hφ
  set F := f.toFun ∘ φ.symm with hFdef
  have hxsrc : P ∈ φ.source := mem_chart_source ℂ P
  have hmeroF : MeromorphicAt F (φ P) := f.meromorphic P
  set n : ℤ := f.orderAtPoint P with hn
  have hn_neg : n < 0 := hP
  have hordF : meromorphicOrderAt F (φ P) = (n : ℤ) :=
    f.meromorphicOrderAt_chartPullback_of_pole hP
  set N := toMeromorphicNFAt F (φ P) with hNdef
  have hNF : MeromorphicNFAt N (φ P) := meromorphicNFAt_toMeromorphicNFAt
  have hordN : meromorphicOrderAt N (φ P) = (n : ℤ) := by
    rw [hNdef, meromorphicOrderAt_congr hmeroF.eq_nhdsNE_toMeromorphicNFAt.symm, hordF]
  have hNFinv : MeromorphicNFAt (fun w => (N w)⁻¹) (φ P) := by
    have := hNF.inv; simpa [Pi.inv_def] using this
  have hordNinv : meromorphicOrderAt (fun w => (N w)⁻¹) (φ P) = ((-n : ℤ)) := by
    have : meromorphicOrderAt (N⁻¹) (φ P) = -meromorphicOrderAt N (φ P) := meromorphicOrderAt_inv
    rw [hordN] at this; simpa [Pi.inv_def] using this
  have hnn_pos : (0 : ℤ) < -n := by omega
  have hNinvAna : AnalyticAt ℂ (fun w => (N w)⁻¹) (φ P) := by
    refine hNFinv.meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
    rw [hordNinv]; exact_mod_cast le_of_lt hnn_pos
  have hNinvZero : (N (φ P))⁻¹ = 0 := by
    by_contra hne
    rw [hNFinv.meromorphicOrderAt_eq_zero_iff.2 hne] at hordNinv
    rw [eq_comm, WithTop.coe_eq_zero] at hordNinv; omega
  -- The chart pullback `G` equals `N⁻¹` near `φ P` (punctured: both `=ᶠ (N ·)⁻¹`; centre: both `0`).
  set G : ℂ → ℂ := chartInfty ∘ (f.toRiemannSphere) ∘ φ.symm with hGdef
  have hGeq : (fun w => (N w)⁻¹) =ᶠ[𝓝 (φ P)] G := by
    rw [Filter.EventuallyEq, ← nhdsNE_sup_pure (φ P), Filter.eventually_sup]
    refine ⟨?_, ?_⟩
    · have hN_ne : ∀ᶠ w in 𝓝[≠] (φ P), N w ≠ 0 := by
        rw [← meromorphicOrderAt_ne_top_iff_eventually_ne_zero hNF.meromorphicAt, hordN]
        exact WithTop.coe_ne_top
      have hrepr : f.holoRepr ∘ φ.symm =ᶠ[𝓝[≠] (φ P)] N :=
        f.holoRepr_chartPullback_eventuallyEq_NFAt P
      have hcoe : (fun w => f.toRiemannSphere (φ.symm w)) =ᶠ[𝓝[≠] (φ P)]
          (fun w => ((f.holoRepr (φ.symm w) : ℂ) : RiemannSphere)) :=
        f.toRiemannSphere_chartPullback_eventuallyEq_coe P
      filter_upwards [hN_ne, hrepr, hcoe] with w hwN0 hwrepr hwcoe
      show (N w)⁻¹ = chartInfty (f.toRiemannSphere (φ.symm w))
      rw [hwcoe, show f.holoRepr (φ.symm w) = N w from hwrepr,
        RiemannSphere.chartInfty_apply_coe hwN0]
    · simp only [Filter.eventually_pure]
      rw [hNinvZero]
      show (0 : ℂ) = chartInfty (f.toRiemannSphere (φ.symm (φ P)))
      rw [φ.left_inv hxsrc, f.toRiemannSphere_of_pole hP, RiemannSphere.chartInfty_apply_infty]
  refine ⟨hNinvAna.congr hGeq, ?_⟩
  -- Order transfer: `analyticOrderAt G = analyticOrderAt N⁻¹`, and the meromorphic order `−n` pins it.
  rw [← analyticOrderAt_congr hGeq]
  -- `N⁻¹` analytic with meromorphic order `−n`, so its analytic order maps to `−n` under `ℕ → ℤ`.
  rw [hNinvAna.meromorphicOrderAt_eq] at hordNinv
  have hmapeq : ENat.map (Nat.cast : ℕ → ℤ) (analyticOrderAt (fun w => (N w)⁻¹) (φ P))
      = ENat.map (Nat.cast : ℕ → ℤ) ((((-n).toNat : ℕ)) : ℕ∞) := by
    rw [hordNinv]; simp [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -n)]
  have := ENat.map_natCast_injective hmapeq
  rw [this, hn]

/-- **A simple pole is off the critical set** of `F = f.toRiemannSphere`.  At a pole `P` with
`orderAtPoint P = −1`, the reciprocal chart pullback `G = chartInfty ∘ F ∘ (chart P).symm` has analytic
order `1`, so `deriv G (chart P P) ≠ 0` (`deriv_ne_zero_of_analyticOrderAt_eq_one`), hence `G` is locally
injective at `chart P P` (`injOn_nhds_of_deriv_ne_zero`); transporting through the chart homeomorphisms
`chart P` (source) and `chartInfty` (target) — both `OpenPartialHomeomorph`s, injective on their
sources — `F` is locally injective at `P`, i.e. `P ∉ criticalSet F`. -/
theorem notMem_criticalSet_of_orderAtPoint_eq_neg_one (f : MeromorphicFunction X) {P : X}
    (hP : f.orderAtPoint P = -1) :
    P ∉ Jacobians.Discharge.Manifold.criticalSetGeneral f.toRiemannSphere := by
  set φ := chartAt (H := ℂ) P with hφ
  have hPneg : f.orderAtPoint P < 0 := by rw [hP]; norm_num
  obtain ⟨hGana, hGord⟩ := analyticAt_chartInfty_toRiemannSphere_pullback_of_pole f hPneg
  set G : ℂ → ℂ := chartInfty ∘ (f.toRiemannSphere) ∘ φ.symm with hGdef
  -- Order `1` from `orderAtPoint P = −1`.
  have hGord1 : analyticOrderAt G (φ P) = 1 := by
    rw [hGord, hP]; norm_num
  have hGderiv : deriv G (φ P) ≠ 0 :=
    Jacobians.Dolbeault.FormTraceInftyFibre.deriv_ne_zero_of_analyticOrderAt_eq_one hGana hGord1
  -- Local injectivity of `G` at `φ P`.
  obtain ⟨U, hU_nhds, hU_inj⟩ :=
    Jacobians.Discharge.Manifold.injOn_nhds_of_deriv_ne_zero hGana hGderiv
  -- `P ∉ criticalSet` = `∃ V ∈ 𝓝 P, InjOn F V`.
  show ¬ ¬ ∃ V ∈ 𝓝 P, Set.InjOn f.toRiemannSphere V
  rw [not_not]
  -- Pull `U` (a nbhd of `φ P` in the target chart) back to a nbhd `V` of `P` in `X`.
  -- `V := φ.source ∩ φ ⁻¹' U`; on `V`, `F = chartInfty.symm ∘ G ∘ φ` and `φ` lands in `U`.
  refine ⟨φ.source ∩ φ ⁻¹' U, ?_, ?_⟩
  · -- `V ∈ 𝓝 P`: `φ.source` open with `P ∈`, and `φ` continuous at `P` with `φ P ∈ U`.
    have h1 : φ.source ∈ 𝓝 P := φ.open_source.mem_nhds (mem_chart_source ℂ P)
    have h2 : φ ⁻¹' U ∈ 𝓝 P :=
      (φ.continuousAt (mem_chart_source ℂ P)).preimage_mem_nhds hU_nhds
    exact Filter.inter_mem h1 h2
  · -- `InjOn F V`: `F x = F y` ⟹ `G (φ x) = G (φ y)` (as `F = chartInfty.symm ∘ G ∘ φ`-ish on `V`) ⟹
    -- `φ x = φ y` (`G` injective on `U`) ⟹ `x = y` (`φ` injective on its source).
    intro x ⟨hxsrc, hxU⟩ y ⟨hysrc, hyU⟩ hFxy
    -- `G (φ x) = chartInfty (F x)` and `G (φ y) = chartInfty (F y)`.
    have hGx : G (φ x) = chartInfty (f.toRiemannSphere x) := by
      show chartInfty (f.toRiemannSphere (φ.symm (φ x))) = chartInfty (f.toRiemannSphere x)
      rw [φ.left_inv hxsrc]
    have hGy : G (φ y) = chartInfty (f.toRiemannSphere y) := by
      show chartInfty (f.toRiemannSphere (φ.symm (φ y))) = chartInfty (f.toRiemannSphere y)
      rw [φ.left_inv hysrc]
    have hGeq : G (φ x) = G (φ y) := by rw [hGx, hGy, hFxy]
    have hφeq : φ x = φ y := hU_inj hxU hyU hGeq
    exact φ.injOn hxsrc hysrc hφeq

/-- **`∞` is off the branch locus when every pole is simple.**  The fibre `F⁻¹{∞}` is exactly the pole
set of `f`, enumerated by `inftyFibreEnum`.  If every pole is simple (`hsimpleInf : ∀ i, orderAtPoint
(inftyFibreEnum f i) = −1`), then no pole is in `criticalSet F`
(`notMem_criticalSet_of_orderAtPoint_eq_neg_one`); since `branchLocus F = F '' criticalSet F` and every
preimage of `∞` is a pole, `∞ ∉ branchLocus F`. -/
theorem infty_notMem_branchLocus_of_simpleInfty (f : MeromorphicFunction X)
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1) :
    OnePoint.infty ∉ branchLocus f.toRiemannSphere := by
  rw [branchLocus, Set.mem_image]
  rintro ⟨a, ha_crit, ha_inf⟩
  -- `F a = ∞` ⟹ `a` is a pole ⟹ `a = inftyFibreEnum f i` for some `i` ⟹ `a` simple ⟹ `a ∉ criticalSet`.
  obtain ⟨i, hi⟩ := inftyFibreEnum_surj f ha_inf
  have ha_simple : f.orderAtPoint a = -1 := by rw [← hi]; exact hsimpleInf i
  exact notMem_criticalSet_of_orderAtPoint_eq_neg_one f ha_simple ha_crit

/-- **A `LocalSheetSystem` of `F = f.toRiemannSphere` at `∞`**, from simple `∞`-poles.  Since `∞ ∉
branchLocus F` (`infty_notMem_branchLocus_of_simpleInfty`) and `F` is a nonconstant holomorphic map to
`ℂℙ¹` (`f.div ≠ 0`), Forster §4.22 (`exists_localSheetSystem`) provides the moving sheets sweeping the
`∞`-fibre over a sphere neighbourhood `V ∋ ∞`.  This is the `∞`-analogue of `exists_sphereSheetSystem`
(specialized to finite values); it is the geometric source of an `InftyMovingCoherenceData` (the moving
sheets supply the index bijection at `∞`), exactly as the finite sphere sheet system supplies the finite
`Cfull` datum via `ofSphereSheetSystemCanon`. -/
theorem exists_inftySheetSystem (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1) :
    Nonempty (Jacobians.LocalSheetSystem f.toRiemannSphere OnePoint.infty) :=
  Jacobians.exists_localSheetSystem f.toRiemannSphere f.contMDiff_toRiemannSphere
    (f.toRiemannSphere_not_isConstant (exists_orderAtPoint_ne_zero f hdiv))
    (infty_notMem_branchLocus_of_simpleInfty f hsimpleInf)

/-! ## The reduction of `hcoh_geom` to the large-`z` diagonal

The target `∞`-coherence is `recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF
ω₀ f Dinf)`.  Since `recipCoeff R ζ = −R(ζ⁻¹)·ζ⁻²` depends on `R` *only* through `R(ζ⁻¹)`, this is
*equivalent* to the underlying functions agreeing for large `z` (i.e. at `ζ⁻¹`, `ζ → 0`):

> `∀ᶠ ζ in 𝓝[≠] 0, valueChartTrace ω₀ f Φ (ζ⁻¹) = inftyMovingSumNF ω₀ f Dinf (ζ⁻¹)`.

This is the honest, non-circular residual: the §VIII.3 statement "the trace = the moving `∞`-fibre sum near
`∞`" read in the value coordinate (large `z`).  It is a germ-equality on a *punctured* neighbourhood of
`0` (equivalently: for `|z|` large), **never evaluating at `∞` itself** — so no junk-value defect (the
value-trace reads `g` at the moving fibre points `Φ z`, all genuine non-`∞` points for large finite `z`).
And it is the moving-fibre-sum identity, *not* the residue cancellation — non-circular. -/

/-- **`hcoh_geom` from the large-`z` diagonal.**  `recipCoeff R₁ =ᶠ[𝓝[≠] 0] recipCoeff R₂` whenever the
functions agree at `ζ⁻¹` for `ζ` near `0` (`hdiag_inf`): both `recipCoeff`s are `−·(ζ⁻¹)·ζ⁻²`, so the
shared `R(ζ⁻¹)` value makes them equal.  This is the clean reduction of the `∞`-coherence `hcoh_geom` to
the large-`z` value-trace / `∞`-moving-sum agreement (the genuine §VIII.3 `∞`-single-valuedness). -/
theorem recipCoeff_eventuallyEq_of_eventuallyEq_inv {R₁ R₂ : ℂ → ℂ}
    (hdiag_inf : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), R₁ (ζ⁻¹) = R₂ (ζ⁻¹)) :
    recipCoeff R₁ =ᶠ[𝓝[≠] 0] recipCoeff R₂ := by
  filter_upwards [hdiag_inf] with ζ hζ
  show -(R₁ (ζ⁻¹)) * ζ ^ (-2 : ℤ) = -(R₂ (ζ⁻¹)) * ζ ^ (-2 : ℤ)
  rw [hζ]

/-- **`hcoh_geom` from the large-`z` diagonal (the `inftyFibreDataNF_full` instance).**  Specialization of
`recipCoeff_eventuallyEq_of_eventuallyEq_inv` to the value trace `R₁ := valueChartTrace ω₀ f Φ` and the
`∞`-moving sum `R₂ := inftyMovingSumNF ω₀ f Dinf`, giving the exact `hcoh_geom` shape consumed by
`residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg`. -/
theorem hcoh_geom_of_diagonalInfty (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (Dinf : InftyFibreDataNF g f)
    (hdiag_inf : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      valueChartTrace ω₀ f Φ (ζ⁻¹) = inftyMovingSumNF ω₀ f Dinf (ζ⁻¹)) :
    recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf) :=
  recipCoeff_eventuallyEq_of_eventuallyEq_inv hdiag_inf

/-! ## Step (3a): the `∞`-moving sum as a fixed-chart moving fibre sum (reciprocal-chart bookkeeping)

The `∞`-moving sum `inftyMovingSumNF ω₀ f Dinf z = ∑ i, chartIntegrand ω₀ g (Dinf.xs i) (recipSheet i
(z⁻¹))·deriv (w ↦ recipSheet i (w⁻¹)) z` reads the *reciprocal-chart* planar sections `recipSheet i :=
(inftyFibreTraceNF ω₀ f Dinf).sheet i` (the planar inverses of the repaired reciprocals `recip i`, with
`recipSheet i 0 = chart (Dinf.xs i)(Dinf.xs i)`).  Define the **manifold sections** through the
`∞`-fibre poles, `inftyManifoldSec i z := (chart (Dinf.xs i)).symm (recipSheet i (z⁻¹))`.  For `z⁻¹` near
`0` (i.e. `z` large), `recipSheet i (z⁻¹)` lies in `chart (Dinf.xs i).target` (continuity, since
`recipSheet i 0 = chart (Dinf.xs i)(Dinf.xs i) ∈ target`), so the chart and its inverse cancel:

* `chart (Dinf.xs i)(inftyManifoldSec i z) = recipSheet i (z⁻¹)`;
* `deriv (w ↦ chart (Dinf.xs i)(inftyManifoldSec i w)) z = deriv (w ↦ recipSheet i (w⁻¹)) z`.

Hence `inftyMovingSumNF ω₀ f Dinf z = ∑ i, chartIntegrand ω₀ g (Dinf.xs i) (chart (Dinf.xs i)
(inftyManifoldSec i z))·deriv (w ↦ chart (Dinf.xs i)(inftyManifoldSec i w)) z` — the **fixed-chart moving
fibre sum** along `inftyManifoldSec`, the exact RHS shape that `traceCoeff_diagonal_eq_fixedSum`
produces.  This is pure reciprocal-chart bookkeeping (no monodromy), discharged in full. -/

/-- **The manifold sections through the `∞`-fibre poles.**  `inftyManifoldSec ω₀ f Dinf i z` is the
manifold point on the `i`-th `∞`-fibre sheet over the value `z`: the chart inverse (at the pole `Dinf.xs
i`) of the reciprocal-chart planar section `recipSheet i` evaluated at the reciprocal coordinate `z⁻¹`.
For `z` large (`z⁻¹` near `0`), `recipSheet i (z⁻¹)` is near the chart-target point `pre i`, so this is a
genuine manifold point near the pole `Dinf.xs i`. -/
noncomputable def inftyManifoldSec (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) : ℂ → X :=
  fun z => (chartAt ℂ (Dinf.xs i)).symm ((inftyFibreTraceNF ω₀ f Dinf).sheet i (z⁻¹))

/-- **The reciprocal section value at `0` is the pole's chart image** (`recipSheet i 0 = pre i =
chart (Dinf.xs i)(Dinf.xs i)`). -/
theorem recipSheet_zero (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    (inftyFibreTraceNF ω₀ f Dinf).sheet i 0 = (chartAt ℂ (Dinf.xs i)) (Dinf.xs i) := by
  have := (inftyFibreTraceNF ω₀ f Dinf).sheet_base i
  rwa [inftyFibreTraceNF_b, inftyFibreTraceNF_pre] at this

/-- **Eventually (`ζ` near `0`), the reciprocal section lands in the pole's chart target.**  At `ζ = 0`
it is `recipSheet i 0 = pre i = chart (Dinf.xs i)(Dinf.xs i) ∈ target` (`recipSheet_zero`); continuity of
`recipSheet i` (analytic at `0`) and openness of the target extend this to a neighbourhood of `0`. -/
theorem eventually_recipSheet_mem_target (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ),
      (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target := by
  have hmem : (inftyFibreTraceNF ω₀ f Dinf).sheet i 0 ∈ (chartAt ℂ (Dinf.xs i)).target := by
    rw [recipSheet_zero]; exact (chartAt ℂ (Dinf.xs i)).map_source (mem_chart_source ℂ (Dinf.xs i))
  have hcont : ContinuousAt ((inftyFibreTraceNF ω₀ f Dinf).sheet i) 0 := by
    have han := (inftyFibreTraceNF ω₀ f Dinf).sheet_analytic i
    rw [inftyFibreTraceNF_b] at han
    exact han.continuousAt
  exact hcont.eventually_mem ((chartAt ℂ (Dinf.xs i)).open_target.mem_nhds hmem)

/-- **The reciprocal section is analytic (hence continuous) on a punctured neighbourhood of `0`.**  The
`inftyFibreTraceNF` sheets are `AnalyticAt 0`; analyticity propagates to a full neighbourhood
(`AnalyticAt.eventually_analyticAt`). -/
theorem eventually_recipSheet_analyticAt (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), AnalyticAt ℂ ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ := by
  have han := (inftyFibreTraceNF ω₀ f Dinf).sheet_analytic i
  rw [inftyFibreTraceNF_b] at han
  exact han.eventually_analyticAt

/-! ## The `∞`-manifold sections are sections of the value coordinate `f.holoRepr`

The geometric heart of the index bijection: the manifold sections `inftyManifoldSec i z` are genuine
sections of the finite value coordinate `f.holoRepr` for large `z` (`z⁻¹` near `0`, `≠ 0`).  This is the
reciprocal-chart analogue of "the sheets are sections of `f`": the planar sheet `recipSheet i` is the
right-inverse of the repaired reciprocal `recip i` (a zero of order `1`), and `recip i` *is* the literal
reciprocal `1/f` off the centre (`hrecip_germ`), so `recipSheet i ζ` reads the manifold point whose
`f.holoRepr` is `ζ⁻¹`.  The off-centre fact `recipSheet i ζ ≠ pre i` (for `ζ ≠ 0`) — needed to invoke
the punctured germ-link — is *automatic*: `recip i (pre i) = 0 ≠ ζ`. -/

/-- **The reciprocal sheet right-inverts the repaired reciprocal.**  The planar sheet
`recipSheet i = (inftyFibreTraceNF ω₀ f Dinf).sheet i` is the planar inverse of `recip i` chosen by
`exists_planar_section`, so `recip i (recipSheet i ζ) = ζ` for `ζ` near `0` (the right-inverse field of
`exists_planar_section`). -/
theorem inftyRecipSheet_rightInverse (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), Dinf.recip i ((inftyFibreTraceNF ω₀ f Dinf).sheet i ζ) = ζ :=
  -- `recip i (pre i) = 0` (`hrecip_val`) is the base value `b` of `exists_planar_section`, so its
  -- right-inverse field reads `∀ᶠ w in 𝓝 0, recip i (sheet i w) = w` (the sheet *is* `Classical.choose`).
  (Classical.choose_spec
    (exists_planar_section (Dinf.hrecip_an i) (Dinf.hrecip_deriv i) (Dinf.hrecip_val i))).2.2.2

/-- **The reciprocal sheet is off the centre for `ζ ≠ 0` near `0`.**  If `recipSheet i ζ = pre i` then
`recip i (recipSheet i ζ) = recip i (pre i) = 0` (`hrecip_val`); but the right-inverse gives
`recip i (recipSheet i ζ) = ζ` (eventually), so `ζ = 0`.  Hence for `ζ ≠ 0` near `0`,
`recipSheet i ζ ≠ pre i = chart (Dinf.xs i)(Dinf.xs i)`. -/
theorem eventually_recipSheet_ne (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ≠ (chartAt ℂ (Dinf.xs i)) (Dinf.xs i) := by
  filter_upwards [nhdsWithin_le_nhds (inftyRecipSheet_rightInverse ω₀ f Dinf i),
    self_mem_nhdsWithin] with ζ hrinv hζ0
  have hζ : ζ ≠ 0 := by simpa using hζ0
  intro hcontra
  apply hζ
  rw [← hrinv, hcontra, Dinf.hrecip_val i]

/-- **The reciprocal sheet tends to the pole centre along the punctured filter.**  `recipSheet i ζ →
pre i = chart (Dinf.xs i)(Dinf.xs i)` as `ζ → 0` within `≠ 0` (continuity, with value `pre i` at `0`),
*and* stays `≠ pre i` (`eventually_recipSheet_ne`), so it tends to `pre i` within `≠ pre i`.  This is the
filter map that pulls the punctured germ-link `hrecip_germ` of `recip i` back to `ζ`. -/
theorem tendsto_recipSheet_nhdsNE (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    Tendsto ((inftyFibreTraceNF ω₀ f Dinf).sheet i) (𝓝[≠] (0 : ℂ))
      (𝓝[≠] ((chartAt ℂ (Dinf.xs i)) (Dinf.xs i))) := by
  have hcont : ContinuousAt ((inftyFibreTraceNF ω₀ f Dinf).sheet i) 0 := by
    have han := (inftyFibreTraceNF ω₀ f Dinf).sheet_analytic i
    rw [inftyFibreTraceNF_b] at han
    exact han.continuousAt
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, eventually_recipSheet_ne ω₀ f Dinf i⟩
  -- `recipSheet i → recipSheet i 0 = pre i` (continuity), restricted to the punctured filter.
  have htend : Tendsto ((inftyFibreTraceNF ω₀ f Dinf).sheet i) (𝓝[≠] (0 : ℂ))
      (𝓝 ((inftyFibreTraceNF ω₀ f Dinf).sheet i 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  rwa [recipSheet_zero] at htend

/-- **`f.holoRepr (inftyManifoldSec i z) = z` for large `z`.**  The manifold section
`inftyManifoldSec i z = chart⁻¹ (recipSheet i (z⁻¹))` is a section of the value coordinate `f.holoRepr`
for `z` with `z⁻¹ ≠ 0` near `0` (i.e. `z` large): with `ζ = z⁻¹ ≠ 0` near `0`, `recipSheet i ζ` is off
the pole centre (`eventually_recipSheet_ne`) and lands in the chart target, so the germ-link
`recip i =ᶠ[𝓝[≠] pre i] (1/f in charts)` gives `(f.holoRepr (chart⁻¹ (recipSheet i ζ)))⁻¹ =
recip i (recipSheet i ζ) = ζ`, hence `f.holoRepr (inftyManifoldSec i z) = ζ⁻¹ = z`. -/
theorem eventually_holoRepr_inftyManifoldSec (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      f.holoRepr (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)) = ζ⁻¹ := by
  -- Pull the punctured germ-link of `recip i` back along `recipSheet i`.
  have hgermPull : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      Dinf.recip i ((inftyFibreTraceNF ω₀ f Dinf).sheet i ζ)
        = (f.holoRepr ((chartAt ℂ (Dinf.xs i)).symm ((inftyFibreTraceNF ω₀ f Dinf).sheet i ζ)))⁻¹ :=
    (tendsto_recipSheet_nhdsNE ω₀ f Dinf i).eventually (Dinf.hrecip_germ i)
  filter_upwards [hgermPull, nhdsWithin_le_nhds (inftyRecipSheet_rightInverse ω₀ f Dinf i),
    self_mem_nhdsWithin] with ζ hgerm hrinv hζ0
  have hζ : ζ ≠ 0 := by simpa using hζ0
  -- `(f.holoRepr (chart⁻¹ (recipSheet i ζ)))⁻¹ = recip i (recipSheet i ζ) = ζ`, so the value `= ζ⁻¹`.
  have hval : (f.holoRepr (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)))⁻¹ = ζ := by
    unfold inftyManifoldSec
    rw [inv_inv, ← hgerm, hrinv]
  rw [← inv_inv (f.holoRepr (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))), hval]

/-- **`f.holoRepr (inftyManifoldSec i ·) = id` on a *neighbourhood* of `ζ⁻¹` (large `z`).**  The
neighbourhood-form of the section property, needed by `chartPullback_section_rinv` (which wants the
right-inverse on a full `𝓝 (ζ⁻¹)`).  Three ingredients, each `eventually-eventually` (a full nbhd of
`ζ⁻¹` for `ζ` near `0`): the germ-link of `recip i` *as a full-nbhd statement at off-centre points*
(`eventually_nhdsNE_eventually_nhds_iff`, pulled back along `recipSheet i → centre`), the right-inverse
(`inftyRecipSheet_rightInverse`, spread by `eventually_eventually_nhds`), and `w ≠ 0`. -/
theorem eventually_holoRepr_inftyManifoldSec_nhds (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ∀ᶠ w in 𝓝 (ζ⁻¹),
      f.holoRepr (inftyManifoldSec ω₀ f Dinf i w) = w := by
  -- (1) Germ-link as a full-nbhd statement at off-centre points, pulled back along `recipSheet i`.
  have hgerm_nbhd : ∀ᶠ u in 𝓝[≠] ((chartAt ℂ (Dinf.xs i)) (Dinf.xs i)), ∀ᶠ v in 𝓝 u,
      Dinf.recip i v = (f.holoRepr ((chartAt ℂ (Dinf.xs i)).symm v))⁻¹ :=
    (eventually_nhdsNE_eventually_nhds_iff (p := fun v => Dinf.recip i v
      = (f.holoRepr ((chartAt ℂ (Dinf.xs i)).symm v))⁻¹)).2 (Dinf.hrecip_germ i)
  have hgermζ : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ∀ᶠ v in 𝓝 ((inftyFibreTraceNF ω₀ f Dinf).sheet i ζ),
      Dinf.recip i v = (f.holoRepr ((chartAt ℂ (Dinf.xs i)).symm v))⁻¹ :=
    (tendsto_recipSheet_nhdsNE ω₀ f Dinf i).eventually hgerm_nbhd
  -- (2) Right-inverse spread to a full nbhd of `ζ` (for `ζ` near `0`).
  have hrinvζ : ∀ᶠ ζ in 𝓝 (0 : ℂ), ∀ᶠ η in 𝓝 ζ,
      Dinf.recip i ((inftyFibreTraceNF ω₀ f Dinf).sheet i η) = η :=
    eventually_eventually_nhds.2 (inftyRecipSheet_rightInverse ω₀ f Dinf i)
  filter_upwards [hgermζ, nhdsWithin_le_nhds hrinvζ,
    nhdsWithin_le_nhds (eventually_recipSheet_analyticAt ω₀ f Dinf i), self_mem_nhdsWithin]
    with ζ hgerm hrinv hana hζ0
  have hζ : ζ ≠ 0 := by simpa using hζ0
  -- Continuity of `recipSheet i` at `ζ` (to pull `hgerm` back along `recipSheet i`).
  have hsheetCont : ContinuousAt ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ := hana.continuousAt
  -- Pull the germ-link back along `recipSheet i` (continuous at `ζ`) to a nbhd of `ζ` in `η`.
  have hgermη : ∀ᶠ η in 𝓝 ζ,
      Dinf.recip i ((inftyFibreTraceNF ω₀ f Dinf).sheet i η)
        = (f.holoRepr ((chartAt ℂ (Dinf.xs i)).symm ((inftyFibreTraceNF ω₀ f Dinf).sheet i η)))⁻¹ :=
    hsheetCont.eventually hgerm
  -- Combine into the section identity at `η` near `ζ`, then pull back along `w ↦ w⁻¹` to `w` near `ζ⁻¹`.
  have hsecη : ∀ᶠ η in 𝓝 ζ, f.holoRepr (inftyManifoldSec ω₀ f Dinf i (η⁻¹)) = η⁻¹ := by
    filter_upwards [hgermη, hrinv, (continuousAt_id.eventually_ne hζ)] with η hg hr hηne
    have hval : (f.holoRepr (inftyManifoldSec ω₀ f Dinf i (η⁻¹)))⁻¹ = η := by
      unfold inftyManifoldSec; rw [inv_inv, ← hg, hr]
    rw [← inv_inv (f.holoRepr (inftyManifoldSec ω₀ f Dinf i (η⁻¹))), hval]
  -- `w ↦ w⁻¹` is continuous at `ζ⁻¹` with value `(ζ⁻¹)⁻¹ = ζ`, so `hsecη` (a nbhd of `ζ`) pulls back to
  -- a nbhd of `ζ⁻¹` in `w`; at `w` the identity reads `f.holoRepr (inftyManifoldSec i w) = w`.
  have hinvTend : Tendsto (fun w : ℂ => w⁻¹) (𝓝 (ζ⁻¹)) (𝓝 ζ) := by
    have := (continuousAt_inv₀ (inv_ne_zero hζ)).tendsto; rwa [inv_inv] at this
  filter_upwards [hinvTend.eventually hsecη, (continuousAt_id.eventually_ne (inv_ne_zero hζ))]
    with w hw hwne
  rwa [inv_inv] at hw

/-- **`inftyManifoldSec i (ζ⁻¹) ≠ Dinf.xs i` and tends to it.**  For `ζ ≠ 0` near `0`, the manifold
section is *not* the pole `Dinf.xs i` (its reciprocal-chart image `recipSheet i ζ ≠ pre i` by
`eventually_recipSheet_ne`, transported through the injective chart inverse), yet it tends to
`Dinf.xs i` as `ζ → 0`.  Together these place it, for `ζ` small, in any isolating neighbourhood of the
pole while staying off the pole — so it is a *non-pole* (poles are isolated). -/
theorem eventually_inftyManifoldSec_ne (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), inftyManifoldSec ω₀ f Dinf i (ζ⁻¹) ≠ Dinf.xs i := by
  filter_upwards [eventually_recipSheet_ne ω₀ f Dinf i,
    nhdsWithin_le_nhds (eventually_recipSheet_mem_target ω₀ f Dinf i)] with ζ hne hmem
  unfold inftyManifoldSec
  rw [inv_inv]
  intro hcontra
  -- `chart⁻¹ (recipSheet i ζ) = Dinf.xs i ⟹ recipSheet i ζ = chart (Dinf.xs i) (Dinf.xs i)` (apply chart).
  apply hne
  have := congrArg (chartAt ℂ (Dinf.xs i)) hcontra
  rwa [(chartAt ℂ (Dinf.xs i)).right_inv hmem] at this

/-- **`inftyManifoldSec i (ζ⁻¹)` tends to the pole `Dinf.xs i`.**  `recipSheet i ζ → pre i`
(continuity) lands eventually in the chart target, where `chart⁻¹` is continuous, so
`inftyManifoldSec i ζ⁻¹ = chart⁻¹ (recipSheet i ζ) → chart⁻¹ (pre i) = Dinf.xs i`. -/
theorem tendsto_inftyManifoldSec (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    Tendsto (fun ζ => inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)) (𝓝 (0 : ℂ)) (𝓝 (Dinf.xs i)) := by
  have hcont : Tendsto ((inftyFibreTraceNF ω₀ f Dinf).sheet i) (𝓝 (0 : ℂ))
      (𝓝 ((chartAt ℂ (Dinf.xs i)) (Dinf.xs i))) := by
    have han := (inftyFibreTraceNF ω₀ f Dinf).sheet_analytic i
    rw [inftyFibreTraceNF_b] at han
    have := han.continuousAt.tendsto
    rwa [recipSheet_zero] at this
  -- `chart⁻¹` continuous at `pre i ∈ target`, value `Dinf.xs i`.
  have hsymm : ContinuousAt (chartAt ℂ (Dinf.xs i)).symm
      ((chartAt ℂ (Dinf.xs i)) (Dinf.xs i)) :=
    (chartAt ℂ (Dinf.xs i)).continuousAt_symm ((chartAt ℂ (Dinf.xs i)).map_source
      (mem_chart_source ℂ (Dinf.xs i)))
  have htend := hsymm.tendsto.comp hcont
  rw [(chartAt ℂ (Dinf.xs i)).left_inv (mem_chart_source ℂ (Dinf.xs i))] at htend
  -- `(fun ζ => inftyManifoldSec i ζ⁻¹) = (chart⁻¹ ∘ recipSheet i)` (since `inftyManifoldSec i z` uses
  -- `recipSheet i (z⁻¹)`, here `z = ζ⁻¹` so `z⁻¹ = ζ`).
  have hrw : (fun ζ => inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))
      = (chartAt ℂ (Dinf.xs i)).symm ∘ ((inftyFibreTraceNF ω₀ f Dinf).sheet i) := by
    funext ζ; unfold inftyManifoldSec; rw [inv_inv]; rfl
  rw [hrw]; exact htend

/-- **The manifold section is a non-pole for large `z`.**  For `ζ ≠ 0` near `0`,
`inftyManifoldSec i (ζ⁻¹)` lies in the pole's isolating neighbourhood (`tendsto_inftyManifoldSec`) yet
is off the pole (`eventually_inftyManifoldSec_ne`), so its `orderAtPoint` is `0 ≥ 0`. -/
theorem eventually_inftyManifoldSec_nonpole (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), 0 ≤ f.orderAtPoint (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)) := by
  obtain ⟨t, ht_nhds, ht⟩ := f.orderAtPoint_isolated_at (Dinf.xs i)
  have hint : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), inftyManifoldSec ω₀ f Dinf i (ζ⁻¹) ∈ t :=
    (tendsto_inftyManifoldSec ω₀ f Dinf i).mono_left nhdsWithin_le_nhds |>.eventually_mem ht_nhds
  filter_upwards [hint, eventually_inftyManifoldSec_ne ω₀ f Dinf i] with ζ hmem hne
  rw [ht _ hmem hne]

/-- **The manifold section lands in the fibre `F⁻¹(coe (ζ⁻¹))`.**  Combining the section property
(`f.holoRepr (inftyManifoldSec i ζ⁻¹) = ζ⁻¹`) with non-poleness
(`eventually_inftyManifoldSec_nonpole`): `f.toRiemannSphere (inftyManifoldSec i ζ⁻¹) = coe (holoRepr) =
coe (ζ⁻¹)`.  So `inftyManifoldSec i ζ⁻¹` is a genuine point of the fibre over the finite value `coe
(ζ⁻¹)`, for `ζ ≠ 0` near `0`. -/
theorem eventually_inftyManifoldSec_mem_fibre (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      f.toRiemannSphere (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)) = (((ζ⁻¹ : ℂ) : RiemannSphere)) := by
  filter_upwards [eventually_inftyManifoldSec_nonpole ω₀ f Dinf i,
    eventually_holoRepr_inftyManifoldSec ω₀ f Dinf i] with ζ hnp hrepr
  rw [f.toRiemannSphere_of_nonneg hnp, hrepr]

/-! ## The `∞`-manifold sections are an injective enumeration of the fibre (the index bijection's domain)

The manifold sections `inftyManifoldSec · (ζ⁻¹)` are **injective** for `ζ ≠ 0` near `0`: each tends to a
distinct pole `Dinf.xs k` (the poles are distinct, `Dinf.xs` injective), so for small `ζ` they live in
disjoint neighbourhoods (T2 separation).  Combined with the cardinality count from the `∞`-sheet system
`S` (`#Dinf.ι = S.n = #(F⁻¹(coe ζ⁻¹))`), an injective map into the fibre of equal cardinality is onto, so
the manifold sections **enumerate the entire fibre** — the reciprocal-chart analogue of
`sheetValues_range_eq_fibre`. -/

/-- **Pairwise eventual separation of the manifold sections.**  For distinct poles `k₁ ≠ k₂`, the
sections `inftyManifoldSec k₁ (ζ⁻¹)` and `inftyManifoldSec k₂ (ζ⁻¹)` tend to the *distinct* poles
`Dinf.xs k₁ ≠ Dinf.xs k₂` (`tendsto_inftyManifoldSec`, `Dinf.xs` injective via `Function.Injective`),
so for `ζ` near `0` they lie in disjoint neighbourhoods (T2 separation), hence are distinct. -/
theorem eventually_inftyManifoldSec_pairwise_ne (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Dinf : InftyFibreDataNF g f) (hxs_inj : Function.Injective Dinf.xs)
    {k₁ k₂ : Dinf.ι} (hk : k₁ ≠ k₂) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ),
      inftyManifoldSec ω₀ f Dinf k₁ (ζ⁻¹) ≠ inftyManifoldSec ω₀ f Dinf k₂ (ζ⁻¹) := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hxU₁, hxU₂, hdisj⟩ := t2_separation (hxs_inj.ne hk)
  have h1 : ∀ᶠ ζ in 𝓝 (0 : ℂ), inftyManifoldSec ω₀ f Dinf k₁ (ζ⁻¹) ∈ U₁ :=
    (tendsto_inftyManifoldSec ω₀ f Dinf k₁).eventually_mem (hU₁.mem_nhds hxU₁)
  have h2 : ∀ᶠ ζ in 𝓝 (0 : ℂ), inftyManifoldSec ω₀ f Dinf k₂ (ζ⁻¹) ∈ U₂ :=
    (tendsto_inftyManifoldSec ω₀ f Dinf k₂).eventually_mem (hU₂.mem_nhds hxU₂)
  filter_upwards [h1, h2] with ζ hζ1 hζ2 hcontra
  exact (Set.disjoint_left.mp hdisj) hζ1 (hcontra ▸ hζ2)

/-- **The manifold sections are eventually injective.**  Combining the pairwise separations
(`eventually_inftyManifoldSec_pairwise_ne`) over the finitely many off-diagonal pairs of `Dinf.ι`:
for `ζ` near `0`, `fun k => inftyManifoldSec k (ζ⁻¹)` is injective. -/
theorem eventually_inftyManifoldSec_injective (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Dinf : InftyFibreDataNF g f) (hxs_inj : Function.Injective Dinf.xs) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), Function.Injective (fun k => inftyManifoldSec ω₀ f Dinf k (ζ⁻¹)) := by
  classical
  -- Combine the pairwise separations over the finite set of off-diagonal pairs.
  have hpair : ∀ᶠ ζ in 𝓝 (0 : ℂ), ∀ p : Dinf.ι × Dinf.ι, p.1 ≠ p.2 →
      inftyManifoldSec ω₀ f Dinf p.1 (ζ⁻¹) ≠ inftyManifoldSec ω₀ f Dinf p.2 (ζ⁻¹) := by
    rw [eventually_all]
    intro p
    rcases eq_or_ne p.1 p.2 with h | h
    · exact Filter.Eventually.of_forall (fun ζ hcontra => absurd h hcontra)
    · filter_upwards [eventually_inftyManifoldSec_pairwise_ne ω₀ f Dinf hxs_inj h] with ζ hζ _
      exact hζ
  filter_upwards [hpair] with ζ hζ k₁ k₂ hk
  by_contra hne
  exact hζ (k₁, k₂) hne hk

/-! ## The `∞`-manifold sections are smooth (the differentiability fields)

`inftyManifoldSec i = chart⁻¹ ∘ recipSheet i ∘ (·⁻¹)` is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` at `ζ⁻¹` (large):
`·⁻¹` analytic at `ζ⁻¹ ≠ 0`, `recipSheet i` analytic near `ζ` (`eventually_recipSheet_analyticAt`),
`chart⁻¹` is `C^ω` on the chart target (where `recipSheet i ζ` lands).  This supplies the
continuity/differentiability fields of `hbij` via the finite helpers
`differentiableAt_chart_pullback_section` / `transition_differentiableAt_overlap`. -/

/-- **The manifold sections are smooth for large `z`.**  For `ζ ≠ 0` near `0` with
`recipSheet i ζ ∈ chart target`, `inftyManifoldSec i` is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` at `ζ⁻¹`:
`w ↦ w⁻¹` is `C^ω` at `ζ⁻¹ ≠ 0`, `recipSheet i` is `C^ω` (analytic) at `(ζ⁻¹)⁻¹ = ζ`, and `chart⁻¹` is
`C^ω` on the chart target. -/
theorem inftyManifoldSec_contMDiffAt (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) {ζ : ℂ} (hζ : ζ ≠ 0)
    (hana : AnalyticAt ℂ ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ)
    (hmem : (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (inftyManifoldSec ω₀ f Dinf i) (ζ⁻¹) := by
  -- `w ↦ w⁻¹` is `C^ω` at `ζ⁻¹` (≠ 0).
  have hinv : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w : ℂ => w⁻¹) (ζ⁻¹) := by
    rw [contMDiffAt_iff_contDiffAt]
    exact (contDiffAt_inv ℂ (inv_ne_zero hζ))
  -- `recipSheet i` is `C^ω` at `(ζ⁻¹)⁻¹ = ζ` (analytic).
  have hsheet : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ((ζ⁻¹)⁻¹) := by
    rw [inv_inv, contMDiffAt_iff_contDiffAt]
    exact hana.contDiffAt
  -- `chart⁻¹` is `C^ω` at `recipSheet i ((ζ⁻¹)⁻¹) = recipSheet i ζ ∈ chart target`.
  have hchart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ (Dinf.xs i)).symm
      ((inftyFibreTraceNF ω₀ f Dinf).sheet i ((ζ⁻¹)⁻¹)) := by
    rw [inv_inv]
    exact ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := Dinf.xs i)) _ hmem).contMDiffAt
      ((chartAt ℂ (Dinf.xs i)).open_target.mem_nhds hmem)
  -- Compose: `inftyManifoldSec i = chart⁻¹ ∘ (recipSheet i ∘ (·⁻¹))`.
  exact hchart.comp (ζ⁻¹) (hsheet.comp (ζ⁻¹) hinv)

/-! ## The cardinality count and the fibre-enumeration of the manifold sections (via the `∞`-sheet system)

The genuine geometric content the `∞`-sheet system `S` supplies (the reciprocal-chart analogue of
`sheetValues_range_eq_fibre`): the number of `∞`-poles equals the degree, so the injective manifold
sections sweep the *entire* finite-value fibre.  Concretely:

* `coe ζ⁻¹ ∈ S.V` for `ζ` near `0` (large `z`): `coe ζ⁻¹ → ∞` (`OnePoint.tendsto_coe_infty` ∘ the inverse
  tending to `cobounded`), and `S.V` is a neighbourhood of `∞`.
* `#Dinf.ι = S.n`: both `Dinf.xs` and the `∞`-sheets `S.sheet · ∞` injectively enumerate the pole set
  `F⁻¹{∞}` (the symmetric lever `equivOfInjective_image_eq` ⟹ an index `Equiv`).
* `#(F⁻¹(coe ζ⁻¹)) = S.n`: the sheets `S.sheet · (coe ζ⁻¹)` injectively enumerate `F⁻¹(coe ζ⁻¹)`.

So the injective manifold sections (`eventually_inftyManifoldSec_injective`) with range `⊆ F⁻¹(coe ζ⁻¹)`
(`eventually_inftyManifoldSec_mem_fibre`) and `#Dinf.ι = #(F⁻¹(coe ζ⁻¹))` have range *equal to* the fibre
(an injective map into a finite set of equal cardinality is onto). -/

/-- **`coe ζ⁻¹ ∈ S.V` for `ζ` near `0`.**  `coe ζ⁻¹ → ∞` as `ζ → 0` within `≠ 0` (`OnePoint.tendsto_coe_infty`
composed with `·⁻¹` tending to `cobounded ℂ ≤ coclosedCompact ℂ`), and `S.V` is an open neighbourhood of
`∞`. -/
theorem eventually_coe_inv_mem_V (f : MeromorphicFunction X)
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere OnePoint.infty) :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), (((ζ⁻¹ : ℂ) : RiemannSphere)) ∈ S.V := by
  have htend : Tendsto (fun ζ : ℂ => ((ζ⁻¹ : ℂ) : RiemannSphere)) (𝓝[≠] (0 : ℂ)) (𝓝 OnePoint.infty) :=
    OnePoint.tendsto_coe_infty.comp (Filter.tendsto_inv₀_nhdsNE_zero.mono_right
      (by rw [Filter.coclosedCompact_eq_cocompact]; exact Metric.cobounded_le_cocompact))
  exact htend.eventually_mem (S.isOpen_V.mem_nhds S.mem_V)

/-- **`#Dinf.ι = S.n`.**  Both `Dinf.xs` and the `∞`-sheets `S.sheet · ∞` injectively enumerate the pole
set `F⁻¹{∞}` (`Dinf.xs` by `hxs_range`; the sheets by `S.fibre_eq ∞ S.mem_V` + `S.sheet_inj ∞ S.mem_V`),
so the symmetric lever `equivOfInjective_image_eq` produces an `Equiv Dinf.ι (Fin S.n)`, whence
`Fintype.card Dinf.ι = S.n`. -/
theorem card_inftyFibre_eq_sheetCount (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (hxs_inj : Function.Injective Dinf.xs)
    (hxs_range : Set.range Dinf.xs = f.toRiemannSphere ⁻¹' {OnePoint.infty})
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere OnePoint.infty) :
    Fintype.card Dinf.ι = S.n := by
  -- `Dinf.xs` and `S.sheet · ∞` both enumerate `F⁻¹{∞}` injectively; produce an index `Equiv`.
  obtain ⟨e, _⟩ := Jacobians.Dolbeault.FormTraceMovingFibre.equivOfInjective_image_eq hxs_inj
    (S.sheet_inj OnePoint.infty S.mem_V)
    (by rw [hxs_range, S.fibre_eq OnePoint.infty S.mem_V])
  rw [← Fintype.card_fin S.n]
  exact Fintype.card_congr e

/-- **The manifold sections enumerate the entire finite-value fibre.**  For `ζ ≠ 0` near `0`, the
injective manifold sections `fun k => inftyManifoldSec k (ζ⁻¹)` (`eventually_inftyManifoldSec_injective`)
have range `⊆ F⁻¹(coe ζ⁻¹)` (`eventually_inftyManifoldSec_mem_fibre`), and `#Dinf.ι = S.n =
#(F⁻¹(coe ζ⁻¹))` (`card_inftyFibre_eq_sheetCount`, `S.fibre_eq` + `S.sheet_inj` at `coe ζ⁻¹`), so the
range is *exactly* the fibre (an injective map into a finite set of equal cardinality is onto).  The
reciprocal-chart analogue of `sheetValues_range_eq_fibre`. -/
theorem eventually_inftyManifoldSec_range_eq_fibre (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Dinf : InftyFibreDataNF g f) (hxs_inj : Function.Injective Dinf.xs)
    (hxs_range : Set.range Dinf.xs = f.toRiemannSphere ⁻¹' {OnePoint.infty})
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere OnePoint.infty) :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      Set.range (fun k => inftyManifoldSec ω₀ f Dinf k (ζ⁻¹))
        = f.toRiemannSphere ⁻¹' {(((ζ⁻¹ : ℂ) : RiemannSphere))} := by
  classical
  have hcardD : Fintype.card Dinf.ι = S.n :=
    card_inftyFibre_eq_sheetCount f Dinf hxs_inj hxs_range S
  filter_upwards [nhdsWithin_le_nhds (eventually_inftyManifoldSec_injective ω₀ f Dinf hxs_inj),
    Filter.eventually_all.mpr (fun k => eventually_inftyManifoldSec_mem_fibre ω₀ f Dinf k),
    eventually_coe_inv_mem_V f S] with ζ hinj hmem hVζ
  -- The sheets `S.sheet · (coe ζ⁻¹)` injectively enumerate the fibre, so `#fibre = S.n`.
  set Fib := f.toRiemannSphere ⁻¹' {(((ζ⁻¹ : ℂ) : RiemannSphere))} with hFib
  have hsheetFib : Fib = Set.range (fun k => S.sheet k (((ζ⁻¹ : ℂ) : RiemannSphere))) :=
    S.fibre_eq _ hVζ
  -- `q := fun k => inftyManifoldSec k ζ⁻¹` is injective with range ⊆ Fib; corestrict to Fib.
  have hsub : Set.range (fun k => inftyManifoldSec ω₀ f Dinf k (ζ⁻¹)) ⊆ Fib := by
    rintro x ⟨k, rfl⟩; rw [hFib, Set.mem_preimage, Set.mem_singleton_iff]; exact hmem k
  -- Compare finite cardinalities: both have ncard `S.n`, range q ⊆ Fib ⟹ equal.
  have hFibFin : Fib.Finite := hsheetFib ▸ Set.finite_range _
  refine Set.eq_of_subset_of_ncard_le hsub ?_ hFibFin
  -- `#Fib ≤ #(range q)`: `#Fib = S.n` (sheet enumeration), `#(range q) = #Dinf.ι = S.n`.
  have hFibCard : Fib.ncard = S.n := by
    rw [hsheetFib, Set.ncard_range_of_injective (S.sheet_inj _ hVζ), Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hqCard : (Set.range (fun k => inftyManifoldSec ω₀ f Dinf k (ζ⁻¹))).ncard
      = Fintype.card Dinf.ι := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
  rw [hFibCard, hqCard, hcardD]

/-! ## Step (3a): the `∞`-moving sum as a fixed-chart moving fibre sum (reciprocal-chart bookkeeping)

The `∞`-moving sum `inftyMovingSumNF ω₀ f Dinf z = ∑ i, chartIntegrand ω₀ g (Dinf.xs i) (recipSheet i
(z⁻¹))·deriv (w ↦ recipSheet i (w⁻¹)) z` reads the reciprocal-chart planar sections `recipSheet i :=
(inftyFibreTraceNF ω₀ f Dinf).sheet i`.  Via the manifold sections `inftyManifoldSec i z =
(chart (Dinf.xs i)).symm (recipSheet i (z⁻¹))`, for `z` large (`z⁻¹` near `0`, so `recipSheet i (z⁻¹) ∈
chart (Dinf.xs i).target`) the chart cancels and `inftyMovingSumNF ω₀ f Dinf z` *equals the fixed-chart
moving fibre sum* along `inftyManifoldSec` — the RHS shape `traceCoeff_diagonal_eq_fixedSum` produces.
Pure reciprocal-chart bookkeeping (no monodromy). -/

/-- **The `∞`-moving sum equals the fixed-chart moving fibre sum** along `inftyManifoldSec`, at `z = ζ⁻¹`
(`ζ ≠ 0`), given the chart-target memberships: the per-`i` value membership `hmem`
(`recipSheet i ζ ∈ target`) for the value factor, and the eventual membership `hmemEv`
(`recipSheet i (w⁻¹) ∈ target` for `w` near `ζ⁻¹`) for the derivative factor.  Both come from
`eventually_recipSheet_mem_target` for `ζ` small enough.  *Proof.*  Termwise: the value factor's argument
`recipSheet i ζ = chart (Dinf.xs i)(inftyManifoldSec i (ζ⁻¹))` (chart∘symm cancellation at the target
point); the derivative factor's functions agree near `ζ⁻¹` (same cancellation), so equal derivatives. -/
theorem inftyMovingSumNF_eq_fixedSum (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) {ζ : ℂ} (_hζ : ζ ≠ 0)
    (hmem : ∀ i, (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target)
    (hmemEv : ∀ i, ∀ᶠ w in 𝓝 (ζ⁻¹),
      (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹) ∈ (chartAt ℂ (Dinf.xs i)).target) :
    inftyMovingSumNF ω₀ f Dinf (ζ⁻¹)
      = ∑ i, chartIntegrand ω₀ g (Dinf.xs i)
            ((chartAt ℂ (Dinf.xs i)) (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)))
          * deriv (fun w => (chartAt ℂ (Dinf.xs i)) (inftyManifoldSec ω₀ f Dinf i w)) (ζ⁻¹) := by
  show (∑ i, chartIntegrand ω₀ g (Dinf.xs i) ((inftyFibreTraceNF ω₀ f Dinf).sheet i ((ζ⁻¹)⁻¹))
        * deriv (fun w => (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹)) (ζ⁻¹)) = _
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inv_inv]
  congr 1
  · -- value factor: `recipSheet i ζ = chart (Dinf.xs i)(inftyManifoldSec i (ζ⁻¹))`.
    rw [show (chartAt ℂ (Dinf.xs i)) (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))
          = (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ from by
        unfold inftyManifoldSec; rw [inv_inv, (chartAt ℂ (Dinf.xs i)).right_inv (hmem i)]]
  · -- derivative factor: the two functions agree near `ζ⁻¹`.
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hmemEv i] with w hw
    show (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹)
      = (chartAt ℂ (Dinf.xs i)) (inftyManifoldSec ω₀ f Dinf i w)
    unfold inftyManifoldSec
    rw [(chartAt ℂ (Dinf.xs i)).right_inv hw]

/-! ## Step (3b): the `∞`-analogue of `traceCoeff_diagonal_eq_fixedSum` (bare fixed frame)

`traceCoeff_diagonal_eq_fixedSum` (`FormTraceMovingFibre`) proves the *finite* diagonal identity — the
re-selected fibre trace equals the fixed-chart moving fibre sum — but ties the fixed chart frame to a
`FibreRegularData` over a *finite* base value.  At `∞` the natural fixed frame is the **pole set**
`Dinf.xs` (mapping to `∞`, *not* a finite-value fibre), so we transcribe `traceCoeff_diagonal_eq_fixedSum`
with the chart frame supplied as a *bare* indexed family `xsD : ιD → X` (the proof never uses the analytic
fields of the reference `FibreRegularData` — only its `ι`/`xs` as the chart frame and the explicit
index-bijection + chart-membership hypotheses).  This is the §VIII.3 well-definedness lever
(`movingSummand_chartIndep`) read with the pole charts as the fixed frame. -/

/-- **Diagonal trace = fixed-(bare-)frame moving fibre sum.**  Generalization of
`traceCoeff_diagonal_eq_fixedSum` with the fixed chart frame a bare `xsD : ιD → X` (instead of a
`FibreRegularData`'s fibre points).  Verbatim transcription of the finite proof (which uses only the
frame's `ι`/`xs` and the explicit hypotheses — never the reference fibre's analytic fields).  The
re-selected fibre `D'` over `b'`, the index bijection `e : D'.ι ≃ ιD`, the section identification
(`hxs`/`hsheet_deriv`), and the chart membership/transitions (`hmem`/`htrans_diff`/`htrans_diff_inv`)
discharge the diagonal via `movingSummand_chartIndep`. -/
theorem traceCoeff_diagonal_eq_fixedFrame {ιD : Type} [Fintype ιD] (xsD : ιD → X)
    (sec : ιD → ℂ → X) {b' : ℂ}
    (D' : FibreRegularData g f b') (e : D'.ι ≃ ιD)
    (hxs : ∀ i', D'.xs i' = sec (e i') b')
    (hsheet_deriv : ∀ i', deriv ((fibreTrace ω₀ f D').sheet i') b'
      = deriv (fun z => (chartAt ℂ (sec (e i') b')) (sec (e i') z)) b')
    (hcont : ∀ i, ContinuousAt (sec i) b')
    (hsP_diff : ∀ i, DifferentiableAt ℂ (fun z => (chartAt ℂ (sec i b')) (sec i z)) b')
    (hmem : ∀ i, sec i b' ∈ (chartAt ℂ (xsD i)).source)
    (htrans_diff : ∀ i, DifferentiableAt ℂ
      (fun w => (chartAt ℂ (xsD i)) ((chartAt ℂ (sec i b')).symm w)) ((chartAt ℂ (sec i b')) (sec i b')))
    (htrans_diff_inv : ∀ i, DifferentiableAt ℂ
      (fun w => (chartAt ℂ (sec i b')) ((chartAt ℂ (xsD i)).symm w)) ((chartAt ℂ (xsD i)) (sec i b'))) :
    (fibreTrace ω₀ f D').traceCoeff b'
      = ∑ i, chartIntegrand ω₀ g (xsD i) ((chartAt ℂ (xsD i)) (sec i b'))
        * deriv (fun z => (chartAt ℂ (xsD i)) (sec i z)) b' := by
  have hdiagsum : (fibreTrace ω₀ f D').traceCoeff b'
      = ∑ i', chartIntegrand ω₀ g (D'.xs i') ((chartAt ℂ (D'.xs i')) (D'.xs i'))
        * deriv ((fibreTrace ω₀ f D').sheet i') b' := by
    show (∑ i', (fibreTrace ω₀ f D').coeff i' ((fibreTrace ω₀ f D').sheet i' b')
        * deriv ((fibreTrace ω₀ f D').sheet i') b') = _
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    rw [fibreTrace_coeff,
      show (fibreTrace ω₀ f D').sheet i' b' = (chartAt ℂ (D'.xs i')) (D'.xs i') from
        (fibreTrace ω₀ f D').sheet_base i']
  rw [hdiagsum]
  rw [← Equiv.sum_comp e (fun i => chartIntegrand ω₀ g (xsD i) ((chartAt ℂ (xsD i)) (sec i b'))
    * deriv (fun z => (chartAt ℂ (xsD i)) (sec i z)) b')]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  rw [hxs i', hsheet_deriv i']
  have hself_diff : DifferentiableAt ℂ
      (fun w => (chartAt ℂ (sec (e i') b')) ((chartAt ℂ (sec (e i') b')).symm w))
      ((chartAt ℂ (sec (e i') b')) (sec (e i') b')) := by
    have heqid : (fun w => (chartAt ℂ (sec (e i') b')) ((chartAt ℂ (sec (e i') b')).symm w))
        =ᶠ[𝓝 ((chartAt ℂ (sec (e i') b')) (sec (e i') b'))] id := by
      filter_upwards [(chartAt ℂ (sec (e i') b')).open_target.mem_nhds
        ((chartAt ℂ (sec (e i') b')).map_source (mem_chart_source ℂ (sec (e i') b')))] with w hw
      simp only [(chartAt ℂ (sec (e i') b')).right_inv hw, id_eq]
    exact (differentiableAt_id).congr_of_eventuallyEq heqid
  exact movingSummand_chartIndep ω₀ g (sec (e i')) (sec (e i') b') (xsD (e i')) (hcont (e i'))
    (hsP_diff (e i')) (mem_chart_source ℂ (sec (e i') b')) (hmem (e i')) hself_diff
    (htrans_diff (e i')) hself_diff (htrans_diff_inv (e i'))

/-- **`inftyManifoldSec i (ζ⁻¹)` lies in the pole's chart source.**  It is `(chart (Dinf.xs i)).symm
(recipSheet i ζ)` and `recipSheet i ζ ∈ chart (Dinf.xs i).target`, so its chart inverse lands in the
source (`PartialEquiv.map_target`). -/
theorem inftyManifoldSec_mem_source (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) {ζ : ℂ}
    (hmem : (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target) :
    inftyManifoldSec ω₀ f Dinf i (ζ⁻¹) ∈ (chartAt ℂ (Dinf.xs i)).source := by
  unfold inftyManifoldSec
  rw [inv_inv]
  exact (chartAt ℂ (Dinf.xs i)).map_target hmem

/-! ## Step (3c): the per-`ζ` diagonal `valueChartTrace (ζ⁻¹) = inftyMovingSumNF (ζ⁻¹)`

Combining the bare-frame diagonal (`traceCoeff_diagonal_eq_fixedFrame`, with the pole charts `Dinf.xs` as
the fixed frame and the manifold sections `inftyManifoldSec`) and the reciprocal-chart bookkeeping
(`inftyMovingSumNF_eq_fixedSum`), the per-`ζ` diagonal identity holds *given the index bijection + section
identification at `ζ`* (the genuine §VIII.3 `∞`-monodromy content — the reciprocal-chart analogue of the
finite `diagonal_of_pointwiseBijection`). -/

/-- **The per-`ζ` `∞`-diagonal.**  For `ζ ≠ 0` with the chart memberships (`hmem`/`hmemEv`), and the index
bijection `e : (Φ ζ⁻¹).ι ≃ Dinf.ι` matching the re-selected fibre `Φ ζ⁻¹` over the value `ζ⁻¹` to the
`∞`-fibre poles along the manifold sections `inftyManifoldSec` (`hxs`/`hsheet_deriv` + the chart
differentiability), the value trace equals the `∞`-moving sum at `ζ⁻¹`:

> `valueChartTrace ω₀ f Φ (ζ⁻¹) = inftyMovingSumNF ω₀ f Dinf (ζ⁻¹)`. -/
theorem diagonalInfty_pointwise (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (Dinf : InftyFibreDataNF g f)
    {ζ : ℂ} (hζ : ζ ≠ 0)
    (hmem : ∀ i, (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target)
    (hmemEv : ∀ i, ∀ᶠ w in 𝓝 (ζ⁻¹),
      (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹) ∈ (chartAt ℂ (Dinf.xs i)).target)
    (e : (Φ (ζ⁻¹)).ι ≃ Dinf.ι)
    (hxs : ∀ i', (Φ (ζ⁻¹)).xs i' = inftyManifoldSec ω₀ f Dinf (e i') (ζ⁻¹))
    (hsheet_deriv : ∀ i', deriv ((fibreTrace ω₀ f (Φ (ζ⁻¹))).sheet i') (ζ⁻¹)
      = deriv (fun z => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf (e i') (ζ⁻¹)))
          (inftyManifoldSec ω₀ f Dinf (e i') z)) (ζ⁻¹))
    (hcont : ∀ i, ContinuousAt (inftyManifoldSec ω₀ f Dinf i) (ζ⁻¹))
    (hsP_diff : ∀ i, DifferentiableAt ℂ (fun z => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)))
        (inftyManifoldSec ω₀ f Dinf i z)) (ζ⁻¹))
    (htrans_diff : ∀ i, DifferentiableAt ℂ
      (fun w => (chartAt ℂ (Dinf.xs i)) ((chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))).symm w))
        ((chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))) (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))))
    (htrans_diff_inv : ∀ i, DifferentiableAt ℂ
      (fun w => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))) ((chartAt ℂ (Dinf.xs i)).symm w))
        ((chartAt ℂ (Dinf.xs i)) (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)))) :
    valueChartTrace ω₀ f Φ (ζ⁻¹) = inftyMovingSumNF ω₀ f Dinf (ζ⁻¹) := by
  rw [valueChartTrace_apply,
    traceCoeff_diagonal_eq_fixedFrame (xsD := Dinf.xs) (sec := inftyManifoldSec ω₀ f Dinf)
      (D' := Φ (ζ⁻¹)) e hxs hsheet_deriv hcont hsP_diff
      (fun i => inftyManifoldSec_mem_source ω₀ f Dinf i (hmem i)) htrans_diff htrans_diff_inv,
    inftyMovingSumNF_eq_fixedSum ω₀ f Dinf hζ hmem hmemEv]

/-! ## Step (4): the `∞`-moving-coherence datum and the `hcoh_geom` assembly

We package the residual §VIII.3 `∞`-monodromy content — the *eventually-quantified index bijection +
section identification at `∞`* — into one structure `InftyMovingCoherenceData`, exactly mirroring the
finite `MovingCoherenceDatum.ofBijection`'s `hbij`.  Its single content field is, for `ζ` in a punctured
neighbourhood of `0` (large `z = ζ⁻¹`), an index bijection `e : (Φ ζ⁻¹).ι ≃ Dinf.ι` matching the
re-selected fibre `Φ ζ⁻¹` over `ζ⁻¹` to the `∞`-fibre poles along the manifold sections
`inftyManifoldSec`, plus the section identification (`hxs`/`hsheet_deriv`) and the chart-pullback
differentiability.  The chart-target memberships are discharged *internally* (from the analyticity of the
reciprocal sections near `0`, `eventually_recipSheet_analyticAt`, and `eventually_recipSheet_mem_target`),
so the caller supplies only the genuine monodromy.

From such a datum, `hcoh_geom` follows: the per-`ζ` diagonal (`diagonalInfty_pointwise`) gives
`valueChartTrace (ζ⁻¹) = inftyMovingSumNF (ζ⁻¹)` for `ζ` near `0`, and `hcoh_geom_of_diagonalInfty`
upgrades that large-`z` agreement to the reciprocal-chart germ-equality `hcoh_geom`. -/

/-- **A single-`i` `hmemEv` from continuity at `ζ`.**  Given the reciprocal section continuous at `ζ`
(`hcont`) with `recipSheet i ζ ∈ chart (Dinf.xs i).target` (`hmemζ`), the chart-target membership of
`recipSheet i (w⁻¹)` holds for `w` near `ζ⁻¹` (`w ↦ w⁻¹` continuous at `ζ⁻¹`, value `ζ`; openness of the
target). -/
theorem hmemEv_of_cont (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) {ζ : ℂ} (hζ : ζ ≠ 0)
    (hcont : ContinuousAt ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ)
    (hmemζ : (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target) :
    ∀ᶠ w in 𝓝 (ζ⁻¹), (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹) ∈ (chartAt ℂ (Dinf.xs i)).target := by
  have hinvcont : ContinuousAt (fun w : ℂ => w⁻¹) (ζ⁻¹) := continuousAt_inv₀ (inv_ne_zero hζ)
  have hcompcont : ContinuousAt (fun w => (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹)) (ζ⁻¹) := by
    have : (fun w : ℂ => (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹))
        = ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ∘ (fun w : ℂ => w⁻¹) := rfl
    rw [this]; refine ContinuousAt.comp ?_ hinvcont; rwa [inv_inv]
  refine hcompcont.eventually_mem ?_
  show (chartAt ℂ (Dinf.xs i)).target ∈ 𝓝 ((inftyFibreTraceNF ω₀ f Dinf).sheet i (ζ⁻¹)⁻¹)
  rw [inv_inv]
  exact (chartAt ℂ (Dinf.xs i)).open_target.mem_nhds hmemζ

/-- **The `∞`-moving-coherence datum** (the §VIII.3 `∞`-monodromy obligation, packaged).  For a global
fibre selection `Φ` and the `∞`-fibre data `Dinf`, the data exhibiting the value trace as the moving
`∞`-fibre sum near `∞`: an *eventually-quantified* (in `ζ` near `0`, i.e. large `z = ζ⁻¹`) index bijection
`e : (Φ ζ⁻¹).ι ≃ Dinf.ι` matching the re-selected fibre to the `∞`-fibre poles along the manifold sections
`inftyManifoldSec`, with the section identification and chart-pullback differentiability.  This is the
reciprocal-chart analogue of the finite `MovingCoherenceDatum.ofBijection` `hbij` field — the genuine
remaining `∞`-content (the continuously-varying index bijection at `∞`).  The chart-target memberships are
*not* fields (discharged internally from analyticity of the reciprocal sections near `0`). -/
structure InftyMovingCoherenceData (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) (Dinf : InftyFibreDataNF g f)
    where
  /-- **The eventually-quantified index bijection + section identification at `∞`.** -/
  hbij : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ∃ e : (Φ (ζ⁻¹)).ι ≃ Dinf.ι,
    (∀ i', (Φ (ζ⁻¹)).xs i' = inftyManifoldSec ω₀ f Dinf (e i') (ζ⁻¹)) ∧
    (∀ i', deriv ((fibreTrace ω₀ f (Φ (ζ⁻¹))).sheet i') (ζ⁻¹)
      = deriv (fun z => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf (e i') (ζ⁻¹)))
          (inftyManifoldSec ω₀ f Dinf (e i') z)) (ζ⁻¹)) ∧
    (∀ i, ContinuousAt (inftyManifoldSec ω₀ f Dinf i) (ζ⁻¹)) ∧
    (∀ i, DifferentiableAt ℂ (fun z => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)))
        (inftyManifoldSec ω₀ f Dinf i z)) (ζ⁻¹)) ∧
    (∀ i, DifferentiableAt ℂ
      (fun w => (chartAt ℂ (Dinf.xs i)) ((chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))).symm w))
        ((chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))) (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)))) ∧
    (∀ i, DifferentiableAt ℂ
      (fun w => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))) ((chartAt ℂ (Dinf.xs i)).symm w))
        ((chartAt ℂ (Dinf.xs i)) (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))))

/-- **`hcoh_geom` from an `∞`-moving-coherence datum.**  The per-`ζ` diagonal
(`diagonalInfty_pointwise`) holds for `ζ` near `0` (the datum's `hbij` + the internally-discharged chart
memberships), giving `valueChartTrace (ζ⁻¹) = inftyMovingSumNF (ζ⁻¹)` eventually; `hcoh_geom_of_diagonalInfty`
upgrades it to the reciprocal-chart germ-equality `hcoh_geom`.  This is the assembled §VIII.3
`∞`-single-valuedness — the reciprocal-chart analogue of `MovingCoherenceDatum.coherent`. -/
theorem hcoh_geom_of_inftyMovingCoherenceData (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (Dinf : InftyFibreDataNF g f)
    (C : InftyMovingCoherenceData ω₀ g f Φ Dinf) :
    recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf) := by
  classical
  refine hcoh_geom_of_diagonalInfty ω₀ f Φ Dinf ?_
  -- The chart-target memberships (eventually near `0`): analyticity + target membership of the
  -- reciprocal sections, both eventual near `0`.
  have hmemAll : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      ∀ i, AnalyticAt ℂ ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ
        ∧ (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target := by
    rw [Filter.eventually_all]
    intro i
    exact nhdsWithin_le_nhds
      ((eventually_recipSheet_analyticAt ω₀ f Dinf i).and (eventually_recipSheet_mem_target ω₀ f Dinf i))
  filter_upwards [C.hbij, hmemAll, self_mem_nhdsWithin] with ζ hbij hmemAll hζ0
  have hζ : ζ ≠ 0 := by simpa using hζ0
  obtain ⟨e, hxs, hsheet_deriv, hcont, hsP_diff, htrans_diff, htrans_diff_inv⟩ := hbij
  -- Discharge the per-`i` memberships from `hmemAll`.
  have hmem : ∀ i, (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target :=
    fun i => (hmemAll i).2
  have hmemEv : ∀ i, ∀ᶠ w in 𝓝 (ζ⁻¹),
      (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹) ∈ (chartAt ℂ (Dinf.xs i)).target :=
    fun i => hmemEv_of_cont ω₀ f Dinf i hζ (hmemAll i).1.continuousAt (hmemAll i).2
  exact diagonalInfty_pointwise ω₀ f Φ Dinf hζ hmem hmemEv e hxs hsheet_deriv hcont hsP_diff
    htrans_diff htrans_diff_inv

/-! ## Step (4'): constructing the `∞`-moving-coherence datum from the `∞`-sheet system

The reciprocal-chart analogue of the *finite* `MovingCoherenceDatum.ofSphereSheetSystemCanon`: the
`InftyMovingCoherenceData` is built from the `∞`-sheet system `S` (`exists_inftySheetSystem`), with the
*only* `Φ`-input the **canonical-fibre condition** (near `∞`, `(Φ ζ⁻¹).xs` injectively enumerates the
fibre `F⁻¹(coe ζ⁻¹)`).  The index bijection `e` is reconstructed *pointwise* from set-equality
(`equivOfInjective_image_eq`: both `(Φ ζ⁻¹).xs` and `inftyManifoldSec · (ζ⁻¹)` enumerate the same fibre,
the latter via `eventually_inftyManifoldSec_range_eq_fibre` — the `S`-supplied degree count); all
differentiability fields are discharged by the *same* finite helpers used in
`MovingCoherenceDatum.ofSheetSections` (`differentiableAt_chart_pullback_section`,
`transition_differentiableAt_overlap`, `fibreTrace_sheet_eventuallyEq` via `chartPullback_section_rinv`),
read on the manifold sections `inftyManifoldSec`.  No labeling, no monodromy — the symmetric lever at
`∞`. -/

/-- **The `∞`-moving-coherence datum from the `∞`-sheet system + canonical fibre.**  The reciprocal-chart
analogue of `MovingCoherenceDatum.ofSphereSheetSystemCanon`.  From the `∞`-sheet system `S`
(`exists_inftySheetSystem`) — supplying the degree count `#Dinf.ι = S.n = #(F⁻¹(coe ζ⁻¹))` so the
manifold sections sweep the whole fibre — the `∞`-pole enumeration data (`hxs_inj`/`hxs_range`), and the
**canonical-fibre condition** `hΦinj`/`hΦrange` (near `∞`, `(Φ ζ⁻¹).xs` injectively enumerates
`F⁻¹(coe ζ⁻¹)`), the `InftyMovingCoherenceData`.  The genuine §VIII.3 `∞`-content (the
continuously-varying index bijection) is the pointwise set-equality of `(Φ ζ⁻¹).xs` and
`inftyManifoldSec · (ζ⁻¹)` (both enumerate the fibre), reconstructed by the symmetric lever
`equivOfInjective_image_eq`; the differentiability rides on the finite section helpers. -/
noncomputable def InftyMovingCoherenceData.ofInftySheetSystem
    (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (Dinf : InftyFibreDataNF g f)
    (hxs_inj : Function.Injective Dinf.xs)
    (hxs_range : Set.range Dinf.xs = f.toRiemannSphere ⁻¹' {OnePoint.infty})
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere OnePoint.infty)
    (hΦinj : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), Function.Injective (Φ (ζ⁻¹)).xs)
    (hΦrange : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      Set.range (Φ (ζ⁻¹)).xs = f.toRiemannSphere ⁻¹' {(((ζ⁻¹ : ℂ) : RiemannSphere))}) :
    InftyMovingCoherenceData ω₀ g f Φ Dinf where
  hbij := by
    classical
    -- The manifold sections are smooth, lie in the chart sources, are sections of `f.holoRepr` on a
    -- neighbourhood, are injective, and enumerate the fibre — all eventual near `0`.
    have hsmoothEv : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ∀ i,
        ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (inftyManifoldSec ω₀ f Dinf i) (ζ⁻¹) := by
      rw [eventually_all]
      intro i
      filter_upwards [nhdsWithin_le_nhds (eventually_recipSheet_analyticAt ω₀ f Dinf i),
        nhdsWithin_le_nhds (eventually_recipSheet_mem_target ω₀ f Dinf i), self_mem_nhdsWithin]
        with ζ hana hmem hζ0
      exact inftyManifoldSec_contMDiffAt ω₀ f Dinf i (by simpa using hζ0) hana hmem
    have hmemSrcEv : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ∀ i,
        inftyManifoldSec ω₀ f Dinf i (ζ⁻¹) ∈ (chartAt ℂ (Dinf.xs i)).source := by
      rw [eventually_all]
      intro i
      filter_upwards [nhdsWithin_le_nhds (eventually_recipSheet_mem_target ω₀ f Dinf i)] with ζ hmem
      exact inftyManifoldSec_mem_source ω₀ f Dinf i hmem
    have hsecEv : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ∀ i, ∀ᶠ w in 𝓝 (ζ⁻¹),
        f.holoRepr (inftyManifoldSec ω₀ f Dinf i w) = w :=
      eventually_all.mpr (fun i => eventually_holoRepr_inftyManifoldSec_nhds ω₀ f Dinf i)
    -- Combine with the canonical-fibre conditions, the section injectivity, and the fibre enumeration.
    filter_upwards [hΦinj, hΦrange, eventually_inftyManifoldSec_range_eq_fibre ω₀ f Dinf hxs_inj
      hxs_range S, nhdsWithin_le_nhds (eventually_inftyManifoldSec_injective ω₀ f Dinf hxs_inj),
      hsmoothEv, hmemSrcEv, hsecEv]
      with ζ hΦinjζ hΦrangeζ hsecRange hsecInj hsmooth hmemSrc hsec
    -- The symmetric lever: a value-matching index bijection from set-equality of the two fibre
    -- enumerations `(Φ ζ⁻¹).xs` and `inftyManifoldSec · (ζ⁻¹)` (both equal `F⁻¹(coe ζ⁻¹)`).
    obtain ⟨e, he⟩ := Jacobians.Dolbeault.FormTraceMovingFibre.equivOfInjective_image_eq hΦinjζ
      hsecInj (by rw [hΦrangeζ, ← hsecRange])
    refine ⟨e, he, ?_, fun i => (hsmooth i).continuousAt,
      fun i => differentiableAt_chart_pullback_section (hsmooth i), ?_, ?_⟩
    · -- **The section-derivative match** (`hsheet_deriv`).  Mirror of the finite `ofSheetSections`:
      -- the planar sheet of `fibreTrace ω₀ f (Φ ζ⁻¹)` germ-equals the chart-pullback of
      -- `inftyManifoldSec (e i')`, so their derivatives at `ζ⁻¹` agree.
      intro i'
      obtain ⟨_, hrinv_cont, hrinv_rinv⟩ :=
        chartPullback_section_rinv f (sec := inftyManifoldSec ω₀ f Dinf (e i')) (b₀ := ζ⁻¹)
          (x := inftyManifoldSec ω₀ f Dinf (e i') (ζ⁻¹)) rfl
          (hsmooth (e i')).continuousAt (hsec (e i'))
      have hsheet := Jacobians.Dolbeault.FormTraceSheet.fibreTrace_sheet_eventuallyEq ω₀ f (Φ (ζ⁻¹)) i'
        (s := fun z => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf (e i') (ζ⁻¹)))
          (inftyManifoldSec ω₀ f Dinf (e i') z))
        (by rw [he i']) hrinv_cont (by rw [he i']; exact hrinv_rinv)
      exact hsheet.deriv_eq
    · -- chart transition `chart_{Dinf.xs i} ∘ chart_{inftyManifoldSec i ζ⁻¹}.symm` differentiable.
      intro i
      exact transition_differentiableAt_overlap (mem_chart_source ℂ _) (hmemSrc i)
    · -- chart transition `chart_{inftyManifoldSec i ζ⁻¹} ∘ chart_{Dinf.xs i}.symm` differentiable.
      intro i
      exact transition_differentiableAt_overlap (hmemSrc i) (mem_chart_source ℂ _)

/-! ## Step (5): wiring the `∞`-coherence datum into the kirovGenus-`0` capstone

Replacing the bare `∞`-coherence hypothesis `hcoh_geom` of
`residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg` by an
`InftyMovingCoherenceData` (at `Φ := canonicalFibreSelection`, `Dinf := inftyFibreDataNF_full`), the deep
`∞`-coherence is now reduced — *soundly* — to the genuine §VIII.3 `∞`-monodromy datum (the
continuously-varying index bijection at `∞`), the reciprocal-chart analogue of the finite `Cfull` datum.
This is the most-reduced kirovGenus-`0` Gate A capstone: every analytic heart is now a *geometric datum* (the
finite `Cfull`/`hreg` discharged by the symmetric lever; the `∞`-coherence reduced to its monodromy
datum), with only `hbnd` and the discrete genericity bookkeeping remaining as named obligations. -/

/-- **Gate A `∑Res = 0` (kirovGenus `0`, simple `∞`-poles, canonical selection) with the `∞`-coherence reduced
to its moving-coherence datum.**  Identical to `residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg`
except the bare `∞`-coherence `hcoh_geom` is replaced by an `InftyMovingCoherenceData` `Cinf` (at the
canonical selection and the full `∞`-fibre data) — the §VIII.3 `∞`-monodromy obligation (the
continuously-varying index bijection at `∞`).  `hcoh_geom` is recovered internally by
`hcoh_geom_of_inftyMovingCoherenceData`.  This is the reciprocal-chart analogue of discharging the finite
`Cfull` from `movingCoherenceDatum_canonical`: the deep `∞`-coherence is now a geometric datum, not an
opaque germ-hypothesis. -/
theorem residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyData
    (hdiv : (f.div : Divisor X) ≠ 0)
    (hgood : ∀ p, (∃ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      GoodValue g f hdiv p)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ) (hbr : branchValues f hdiv ⊆ br)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hoff_cs : ∀ i, (((cs i : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hc_good : ∀ i, GoodValue g f hdiv (cs i))
    (hgmero : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∀ j,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an_offpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x))
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i)))
    (hnonpole_inf_an : ∀ k, inftyFibreEnum f k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (inftyFibreEnum f k)).symm z))
        ((chartAt ℂ (inftyFibreEnum f k)) (inftyFibreEnum f k)))
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z)
        (𝓝[≠] b₀) (𝓝 0))
    (Cinf : InftyMovingCoherenceData ω₀ g f (canonicalFibreSelection g f hdiv)
      (inftyFibreDataNF_full g f hsimpleInf hmeroInf)) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg hdiv hgood m cs ρ hcs_ball hcs_inj
    br hbr hcenters_cs hoff_cs hc_good hgmero hgood_reg hgmero_reg hg_an_offpoles hsimpleInf hmeroInf
    hnonpole_inf_an hbnd
    (hcoh_geom_of_inftyMovingCoherenceData ω₀ f (canonicalFibreSelection g f hdiv)
      (inftyFibreDataNF_full g f hsimpleInf hmeroInf) Cinf)

/-! ### The canonical-fibre conditions at `∞` (the only `Φ`-input the `∞`-engine needs)

The reciprocal-chart analogues of `canonicalFibreSelection_hΦinjReg` / `hΦrangeReg`: near `∞` (i.e. `ζ`
near `0`, `ζ⁻¹` a large finite value), the canonical selection enumerates the full fibre `F⁻¹(coe ζ⁻¹)`.
A large value `ζ⁻¹` is *off* the finite exceptional set `image cs ∪ br` (`ζ⁻¹ → ∞` leaves any bounded
set), so it is a **good value** (`hgood_reg`), where the canonical selection is the full-fibre datum.
These supply the `hΦinj`/`hΦrange` of `InftyMovingCoherenceData.ofInftySheetSystem`. -/

/-- **A large finite value `ζ⁻¹` avoids any finite exceptional set.**  `ζ⁻¹ → ∞` (cobounded) as `ζ → 0`
within `≠ 0`, and a finite `Finset ℂ` is bounded, so `ζ⁻¹ ∉ s` for `ζ` near `0`. -/
theorem eventually_inv_notMem_finset (s : Finset ℂ) :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ζ⁻¹ ∉ s := by
  have hmem : (↑s : Set ℂ)ᶜ ∈ Bornology.cobounded ℂ :=
    Bornology.isBounded_def.mp s.finite_toSet.isBounded
  have h := Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ)
  filter_upwards [h.eventually_mem hmem] with ζ hζ
  simpa using hζ

/-- **`hΦrange` at `∞` for the canonical selection.**  For `ζ` near `0`, `ζ⁻¹ ∉ image cs ∪ br`
(`eventually_inv_notMem_finset`), so `ζ⁻¹` is a good value (`hgood_reg`), where the canonical selection's
fibre points enumerate the full fibre `F⁻¹(coe ζ⁻¹)` (`canonicalFibreSelection_xs_range`). -/
theorem canonicalFibreSelection_hΦrange_infty (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (cs : Finset ℂ) (br : Finset ℂ)
    (hgood_reg : ∀ w ∉ cs ∪ br, GoodValue g f hdiv w) :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      Set.range (canonicalFibreSelection g f hdiv (ζ⁻¹)).xs
        = f.toRiemannSphere ⁻¹' {(((ζ⁻¹ : ℂ) : RiemannSphere))} := by
  filter_upwards [eventually_inv_notMem_finset (cs ∪ br)] with ζ hζ
  exact canonicalFibreSelection_xs_range g f hdiv (hgood_reg (ζ⁻¹) hζ)

/-- **`hΦinj` at `∞` for the canonical selection.**  Same good-value neighbourhood: for `ζ` near `0`,
`ζ⁻¹` is a good value, where the canonical selection's fibre points are injective
(`canonicalFibreSelection_xs_injective`). -/
theorem canonicalFibreSelection_hΦinj_infty (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (cs : Finset ℂ) (br : Finset ℂ)
    (hgood_reg : ∀ w ∉ cs ∪ br, GoodValue g f hdiv w) :
    ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), Function.Injective (canonicalFibreSelection g f hdiv (ζ⁻¹)).xs := by
  filter_upwards [eventually_inv_notMem_finset (cs ∪ br)] with ζ hζ
  exact canonicalFibreSelection_xs_injective g f hdiv (hgood_reg (ζ⁻¹) hζ)

/-- **`range (inftyFibreEnum f) = F⁻¹{∞}`.**  `inftyFibreEnum` enumerates exactly the poles of `f`
(`inftyFibreEnum_mem` / `inftyFibreEnum_surj`), which is the fibre `F⁻¹{∞}`. -/
theorem inftyFibreEnum_range (f : MeromorphicFunction X) :
    Set.range (inftyFibreEnum f) = f.toRiemannSphere ⁻¹' {OnePoint.infty} := by
  ext x
  simp only [Set.mem_range, Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ inftyFibreEnum_mem f i, fun hx => inftyFibreEnum_surj f hx⟩

/-- **Gate A `∑Res = 0` (kirovGenus `0`, simple `∞`-poles, canonical selection) — `∞`-coherence FULLY
CLOSED.**  Identical hypotheses to `residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg`, with
the bare `∞`-coherence `hcoh_geom` **constructed internally** from the `∞`-sheet system
(`exists_inftySheetSystem`, gated by the simple `∞`-poles `hsimpleInf`) via
`InftyMovingCoherenceData.ofInftySheetSystem` — the reciprocal-chart analogue of discharging the finite
`Cfull` from `movingCoherenceDatum_canonical`.  The §VIII.3 `∞`-single-valuedness is now a *theorem*: the
canonical-fibre conditions near `∞` (`canonicalFibreSelection_hΦinj_infty` / `hΦrange_infty`, from
`hgood_reg`) feed the symmetric lever, the degree count rides on the `∞`-sheet system, and the
differentiability on the finite section helpers.  **Gate A `∑Res = 0` now rests on only `hbnd` (the
branch-value boundedness) + the discrete genericity bookkeeping** — no `∞`-coherence hypothesis. -/
theorem residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyClosed
    (hdiv : (f.div : Divisor X) ≠ 0)
    (hgood : ∀ p, (∃ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      GoodValue g f hdiv p)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ) (hbr : branchValues f hdiv ⊆ br)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hoff_cs : ∀ i, (((cs i : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hc_good : ∀ i, GoodValue g f hdiv (cs i))
    (hgmero : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∀ j,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an_offpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x))
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i)))
    (hnonpole_inf_an : ∀ k, inftyFibreEnum f k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (inftyFibreEnum f k)).symm z))
        ((chartAt ℂ (inftyFibreEnum f k)) (inftyFibreEnum f k)))
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z)
        (𝓝[≠] b₀) (𝓝 0)) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyData hdiv hgood m cs ρ hcs_ball
    hcs_inj br hbr hcenters_cs hoff_cs hc_good hgmero hgood_reg hgmero_reg hg_an_offpoles hsimpleInf
    hmeroInf hnonpole_inf_an hbnd
    (InftyMovingCoherenceData.ofInftySheetSystem ω₀ f (canonicalFibreSelection g f hdiv)
      (inftyFibreDataNF_full g f hsimpleInf hmeroInf)
      (by rw [inftyFibreDataNF_full_xs]; exact inftyFibreEnum_injective f)
      (by rw [inftyFibreDataNF_full_xs]; exact inftyFibreEnum_range f)
      (exists_inftySheetSystem f hdiv hsimpleInf).some
      (canonicalFibreSelection_hΦinj_infty g f hdiv (Finset.univ.image cs) br hgood_reg)
      (canonicalFibreSelection_hΦrange_infty g f hdiv (Finset.univ.image cs) br hgood_reg))

end Jacobians.Dolbeault.SerreResidueTheorem
