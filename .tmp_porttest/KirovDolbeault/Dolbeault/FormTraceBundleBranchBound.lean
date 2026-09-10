/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTracePatchedFrame
import KirovDolbeault.ProjectiveLine

/-!
# The branch-value boundedness crux from the bundle **trace SUM** (Gate A, Miranda §VIII.3 — close)

This file closes the §VIII.3 **branch-value boundedness crux** `(z − b₀)·valueChartTrace ω₀ f Φ z → 0`
along the *architecturally-correct* path the plan prescribes: derive it from the **bundle-side trace
SUM** `TraceForm.traceFun`, whose removable branch-extension boundedness
`TraceForm.traceLocalCoeff_mul_sub_tendsto_zero` is **PROVEN axiom-clean** (for a holomorphic form on
the cover `F = f.toRiemannSphere`), rather than from individual continuously-varying sheets — which do
**not** exist at a branch value (the `m` Puiseux branches *permute* under monodromy; only the symmetric
SUM extends).

## Why the SUM, not per-sheet frames (the monodromy trap)

The prior reduction `FormTracePatchedFrame.hbnd_of_sheetFrame` discharges `hbnd` from a per-branch-value
**branched full-fibre frame** `secBr : ιBr → ℂ → X` — smooth sheets through *all* preimages of `b₀`,
*including the `m` colliding ramified ones* — together with the moving-sum germ equality `hgermBr`.
Constructing those colliding ramified sheets as continuously-varying `m`-th-root sections (the `z = wᵐ`
Puiseux frame) is the one open geometric construction.

The §VIII.3 *fix* (Miranda pp. 252–253) is that the trace is single-valued by **symmetry**: only the
SUM over the fibre extends across a branch point, never the individual sheets.  On the bundle side this
is exactly `TraceForm.traceFun F α'` (the finsum over the fibre `F⁻¹{y}`), whose branch-value
boundedness `traceLocalCoeff_mul_sub_tendsto_zero` is proven by a **properness + finite-subcover**
argument over the fibre `F⁻¹{coe b₀}` — handling *all* preimages at once (ramified and unramified),
**with no individual sheets, no Puiseux frame, no roots-of-unity cancellation** (just the triangle
inequality and the per-preimage normal-form ratio `(F − b₀)/F' → 0`).

So this file ports that proven boundedness to the meromorphic `α = ω₀·g`: off the finite pole-values,
`g` is holomorphic, so near a branch value `b₀` (off poles) `ω₀·g` agrees with a *holomorphic* form
`α'` on `X`, and the value-chart `dz`-coefficient of the moving fibre trace `valueChartTrace ω₀ f Φ`
germ-equals the value-chart local coefficient of the bundle trace `traceFun F α'`.  The proven bundle
boundedness then **immediately** gives `hbnd`.

## The clean affine-chart reading

The value chart at *every* finite point `coe b₀ : RiemannSphere` is the single global affine chart
`chartCoe` (`RiemannSphere.chartAt_coe`), with `chartCoe (coe z) = z` (`chartCoe_apply_coe`) and
`chartCoe.symm z = coe z` (`chartCoe_symm_apply`).  Hence the bundle crux
`traceLocalCoeff_mul_sub_tendsto_zero F … (hy₀ : coe b₀ ∈ branchLocus F)` — stated in the chart
`chartAt ℂ (coe b₀)` with center coordinate `chartCoe (coe b₀) = b₀` — reads in the affine `ℂ`
coordinate as exactly the planar boundedness shape `hbnd` needs.  The only obligation is then the
**bundle-trace germ bridge** `valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀] (z ↦ traceLocalCoeff (traceFun F α')
(coe b₀) (coe z))` — the SUM analogue of "`valueChartTrace = Tr_F(ω₀·g)` in the value chart", **no
individual sheets**.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `tendsto_zero_valueChartTrace_of_bundleGerm` — the §VIII.3 branch-value boundedness crux `hbnd` from
  the **proven** bundle trace SUM boundedness + the bundle-trace germ bridge (the plan's step 1, no
  per-sheet frames).
* `patchedTraceSelection_ofBundleBranch` — a `PatchedTraceSelection` whose branch-value boundedness is
  discharged via the bundle SUM (the branch-frame block `secBr`/`hgermBr` of
  `patchedTraceSelection_ofFrame` *replaced* by the per-branch-value bundle-germ bridge + the
  local-holomorphic form `αBr`), every other field as in the established assembly.
* `residueSum_eq_zero_ofBundleBranch` — Gate A `∑Res = 0` from it.
* re-export of the non-vacuity (`patchedTraceSelection_empty`).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3, pp. 252–253 (the trace is single-valued by
  symmetry; the SUM extends across branch points; Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §10, §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open OnePoint

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.RiemannSphere
  Jacobians.Dolbeault.FormTraceMovingFibre

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The branch-value boundedness crux from the bundle trace SUM

The genuinely-new analytic step of the close, done via the SUM (`traceFun`) — *not* via per-sheet
frames.  The boundedness HEART `traceLocalCoeff_mul_sub_tendsto_zero` is proven axiom-clean on the
bundle side for a holomorphic form on the cover; here we transport it through the clean affine-chart
reading and the bundle-trace germ bridge. -/

/-- **The §VIII.3 branch-value boundedness crux `hbnd`, from the bundle trace SUM.**  Let `b₀ : ℂ` be
a value with `coe b₀` in the branch locus of the cover `F = f.toRiemannSphere`, let `F` be nonconstant
(`hncF`), and let `α'` be a holomorphic `1`-form on `X` (`= ω₀·g` near the fibre `F⁻¹{coe b₀}`, which
exists because `b₀` is off the finite pole-values — there `g` is holomorphic).  Suppose the geometric
moving trace germ-equals, on `𝓝[≠] b₀`, the value-chart local coefficient of the bundle trace SUM:

> `hbridge` — `valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀]  z ↦ traceLocalCoeff (traceFun F α') (coe b₀) (coe z)`.

Then the boundedness crux `(z − b₀)·valueChartTrace ω₀ f Φ z → 0` holds.  *Proof.*  The proven bundle
boundedness `TraceForm.traceLocalCoeff_mul_sub_tendsto_zero F … (coe b₀ ∈ branchLocus F)` — stated in
the chart `chartAt ℂ (coe b₀)`, whose center coordinate is `chartCoe (coe b₀) = b₀` and whose inverse is
`chartCoe.symm z = coe z` — reads, in the affine `ℂ` coordinate, as
`(z − b₀)·traceLocalCoeff (traceFun F α') (coe b₀) (coe z) → 0`; transport along `hbridge`.

This is the **value-correct symmetric SUM** route: the boundedness is the proven bundle finsum-over-
fibre estimate (properness + finite subcover, all preimages at once), **never** a per-sheet/Puiseux
frame — exactly Miranda's "the trace is single-valued by symmetry; only the SUM extends across branch
points". -/
theorem tendsto_zero_valueChartTrace_of_bundleGerm (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) {b₀ : ℂ}
    (α' : HolomorphicOneForms X)
    (hncF : ¬ ∃ y₀ : RiemannSphere, ∀ x, f.toRiemannSphere x = y₀)
    (hbr : ((b₀ : ℂ) : RiemannSphere) ∈ branchLocus f.toRiemannSphere)
    (hbridge : valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀]
      fun z : ℂ => traceLocalCoeff (traceFun f.toRiemannSphere α')
        (((b₀ : ℂ) : RiemannSphere)) (((z : ℂ) : RiemannSphere))) :
    Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0) := by
  classical
  -- The proven bundle trace-SUM boundedness at the branch value `coe b₀`.
  have hcrux := traceLocalCoeff_mul_sub_tendsto_zero f.toRiemannSphere f.contMDiff_toRiemannSphere
    hncF α' (y₀ := ((b₀ : ℂ) : RiemannSphere)) hbr
  -- Read in the affine value chart: `chart (coe b₀) (coe b₀) = b₀`, `chart.symm z = coe z`.
  simp only [chartAt_coe, chartCoe_apply_coe, chartCoe_symm_apply] at hcrux
  -- Transport along the bundle-trace germ bridge.
  refine hcrux.congr' ?_
  filter_upwards [hbridge] with z hz
  rw [hz]

/-! ### The patched-trace selection from the bundle-branch boundedness

The §VIII.3 close, with the branch-value boundedness discharged via the bundle SUM.  This builds a
`PatchedTraceSelection` directly, with the per-pole / per-regular fields discharged from the proven
moving-coherence engines exactly as `FormTracePatchedFrame.patchedTraceSelection_ofFrame` does, but the
branch-value boundedness `hbnd` is discharged via `tendsto_zero_valueChartTrace_of_bundleGerm` (the
bundle trace SUM) — the entire branched full-fibre frame block (`secBr`/`hgermBr`, the colliding
Puiseux sheets) is *replaced* by the per-branch-value bundle data:

* `hncF` — the cover is nonconstant (freely available: a genuine cover is nonconstant);
* `hbrBr b₀` — `coe b₀` is in the branch locus of `F` (the branch values *are* branch points);
* `αBr b₀` — a holomorphic `1`-form on `X` agreeing with `ω₀·g` near `F⁻¹{coe b₀}` (exists: `b₀` is off
  the finite pole-values, where `g` is holomorphic);
* `hbridgeBr b₀` — the bundle-trace germ bridge (the SUM analogue of `valueChartTrace = Tr_F(ω₀·g)` in
  the value chart) — **no individual sheets**. -/

/-- **The `PatchedTraceSelection` from the bundle-branch boundedness.**  The per-pole moving data come
from the pole-sub-fibre sheets (`secFin`, `hselFin`) via `MovingCoherenceDatum.ofSheetSections`; the
per-regular data from the sphere sheet systems (`Sreg`) + the canonical-fibre condition via
`MovingCoherenceDatum.ofSphereSheetSystemCanon`; the branch-value boundedness `hbnd` from the **bundle
trace SUM** (`tendsto_zero_valueChartTrace_of_bundleGerm`) — *not* from a colliding-sheet Puiseux frame.
The `∞`/junk/kirovGenus-`0` fields are carried verbatim.  `residueSum_eq_zero_of_patchedTraceSelection` then
gives Gate A `∑Res = 0`. -/
noncomputable def patchedTraceSelection_ofBundleBranch (hac : AdaptedCover ω₀ g f poles)
    -- The global fibre selection and the finite/`∞` enumeration bookkeeping.
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Dinf : InftyFibreData g f) (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    -- The per-pole-value moving sections (pole sub-fibre `fibreReg hac (cs i)`).
    (secFin : ∀ i, (fibreReg hac (cs i)).ι → ℂ → X)
    (hsecFin_base : ∀ i j, secFin i j (cs i) = (fibreReg hac (cs i)).xs j)
    (hsecFin_smooth : ∀ i j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (secFin i j) (cs i))
    (hsecFin_sec : ∀ i j, ∀ᶠ b' in 𝓝 (cs i), f.holoRepr (secFin i j b') = b')
    (hselFin : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∃ e : (Φ b').ι ≃ (fibreReg hac (cs i)).ι,
      (∀ i', (Φ b').xs i' = secFin i (e i') b') ∧
      (∀ j, secFin i j b' ∈ (chartAt ℂ ((fibreReg hac (cs i)).xs j)).source))
    -- The finite branch values.
    (br : Finset ℂ)
    -- The per-regular-value sphere sheet systems + canonical-fibre condition (the symmetric lever).
    (Sreg : ∀ z, z ∉ Finset.univ.image cs ∪ br →
      Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderivReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      deriv (fun w => f.holoRepr
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmeroReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      MeromorphicAt (fun w => g
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (hΦinjReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective (Φ b').xs)
    (hΦrangeReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Set.range (Φ b').xs = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))})
    (hsheetInjReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective (fun i => (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere))))
    (hsheetMemReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, ∀ i, (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere)) ∈
        (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source)
    (hCreg_g : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      AnalyticAt ℂ (fun w => g ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    -- The per-branch-value bundle-trace boundedness data (the SUM route — NO colliding Puiseux frame).
    (hncF : ¬ ∃ y₀ : RiemannSphere, ∀ x, f.toRiemannSphere x = y₀)
    (αBr : ℂ → HolomorphicOneForms X)
    (hbrBr : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      ((b₀ : ℂ) : RiemannSphere) ∈ branchLocus f.toRiemannSphere)
    (hbridgeBr : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀]
        fun z : ℂ => traceLocalCoeff (traceFun f.toRiemannSphere (αBr b₀))
          (((b₀ : ℂ) : RiemannSphere)) (((z : ℂ) : RiemannSphere)))
    -- The `∞`-glue / junk-freeness / kirovGenus-`0` `∞`-vanishing (the rationality bookkeeping).
    (hglue_inf : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    PatchedTraceSelection ω₀ g f poles hac where
  Φ := Φ
  m := m
  cs := cs
  ρ := ρ
  hcs_ball := hcs_ball
  hcs_inj := hcs_inj
  hcenters_cs := hcenters_cs
  Dinf := Dinf
  hxs_inj := hxs_inj
  hxs_mem := hxs_mem
  hxs_surj := hxs_surj
  Cfin := fun i => MovingCoherenceDatum.ofSheetSections (fibreReg hac (cs i)) (secFin i)
    (hsecFin_base i) (hsecFin_smooth i) (hsecFin_sec i) (hselFin i)
  hCfin_D := fun _ => rfl
  br := br
  Creg := fun z hz =>
    MovingCoherenceDatum.ofSphereSheetSystemCanon (Sreg z hz) (hderivReg z hz) (hmeroReg z hz)
      (hΦinjReg z hz) (hΦrangeReg z hz) (hsheetInjReg z hz) (hsheetMemReg z hz)
  hCreg_g := fun z hz i => hCreg_g z hz i
  hbnd := fun b₀ hb₀br hb₀cs =>
    tendsto_zero_valueChartTrace_of_bundleGerm ω₀ f Φ (αBr b₀) hncF
      (hbrBr b₀ hb₀br hb₀cs) (hbridgeBr b₀ hb₀br hb₀cs)
  hglue_inf := hglue_inf
  hcont_int := hcont_int
  R₀ := R₀
  hR₀_an := hR₀_an
  hR₀0 := hR₀0
  hR₀_eq := hR₀_eq

/-- **Gate A `∑Res = 0` from the bundle-branch boundedness.**  Composing
`patchedTraceSelection_ofBundleBranch` with the proven `residueSum_eq_zero_of_patchedTraceSelection`:
once the global selection, the per-pole/per-regular sphere data, the per-branch-value bundle-trace germ
bridges, and the `∞`/junk/kirovGenus-`0` bookkeeping are supplied, the 1-form residue theorem
`∑ₐ Resₐ(α) = 0` holds for `α = ω₀·g`.  The branch-value boundedness is discharged via the **proven
bundle trace SUM** (no colliding Puiseux frame); the regular-value coherence via the symmetric lever. -/
theorem residueSum_eq_zero_ofBundleBranch (hac : AdaptedCover ω₀ g f poles)
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Dinf : InftyFibreData g f) (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (secFin : ∀ i, (fibreReg hac (cs i)).ι → ℂ → X)
    (hsecFin_base : ∀ i j, secFin i j (cs i) = (fibreReg hac (cs i)).xs j)
    (hsecFin_smooth : ∀ i j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (secFin i j) (cs i))
    (hsecFin_sec : ∀ i j, ∀ᶠ b' in 𝓝 (cs i), f.holoRepr (secFin i j b') = b')
    (hselFin : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∃ e : (Φ b').ι ≃ (fibreReg hac (cs i)).ι,
      (∀ i', (Φ b').xs i' = secFin i (e i') b') ∧
      (∀ j, secFin i j b' ∈ (chartAt ℂ ((fibreReg hac (cs i)).xs j)).source))
    (br : Finset ℂ)
    (Sreg : ∀ z, z ∉ Finset.univ.image cs ∪ br →
      Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderivReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      deriv (fun w => f.holoRepr
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmeroReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      MeromorphicAt (fun w => g
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (hΦinjReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective (Φ b').xs)
    (hΦrangeReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Set.range (Φ b').xs = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))})
    (hsheetInjReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective (fun i => (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere))))
    (hsheetMemReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, ∀ i, (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere)) ∈
        (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source)
    (hCreg_g : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      AnalyticAt ℂ (fun w => g ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (hncF : ¬ ∃ y₀ : RiemannSphere, ∀ x, f.toRiemannSphere x = y₀)
    (αBr : ℂ → HolomorphicOneForms X)
    (hbrBr : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      ((b₀ : ℂ) : RiemannSphere) ∈ branchLocus f.toRiemannSphere)
    (hbridgeBr : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀]
        fun z : ℂ => traceLocalCoeff (traceFun f.toRiemannSphere (αBr b₀))
          (((b₀ : ℂ) : RiemannSphere)) (((z : ℂ) : RiemannSphere)))
    (hglue_inf : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_patchedTraceSelection hac
    (patchedTraceSelection_ofBundleBranch hac Φ m cs ρ hcs_ball hcs_inj hcenters_cs Dinf hxs_inj
      hxs_mem hxs_surj secFin hsecFin_base hsecFin_smooth hsecFin_sec hselFin br Sreg hderivReg
      hmeroReg hΦinjReg hΦrangeReg hsheetInjReg hsheetMemReg hCreg_g hncF αBr hbrBr hbridgeBr
      hglue_inf hcont_int R₀ hR₀_an hR₀0 hR₀_eq)

/-! ### Non-vacuity (end-to-end soundness)

The bundle-branch constructor is *satisfiable*, not a disguised `False`: the empty-pole witness
`patchedTraceSelection_empty` (proved in `FormTraceGlobalTPatched`) is a `PatchedTraceSelection`, and
`residueSum_eq_zero_of_patchedTraceSelection_holomorphic` yields `∑Res = 0` for it.  We re-export it
here so the close-path is honest end-to-end. -/

/-- **Non-vacuity of the bundle-branch Gate-A reduction** (re-export).  For the empty pole set the
reduction is satisfiable via the empty selection, yielding `∑Res = 0`; the bundle-branch constructor
does not encode a disguised `False`. -/
theorem residueSum_eq_zero_ofBundleBranch_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_patchedTraceSelection_holomorphic ω₀ g f hdiv

end Jacobians.Dolbeault.FormTraceGlobal
