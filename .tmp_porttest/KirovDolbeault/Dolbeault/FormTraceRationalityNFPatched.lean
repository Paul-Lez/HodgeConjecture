/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceFullFibreRationalityNF
import KirovDolbeault.Dolbeault.FormTraceCoherenceFromMoving
import KirovDolbeault.Dolbeault.FormTraceGlobalTPatched
import KirovDolbeault.Dolbeault.FormTraceBundleBranchBound
import KirovDolbeault.Dolbeault.FormTraceBundleBridge

/-!
# Gate A `∑Res = 0` from the **branch-patched** geometric trace, *sound* `∞` fibre (Miranda §VIII.3)

`Jacobians.Dolbeault.FormTraceFullFibre.traceRationalityDataNF_ofMovingData`
(`FormTraceCoherenceFromMovingNF`) builds the sound full-fibre reduction target `TraceRationalityDataNF`
from a global selection `Φ`, per-pole moving data, and — as *caller hypotheses* — the kirovGenus-`0`
remainder vanishing `hentire`/`hrecip_cont` against the **raw** trace `valueChartTrace ω₀ f Φ`.

That `hentire` (`AnalyticOnNhd ℂ (valueChartTrace ω₀ f Φ - L.R) Set.univ`) is, however, a
**latent false hypothesis for the canonical full-fibre selection**: at a *branch value* of the cover the
raw geometric trace `valueChartTrace` takes a *partial-sum* value, **not** the removable-singularity
limit (`FormTraceGlobalTPatched`, the docstring explicitly flags `BranchAwareTraceSelection.hbranch` —
continuity of the raw trace at a branch value — as **false**).  So the raw trace is *discontinuous*
across branch points and cannot be entire.

This file is the **value-correct** analogue.  It assembles `TraceRationalityDataNF` with the geometric
trace replaced by the **branch-patched** trace

> `T := valueChartTracePatched ω₀ f Φ br`,

which equals `valueChartTrace` off the finite branch values `br` and the removable-singularity limit at
each of them — the *planar shadow* of the proven bundle trace `traceFun` extension
(`TraceForm.traceExtendsAt_branchPoint`, axiom-clean).  With this `T`:

* the kirovGenus-`0` `hentire` is **proven internally** (not assumed) via the off-centre analyticity
  `analyticAt_valueChartTracePatched_off_centres` (regular values by the moving coherence; branch values
  by the value-correct removable extension `tendsto_zero_valueChartTrace_of_bundleGerm`/the boundedness
  crux) + the junk-freeness `hcont_int`, through `analyticOnNhd_remainder_of_junkFree'`;
* `hrecip_cont` is `continuousAt_recipCoeff_of_vanishing` (the kirovGenus-`0` `R₀ 0 = 0` `∞`-vanishing);
* `agree` (finite) uses `valueChartTracePatched =ᶠ[𝓝[≠] p] valueChartTrace` (the patch is inert off the
  branch values) chained with the per-pole moving coherence `hcoh_fin_of_movingDatum`;
* `agree_infty` uses `recipCoeff (valueChartTracePatched) =ᶠ[𝓝[≠] 0] recipCoeff (valueChartTrace)`
  (`recipCoeff_valueChartTracePatched_eventuallyEq`) chained with the **sound** `∞`-coherence `hcoh_inf`
  against `inftyFibreTraceNF` (the repaired reciprocal — `FormTraceInftyFibreNF`).

So this constructor removes the `hentire`/`hrecip_cont` *false-field risk* of the raw route, replacing
them by the genuinely-satisfiable boundedness-crux/junk-free inputs, and keeps the sound `∞`-fibre.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `traceRationalityDataNF_ofPatched` — a sound `TraceRationalityDataNF` from a global selection `Φ`, the
  branch set `br`, the off-centre analyticity inputs (`hreg` regular-value analyticity + `hbnd`
  branch-value boundedness), per-pole moving data, junk-freeness `hcont_int`, the kirovGenus-`0`
  `∞`-vanishing `R₀`, and the **sound** `∞`-fibre data + coherence;
* `residueSum_eq_zero_of_patchedTraceRationalityNF` — Gate A `∑Res = 0` from it;
* `traceRationalityDataNF_ofPatched_holomorphic` — end-to-end non-vacuity (empty-pole), confirming the
  reduction is honest (not a disguised `False`).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (the trace `Tr`, Lemma 3.2; the
  trace is single-valued and meromorphic on `ℂℙ¹`, extending across branch points; the residue at `∞`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceFullFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormResidueTheorem
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTraceLiouville
  Jacobians.Dolbeault.FormTraceMovingFibre

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### Meromorphy of the patched trace at the finite centres

The patched trace germ-equals the raw trace on every punctured neighbourhood
(`valueChartTracePatched_eventuallyEq`); the raw trace is meromorphic at each pole-value via the moving
datum (`meromorphicAt_valueChartTrace_of_movingDatum`).  Hence the patched trace is too — the input the
principal-part extraction consumes. -/

/-- **Meromorphy of the patched trace at a centre.**  At a finite pole-value `p` with a moving datum
`C` whose fixed fibre is `D p`, the branch-patched trace `valueChartTracePatched ω₀ f Φ br` is
`MeromorphicAt p`: it germ-equals the raw trace off `p` (`valueChartTracePatched_eventuallyEq`), which
is meromorphic at `p` (`meromorphicAt_valueChartTrace_of_movingDatum`). -/
theorem meromorphicAt_valueChartTracePatched_of_movingDatum
    {Φ : (b : ℂ) → FibreRegularData g f b} {D : (p : ℂ) → FibreRegularData g f p} {p : ℂ}
    (br : Finset ℂ) (C : MovingCoherenceDatum ω₀ g f Φ p) (hCD : C.D = D p) :
    MeromorphicAt (valueChartTracePatched ω₀ f Φ br) p :=
  (meromorphicAt_valueChartTrace_of_movingDatum C hCD).congr
    (valueChartTracePatched_eventuallyEq ω₀ f Φ br p).symm

/-! ### The off-centre analyticity of the patched trace (`hT_off`)

Mirrors `PatchedTraceSelection.hT_off`: regular values via the moving coherence (`hreg`), branch values
via the value-correct removable extension (`hbnd` boundedness + punctured analyticity from `hreg`).  The
punctured-analyticity input of the branch-value engine is supplied from `hreg`
(`eventually_analyticAt_valueChartTrace_of_reg`), so the only branch-specific datum is `hbnd`. -/

/-- **Off-centre analyticity of the patched trace.**  With `centres := Finset.univ.image cs`: given the
regular-value analyticity of the *raw* trace off `centres ∪ br` (`hreg`) and the branch-value
boundedness crux off `centres` (`hbnd`), the **patched** trace is analytic at every value off
`centres`.  This is the value-correct `hT_off` — branch values handled by the removable extension, *no*
false continuity demand.  (`analyticAt_valueChartTracePatched_off_centres`, with the punctured
analyticity fed from `hreg`.) -/
theorem hT_off_patched {Φ : (b : ℂ) → FibreRegularData g f b} {m : ℕ} {cs : Fin m → ℂ} {br : Finset ℂ}
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    {z : ℂ} (hz : z ∉ Finset.univ.image cs) :
    AnalyticAt ℂ (valueChartTracePatched ω₀ f Φ br) z :=
  analyticAt_valueChartTracePatched_off_centres ω₀ f Φ (Finset.univ.image cs) br hreg
    (fun b₀ hb₀br hb₀cs =>
      ⟨eventually_analyticAt_valueChartTrace_of_reg ω₀ f Φ (Finset.univ.image cs) br hreg b₀,
        hbnd b₀ hb₀br hb₀cs⟩)
    hz

/-! ### The sound `TraceRationalityDataNF` from the patched trace

We assemble `TraceRationalityDataNF` with `T := valueChartTracePatched ω₀ f Φ br`.  The internal
`LaurentForm L` is `T`'s finite principal parts; the kirovGenus-`0` Liouville agreement `T = L.R` is proven
from the *internally-discharged* `hentire` (`analyticOnNhd_remainder_of_junkFree'` from `hT_off_patched`
+ the junk-freeness `hcont_int`) and `hrecip_cont` (`continuousAt_recipCoeff_of_vanishing` from the
kirovGenus-`0` `∞`-vanishing `R₀`).  Then `agree`/`agree_infty` follow from `T = L.R` + the per-pole moving
coherence / the sound `∞`-coherence. -/

/-- **A sound `TraceRationalityDataNF` from the branch-patched geometric trace.**  With
`T := valueChartTracePatched ω₀ f Φ br`:

* `hreg` / `hbnd` — the off-centre analyticity inputs (regular-value analyticity of the *raw* trace off
  `centres ∪ br`; the branch-value boundedness crux off `centres`).  These give the value-correct
  `hT_off` (`hT_off_patched`) — the genuinely-satisfiable replacement of the false raw-trace continuity;
* `Cfin` / `hCfin_D` — the per-pole-value moving coherence data (fixed fibre `D (cs i)`), giving both
  the meromorphy at the centres and the finite coherence;
* `hcont_int` — junk-freeness (`T − L.R` continuous at each centre), giving `hentire` via
  `analyticOnNhd_remainder_of_junkFree'`;
* `R₀` (`hR₀_an`/`hR₀0`/`hR₀_eq`) — the kirovGenus-`0` `∞`-vanishing, giving `hrecip_cont` via
  `continuousAt_recipCoeff_of_vanishing`;
* `Dinf` (sound `InftyFibreDataNF`) + `hcoh_inf` — the sound `∞`-fibre data and coherence against
  `inftyFibreTraceNF`.

Producing one ⇒ Gate A `∑Res = 0` (sound `∞`-fibre, value-correct trace). -/
noncomputable def traceRationalityDataNF_ofPatched
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    (D : (p : ℂ) → FibreRegularData g f p)
    (Cfin : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (hCfin_D : ∀ i, (Cfin i).D = D (cs i))
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (D p).xs i = a)
    (Dinf : InftyFibreDataNF g f) (hxsInf_inj : Function.Injective Dinf.xs)
    (hxsInf_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hcoh_inf : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f Dinf).traceCoeff)
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    TraceRationalityDataNF ω₀ g f poles := by
  classical
  -- The branch-patched geometric trace and its meromorphy at the centres.
  set T := valueChartTracePatched ω₀ f Φ br with hT
  have hT_mero : ∀ i, MeromorphicAt T (cs i) := fun i =>
    meromorphicAt_valueChartTracePatched_of_movingDatum br (Cfin i) (hCfin_D i)
  -- Finite principal-part `LaurentForm`.
  set hPP := exists_laurentForm_principalPart cs ρ hcs_ball hcs_inj hT_mero with hPP_def
  set L := hPP.choose with hL_def
  have hLcenters : Finset.univ.image L.a = Finset.univ.image cs := hPP.choose_spec.1
  have hLrem : ∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧ (T - L.R) =ᶠ[𝓝[≠] (cs j)] R :=
    hPP.choose_spec.2
  -- `hentire`: the off-centre analyticity (value-correct `hT_off`) + junk-freeness, packaged by
  -- `analyticOnNhd_remainder_of_junkFree'`.
  have hT_off : ∀ z ∉ Finset.univ.image L.a, AnalyticAt ℂ T z := by
    intro z hz
    rw [hLcenters] at hz
    exact hT_off_patched hreg hbnd hz
  have hrem : ∀ p ∈ Finset.univ.image L.a, ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧ (T - L.R) =ᶠ[𝓝[≠] p] R := by
    intro p hp
    rw [hLcenters] at hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    exact hLrem i
  have hcont : ∀ p ∈ Finset.univ.image L.a, ContinuousAt (T - L.R) p :=
    hcont_int L hLcenters hLrem
  have hentire : AnalyticOnNhd ℂ (T - L.R) Set.univ :=
    analyticOnNhd_remainder_of_junkFree' hT_off hrem hcont
  -- `hrecip_cont`: the kirovGenus-`0` `∞`-vanishing.
  have hrecip : ContinuousAt (recipCoeff (T - L.R)) 0 :=
    continuousAt_recipCoeff_of_vanishing hR₀_an hR₀0 (hR₀_eq L hLcenters)
  -- The Liouville agreement `T = L.R`.
  have hTL : T = L.R :=
    coeff_eq_of_entire_diff_of_recipCoeff_continuousAt hentire hrecip
  refine
    { L := L
      D := D
      hxs_inj := hxs_inj
      hxs_mem := hxs_mem
      hxs_surj := hxs_surj
      Dinf := Dinf
      hxsInf_inj := hxsInf_inj
      hxsInf_mem := hxsInf_mem
      hxsInf_surj := hxsInf_surj
      hcenters := by rw [hLcenters]; exact hcenters_cs
      agree := ?_
      agree_infty := ?_ }
  · -- finite agreement: `L.R = T`, and `T =ᶠ[𝓝[≠] cs i] (fibreTrace …).traceCoeff` (patched germ-equals
    -- raw off branches, then moving coherence).
    intro p hp
    rw [hLcenters] at hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    rw [← hTL]
    -- `T =ᶠ[𝓝[≠] cs i] valueChartTrace =ᶠ[𝓝[≠] cs i] (fibreTrace …).traceCoeff`.
    refine (valueChartTracePatched_eventuallyEq ω₀ f Φ br (cs i)).trans ?_
    exact (hcoh_fin_of_movingDatum (Cfin i) (hCfin_D i)).filter_mono nhdsWithin_le_nhds
  · -- `∞` agreement: `recipCoeff L.R = recipCoeff T`, and the sound `∞`-coherence.
    rw [← hTL]
    exact hcoh_inf

/-- **Gate A `∑Res = 0` from the branch-patched geometric trace (sound `∞`).**  The sound
`TraceRationalityDataNF` route closed via `residueSum_eq_zero_of_traceRationalityDataNF`. -/
theorem residueSum_eq_zero_of_patchedTraceRationalityNF
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    (D : (p : ℂ) → FibreRegularData g f p)
    (Cfin : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (hCfin_D : ∀ i, (Cfin i).D = D (cs i))
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (D p).xs i = a)
    (Dinf : InftyFibreDataNF g f) (hxsInf_inj : Function.Injective Dinf.xs)
    (hxsInf_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hcoh_inf : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f Dinf).traceCoeff)
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_traceRationalityDataNF ω₀ g f poles
    (traceRationalityDataNF_ofPatched Φ m cs ρ hcs_ball hcs_inj br hreg hbnd D Cfin hCfin_D
      hxs_inj hxs_mem hxs_surj Dinf hxsInf_inj hxsInf_mem hxsInf_surj hcenters_cs hcoh_inf
      hcont_int R₀ hR₀_an hR₀0 hR₀_eq)

/-! ### Discharging the off-centre analyticity inputs (`hreg` / `hbnd`)

The two off-centre analyticity inputs of `traceRationalityDataNF_ofPatched` reduce, via *proven*
atoms, to the standard regular-value geometry — *no* Puiseux frame:

* `hreg` (regular-value analyticity) is `analyticAt_valueChartTrace_of_movingDatum` (the symmetric-lever
  moving coherence + `g`-analyticity at the fibre);
* `hbnd` (branch-value boundedness `(z − b₀)·valueChartTrace z → 0`) is the **bundle trace SUM**
  boundedness `tendsto_zero_valueChartTrace_of_bundleGerm` (resting on the axiom-clean
  `TraceForm.traceLocalCoeff_mul_sub_tendsto_zero`), with the bundle-trace germ bridge `hbridgeBr`
  discharged from the eventual sphere-sheet coherence `hbridgeBr_of_eventual_sphereCoherence` — Miranda's
  "the SUM extends across branch points", never an individual colliding sheet.

This is the `T := traceFun` discharge of the kirovGenus-`0` analyticity content: the planar trace inherits
analyticity across branch points from the proven bundle trace `traceFun` extension. -/

/-- **`hbnd` (branch-value boundedness) from the eventual sphere coherence + a local form `αBr`.**  At a
branch value `b₀` (in the branch locus of the cover, `hbr`; `f` nonconstant, `hncF`) with a holomorphic
local representative `αBr` of `α = ω₀·g` near the fibre, the boundedness crux
`(z − b₀)·valueChartTrace ω₀ f Φ z → 0` holds, *provided* the eventual sphere-sheet coherence `hev`
(the value-correct symmetric-SUM identification: near `b₀` each regular value carries a sphere sheet
system whose planar fibre trace equals the geometric trace, and `αBr = ω₀·g` at the fibre).

The bundle-trace germ bridge is `hbridgeBr_of_eventual_sphereCoherence`; the boundedness is the proven
bundle SUM `tendsto_zero_valueChartTrace_of_bundleGerm` (axiom-clean
`TraceForm.traceLocalCoeff_mul_sub_tendsto_zero`). -/
theorem hbnd_of_eventual_sphereCoherence (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) {b₀ : ℂ}
    (αBr : HolomorphicOneForms X)
    (hncF : ¬ ∃ y₀ : RiemannSphere, ∀ x, f.toRiemannSphere x = y₀)
    (hbr : ((b₀ : ℂ) : RiemannSphere) ∈ branchLocus f.toRiemannSphere)
    (hev : ∀ᶠ z in 𝓝[≠] b₀,
      ∃ (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
        (hderiv : ∀ i, deriv (fun w => f.holoRepr
            ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
          ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
            (S.sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
        (_hmero : ∀ i, MeromorphicAt
          (fun w => g ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
          ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
            (S.sheet i (((z : ℂ) : RiemannSphere))))),
        valueChartTrace ω₀ f Φ z
            = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv _hmero)).traceCoeff z ∧
        (∀ i, αBr.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))
          = g (S.sheet i (((z : ℂ) : RiemannSphere))) • ω₀.toFun (S.sheet i (((z : ℂ) : RiemannSphere))))) :
    Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0) :=
  Jacobians.Dolbeault.FormTraceGlobal.tendsto_zero_valueChartTrace_of_bundleGerm ω₀ f Φ αBr hncF hbr
    (Jacobians.Dolbeault.FormTraceGlobal.hbridgeBr_of_eventual_sphereCoherence ω₀ αBr g f Φ hev)

/-- **`hreg` (regular-value analyticity) from a moving coherence datum.**  At a regular value `z` with a
moving coherence datum `C` whose fixed fibre `C.D` has `g`'s chart-pullback analytic at each fibre point
(`hg`), the geometric trace `valueChartTrace ω₀ f Φ` is analytic at `z` (the symmetric-lever coherence
`MovingCoherenceDatum.coherent` + `analyticAt_valueChartTrace_of_eventuallyEq`).  Re-export of
`FormTraceMovingFibre.analyticAt_valueChartTrace_of_movingDatum`. -/
theorem hreg_of_movingDatum {Φ : (b : ℂ) → FibreRegularData g f b} {z : ℂ}
    (C : MovingCoherenceDatum ω₀ g f Φ z)
    (hg : ∀ i, AnalyticAt ℂ (fun w => g ((chartAt ℂ (C.D.xs i)).symm w))
      ((chartAt ℂ (C.D.xs i)) (C.D.xs i))) :
    AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z :=
  Jacobians.Dolbeault.FormTraceMovingFibre.analyticAt_valueChartTrace_of_movingDatum C hg

/-! ### The sound `∞`-moving reparametrization bridge (the `hcoh_inf` engine, repaired reciprocal)

The sound `∞`-coherence `hcoh_inf` is `recipCoeff (valueChartTracePatched) =ᶠ[𝓝[≠] 0]
(inftyFibreTraceNF ω₀ f Dinf).traceCoeff` (against the *repaired* `∞`-fibre trace, `FormTraceInftyFibreNF`).
As in the finite case, the `∞`-fibre trace coefficient is the `recipCoeff` of a *finite* `∞`-moving sum
read in the reciprocal chart — the `−ζ⁻²` Jacobian of `z = 1/ζ` cancels the moving-sum reparametrization
(Miranda's "the SUM extends across `∞`").  We mirror the proven `recipCoeff_inftyMovingSum_eq_traceCoeff`
verbatim, but with the **sound** `inftyFibreTraceNF` sheets (the genuinely-analytic repaired reciprocal),
so the resulting bridge feeds the sound `agree_infty`/`hcoh_inf` *without* the buggy `InftyFibreData`.

The proof is structure-driven (only the `FibreTrace` interface + `inftyFibreTraceNF_b`/`_coeff`), so it
is a clean transcription. -/

/-- **The finite `∞`-moving sum along the *repaired* reciprocal sheets** of an `InftyFibreDataNF`: the
value-coordinate fibre sum `∑ i, chartIntegrand ω₀ g (Dinf.xs i) (sheet i (b'⁻¹)) · deriv (b' ↦ sheet i
(b'⁻¹)) b'`, read at the finite value `b'`, with `sheet := (inftyFibreTraceNF ω₀ f Dinf).sheet` (the
planar inverses of the genuinely-analytic repaired reciprocal).  The sound `∞`-analogue of
`inftyMovingSum`. -/
noncomputable def inftyMovingSumNF (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) : ℂ → ℂ :=
  fun b' => ∑ i, chartIntegrand ω₀ g (Dinf.xs i) ((inftyFibreTraceNF ω₀ f Dinf).sheet i (b'⁻¹))
    * deriv (fun w => (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹)) b'

/-- **The sound reparametrization identity (the `dζ` Jacobian cancellation, repaired reciprocal).**
`recipCoeff (inftyMovingSumNF ω₀ f Dinf)` equals the sound `∞`-fibre trace coefficient
`(inftyFibreTraceNF ω₀ f Dinf).traceCoeff` on a punctured neighbourhood of `0`.  Verbatim transcription
of `recipCoeff_inftyMovingSum_eq_traceCoeff` with the `inftyFibreTraceNF` sheets (the genuinely-analytic
repaired reciprocal — `sheet_analytic`, `inftyFibreTraceNF_b = 0`, `inftyFibreTraceNF_coeff =
chartIntegrand` all hold identically). -/
theorem recipCoeff_inftyMovingSumNF_eq_traceCoeff (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Dinf : InftyFibreDataNF g f) :
    recipCoeff (inftyMovingSumNF ω₀ f Dinf) =ᶠ[𝓝[≠] 0]
      (inftyFibreTraceNF ω₀ f Dinf).traceCoeff := by
  classical
  -- Each repaired reciprocal-chart sheet is differentiable on a punctured neighbourhood of `0`.
  have hdiff : ∀ i : Dinf.ι, ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      DifferentiableAt ℂ ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ := by
    intro i
    have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ := by
      have han := ((inftyFibreTraceNF ω₀ f Dinf).sheet_analytic i).eventually_analyticAt
      rw [inftyFibreTraceNF_b] at han
      filter_upwards [han] with ζ hζ using hζ.differentiableAt
    exact nhdsWithin_le_nhds hev
  have hall : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      (∀ i : Dinf.ι, DifferentiableAt ℂ ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ) ∧ ζ ≠ 0 := by
    rw [Filter.eventually_and]
    refine ⟨?_, ?_⟩
    · rw [eventually_all]; exact hdiff
    · filter_upwards [self_mem_nhdsWithin] with ζ hζ; simpa using hζ
  filter_upwards [hall] with ζ ⟨hdζ, hζne⟩
  show -(inftyMovingSumNF ω₀ f Dinf (ζ⁻¹)) * ζ ^ (-2 : ℤ)
    = ∑ i, (inftyFibreTraceNF ω₀ f Dinf).coeff i ((inftyFibreTraceNF ω₀ f Dinf).sheet i ζ)
        * deriv ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ
  rw [inftyMovingSumNF]
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hchain : deriv (fun w => (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹)) (ζ⁻¹)
      = deriv ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ * (-((ζ⁻¹ ^ 2)⁻¹)) := by
    rw [show (fun w => (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹))
        = (inftyFibreTraceNF ω₀ f Dinf).sheet i ∘ (fun w : ℂ => w⁻¹) from rfl]
    rw [deriv_comp (ζ⁻¹) (by rw [inv_inv]; exact hdζ i) (differentiableAt_inv (by simpa using hζne)),
      deriv_inv, inv_inv]
  rw [inv_inv, hchain, inftyFibreTraceNF_coeff]
  set c := chartIntegrand ω₀ g (Dinf.xs i) ((inftyFibreTraceNF ω₀ f Dinf).sheet i ζ) with hc
  set d := deriv ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ with hd
  rw [zpow_neg, zpow_two]
  field_simp

/-- **The sound `∞`-coherence `hcoh_inf` from the `∞`-moving coherence (repaired reciprocal).**  If the
reciprocal coefficient of the patched trace germ-equals the `recipCoeff` of the sound `∞`-moving sum off
`0` (`hcoh` — the §VIII.3 `∞`-single-valuedness, the `∞`-analogue of the finite moving coherence), then it
germ-equals the sound `∞`-fibre trace coefficient:

> `recipCoeff (valueChartTracePatched ω₀ f Φ br) =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f Dinf).traceCoeff`.

This is the exact `hcoh_inf` input of `traceRationalityDataNF_ofPatched`, reduced to the single genuine
`∞`-moving residual `hcoh` (chained through the proven reparametrization
`recipCoeff_inftyMovingSumNF_eq_traceCoeff`). -/
theorem hcoh_inf_of_inftyMovingCoherenceNF (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) (br : Finset ℂ)
    (Dinf : InftyFibreDataNF g f)
    (hcoh : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf)) :
    recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f Dinf).traceCoeff :=
  hcoh.trans (recipCoeff_inftyMovingSumNF_eq_traceCoeff ω₀ f Dinf)

/-! ### The top-level sound geometric assembly (Gate A on the precise residuals)

Wiring all the discharge helpers, this reduces Gate A `∑Res = 0` — *soundly* (sound `∞`-fibre,
value-correct branch-patched trace) and axiom-clean — to a precise list of **genuine §VIII.3
geometric residuals**, with `f` a nonconstant cover (`hncF`):

* `Φ`, `cs`/`ρ`, `D`/`hxs_*`, `hcenters_cs`, the enumeration bookkeeping — the global selection + discrete
  fibre data (wall 2 bookkeeping);
* `Creg z` (off `cs ∪ br`) + `hCreg_g` — the per-regular-value moving coherence (symmetric lever, giving
  `hreg`);
* `br`, `hbr`, `αBr`, `hevBr` — the finite branch values, their branch-locus membership, a local
  holomorphic representative of `α = ω₀·g`, and the eventual sphere-sheet coherence (giving `hbnd` via the
  proven bundle SUM);
* `xsInf`/`hsimpleInf` (simple `∞`-poles) — the sound `∞`-fibre data `InftyFibreDataNF.ofRegular`;
* `hcoh` — the `∞`-moving coherence (the `∞`-single-valuedness; giving `hcoh_inf`);
* `hcont_int`, `R₀`/`hR₀_*` — junk-freeness + the kirovGenus-`0` `∞`-vanishing.

This is the sound replacement of the *raw*-trace route: `hentire` is **proven** (not assumed), the
`∞`-fibre is the sound `InftyFibreDataNF`, and the kirovGenus-`0` analyticity rides on the proven bundle trace
`traceFun` extension (`TraceForm.traceExtendsAt_branchPoint`, axiom-clean). -/
theorem residueSum_eq_zero_of_patchedGeometry
    (hncF : ¬ ∃ y₀ : RiemannSphere, ∀ x, f.toRiemannSphere x = y₀)
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (Creg : ∀ z, z ∉ Finset.univ.image cs ∪ br → MovingCoherenceDatum ω₀ g f Φ z)
    (hCreg_g : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      AnalyticAt ℂ (fun w => g ((chartAt ℂ ((Creg z hz).D.xs i)).symm w))
        ((chartAt ℂ ((Creg z hz).D.xs i)) ((Creg z hz).D.xs i)))
    (αBr : ℂ → HolomorphicOneForms X)
    (hbr : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      ((b₀ : ℂ) : RiemannSphere) ∈ branchLocus f.toRiemannSphere)
    (hevBr : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      ∀ᶠ z in 𝓝[≠] b₀,
        ∃ (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
          (hderiv : ∀ i, deriv (fun w => f.holoRepr
              ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
            ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
              (S.sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
          (_hmero : ∀ i, MeromorphicAt
            (fun w => g ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
            ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
              (S.sheet i (((z : ℂ) : RiemannSphere))))),
          valueChartTrace ω₀ f Φ z
              = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv _hmero)).traceCoeff z ∧
          (∀ i, (αBr b₀).toFun (S.sheet i (((z : ℂ) : RiemannSphere)))
            = g (S.sheet i (((z : ℂ) : RiemannSphere)))
              • ω₀.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))))
    (D : (p : ℂ) → FibreRegularData g f p)
    (Cfin : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (hCfin_D : ∀ i, (Cfin i).D = D (cs i))
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (D p).xs i = a)
    {ιInf : Type} [Fintype ιInf] (xsInf : ιInf → X)
    (hsimpleInf : ∀ i, f.orderAtPoint (xsInf i) = -1)
    (hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (xsInf i)).symm z))
      ((chartAt ℂ (xsInf i)) (xsInf i)))
    (hxsInf_inj : Function.Injective xsInf)
    (hxsInf_mem : ∀ i, xsInf i ∈ poles ∧ f.toRiemannSphere (xsInf i) = OnePoint.infty)
    (hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, xsInf i = a)
    (hcoh : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0]
        recipCoeff (inftyMovingSumNF ω₀ f (InftyFibreDataNF.ofRegular g f xsInf hsimpleInf hmeroInf)))
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_patchedTraceRationalityNF Φ m cs ρ hcs_ball hcs_inj br
    (fun w hw => hreg_of_movingDatum (Creg w hw) (hCreg_g w hw))
    (fun b₀ hb₀br hb₀cs =>
      hbnd_of_eventual_sphereCoherence ω₀ g f Φ (αBr b₀) hncF (hbr b₀ hb₀br hb₀cs)
        (hevBr b₀ hb₀br hb₀cs))
    D Cfin hCfin_D hxs_inj hxs_mem hxs_surj
    (InftyFibreDataNF.ofRegular g f xsInf hsimpleInf hmeroInf) hxsInf_inj hxsInf_mem hxsInf_surj
    hcenters_cs
    (hcoh_inf_of_inftyMovingCoherenceNF ω₀ g f Φ br _ hcoh)
    hcont_int R₀ hR₀_an hR₀0 hR₀_eq

/-! ### Non-vacuity (end-to-end soundness)

For the empty pole set the empty fibre selection assembles into a `TraceRationalityDataNF` through the
patched constructor: no finite pole-values (the per-pole moving data vacuous), no branch values (`br = ∅`,
so the patch is inert and the raw/patched traces coincide and are the zero function), the empty sound
`∞`-fibre, the zero trace, and the trivially-true kirovGenus-`0`/`∞` fields.  Confirms the sound *value-correct*
reduction is honest (not a disguised `False`). -/

/-- **Non-vacuity of the patched sound `TraceRationalityDataNF` reduction.**  For the empty pole set the
reduction is satisfiable via the empty selection and `br = ∅`, yielding `∑Res = 0`. -/
theorem residueSum_eq_zero_of_patchedTraceRationalityNF_holomorphic (ω₀ : HolomorphicOneForms X)
    (g : X → ℂ) (f : MeromorphicFunction X) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 := by
  -- `valueChartTracePatched … ∅ = valueChartTrace … = 0` for the empty selection.
  have hpatch0 : valueChartTracePatched ω₀ f (fun p => emptyFibreRegularData g f p) ∅
      = fun _ => (0 : ℂ) := by
    funext z
    rw [valueChartTracePatched_of_not_mem ω₀ f _ _ (Finset.notMem_empty z),
      valueChartTrace_emptySelection ω₀ f]
  refine residueSum_eq_zero_of_patchedTraceRationalityNF (g := g) (poles := (∅ : Finset X))
    (fun p => emptyFibreRegularData g f p)
    0 Fin.elim0 0 (fun i => i.elim0) (fun i => i.elim0) (∅ : Finset ℂ)
    (fun w _ => by rw [valueChartTrace_emptySelection ω₀ f]; exact analyticAt_const)
    (fun b₀ hb₀ _ => absurd hb₀ (Finset.notMem_empty b₀))
    (fun p => emptyFibreRegularData g f p)
    (fun i => i.elim0) (fun i => i.elim0)
    (fun _ i => i.elim) (fun _ i => i.elim)
    (fun _ a ha => absurd ha (Finset.notMem_empty a))
    (emptyInftyFibreDataNF g f) (fun i => i.elim) (fun i => i.elim)
    (fun a ha => absurd ha (Finset.notMem_empty a))
    (by simp)
    (by rw [hpatch0, recipCoeff_zero, traceCoeff_inftyFibreTraceNF_empty ω₀ f])
    ?_ (fun _ => (0 : ℂ)) analyticAt_const rfl ?_
  · -- junk-freeness: `T − L.R = 0 − 0 = 0` is continuous (empty centres ⟹ `L.R = 0`).
    intro L hLa _ p hp
    have hLR0 : L.R = fun _ => (0 : ℂ) :=
      laurentForm_R_eq_zero_of_emptyImage
        (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
    rw [hpatch0, hLR0]
    have h0 : ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) = fun _ : ℂ => (0 : ℂ) := by funext z; simp
    rw [h0]; exact continuousAt_const
  · -- kirovGenus-`0` `∞`-vanishing: `recipCoeff (0 − 0) =ᶠ 0`.
    intro L hLa
    have hLR0 : L.R = fun _ => (0 : ℂ) :=
      laurentForm_R_eq_zero_of_emptyImage
        (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
    rw [hpatch0, hLR0]
    have h0 : ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) = fun _ : ℂ => (0 : ℂ) := by funext z; simp
    rw [h0, recipCoeff_zero]

end Jacobians.Dolbeault.FormTraceFullFibre
