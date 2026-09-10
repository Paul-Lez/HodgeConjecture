/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceFibre
import KirovDolbeault.Dolbeault.FormTraceInftyRecip

/-!
# The `∞`-fibre reciprocal-chart trace (Gate A, §VIII.3 step 5 — `infty_eq` reduced to agreement)

This file builds the **`∞`-fibre** analogue of `Jacobians.Dolbeault.FormTraceFibre`: Miranda's
Lemma 3.2 read at the pole fibre `F⁻¹(∞)` in the reciprocal chart `ζ = 1/w` of `ℂℙ¹` (base coordinate
`0`).  It reduces the `infty_eq` field of `TraceRationalityWitness` — in its reciprocal-chart form
`resAt (recipCoeff L.R) 0 = ∑_{a : F a = ∞} Res_a α` (the proved bridge
`FormTraceInftyRecip.resAtInfty_eq_resAt_recipCoeff`) — to a single honest geometric input,
*structurally identical to the finite case*: **`recipCoeff L.R` agrees with the reciprocal-chart trace
coefficient off `0`**.

## The reciprocal-chart `∞`-fibre, via the generic `FibreTrace`

The finite-centre engine `FormTraceFibre.fibreReg`/`fibreTrace` is hard-wired to the value chart
`w = f.holoRepr` (its `FibreRegularData` carries the chart-pullback of `f.holoRepr`).  Near `∞` the
relevant value coordinate is the **reciprocal** `ζ = 1/f.holoRepr`, so we cannot reuse
`FibreRegularData` directly.  Instead we build the trace over the `∞` fibre using the *generic*
`Jacobians.MeromorphicTrace.FibreTrace` (sheets + coefficients), with

* `b := 0` — the reciprocal coordinate of `∞`;
* `pre i := chart_{xs i} (xs i)` and `coeff i := chartIntegrand ω₀ g (xs i)` — **the same source-chart
  data as the finite case** (the `1`-form `α = ω₀·g`'s chart integrand at the fibre point `xs i`), so
  bridge (c) `resAt (coeff i) (pre i) = formFnResidue ω₀ g (xs i)` (`resAt_chartIntegrand_eq_formFnResidue`)
  is *unchanged* — the residue of `α` at a point is read in the source chart, independent of the value
  chart;
* `sheet i` — the planar inverse of the **reciprocal-chart cover map** `z ↦ 1/f.holoRepr(chart⁻¹ z)`
  (a local biholomorphism at `pre i` sending `pre i ↦ 0`, when the pole `xs i` is *unramified for `f`
  over `∞`* — `f` simple there), supplied by `exists_planar_section`.

With this, Lemma 3.2 (`FibreTrace.resAt_traceCoeff'`, unconditional) gives
`resAt (∞-trace coeff) 0 = ∑ i, formFnResidue ω₀ g (xs i)` — the `∞`-fibre residue sum.  Then if
`recipCoeff L.R` agrees with the `∞`-trace coefficient off `0`, `resAt_congr` turns the LHS of the
reciprocal `infty_eq` into the `∞`-fibre residue sum.

## The `∞`-regularity input

A pole `a` of `α` mapping to `∞` is *unramified for `f` over `∞`* iff the reciprocal `1/f.holoRepr`
read in charts is a local biholomorphism at `chart a` (analytic, nonzero derivative, value `0`).  We
carry this as the structure `InftyFibreData` (the honest geometric input — `f` unramified over `∞` at
the pole fibre, e.g. the generic-cover choice), mirroring `FibreRegularData` field-for-field.

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `inftyFibreTrace` — the generic `FibreTrace` over the `∞` fibre (base `0`), from `InftyFibreData`;
* `resAt_traceCoeff_inftyFibreTrace` — the `∞`-fibre Lemma 3.2:
  `resAt (∞-trace coeff) 0 = ∑ i, formFnResidue ω₀ g (xs i)`;
* `inftyResidueSum_eq_filter` — the `∞`-fibre residue sum equals the fibre-restricted pole-set sum
  `∑_{a : F a = ∞} Res_a α` (when `xs` enumerates exactly the `∞` fibre);
* `resAt_recipCoeff_eq_inftyResidueSum_of_agree` — the reciprocal `infty_eq`, from the agreement
  `recipCoeff L.R =ᶠ[𝓝[≠] 0] (∞-trace coeff)`.

This is the honest reduction of `infty_eq` to the same "`L` represents `Tr_F α`" agreement the finite
case rests on — the residual content is now uniformly *agreement of `L` with the trace germ* (finite
charts + reciprocal chart), i.e. the trace's global rationality.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; the residue
  at infinity).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceInftyFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceInftyRecip

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {g : X → ℂ}

/-! ### The `∞`-fibre regularity data (the reciprocal-chart cover, unramified over `∞`) -/

/-- **Per-`∞`-fibre regularity data** for the cover `f` over `∞`: a finite family of fibre points
`xs : ι → X` (the poles of `α` mapping to `∞`), each *unramified for `f` over `∞`* — the
**reciprocal-chart cover map** `z ↦ (f.holoRepr (chart⁻¹ z))⁻¹` is a local biholomorphism at
`pre i = chart (xs i)`, sending it to the reciprocal coordinate `0` of `∞`.  This is the honest
geometric input the `∞`-fibre `FibreTrace` is built from (the generic-cover choice makes `f`
unramified over `∞`).  Mirrors `FibreRegularData`, with `1/f.holoRepr` (the reciprocal value) in place
of `f.holoRepr`. -/
structure InftyFibreData (g : X → ℂ) (f : MeromorphicFunction X) where
  /-- The sheet index. -/
  ι : Type
  /-- Finiteness of the index. -/
  fintype_ι : Fintype ι
  /-- The fibre points (poles of `α` over `∞`). -/
  xs : ι → X
  /-- The reciprocal-chart cover `z ↦ (f.holoRepr (chart⁻¹ z))⁻¹` is analytic at `pre i`. -/
  hrecip_an : ∀ i, AnalyticAt ℂ
    (fun z => (f.holoRepr ((chartAt ℂ (xs i)).symm z))⁻¹) ((chartAt ℂ (xs i)) (xs i))
  /-- `xs i` is unramified for `f` over `∞`: the reciprocal-chart cover derivative is nonzero. -/
  hrecip_deriv : ∀ i, deriv
    (fun z => (f.holoRepr ((chartAt ℂ (xs i)).symm z))⁻¹) ((chartAt ℂ (xs i)) (xs i)) ≠ 0
  /-- `xs i` maps to `∞`: the reciprocal value `1/f.holoRepr (xs i)` is `0`. -/
  hrecip_val : ∀ i, (f.holoRepr (xs i))⁻¹ = 0
  /-- `g`'s chart-pullback is meromorphic at each `pre i` (so `α·g` has an isolated singularity). -/
  hg_mero : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (xs i)).symm z)) ((chartAt ℂ (xs i)) (xs i))

attribute [instance] InftyFibreData.fintype_ι

/-- The reciprocal-chart cover `z ↦ (f.holoRepr (chart⁻¹ z))⁻¹` evaluated at `pre i = chart (xs i)`
is `0` (the reciprocal coordinate of `∞`). -/
theorem InftyFibreData.recipval (f : MeromorphicFunction X)
    (D : InftyFibreData g f) (i : D.ι) :
    (fun z => (f.holoRepr ((chartAt ℂ (D.xs i)).symm z))⁻¹) ((chartAt ℂ (D.xs i)) (D.xs i)) = 0 := by
  show (f.holoRepr ((chartAt ℂ (D.xs i)).symm ((chartAt ℂ (D.xs i)) (D.xs i))))⁻¹ = 0
  rw [(chartAt ℂ (D.xs i)).left_inv (mem_chart_source ℂ (D.xs i))]
  exact D.hrecip_val i

/-! ### The `∞`-fibre `FibreTrace` (generic, reciprocal-chart sheets) -/

/-- **The `FibreTrace` over the `∞` fibre.**  From the `∞`-regularity data `D`, build the fibre trace
over the reciprocal base `0` whose sheets are the planar section germs of the reciprocal-chart cover
(bridge (a) at `∞`) and whose coefficients are the chart integrands of `α = ω₀·g` (bridges (b)/(c),
*identical to the finite case* — the residue of `α` is read in the source chart).  The `pre i` are the
source-chart coordinates of the fibre points, so `resAt (coeff i) (pre i) = formFnResidue ω₀ g (xs i)`
definitionally. -/
noncomputable def inftyFibreTrace (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreData g f) : FibreTrace where
  ι := D.ι
  fintype_ι := D.fintype_ι
  b := 0
  sheet := fun i =>
    Classical.choose (exists_planar_section (D.hrecip_an i) (D.hrecip_deriv i) (D.recipval f i))
  pre := fun i => (chartAt ℂ (D.xs i)) (D.xs i)
  sheet_analytic := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hrecip_an i) (D.hrecip_deriv i)
      (D.recipval f i))).1
  sheet_deriv_ne := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hrecip_an i) (D.hrecip_deriv i)
      (D.recipval f i))).2.2.1
  sheet_base := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hrecip_an i) (D.hrecip_deriv i)
      (D.recipval f i))).2.1
  coeff := fun i => chartIntegrand ω₀ g (D.xs i)
  coeff_mero := fun i => meromorphicAt_chartIntegrand ω₀ g (D.xs i) (D.hg_mero i)

@[simp] theorem inftyFibreTrace_b (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreData g f) : (inftyFibreTrace ω₀ f D).b = 0 := rfl

@[simp] theorem inftyFibreTrace_pre (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreData g f) (i : D.ι) :
    (inftyFibreTrace ω₀ f D).pre i = (chartAt ℂ (D.xs i)) (D.xs i) := rfl

@[simp] theorem inftyFibreTrace_coeff (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreData g f) (i : D.ι) :
    (inftyFibreTrace ω₀ f D).coeff i = chartIntegrand ω₀ g (D.xs i) := rfl

/-- **Bridge (c) at `∞`, assembled.**  The per-sheet residue of the `∞`-fibre trace equals
`formFnResidue`: `resAt ((inftyFibreTrace ω₀ f D).coeff i) ((inftyFibreTrace ω₀ f D).pre i)
= formFnResidue ω₀ g (xs i)` — identical to the finite case (source-chart residue). -/
@[simp] theorem resAt_inftyFibreTrace_coeff (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreData g f) (i : D.ι) :
    resAt ((inftyFibreTrace ω₀ f D).coeff i) ((inftyFibreTrace ω₀ f D).pre i)
      = formFnResidue ω₀ g (D.xs i) := by
  rw [inftyFibreTrace_coeff, inftyFibreTrace_pre]
  exact resAt_chartIntegrand_eq_formFnResidue ω₀ g (D.xs i)

/-- **Lemma 3.2 over the `∞` fibre (reciprocal chart).**  The trace residue at the reciprocal base
`0` equals the `∞`-fibre residue sum of `α = ω₀·g`:

> `Res_0 (Tr_F α over the ∞-fibre, reciprocal chart) = ∑ i, formFnResidue ω₀ g (xs i)`.

This is `FibreTrace.resAt_traceCoeff'` (now unconditional) composed with bridge (c) at `∞`
(`resAt_inftyFibreTrace_coeff`).  It is the `∞`-fibre analogue of `resAt_traceCoeff_fibreTrace`. -/
theorem resAt_traceCoeff_inftyFibreTrace (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreData g f) :
    resAt (inftyFibreTrace ω₀ f D).traceCoeff 0 = ∑ i, formFnResidue ω₀ g (D.xs i) := by
  have h := (inftyFibreTrace ω₀ f D).resAt_traceCoeff'
  rw [inftyFibreTrace_b] at h
  rw [h]
  exact Finset.sum_congr rfl (fun i _ => resAt_inftyFibreTrace_coeff ω₀ f D i)

/-! ### The `∞`-fibre residue sum as the fibre-restricted pole-set sum

Pure `Finset` combinatorics, mirroring `FormTraceFibre.fibreResidueSum_eq_filter` for the `∞`
fibre: when `xs` injectively enumerates exactly the poles `a ∈ poles` with `F a = ∞`, the per-fibre
residue sum is the fibre-restricted residue sum that appears in `infty_eq`. -/

/-- **`∞`-fibre residue sum = `∞`-fibre-restricted pole-set sum.**  If the `∞`-regularity data `D`
has `xs` injectively enumerating exactly the poles in the fibre `F⁻¹(∞)` (`hxs_inj`, `hxs_mem`,
`hxs_surj`), then the per-fibre residue sum over `D` equals the `∞`-fibre-restricted residue sum:

> `∑ i, formFnResidue ω₀ g (xs i) = ∑_{a ∈ poles, F a = ∞} formFnResidue ω₀ g a`. -/
theorem inftyResidueSum_eq_filter (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreData g f) (poles : Finset X)
    (hxs_inj : Function.Injective D.xs)
    (hxs_mem : ∀ i, D.xs i ∈ poles ∧ f.toRiemannSphere (D.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, D.xs i = a) :
    ∑ i, formFnResidue ω₀ g (D.xs i)
      = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a := by
  classical
  have hImg : (Finset.univ : Finset D.ι).image D.xs
      = poles.filter (fun a => f.toRiemannSphere a = OnePoint.infty) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨(hxs_mem i).1, (hxs_mem i).2⟩
    · rintro ⟨ha_pole, ha_fib⟩; exact hxs_surj a ha_pole ha_fib
  rw [← hImg, Finset.sum_image (fun i _ j _ h => hxs_inj h)]

/-! ### `infty_eq` reduced to the reciprocal-chart agreement

The honest analogue of `FormTraceRationalReduce.resAt_eq_fibreResidueSum_of_agree` at `∞`: if the
reciprocal coefficient `recipCoeff L.R` agrees with the `∞`-fibre trace coefficient off `0`, then the
reciprocal `infty_eq` holds. -/

/-- **The reciprocal `infty_eq`, from the reciprocal-chart agreement.**  If `recipCoeff L.R` agrees
with the `∞`-fibre trace coefficient `(inftyFibreTrace ω₀ f D).traceCoeff` on a punctured
neighbourhood of `0`, and `D`'s `xs` enumerates exactly the `∞` fibre, then

> `resAt (recipCoeff L.R) 0 = ∑_{a ∈ poles, F a = ∞} formFnResidue ω₀ g a`,

i.e. the reciprocal-chart form `hinftyRecip` of the `infty_eq` field
(`traceRationalityWitness_of_agree_recip`).

*Proof.*  `resAt (recipCoeff L.R) 0 = resAt (∞-trace coeff) 0` (agreement, `resAt_congr`), which is the
`∞`-fibre residue sum (`resAt_traceCoeff_inftyFibreTrace`), which is the `∞`-fibre-restricted pole-set
sum (`inftyResidueSum_eq_filter`). -/
theorem resAt_recipCoeff_eq_inftyResidueSum_of_agree (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (D : InftyFibreData g f) (L : LaurentForm) (poles : Finset X)
    (hxs_inj : Function.Injective D.xs)
    (hxs_mem : ∀ i, D.xs i ∈ poles ∧ f.toRiemannSphere (D.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, D.xs i = a)
    (hagree : recipCoeff L.R =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f D).traceCoeff) :
    resAt (recipCoeff L.R) 0
      = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a := by
  rw [resAt_congr hagree, resAt_traceCoeff_inftyFibreTrace ω₀ f D]
  exact inftyResidueSum_eq_filter ω₀ f D poles hxs_inj hxs_mem hxs_surj

end Jacobians.Dolbeault.FormTraceInftyFibre
