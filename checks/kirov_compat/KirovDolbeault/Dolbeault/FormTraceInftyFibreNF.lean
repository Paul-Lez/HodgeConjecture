/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceFibre
import KirovDolbeault.Dolbeault.FormTraceInftyRecip
import KirovDolbeault.ProperMapDegreeSheets

/-!
# The `∞`-fibre trace via the *repaired* reciprocal (Gate A, §VIII.3 — sound `∞` fibre)

`Jacobians.Dolbeault.FormTraceInftyFibre.InftyFibreData` models the `∞`-fibre trace through the
**literal** reciprocal `z ↦ (f.holoRepr (chart⁻¹ z))⁻¹`, demanding it be `AnalyticAt` at the pole
chart-centre (`hrecip_an`) and vanish there (`hrecip_val`).  Both are **false for a genuine `∞`-pole**:
at a pole `x` the limit-repair `f.holoRepr x = limUnder (𝓝[≠] x) f.toFun` (`MeromorphicLiouville`) does
*not* exist, so `f.holoRepr x` is a junk value — the literal reciprocal is not continuous (let alone
analytic) at the centre, and `(f.holoRepr x)⁻¹` is junk, not `0`.  Consequently the original
`InftyFibreData` is only ever satisfiable *empty* (the repo never builds a non-empty one).

This file fixes that with the **repaired reciprocal**: the meromorphic normal form
`h := toMeromorphicNFAt (f.holoRepr ∘ chart⁻¹)⁻¹` of the reciprocal at the pole centre, supplied by
`Jacobians.ProperMapDegreeSheets.exists_reciprocal_NF`.  It is genuinely `AnalyticAt` at the centre,
vanishes there (`h (centre) = 0`), has analytic order `= the pole order`, and agrees with the literal
reciprocal on the *punctured* neighbourhood `𝓝[≠]`.  Carrying `h` (rather than the junk literal) as the
reciprocal section makes the `∞`-fibre `FibreTrace` honest.

## The honest `∞`-fibre datum

`InftyFibreDataNF` mirrors `FibreRegularData`/`InftyFibreData` but carries the reciprocal section
`recip : ι → ℂ → ℂ` as **data**, with its analyticity / nonzero-derivative / vanishing-at-centre as
fields, plus the germ-link `hrecip_germ` to the literal reciprocal off the centre (the geometric meaning:
`recip i` *is* `1/f` read in charts, away from the pole).  The `∞`-fibre `FibreTrace` (`inftyFibreTraceNF`)
uses `recip i` as the cover map whose planar inverse is the sheet; the chart integrand of `α = ω₀·g` is
the coefficient, exactly as in the finite case (so the per-sheet residue bridge is unchanged).

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `InftyFibreDataNF` / `InftyFibreDataNF.ofRegular` — the honest `∞`-fibre datum and its constructor from
  a **simple pole** (`f.orderAtPoint = −1`, the unramified-over-`∞` case): `exists_reciprocal_NF` supplies
  the repaired analytic reciprocal `h`, whose order-`1` factorization gives `deriv h ≠ 0`.
* `inftyFibreTraceNF` — the generic `FibreTrace` over the `∞` fibre (base `0`), from `InftyFibreDataNF`;
* `resAt_traceCoeff_inftyFibreTraceNF` — the `∞`-fibre Lemma 3.2:
  `resAt (∞-trace coeff) 0 = ∑ i, formFnResidue ω₀ g (xs i)`;
* `inftyResidueSumNF_eq_filter` — the `∞`-fibre residue sum = the `∞`-fibre-restricted pole-set sum;
* `infty_eq_of_agreeNF` — `resAtInfty L.R L.ρ = ∑_{F a = ∞} Res_a α` from the reciprocal-chart agreement
  `recipCoeff L.R =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f D).traceCoeff` (the precise `GlobalTraceData.infty_eq`
  conclusion, with the sound `∞`-fibre trace replacing the buggy one).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; the residue at
  infinity; normal form (3.1)).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceInftyFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceInftyRecip
  Jacobians.ProperMapDegreeSheets

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {g : X → ℂ}

/-! ### Order-`1` analytic ⟹ nonzero derivative (the simple-pole / unramified-over-`∞` lever) -/

/-- An analytic function with a **simple** zero (analytic order `1`) has nonzero derivative there.
Via the order-`1` factorization `h z = (z − z₀)·g z` with `g z₀ ≠ 0` (`analyticOrderAt_eq_natCast`),
`deriv h z₀ = g z₀ ≠ 0`. -/
theorem deriv_ne_zero_of_analyticOrderAt_eq_one {h : ℂ → ℂ} {z₀ : ℂ}
    (hana : AnalyticAt ℂ h z₀) (hord : analyticOrderAt h z₀ = 1) : deriv h z₀ ≠ 0 := by
  have h1 : analyticOrderAt h z₀ = ((1 : ℕ) : ℕ∞) := by exact_mod_cast hord
  obtain ⟨G, hG_an, hG_ne, hfac⟩ := hana.analyticOrderAt_eq_natCast.mp h1
  have hev : h =ᶠ[𝓝 z₀] (fun z => (z - z₀) * G z) := by
    filter_upwards [hfac] with z hz; simpa [pow_one] using hz
  have hd1 : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := by
    simpa using (hasDerivAt_id z₀).sub_const z₀
  have hprod : HasDerivAt (fun z => (z - z₀) * G z) (1 * G z₀ + (z₀ - z₀) * deriv G z₀) z₀ :=
    hd1.mul hG_an.differentiableAt.hasDerivAt
  have hderiv_eq : deriv h z₀ = G z₀ := by rw [hev.deriv_eq, hprod.deriv]; simp
  rw [hderiv_eq]; exact hG_ne

/-! ### The honest `∞`-fibre regularity data (carrying the repaired reciprocal) -/

/-- **Per-`∞`-fibre regularity data (repaired reciprocal).**  For the cover `f` over `∞`: a finite
family of poles `xs : ι → X` of `α` mapping to `∞`, together with the **repaired reciprocal section**
`recip i : ℂ → ℂ` — the analytic normal form of `z ↦ (f.holoRepr (chart⁻¹ z))⁻¹` at the pole centre
`pre i = chart (xs i)`.  Fields:

* `hrecip_an` — `recip i` analytic at `pre i`;
* `hrecip_deriv` — `recip i` has nonzero derivative at `pre i` (`f` *unramified over `∞`* at `xs i`, i.e.
  a simple pole);
* `hrecip_val` — `recip i (pre i) = 0` (the reciprocal coordinate of `∞`);
* `hrecip_germ` — `recip i` agrees with the literal reciprocal `(f.holoRepr (chart⁻¹ ·))⁻¹` on the
  *punctured* neighbourhood of `pre i` (its geometric meaning: `1/f` in charts, away from the pole);
* `hg_mero` — `g`'s chart-pullback is meromorphic at `pre i`.

Unlike `InftyFibreData`, the analyticity/vanishing are about the carried `recip i` (the repaired,
genuinely-analytic normal form), so the structure is *satisfiable for real `∞`-poles*. -/
structure InftyFibreDataNF (g : X → ℂ) (f : MeromorphicFunction X) where
  /-- The sheet index. -/
  ι : Type
  /-- Finiteness of the index. -/
  fintype_ι : Fintype ι
  /-- The fibre points (poles of `α` over `∞`). -/
  xs : ι → X
  /-- The repaired reciprocal section (analytic normal form of `1/f` in charts at the pole centre). -/
  recip : ι → ℂ → ℂ
  /-- `recip i` is analytic at the pole centre `pre i = chart (xs i)`. -/
  hrecip_an : ∀ i, AnalyticAt ℂ (recip i) ((chartAt ℂ (xs i)) (xs i))
  /-- `recip i` has nonzero derivative at the centre (`f` unramified over `∞` at `xs i`: simple pole). -/
  hrecip_deriv : ∀ i, deriv (recip i) ((chartAt ℂ (xs i)) (xs i)) ≠ 0
  /-- `recip i (pre i) = 0` (the reciprocal coordinate of `∞`). -/
  hrecip_val : ∀ i, recip i ((chartAt ℂ (xs i)) (xs i)) = 0
  /-- `recip i` agrees with the literal reciprocal off the centre (its geometric meaning). -/
  hrecip_germ : ∀ i, recip i =ᶠ[𝓝[≠] ((chartAt ℂ (xs i)) (xs i))]
    (fun z => (f.holoRepr ((chartAt ℂ (xs i)).symm z))⁻¹)
  /-- `g`'s chart-pullback is meromorphic at each `pre i` (so `α·g` has an isolated singularity). -/
  hg_mero : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (xs i)).symm z)) ((chartAt ℂ (xs i)) (xs i))

attribute [instance] InftyFibreDataNF.fintype_ι

/-- **Repaired reciprocal at a *simple* pole, packaged.**  At a simple pole `x` of `f`
(`f.orderAtPoint x = −1`), `exists_reciprocal_NF` gives the repaired analytic reciprocal `h`: analytic
at the chart centre, `deriv h (centre) ≠ 0` (order-`1` factorization), `h (centre) = 0`, and
`h =ᶠ[𝓝[≠]] (f.holoRepr (chart⁻¹ ·))⁻¹` off the centre.  A flat packaging (the analytic order `m = 1`
is discharged here) so the `∞`-fibre datum constructor reads the fields directly. -/
theorem exists_reciprocal_simple (f : MeromorphicFunction X) {x : X}
    (hsimple : f.orderAtPoint x = -1) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h ((chartAt ℂ x) x) ∧
      deriv h ((chartAt ℂ x) x) ≠ 0 ∧
      h ((chartAt ℂ x) x) = 0 ∧
      ((fun z => (f.holoRepr ((chartAt ℂ x).symm z))⁻¹) =ᶠ[𝓝[≠] ((chartAt ℂ x) x)] h) := by
  obtain ⟨h, m, hm1, hm_eq, hana, hgerm, hval0, hAO⟩ :=
    exists_reciprocal_NF f (show f.orderAtPoint x < 0 by rw [hsimple]; decide)
  have hm : m = 1 := by rw [hsimple] at hm_eq; omega
  have hAO1 : analyticOrderAt h ((chartAt ℂ x) x) = 1 := by rw [hAO, hm]; rfl
  exact ⟨h, hana, deriv_ne_zero_of_analyticOrderAt_eq_one hana hAO1, hval0, hgerm⟩

/-- **`InftyFibreDataNF` from a simple pole over `∞`.**  At each `xs i` a **simple pole** of `f`
(`f.orderAtPoint (xs i) = −1`, i.e. unramified over `∞`), with `g`'s chart-pullback meromorphic there,
`exists_reciprocal_simple` supplies the repaired analytic reciprocal `h` (analytic, `deriv ≠ 0`,
`h (centre) = 0`, `=ᶠ[𝓝[≠]]` the literal reciprocal).  The honest `∞`-analogue of
`FibreRegularData.ofRegular`. -/
noncomputable def InftyFibreDataNF.ofRegular (g : X → ℂ) (f : MeromorphicFunction X)
    {ι : Type} [Fintype ι] (xs : ι → X)
    (hsimple : ∀ i, f.orderAtPoint (xs i) = -1)
    (hmero : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (xs i)).symm z)) ((chartAt ℂ (xs i)) (xs i))) :
    InftyFibreDataNF g f where
  ι := ι
  fintype_ι := inferInstance
  xs := xs
  recip := fun i => Classical.choose (exists_reciprocal_simple f (hsimple i))
  hrecip_an := fun i => (Classical.choose_spec (exists_reciprocal_simple f (hsimple i))).1
  hrecip_deriv := fun i => (Classical.choose_spec (exists_reciprocal_simple f (hsimple i))).2.1
  hrecip_val := fun i => (Classical.choose_spec (exists_reciprocal_simple f (hsimple i))).2.2.1
  hrecip_germ := fun i => ((Classical.choose_spec (exists_reciprocal_simple f (hsimple i))).2.2.2).symm
  hg_mero := hmero

/-! ### The `∞`-fibre `FibreTrace` (generic, repaired reciprocal-chart sheets)

Identical to `inftyFibreTrace`, but the cover map is the carried repaired reciprocal `D.recip i`
(genuinely analytic at the centre, value `0`, nonzero derivative), so the planar section exists. -/

/-- **The `FibreTrace` over the `∞` fibre, via the repaired reciprocal.**  From `InftyFibreDataNF`,
the sheets are the planar inverses of `recip i` (a genuine local biholomorphism at `pre i ↦ 0`), and the
coefficients are the chart integrands of `α = ω₀·g` — *identical* to the finite case, so the per-sheet
residue bridge `resAt (coeff i) (pre i) = formFnResidue ω₀ g (xs i)` is unchanged. -/
noncomputable def inftyFibreTraceNF (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreDataNF g f) : FibreTrace where
  ι := D.ι
  fintype_ι := D.fintype_ι
  b := 0
  sheet := fun i =>
    Classical.choose (exists_planar_section (D.hrecip_an i) (D.hrecip_deriv i) (D.hrecip_val i))
  pre := fun i => (chartAt ℂ (D.xs i)) (D.xs i)
  sheet_analytic := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hrecip_an i) (D.hrecip_deriv i)
      (D.hrecip_val i))).1
  sheet_deriv_ne := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hrecip_an i) (D.hrecip_deriv i)
      (D.hrecip_val i))).2.2.1
  sheet_base := fun i =>
    (Classical.choose_spec (exists_planar_section (D.hrecip_an i) (D.hrecip_deriv i)
      (D.hrecip_val i))).2.1
  coeff := fun i => chartIntegrand ω₀ g (D.xs i)
  coeff_mero := fun i => meromorphicAt_chartIntegrand ω₀ g (D.xs i) (D.hg_mero i)

@[simp] theorem inftyFibreTraceNF_b (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreDataNF g f) : (inftyFibreTraceNF ω₀ f D).b = 0 := rfl

@[simp] theorem inftyFibreTraceNF_pre (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreDataNF g f) (i : D.ι) :
    (inftyFibreTraceNF ω₀ f D).pre i = (chartAt ℂ (D.xs i)) (D.xs i) := rfl

@[simp] theorem inftyFibreTraceNF_coeff (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreDataNF g f) (i : D.ι) :
    (inftyFibreTraceNF ω₀ f D).coeff i = chartIntegrand ω₀ g (D.xs i) := rfl

/-- **Bridge (c) at `∞`, assembled.**  `resAt ((inftyFibreTraceNF ω₀ f D).coeff i)
((inftyFibreTraceNF ω₀ f D).pre i) = formFnResidue ω₀ g (xs i)` — the source-chart residue, identical
to the finite case. -/
@[simp] theorem resAt_inftyFibreTraceNF_coeff (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (D : InftyFibreDataNF g f) (i : D.ι) :
    resAt ((inftyFibreTraceNF ω₀ f D).coeff i) ((inftyFibreTraceNF ω₀ f D).pre i)
      = formFnResidue ω₀ g (D.xs i) := by
  rw [inftyFibreTraceNF_coeff, inftyFibreTraceNF_pre]
  exact resAt_chartIntegrand_eq_formFnResidue ω₀ g (D.xs i)

/-- **Lemma 3.2 over the `∞` fibre (reciprocal chart, repaired).**  The trace residue at the reciprocal
base `0` equals the `∞`-fibre residue sum of `α = ω₀·g`:

> `Res_0 (Tr_F α over the ∞-fibre) = ∑ i, formFnResidue ω₀ g (xs i)`.

`FibreTrace.resAt_traceCoeff'` (unconditional) composed with bridge (c) at `∞`. -/
theorem resAt_traceCoeff_inftyFibreTraceNF (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreDataNF g f) :
    resAt (inftyFibreTraceNF ω₀ f D).traceCoeff 0 = ∑ i, formFnResidue ω₀ g (D.xs i) := by
  have h := (inftyFibreTraceNF ω₀ f D).resAt_traceCoeff'
  rw [inftyFibreTraceNF_b] at h
  rw [h]
  exact Finset.sum_congr rfl (fun i _ => resAt_inftyFibreTraceNF_coeff ω₀ f D i)

/-! ### The `∞`-fibre residue sum as the fibre-restricted pole-set sum (pure `Finset` combinatorics) -/

/-- **`∞`-fibre residue sum = `∞`-fibre-restricted pole-set sum.**  If `D.xs` injectively enumerates
exactly the poles in the fibre `F⁻¹(∞)`, then
`∑ i, formFnResidue ω₀ g (xs i) = ∑_{a ∈ poles, F a = ∞} formFnResidue ω₀ g a`. -/
theorem inftyResidueSumNF_eq_filter (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (D : InftyFibreDataNF g f) (poles : Finset X)
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

/-! ### `infty_eq` (the `GlobalTraceData` conclusion) from the reciprocal-chart agreement -/

/-- **`infty_eq` from the reciprocal-chart agreement (repaired `∞`-fibre).**  Given the honest
`∞`-fibre data `D` enumerating the poles over `∞`, and the agreement
`recipCoeff L.R =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f D).traceCoeff`, the residue at infinity of `L.R`
is the `∞`-fibre residue sum:

> `resAtInfty L.R L.ρ = ∑_{a ∈ poles, F a = ∞} formFnResidue ω₀ g a`.

`resAtInfty L.R = resAt (recipCoeff L.R) 0` (bridge `resAtInfty_eq_resAt_recipCoeff`)
`= resAt (inftyFibreTraceNF …).traceCoeff 0` (agreement) `= ∑ Res` (Lemma 3.2 + re-indexing).
This is the precise `GlobalTraceData.infty_eq` conclusion, with the *sound* `∞`-fibre trace. -/
theorem infty_eq_of_agreeNF (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (L : LaurentForm) (D : InftyFibreDataNF g f) (poles : Finset X)
    (hxs_inj : Function.Injective D.xs)
    (hxs_mem : ∀ i, D.xs i ∈ poles ∧ f.toRiemannSphere (D.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, D.xs i = a)
    (hagree_infty : recipCoeff L.R =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f D).traceCoeff) :
    resAtInfty L.R L.ρ
      = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a := by
  rw [resAtInfty_eq_resAt_recipCoeff, resAt_congr hagree_infty,
    resAt_traceCoeff_inftyFibreTraceNF ω₀ f D,
    inftyResidueSumNF_eq_filter ω₀ f D poles hxs_inj hxs_mem hxs_surj]

end Jacobians.Dolbeault.FormTraceInftyFibre
