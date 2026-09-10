/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceInftyRecip
import Mathlib.Analysis.Complex.Liouville

/-!
# Liouville vanishing for `dz`-coefficients on `ℂℙ¹` (Gate A, §VIII.3 step 3 — the remainder vanishes)

The deep §VIII.3 trace-rationality argument closes with the **vanishing of the holomorphic remainder**:
after subtracting the finite principal parts of the meromorphic trace `Tr_F α` (a `LaurentForm L`)
one obtains a global *holomorphic* `1`-form on the compact `ℂℙ¹`, which must be **zero** (the sphere
has kirovGenus `0`, `H⁰(ℂℙ¹, Ω) = 0`).  This file proves that vanishing at the level of `dz`-coefficient
functions `ℂ → ℂ`, the representation the trace machinery (`FormTraceFibre`, `FormTraceInftyFibre`,
`recipCoeff`) actually uses.

A global holomorphic `1`-form on `ℂℙ¹`, read in the affine chart, is an **entire** coefficient
`h : ℂ → ℂ` of `dz`; read in the reciprocal chart `ζ = 1/z` it is the coefficient `recipCoeff h`
(`recipCoeff h ζ = −h(ζ⁻¹)·ζ⁻²`, the `dz = −ζ⁻² dζ` Jacobian).  Holomorphy at `∞` means `recipCoeff h`
extends **analytically across `0`**.  The transition forces `h(z) = O(z⁻²) → 0` at `∞`, so the entire
`h` is bounded with limit `0`, hence (complex Liouville,
`Differentiable.eq_const_of_tendsto_cocompact`) `h ≡ 0`.

This is the *coefficient-level* form of `Jacobians.holomorphicOneForm_eq_zero`
(`Jacobians/ProjectiveLine.lean`, the kirovGenus-`0` vanishing proven for honest cotangent-bundle
sections); we re-prove the analytic core directly for raw coefficient functions, so the trace remainder
(a `ℂ → ℂ` coefficient, *not* packaged as a `HolomorphicOneForms RiemannSphere` section) can be
concluded zero without first building a bundle section.

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `coeff_tendsto_cobounded_of_recipCoeff_continuousAt` — `O(z⁻²)` decay at `∞`: an `h : ℂ → ℂ` whose
  reciprocal coefficient `recipCoeff h` is continuous at `0` tends to `0` along `cobounded ℂ`.
* `coeff_eq_zero_of_entire_of_recipCoeff_continuousAt` — **the Liouville vanishing**: an *entire* `h`
  with `recipCoeff h` continuous at `0` is identically `0`.
* `coeff_eqOn_of_entire_diff_of_recipCoeff_continuousAt` — the **two-coefficient** corollary used by
  the trace assembly: if `h₁ − h₂` is entire and `recipCoeff (h₁ − h₂)` is continuous at `0`, then
  `h₁ = h₂` on all of `ℂ` (hence germ-agree at every finite point), and `recipCoeff h₁ = recipCoeff h₂`
  off `0` (germ-agree at `0` in the reciprocal chart) — exactly the `hagree_fin` / `hagree_inf` shape
  of `TraceAgreementData` once the holomorphic-remainder hypotheses are supplied.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`; rationality on `ℂℙ¹`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
* `Jacobians.holomorphicOneForm_eq_zero` (`Jacobians/ProjectiveLine.lean`) — the bundle-section form.
-/

noncomputable section

open Complex Metric Filter Topology Bornology
open scoped Real

namespace Jacobians.Dolbeault.FormTraceLiouville

open Jacobians.Dolbeault Jacobians.Dolbeault.FormTraceInftyRecip

/-! ### `O(z⁻²)` decay at `∞` from analyticity of the reciprocal coefficient

For `z ≠ 0`, `recipCoeff h (z⁻¹) = −h(z)·z²`, so `h(z) = −z⁻²·recipCoeff h (z⁻¹)`.  As `|z| → ∞`,
`z⁻¹ → 0` and (continuity of `recipCoeff h` at `0`) `recipCoeff h (z⁻¹) → recipCoeff h 0` is bounded,
while `z⁻² → 0`; hence `h(z) → 0`.  This is the `O(z⁻²)` decay underlying the Liouville step. -/

/-- **`recipCoeff h` at `z⁻¹` is `−h(z)·z²`** (for `z ≠ 0`).  The transition law `dz = −ζ⁻² dζ` read
the other way: substituting `ζ = z⁻¹` into `recipCoeff h ζ = −h(ζ⁻¹)·ζ⁻²` gives `−h(z)·z²`. -/
theorem recipCoeff_inv (h : ℂ → ℂ) (z : ℂ) :
    recipCoeff h z⁻¹ = -h z * z ^ 2 := by
  show -(h (z⁻¹)⁻¹) * (z⁻¹) ^ (-2 : ℤ) = -h z * z ^ 2
  rw [inv_inv, zpow_neg, zpow_two, ← sq, inv_pow, inv_inv]

/-- **The affine coefficient as a reciprocal expression** (for `z ≠ 0`):
`h z = −z⁻²·recipCoeff h (z⁻¹)`.  This is `recipCoeff_inv` solved for `h z`. -/
theorem coeff_eq_recipCoeff_inv (h : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    h z = -(z⁻¹) ^ 2 * recipCoeff h z⁻¹ := by
  rw [recipCoeff_inv h z]
  have hzz : (z⁻¹) ^ 2 * z ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hz, one_pow]
  have : -(z⁻¹) ^ 2 * (-h z * z ^ 2) = ((z⁻¹) ^ 2 * z ^ 2) * h z := by ring
  rw [this, hzz, one_mul]

/-- **`O(z⁻²)` decay at `∞`.**  If `recipCoeff h` is continuous at `0`, then `h` tends to `0` along
`cobounded ℂ` (i.e. `|z| → ∞`): `h z = −z⁻²·recipCoeff h (z⁻¹)`, with `recipCoeff h (z⁻¹) →
recipCoeff h 0` bounded and `−z⁻² → 0`.  (Mirrors `Jacobians.RiemannSphere.affineCoeff_tendsto_cobounded`,
for a raw coefficient with the reciprocal-continuity hypothesis given directly.) -/
theorem coeff_tendsto_cobounded_of_recipCoeff_continuousAt {h : ℂ → ℂ}
    (hrecip : ContinuousAt (recipCoeff h) 0) :
    Filter.Tendsto h (Bornology.cobounded ℂ) (𝓝 0) := by
  -- `recipCoeff h (z⁻¹) → recipCoeff h 0` along cobounded.
  have hg : Filter.Tendsto (fun z : ℂ => recipCoeff h z⁻¹) (Bornology.cobounded ℂ)
      (𝓝 (recipCoeff h 0)) := hrecip.tendsto.comp tendsto_inv₀_cobounded
  -- `−z⁻² → 0` along cobounded.
  have hz2 : Filter.Tendsto (fun z : ℂ => -(z⁻¹) ^ 2) (Bornology.cobounded ℂ) (𝓝 0) := by
    have := (tendsto_inv₀_cobounded (α := ℂ)).pow 2
    simpa using this.neg
  -- product `−z⁻²·recipCoeff h (z⁻¹) → 0·recipCoeff h 0 = 0`.
  have hprod : Filter.Tendsto (fun z : ℂ => -(z⁻¹) ^ 2 * recipCoeff h z⁻¹)
      (Bornology.cobounded ℂ) (𝓝 0) := by
    have := hz2.mul hg; simpa using this
  refine hprod.congr' ?_
  filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
  rw [coeff_eq_recipCoeff_inv h hz]

/-! ### The Liouville vanishing for coefficients

An entire `h` that tends to `0` at `∞` is constant (`Differentiable.eq_const_of_tendsto_cocompact`),
and the limit `0` forces the constant to be `0`. -/

/-- **Liouville vanishing for `dz`-coefficients.**  An **entire** coefficient `h : ℂ → ℂ`
(`AnalyticOnNhd ℂ h univ`) whose reciprocal coefficient `recipCoeff h` is **continuous at `0`** (the
form extends holomorphically across `∞`) is identically `0`:

> a global holomorphic `1`-form on `ℂℙ¹` is zero.

*Proof.*  `h` is entire hence differentiable; it tends to `0` at `∞`
(`coeff_tendsto_cobounded_of_recipCoeff_continuousAt`, via `cobounded = cocompact` on `ℂ`); by complex
Liouville (`Differentiable.eq_const_of_tendsto_cocompact`) it is the constant `0`.  This is the
coefficient-level form of `Jacobians.holomorphicOneForm_eq_zero`. -/
theorem coeff_eq_zero_of_entire_of_recipCoeff_continuousAt {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h Set.univ) (hrecip : ContinuousAt (recipCoeff h) 0) :
    h = 0 := by
  have hdiff : Differentiable ℂ h := fun z => (hh z (Set.mem_univ z)).differentiableAt
  have hcocompact : Filter.Tendsto h (Filter.cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact coeff_tendsto_cobounded_of_recipCoeff_continuousAt hrecip
  -- complex Liouville: `h` differentiable + `→ 0` at `∞` ⟹ `h = const 0 = 0`.
  have hconst : h = Function.const ℂ (0 : ℂ) := hdiff.eq_const_of_tendsto_cocompact hcocompact
  rw [hconst]; rfl

/-! ### The two-coefficient corollary (the `TraceAgreementData` shape)

For the trace assembly we have two coefficients `h₁ = Tr_F α` and `h₂ = L.R`; their difference is the
*holomorphic remainder* (entire, holomorphic across `∞`).  The Liouville vanishing gives `h₁ = h₂`
everywhere — both as functions on `ℂ` (finite-chart germ-agreement) and, taking `recipCoeff`, off `0`
in the reciprocal chart (`∞`-germ-agreement). -/

/-- **Two-coefficient Liouville agreement.**  If the difference `h₁ − h₂` is entire and its reciprocal
coefficient is continuous at `0` (the remainder is a global holomorphic form), then `h₁ = h₂` on **all
of `ℂ`**.  *Proof.*  `h₁ − h₂ = 0` by `coeff_eq_zero_of_entire_of_recipCoeff_continuousAt`. -/
theorem coeff_eq_of_entire_diff_of_recipCoeff_continuousAt {h₁ h₂ : ℂ → ℂ}
    (hdiff : AnalyticOnNhd ℂ (h₁ - h₂) Set.univ)
    (hrecip : ContinuousAt (recipCoeff (h₁ - h₂)) 0) :
    h₁ = h₂ := by
  have h0 : h₁ - h₂ = 0 := coeff_eq_zero_of_entire_of_recipCoeff_continuousAt hdiff hrecip
  funext z
  have := congrFun h0 z
  simpa [sub_eq_zero] using this

/-- **Finite-chart germ-agreement** from the Liouville agreement: at every finite point `p`, the two
coefficients germ-agree on the punctured neighbourhood `𝓝[≠] p` (in fact they are equal everywhere).
This is the `hagree_fin`-shaped output. -/
theorem coeff_eventuallyEq_of_entire_diff {h₁ h₂ : ℂ → ℂ}
    (hdiff : AnalyticOnNhd ℂ (h₁ - h₂) Set.univ)
    (hrecip : ContinuousAt (recipCoeff (h₁ - h₂)) 0) (p : ℂ) :
    h₁ =ᶠ[𝓝[≠] p] h₂ := by
  have heq : h₁ = h₂ := coeff_eq_of_entire_diff_of_recipCoeff_continuousAt hdiff hrecip
  rw [heq]

/-- **Reciprocal-chart germ-agreement** from the Liouville agreement: `recipCoeff h₁` and
`recipCoeff h₂` germ-agree on `𝓝[≠] 0` (the reciprocal chart matches off the centre).  Since `h₁ = h₂`
everywhere, `recipCoeff h₁ = recipCoeff h₂` everywhere, in particular near `0`.  This is the
`hagree_inf`-shaped output. -/
theorem recipCoeff_eventuallyEq_of_entire_diff {h₁ h₂ : ℂ → ℂ}
    (hdiff : AnalyticOnNhd ℂ (h₁ - h₂) Set.univ)
    (hrecip : ContinuousAt (recipCoeff (h₁ - h₂)) 0) :
    recipCoeff h₁ =ᶠ[𝓝[≠] 0] recipCoeff h₂ := by
  have heq : h₁ = h₂ := coeff_eq_of_entire_diff_of_recipCoeff_continuousAt hdiff hrecip
  rw [heq]

end Jacobians.Dolbeault.FormTraceLiouville
