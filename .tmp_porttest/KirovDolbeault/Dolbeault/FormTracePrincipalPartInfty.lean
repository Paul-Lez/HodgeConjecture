/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTracePrincipalPart
import KirovDolbeault.Dolbeault.FormTraceInftyRecip

/-!
# Principal-part extraction across `∞` for the global trace (Gate A, §VIII.3 step 3 — `∞` part)

`Jacobians.Dolbeault.FormTracePrincipalPart` extracts the finite principal parts of the global trace
coefficient `T : ℂ → ℂ`.  Miranda §VIII.3 step 3 also subtracts the **polynomial part at `∞`** to leave
a *global* holomorphic form on the compact `ℂℙ¹`, vanishing by kirovGenus-`0` Liouville
(`FormTraceLiouville`).  The `∞` chart is the reciprocal chart `ζ = 1/z`, in which the coefficient is
`recipCoeff T` (`FormTraceInftyRecip`); holomorphy at `∞` is continuity of `recipCoeff (T − L.R)` at
`0` (the `GlobalTrace.hrecip` field).

This file provides the `∞`-chart analogue of the finite extraction: `recipCoeff` is **linear**, its
value at `0` is always the junk `0` (the `0^{-2}` Jacobian), and a reciprocal-chart remainder whose
analytic continuation **vanishes at `0`** is continuous at `0` (continuity to that junk value).  The
last fact is the precise, honest shape of `GlobalTrace.hrecip`: the `hrecip` continuity is *equivalent*
to the analytic continuation of `recipCoeff (T − L.R)` vanishing at `0`, i.e. the holomorphic remainder
having no `dζ`-term at `∞`.  Because a holomorphic `1`-form on `ℂℙ¹` is `0` (kirovGenus `0`), this is
genuine §VIII.3 content — not mechanically dischargeable from meromorphy alone — so `hrecip` correctly
remains part of the irreducible global-trace obligation (its analogue `hentire` is dischargeable once
`T` is junk-free, via `exists_entire_of_finitePoles`).

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `recipCoeff_sub` — `recipCoeff` is additive over subtraction (`recipCoeff (R₁ − R₂) = recipCoeff R₁ −
  recipCoeff R₂`).
* `recipCoeff_zero_eval` — `recipCoeff h 0 = 0` for every `h` (the junk `0^{-2}` Jacobian), so the
  `hrecip` continuity is to value `0`.
* `continuousAt_recipRemainder_of_vanishing` — given a reciprocal-chart principal part `negTail 0 b N`
  with analytic continuation `R` of the remainder, if `R 0 = 0` (the holomorphic remainder vanishes at
  `∞`) then `recipCoeff T − negTail 0 b N` is continuous at `0` — exactly `GlobalTrace.hrecip` once
  `recipCoeff L.R` germ-matches `negTail 0 b N`.  This isolates `R 0 = 0` as the irreducible `∞`
  obligation.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`; rationality on `ℂℙ¹`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Filter Topology

namespace Jacobians.Dolbeault.FormTracePrincipalPart

open Jacobians.Dolbeault Jacobians.Dolbeault.FormTraceInftyRecip

/-- **`recipCoeff` is additive over subtraction.**  `recipCoeff (R₁ − R₂) = recipCoeff R₁ −
recipCoeff R₂` (the reciprocal-chart coefficient `ζ ↦ −R(ζ⁻¹)·ζ⁻²` is `ℂ`-linear in `R`). -/
theorem recipCoeff_sub (R₁ R₂ : ℂ → ℂ) :
    recipCoeff (R₁ - R₂) = recipCoeff R₁ - recipCoeff R₂ := by
  funext ζ
  simp only [recipCoeff, Pi.sub_apply]
  ring

/-! ### The junk value of `recipCoeff` at `0`

`recipCoeff h 0 = 0` for every `h` (the `0^{-2}` Jacobian factor is junk-zero in Lean).  Hence the
`GlobalTrace.hrecip` condition `ContinuousAt (recipCoeff (T − L.R)) 0` is precisely "`recipCoeff
(T − L.R)` *tends to `0`* at `0`", i.e. the analytic continuation of the reciprocal coefficient of the
holomorphic remainder *vanishes at `∞`* — the kirovGenus-`0` holomorphic-remainder content (a holomorphic
`1`-form on `ℂℙ¹` has no `dζ`-term at `∞` only if it is `0`).  This is the irreducible §VIII.3 input
that `FormTraceLiouville` consumes; it is *not* mechanically dischargeable from meromorphy alone. -/

/-- **The junk value `recipCoeff h 0 = 0`.**  The `ζ ^ (−2)` factor evaluates to `0` at `ζ = 0`
(`0 ^ (−2 : ℤ) = (0²)⁻¹ = 0` in `ℂ`), so `recipCoeff h 0 = −h(0)·0 = 0`. -/
@[simp] theorem recipCoeff_zero_eval (h : ℂ → ℂ) : recipCoeff h 0 = 0 := by
  show -(h (0⁻¹)) * (0 : ℂ) ^ (-2 : ℤ) = 0
  rw [zpow_neg, zpow_two, mul_zero, inv_zero, mul_zero]

/-- **Reciprocal-chart `hrecip` from a vanishing analytic continuation.**  Suppose `recipCoeff T` is
`MeromorphicAt 0`, with reciprocal-chart principal part `negTail 0 b N` (from
`exists_principalPart_meromorphicAt`) and analytic continuation `R` of the remainder.  If that analytic
continuation *vanishes at `0`* (`hR0 : R 0 = 0` — the holomorphic remainder has no `dζ`-term at `∞`,
the kirovGenus-`0` content), then `recipCoeff T − negTail 0 b N` is **continuous at `0`** (continuity to the
junk value `0`).  This is the precise, honest shape of `GlobalTrace.hrecip`: it isolates `R 0 = 0` as
the single irreducible §VIII.3 obligation at `∞`. -/
theorem continuousAt_recipRemainder_of_vanishing {T : ℂ → ℂ} {N : ℕ} {b : ℕ → ℂ} {R : ℂ → ℂ}
    (hR_an : AnalyticAt ℂ R 0) (hR0 : R 0 = 0)
    (hR_eq : recipCoeff T =ᶠ[𝓝[≠] 0] fun ζ => negTail 0 b N ζ + R ζ) :
    ContinuousAt (fun ζ => recipCoeff T ζ - negTail 0 b N ζ) 0 := by
  -- Off `0`, the remainder equals `R`; at `0` both equal `0` (junk value of `recipCoeff`, `R 0 = 0`).
  -- Value at `0`: `recipCoeff T 0 − negTail 0 b N 0 = 0 − 0 = 0 = R 0`.
  have hnegTail0 : negTail 0 b N 0 = 0 := by
    show ∑ k ∈ Finset.Icc 1 N, b k * ((0 : ℂ) - 0) ^ (-(k : ℤ)) = 0
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [sub_zero, zpow_neg, zpow_natCast, zero_pow (by omega), inv_zero, mul_zero]
  have hval0 : recipCoeff T 0 - negTail 0 b N 0 = R 0 := by
    rw [recipCoeff_zero_eval, hnegTail0, sub_zero, hR0]
  rw [ContinuousAt]
  show Tendsto (fun ζ => recipCoeff T ζ - negTail 0 b N ζ) (𝓝 0) (𝓝 (recipCoeff T 0 - negTail 0 b N 0))
  rw [hval0, ← nhdsNE_sup_pure (0 : ℂ), tendsto_sup]
  refine ⟨?_, ?_⟩
  · -- along `𝓝[≠] 0`: agreement off `0` with the continuous `R`.
    refine (hR_an.continuousAt.continuousWithinAt.tendsto).congr' ?_
    filter_upwards [hR_eq] with ζ hζ
    simp only [hζ]; ring
  · -- along `pure 0`: the value at `0` is `R 0`.
    rw [tendsto_pure_left]
    intro s hs
    show recipCoeff T 0 - negTail 0 b N 0 ∈ s
    rw [hval0]
    exact mem_of_mem_nhds hs

end Jacobians.Dolbeault.FormTracePrincipalPart
