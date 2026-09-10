/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.TraceResidue
import KirovDolbeault.MeromorphicTrace
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The reciprocal-chart residue at `∞` (Gate A, §VIII.3 step 5 — the `infty_eq` close-path)

The `infty_eq` field of `TraceRationalityWitness` (the genuinely-irreducible §VIII.3 atom — see
`Jacobians.Dolbeault.FormTraceRationalReduce`) needs the residue at infinity of the rational trace
`L.R` read as a residue at `0` in the **reciprocal chart** `ζ = 1/z` of `ℂℙ¹`.  Under `z = 1/ζ` the
`1`-form `R(z) dz` becomes `R(1/ζ)·(−1/ζ²) dζ`, so its residue at `∞` is the residue at `0` of the
**reciprocal coefficient** `recipCoeff R ζ := −R(ζ⁻¹)·ζ⁻²`.

This file proves the **one-variable bridge** that turns `resAtInfty L.R L.ρ` into a residue at `0`:

> `resAtInfty L.R L.ρ = resAt (recipCoeff L.R) 0`,

reducing the `infty_eq` field to a Lemma-3.2-at-`0` statement (the residue of the reciprocal-chart
trace coefficient at `0` = the `∞`-fibre residue sum), structurally identical to the *proved*
finite-centre Lemma 3.2 (`FormTraceFibre.resAt_traceCoeff_fibreTrace`).

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

The per-monomial reciprocal residue, in all three exponent ranges:

* `resAt_recipMonomial` — for any `c a : ℂ`, `n : ℤ`:
  `resAt (fun ζ => −(c·(ζ⁻¹ − a)^n)·ζ⁻²) 0 = if n = −1 then −c else 0`,
  the residue at `0` of the reciprocal of the Laurent monomial `c·(z − a)^n`.  Built from
  `resAt_inv_sub_mul` (simple pole `n = −1`, residue `−c`), an analytic-at-`0` argument
  (`n ≤ −2`, residue `0`), and a binomial-expansion sum of below-`−1` monomials (`n ≥ 0`,
  residue `0`).
* `resAtInfty_eq_resAt_recipCoeff` — the `LaurentForm`-level bridge
  `resAtInfty L.R L.ρ = resAt (recipCoeff L.R) 0`, by termwise additivity (`resAt_finsum`) matched
  against `LaurentForm.resAtInfty_eq` (`= −∑_{n i = −1} c i`).

## What remains for `infty_eq` (the residual obligation)

With this bridge, `infty_eq` reduces to: **the residue at `0` of the reciprocal-chart trace
coefficient is the `∞`-fibre residue sum** — Lemma 3.2 in the reciprocal chart at the pole fibre.
This is the genuine §VIII.3 content at `∞`, and it parallels the finite-centre case exactly (the same
`resAt_traceCoeff'` machinery, applied to the reciprocal-chart fibre data over `0`), modulo the global
trace construction.  See `Jacobians.Dolbeault.FormTraceRationalReduce` for the diagnosis.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; the residue
  at infinity).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Real

namespace Jacobians.Dolbeault.FormTraceInftyRecip

open Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

/-! ### The reciprocal coefficient

For a `dz`-coefficient `R : ℂ → ℂ`, the reciprocal-chart coefficient (the `dζ`-coefficient of the
same `1`-form read in `ζ = 1/z`, up to the `−ζ⁻²` Jacobian of `z = 1/ζ`). -/

/-- The **reciprocal-chart coefficient** of `R`: `recipCoeff R ζ := −R(ζ⁻¹)·ζ⁻²`.  Its residue at `0`
is the residue at infinity of `R dz` (the `z = 1/ζ` change of chart). -/
def recipCoeff (R : ℂ → ℂ) : ℂ → ℂ := fun ζ => -(R (ζ⁻¹)) * ζ ^ (-2 : ℤ)

/-! ### The per-monomial reciprocal residue (all three exponent ranges) -/

/-- **Simple-pole reciprocal residue (`n = −1`).**  `resAt (recip of c·(z−a)⁻¹) 0 = −c`.
Off `0`, the reciprocal `−c·(ζ⁻¹ − a)⁻¹·ζ⁻²` simplifies to `(ζ − 0)⁻¹·(−c·(1 − aζ)⁻¹)`, a simple pole
with analytic numerator `−c·(1 − aζ)⁻¹` of value `−c` at `0` (Cauchy, `resAt_inv_sub_mul`). -/
theorem resAt_recip_simplePole (c a : ℂ) :
    resAt (fun ζ => -(c * (ζ⁻¹ - a) ^ (-1 : ℤ)) * ζ ^ (-2 : ℤ)) 0 = -c := by
  have hH : AnalyticAt ℂ (fun ζ => -c * (1 - a * ζ)⁻¹) 0 := by
    apply AnalyticAt.mul analyticAt_const
    apply AnalyticAt.inv
    · fun_prop
    · simp
  rw [resAt_congr (g := fun ζ => (ζ - 0)⁻¹ * ((fun ζ => -c * (1 - a * ζ)⁻¹) ζ)) ?_]
  · rw [resAt_inv_sub_mul hH]; simp
  · -- germ equality off `0`
    have h1 : ∀ᶠ ζ in 𝓝[≠] (0:ℂ), (1 - a * ζ) ≠ 0 := by
      have hc : ContinuousAt (fun ζ : ℂ => 1 - a * ζ) 0 := by fun_prop
      have hne1 : (fun ζ : ℂ => 1 - a * ζ) 0 ≠ 0 := by simp
      filter_upwards [nhdsWithin_le_nhds (hc.eventually_ne hne1)] with ζ hζ; exact hζ
    filter_upwards [self_mem_nhdsWithin, h1] with ζ hζ0 hζ1
    have hζne : ζ ≠ 0 := by simpa using hζ0
    show -(c * (ζ⁻¹ - a) ^ (-1 : ℤ)) * ζ ^ (-2 : ℤ) = (ζ - 0)⁻¹ * (-c * (1 - a * ζ)⁻¹)
    rw [zpow_neg_one, show (ζ ^ (-2 : ℤ)) = (ζ ^ 2)⁻¹ from by rw [zpow_neg, zpow_two, ← sq]]
    have hkey : (ζ⁻¹ - a)⁻¹ = ζ * (1 - a * ζ)⁻¹ := by
      have hrw : ζ⁻¹ - a = (1 - a * ζ) * ζ⁻¹ := by field_simp
      rw [hrw, mul_inv, inv_inv]; ring
    rw [hkey, sub_zero, sq]
    field_simp

/-- **Deep-pole reciprocal residue (`n ≤ −2`).**  `resAt (recip of c·(z−a)^{−m}) 0 = 0` for `m ≥ 2`.
Off `0`, the reciprocal is `−c·(1 − aζ)^{−m}·ζ^{m−2}`, **analytic at `0`** (`m − 2 ≥ 0`, and
`(1 − aζ)^{−m}` analytic since `1 ≠ 0`), hence residue `0`. -/
theorem resAt_recip_negpow (c a : ℂ) (m : ℕ) (hm : 2 ≤ m) :
    resAt (fun ζ => -(c * (ζ⁻¹ - a) ^ (-(m:ℤ))) * ζ ^ (-2 : ℤ)) 0 = 0 := by
  set H : ℂ → ℂ := fun ζ => -c * (1 - a * ζ) ^ (-(m:ℤ)) * ζ ^ ((m:ℤ) - 2) with hH
  have hHana : AnalyticAt ℂ H 0 := by
    apply AnalyticAt.mul
    · apply AnalyticAt.mul analyticAt_const
      have hbase : AnalyticAt ℂ (fun ζ : ℂ => 1 - a * ζ) 0 := by fun_prop
      exact hbase.zpow (z := 0) (n := -(m:ℤ)) (show (1 : ℂ) - a * 0 ≠ 0 by simp)
    · have hmm : ((m:ℤ) - 2) = ((m - 2 : ℕ) : ℤ) := by omega
      rw [hmm]; simp only [zpow_natCast]; fun_prop
  rw [resAt_congr (g := H) ?_, resAt_eq_zero_of_analyticAt hHana]
  have h1 : ∀ᶠ ζ in 𝓝[≠] (0:ℂ), (1 - a * ζ) ≠ 0 := by
    have hc : ContinuousAt (fun ζ : ℂ => 1 - a * ζ) 0 := by fun_prop
    have hne1 : (fun ζ : ℂ => 1 - a * ζ) 0 ≠ 0 := by simp
    filter_upwards [nhdsWithin_le_nhds (hc.eventually_ne hne1)] with ζ hζ; exact hζ
  filter_upwards [self_mem_nhdsWithin, h1] with ζ hζ0 hζ1
  have hζne : ζ ≠ 0 := by simpa using hζ0
  show -(c * (ζ⁻¹ - a) ^ (-(m:ℤ))) * ζ ^ (-2 : ℤ) = H ζ
  rw [hH]
  have hkey : (ζ⁻¹ - a) = (1 - a * ζ) * ζ⁻¹ := by field_simp
  rw [hkey, mul_zpow, inv_zpow, ← zpow_neg]
  simp only []
  rw [show (-(-(m:ℤ))) = (m:ℤ) from by ring]
  rw [show ((m:ℤ) - 2) = (m:ℤ) + (-2 : ℤ) from by ring, zpow_add₀ hζne]
  ring

/-- **Polynomial-numerator reciprocal residue (`n ≥ 0`).**  `resAt (recip of c·(z−a)^n) 0 = 0`.
Off `0`, the binomial expansion makes the reciprocal a finite sum of monomials `ζ^{k−n−2}` with
`k ∈ [0, n]`, all exponents `≤ −2 ≠ −1`, so every term has residue `0` (`resAt_laurentMonomial`). -/
theorem resAt_recip_pospow (c a : ℂ) (n : ℕ) :
    resAt (fun ζ => -(c * (ζ⁻¹ - a) ^ (n:ℤ)) * ζ ^ (-2 : ℤ)) 0 = 0 := by
  set F : ℂ → ℂ := fun ζ =>
    ∑ k ∈ Finset.range (n + 1),
      (-c * ((n.choose k : ℂ) * (-a) ^ k)) * (ζ - 0) ^ ((k : ℤ) - n - 2) with hF
  rw [resAt_congr (g := F) ?_]
  · rw [hF, LaurentForm.resAt_finsum (Finset.range (n + 1))
      (fun k ζ => (-c * ((n.choose k : ℂ) * (-a) ^ k)) * (ζ - 0) ^ ((k : ℤ) - n - 2)) ?_]
    · apply Finset.sum_eq_zero
      intro k hk
      have hkle : (k : ℤ) ≤ n := by have := Finset.mem_range.mp hk; omega
      have hne : ((k : ℤ) - n - 2) ≠ -1 := by omega
      rw [resAt_laurentMonomial, if_neg hne]
    · intro k _
      exact (TraceResidue.LaurentForm.meromorphicAt_monomial
        (-c * ((n.choose k : ℂ) * (-a) ^ k)) 0 ((k : ℤ) - n - 2) 0)
  · filter_upwards [self_mem_nhdsWithin] with ζ hζ0
    have hζne : ζ ≠ 0 := by simpa using hζ0
    show -(c * (ζ⁻¹ - a) ^ (n:ℤ)) * ζ ^ (-2 : ℤ) = F ζ
    rw [hF]
    simp only [sub_zero]
    rw [zpow_natCast, sub_eq_add_neg, add_comm, add_pow]
    rw [show (-(c * ∑ k ∈ Finset.range (n + 1), (-a) ^ k * ζ⁻¹ ^ (n - k) * (n.choose k : ℂ))
          * ζ ^ (-2 : ℤ))
        = ∑ k ∈ Finset.range (n + 1),
            (-c * ((n.choose k : ℂ) * (-a) ^ k)) * (ζ⁻¹ ^ (n - k) * ζ ^ (-2 : ℤ)) from by
      rw [Finset.mul_sum, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro k _; ring]
    apply Finset.sum_congr rfl
    intro k hk
    have hkle : k ≤ n := by have := Finset.mem_range.mp hk; omega
    congr 1
    rw [show ((ζ⁻¹ : ℂ)) = ζ ^ (-1 : ℤ) from by rw [zpow_neg_one]]
    rw [← zpow_natCast (ζ ^ (-1:ℤ)) (n - k), ← zpow_mul,
      show ((-1 : ℤ) * ((n - k : ℕ) : ℤ)) = (k : ℤ) - n from by
        rw [Nat.cast_sub hkle]; ring,
      ← zpow_add₀ hζne]
    norm_num [sub_eq_add_neg]

/-- **The per-monomial reciprocal residue (unified, any `n : ℤ`).**  The residue at `0` of the
reciprocal of the Laurent monomial `c·(z − a)^n` is `−c` if `n = −1` and `0` otherwise:

> `resAt (fun ζ => −(c·(ζ⁻¹ − a)^n)·ζ⁻²) 0 = if n = −1 then −c else 0`.

This is exactly the per-monomial contribution to the residue at infinity (`resAtInfty` of
`c·(z − a)^n` is `−c` if `n = −1` else `0`), confirming the reciprocal-chart picture termwise. -/
theorem resAt_recipMonomial (c a : ℂ) (n : ℤ) :
    resAt (fun ζ => -(c * (ζ⁻¹ - a) ^ n) * ζ ^ (-2 : ℤ)) 0 = if n = -1 then -c else 0 := by
  rcases lt_trichotomy n (-1) with hlt | heq | hgt
  · -- `n ≤ −2`: write `n = −m`, `m ≥ 2`.
    rw [if_neg (by omega)]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    subst hm
    exact resAt_recip_negpow c a m (by omega)
  · -- `n = −1`.
    subst heq; rw [if_pos rfl]; exact resAt_recip_simplePole c a
  · -- `n ≥ 0`.
    rw [if_neg (by omega)]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
    subst hm
    exact resAt_recip_pospow c a m

/-! ### The `LaurentForm`-level bridge `resAtInfty L.R = resAt (recipCoeff L.R) 0`

`L.R` is a finite sum of monomials, so `recipCoeff L.R` is the sum of the per-monomial reciprocals,
and `resAt` is additive (`resAt_finsum`).  Each monomial contributes `−c i` if `n i = −1`, else `0`
(`resAt_recipMonomial`), so the total is `−∑_{n i = −1} c i`, which is exactly `resAtInfty L.R L.ρ`
(`LaurentForm.resAtInfty_eq`). -/

/-- **The reciprocal coefficient of a `LaurentForm` splits over its monomials.** -/
theorem recipCoeff_R (L : LaurentForm) :
    recipCoeff L.R = fun ζ => ∑ i, (fun ζ => -(L.c i * (ζ⁻¹ - L.a i) ^ L.n i) * ζ ^ (-2 : ℤ)) ζ := by
  funext ζ
  simp only [recipCoeff, LaurentForm.R, Finset.sum_mul, neg_mul, ← Finset.sum_neg_distrib]

/-- **The residue-at-infinity reciprocal-chart bridge.**  For a `LaurentForm L`, the residue at
infinity of its rational coefficient equals the residue at `0` of the reciprocal-chart coefficient:

> `resAtInfty L.R L.ρ = resAt (recipCoeff L.R) 0`.

*Proof.*  `recipCoeff L.R` is the finite sum of the per-monomial reciprocals (`recipCoeff_R`); by
`resAt_finsum` and `resAt_recipMonomial` its residue at `0` is `∑ᵢ (if n i = −1 then −c i else 0)
= −∑_{n i = −1} c i`, which is `resAtInfty L.R L.ρ` by `LaurentForm.resAtInfty_eq`.  This turns the
`infty_eq` field into a Lemma-3.2-at-`0` statement in the reciprocal chart. -/
theorem resAtInfty_eq_resAt_recipCoeff (L : LaurentForm) :
    resAtInfty L.R L.ρ = resAt (recipCoeff L.R) 0 := by
  classical
  rw [L.resAtInfty_eq, recipCoeff_R,
    LaurentForm.resAt_finsum Finset.univ
      (fun i ζ => -(L.c i * (ζ⁻¹ - L.a i) ^ L.n i) * ζ ^ (-2 : ℤ))
      (fun i _ => by
        -- each reciprocal monomial is meromorphic at `0`
        have hbase : MeromorphicAt (fun ζ : ℂ => (ζ⁻¹ - L.a i) ^ L.n i) 0 :=
          ((analyticAt_id.meromorphicAt).inv.sub (MeromorphicAt.const _ _)).zpow _
        have h1 : MeromorphicAt (fun ζ : ℂ => -(L.c i * (ζ⁻¹ - L.a i) ^ L.n i)) 0 :=
          (((MeromorphicAt.const (L.c i) 0).mul hbase)).neg
        exact h1.mul ((analyticAt_id.meromorphicAt).zpow _))]
  simp_rw [resAt_recipMonomial]
  -- `∑ᵢ (if n i = −1 then −c i else 0) = −∑_{n i = −1} c i`.
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib]

end Jacobians.Dolbeault.FormTraceInftyRecip
