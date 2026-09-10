/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.TraceResidue
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.GeomSum

/-!
# The ramified residue change-of-variables (Miranda §VIII.3, formula (3.1) + Lemma 3.2 ramified case)

This file builds the **ramified** trace / residue change-of-variables for the local branched cover
`z = wᵐ` (`m ≥ 1`).  It is the keystone atom that lets Gate A handle pole fibres lying over a
*ramification* value of the cover `F` — the case the repo's **unramified** Lemma 3.2
`Jacobians.MeromorphicTrace.FibreTrace.resAt_traceCoeff'` (which models a fibre as `m` distinct
biholomorphic sheets, `deriv (sheet i) b ≠ 0`) cannot express.

## The geometric picture (Miranda §VIII.3, pp. 252–253)

Over a value `q` with a single preimage `p` of multiplicity `m`, choose centered coordinates so the
cover is `z = wᵐ`.  Write the upstairs `1`-form `α = h(w) dw`, with `h` a Laurent series
`Σₙ cₙ wⁿ`.  The **trace** `Tr_m(α)` is the sum over the `m` sheets `w = ζ^j · z^{1/m}`
(`ζ` a primitive `m`-th root of unity).  On sheet `j`, `w = ζ^j w₀` with `w₀ := z^{1/m}` a fixed
branch, and `dw = ζ^j · w₀'(z) dz` with `w₀'(z) = (1/m) w₀^{1-m}` (from `m w₀^{m-1} w₀' = 1`).  Hence
the `dz`-coefficient of sheet `j` is `c·(ζ^j w₀)^n · ζ^j · (1/m) w₀^{1-m}`.  Summing over `j`, the
cross-terms collapse via the **roots-of-unity sum** `∑_{j<m} (ζ^j)^{n+1} = m·[m ∣ n+1]`
(`rootsOfUnity_geom_zsum`), leaving Miranda's

> **(3.1)** `Tr_m(α) = Σₖ c_{km−1} z^{k−1} dz`,    hence    **`Res_{z=0}(Tr_m α) = c_{−1} = Res_{w=0}(α)`**

(the surviving `k = 0` term).  This is **Lemma 3.2** at a ramified fibre.

## The proof route — roots of unity, not contour substitution

Mathlib has **no** `circleIntegral` change-of-variables / winding-number invariance (the repo's
unramified `Jacobians.ResidueChangeOfVariables` works around it via holomorphic primitives, which
needs `deriv ≠ 0`, i.e. the unramified case).  So we do the trace **algebraically**: the per-sheet
`dz`-coefficient of a single Laurent monomial `c·wⁿ` sums, by `rootsOfUnity_geom_zsum`, to the
explicit closed-form `dz`-monomial `monomialTraceCoeff` — a single Laurent monomial in `z` whose
residue is read off directly (`resAt_laurentMonomial`).  No branch of `z^{1/m}` is needed for the
residue read-off; the branch enters only in `monomialTraceCoeff_eq_sheetSum`, the explicit (3.1)
**soundness** identity certifying the closed form *is* the `m`-sheet sum.

## ⚠ Soundness — the trace is the `m`-sheet SUM, never a single sheet

A *single* sheet's pushforward under `w ↦ wᵐ` has residue `m·Res_w`, **not** `Res_w`
(e.g. `h = w⁻¹`, sheet `w₀`: `h(w₀) w₀' = (1/m) z⁻¹`, residue `1/m`, not `1`).  The upstairs residue
is recovered ONLY by the `m`-branch SUM, whose roots-of-unity factor `∑_{j<m}(ζ^j)^0 = m` cancels the
`1/m`.  Accordingly **every** statement here is about the SUM over `range m`; there is no
"single-sheet residue = upstairs residue" lemma (that would be a *false field*).  Sanity:
`m = 2, h = w⁻¹ (n=-1)` gives `monomialTraceCoeff = z⁻¹`, residue `1 = Res_w`;
`m = 2, h = w⁻³ (n=-3)` gives `monomialTraceCoeff = z⁻²`, residue `0 = Res_w(w⁻³)`.

## What is proved here (complete, axiom-clean)

* **`rootsOfUnity_geom_zsum`** — `∑_{j<m}(ζ^j)^N = m·[m ∣ N]` for `ζ` a primitive `m`-th root, `N : ℤ`
  (the cross-term collapse; `geom_sum_eq` + `IsPrimitiveRoot.zpow_eq_one_iff_dvd`).
* **`monomialTraceCoeff`** — the closed-form `dz`-coefficient of `Tr_m(c·wⁿ)`: `c·z^{(n+1)/m−1}` if
  `m ∣ n+1`, else `0` (a single Laurent monomial in `z`).
* **`resAt_monomialTraceCoeff`** — `Res_{z=0}(Tr_m(c·wⁿ)) = Res_{w=0}(c·wⁿ)` (`= c·[n=−1]`).
* **`monomialTraceCoeff_eq_sheetSum`** — the (3.1) **soundness** identity: the closed form equals the
  honest `m`-sheet sum `∑_{j<m} c·(ζ^j w₀)^n · ζ^j · (1/m) w₀^{1−m}` at `z = w₀ᵐ` (`w₀ ≠ 0`).
* **`laurentTraceCoeff` / `resAt_laurentTraceCoeff` / `laurentTraceCoeff_eq_sheetSum`** — the same,
  summed over a finite Laurent principal part `h = ∑_i c_i wⁿⁱ`: the trace residue at `z=0` equals the
  upstairs residue `∑_{i : n_i = −1} c_i`, and the closed form is the `m`-sheet sum of `h`.  This is
  the full ramified Lemma 3.2 at the level of a Laurent polynomial (the residue only sees the
  principal part, so this covers any meromorphic `α`).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3, pp. 252–253 (the trace `Tr`, formula
  **(3.1)**, Lemma 3.2 ramified case).
* `Jacobians/ResidueChangeOfVariables.lean` — the **unramified** (`m = 1`) template.
-/

open Complex Metric Filter Topology Finset
open scoped Real

namespace Jacobians.RamifiedTrace

open Jacobians.Dolbeault Jacobians.TraceResidue

/-! ### The roots-of-unity sum (the cross-term collapse)

The single algebraic fact that makes the `m`-sheet trace single-valued in `z = wᵐ`: summing the
`(n+1)`-th powers of the `m`-th roots of unity gives `m` exactly when `m ∣ n+1`, and `0` otherwise.
For `m ∣ n+1` every term is `1`; otherwise `ζ^{n+1} ≠ 1` and the geometric sum
`∑_{j<m}(ζ^{n+1})^j = ((ζ^{n+1})^m − 1)/(ζ^{n+1} − 1) = 0`. -/

/-- **The roots-of-unity power sum (integer exponent).**  For `ζ` a primitive `m`-th root of unity
and `N : ℤ`,

> `∑_{j ∈ range m} (ζ^j)^N = if (m : ℤ) ∣ N then (m : ℂ) else 0`.

The Miranda §VIII.3 cross-term cancellation: among the `m` sheets, only the powers `N = n+1` divisible
by `m` survive (giving the trace its `z^{k−1}` terms). -/
theorem rootsOfUnity_geom_zsum {m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (N : ℤ) :
    (∑ j ∈ range m, (ζ ^ j) ^ N) = if ((m : ℤ) ∣ N) then (m : ℂ) else 0 := by
  -- `(ζ^j)^N = (ζ^N)^j`, reducing to a geometric sum in `x := ζ^N`.
  have hstep : ∀ j : ℕ, (ζ ^ j) ^ N = (ζ ^ N) ^ j := by
    intro j; rw [← zpow_natCast ζ j, ← zpow_mul, ← zpow_natCast (ζ ^ N) j, ← zpow_mul, mul_comm]
  simp_rw [hstep]
  by_cases hdvd : (m : ℤ) ∣ N
  · -- `m ∣ N`: `ζ^N = 1`, every term is `1`, sum `= m`.
    rw [if_pos hdvd, (hζ.zpow_eq_one_iff_dvd N).mpr hdvd]; simp
  · -- `m ∤ N`: `ζ^N ≠ 1`, the geometric sum vanishes (numerator `(ζ^N)^m − 1 = 0`).
    rw [if_neg hdvd]
    have hne : ζ ^ N ≠ 1 := fun h => hdvd ((hζ.zpow_eq_one_iff_dvd N).mp h)
    rw [geom_sum_eq hne m]
    have hzero : (ζ ^ N) ^ m = 1 := by
      rw [← zpow_natCast (ζ ^ N) m, ← zpow_mul, mul_comm, zpow_mul, hζ.zpow_eq_one, one_zpow]
    rw [hzero, sub_self, zero_div]

/-! ### The closed-form trace coefficient of a single Laurent monomial, and its residue

`monomialTraceCoeff c n m` is the `dz`-coefficient of `Tr_m(c·wⁿ)` as a function of `z`: by (3.1) it
is the single Laurent monomial `c·z^{(n+1)/m − 1}` if `m ∣ n+1` (the only surviving term), and `0`
otherwise.  Its residue at `z = 0` is read off by `resAt_laurentMonomial`: it is `c` exactly when the
`z`-exponent `(n+1)/m − 1 = −1`, i.e. `(n+1)/m = 0`, i.e. (given `m ∣ n+1`, `m > 0`) `n + 1 = 0`, i.e.
`n = −1` — exactly `Res_{w=0}(c·wⁿ)`. -/

/-- **The closed-form `dz`-coefficient of `Tr_m(c·wⁿ)`** (Miranda (3.1)): the single Laurent monomial
`c·z^{(n+1)/m − 1}` if `m ∣ n+1`, else `0`.  Soundness (that this *is* the `m`-sheet sum) is
`monomialTraceCoeff_eq_sheetSum`. -/
noncomputable def monomialTraceCoeff (c : ℂ) (n : ℤ) (m : ℕ) : ℂ → ℂ :=
  fun z => if (m : ℤ) ∣ (n + 1) then c * z ^ ((n + 1) / (m : ℤ) - 1) else 0

/-- **Ramified Lemma 3.2 for a single Laurent monomial.**  The residue at `z = 0` of the ramified
trace of `c·wⁿ` equals its upstairs residue:

> `Res_{z=0}(Tr_m(c·wⁿ)) = resAt (fun w => c·(w − 0)ⁿ) 0 = if n = −1 then c else 0`.

The `k = 0` (`n = −1`) term of (3.1).  *Note* the residue is `c` (not `m·c`): the `1/m` of the chain
rule is exactly cancelled by the `m` surviving sheets — the soundness point. -/
theorem resAt_monomialTraceCoeff (c : ℂ) (n : ℤ) {m : ℕ} (hm : 0 < m) :
    resAt (monomialTraceCoeff c n m) 0 = resAt (fun w => c * (w - 0) ^ n) 0 := by
  rw [resAt_laurentMonomial]
  unfold monomialTraceCoeff
  by_cases hdvd : (m : ℤ) ∣ (n + 1)
  · simp only [hdvd, if_true]
    -- closed form is the Laurent monomial `c·(z − 0)^{(n+1)/m − 1}`.
    rw [show (fun z : ℂ => c * z ^ ((n + 1) / (m : ℤ) - 1))
          = (fun z => c * (z - 0) ^ ((n + 1) / (m : ℤ) - 1)) by funext z; rw [sub_zero]]
    rw [resAt_laurentMonomial]
    by_cases hn : n = -1
    · -- `n = −1`: exponent `(0)/m − 1 = −1`, residue `c`.
      subst hn
      rw [if_pos (show ((-1 : ℤ) + 1) / (m : ℤ) - 1 = -1 by simp), if_pos rfl]
    · -- `n ≠ −1`: then `n + 1 ≠ 0`, and `m ∣ n+1` forces `(n+1)/m ≠ 0`, so exponent `≠ −1`.
      rw [if_neg hn]
      have hn1 : n + 1 ≠ 0 := fun h => hn (by omega)
      obtain ⟨k, hk⟩ := hdvd
      have hk0 : k ≠ 0 := by rintro rfl; rw [hk, mul_zero] at hn1; exact hn1 rfl
      have hkval : (n + 1) / (m : ℤ) = k := by rw [hk, Int.mul_ediv_cancel_left _ (by exact_mod_cast hm.ne')]
      rw [if_neg (by rw [hkval]; omega)]
  · -- `m ∤ n+1`: closed form is `0`, and `n = −1` is impossible (`m ∣ 0`).
    simp only [hdvd, if_false]
    rw [if_neg (show n ≠ -1 by rintro rfl; exact hdvd ⟨0, by ring⟩), resAt_zero]

/-! ### Soundness: the closed form is the `m`-sheet sum (the explicit (3.1) identity)

`monomialTraceCoeff_eq_sheetSum` certifies that `monomialTraceCoeff` is **not** an ad-hoc closed form
but exactly the honest sum over the `m` sheets `w = ζ^j w₀` of the per-sheet `dz`-coefficient
`c·(ζ^j w₀)^n · ζ^j · (1/m) w₀^{1−m}` (sheet `j`: `dw/dz = ζ^j w₀'`, `w₀' = (1/m) w₀^{1−m}`).  This is
where the roots-of-unity collapse happens; the branch `w₀` (any `w₀ ≠ 0` with `z = w₀ᵐ`) appears only
here, and the result is branch-independent. -/

/-- **(3.1), the explicit `m`-sheet-sum identity (soundness).**  For `ζ` a primitive `m`-th root of
unity (`m > 0`) and any branch value `w₀ ≠ 0`, the closed-form trace coefficient at `z = w₀ᵐ` equals
the honest sum over the `m` sheets `w = ζ^j w₀` of the per-sheet `dz`-coefficient:

> `∑_{j<m} c·(ζ^j w₀)^n · (ζ^j · (1/m) w₀^{1−m}) = monomialTraceCoeff c n m (w₀ᵐ)`.

The per-sheet factor `dw/dz = ζ^j w₀'` with `w₀' = (1/m) w₀^{1−m}` (from `m w₀^{m−1} w₀' = 1`); the
sum collapses by `rootsOfUnity_geom_zsum`. -/
theorem monomialTraceCoeff_eq_sheetSum {m : ℕ} (hm : 0 < m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (c : ℂ) (n : ℤ) (w₀ : ℂ) (hw₀ : w₀ ≠ 0) :
    (∑ j ∈ range m, c * (ζ ^ j * w₀) ^ n * (ζ ^ j * ((m : ℂ)⁻¹ * w₀ ^ (1 - (m : ℤ)))))
      = monomialTraceCoeff c n m (w₀ ^ (m : ℤ)) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  -- factor each summand as `(c·(1/m)·w₀^{n+1−m})·(ζ^j)^{n+1}`.
  have hsummand : ∀ j ∈ range m,
      c * (ζ ^ j * w₀) ^ n * (ζ ^ j * ((m : ℂ)⁻¹ * w₀ ^ (1 - (m : ℤ))))
        = (c * (m : ℂ)⁻¹ * w₀ ^ (n + 1 - (m : ℤ))) * (ζ ^ j) ^ (n + 1) := by
    intro j _
    have hζj : ζ ^ j ≠ 0 := pow_ne_zero j (hζ.ne_zero hm.ne')
    have hz1 : (ζ ^ j) ^ (n + 1) = (ζ ^ j) ^ n * ζ ^ j := by rw [zpow_add₀ hζj n 1, zpow_one]
    have hw1 : w₀ ^ (n + 1 - (m : ℤ)) = w₀ ^ n * w₀ ^ (1 - (m : ℤ)) := by
      rw [← zpow_add₀ hw₀]; ring_nf
    rw [mul_zpow (ζ ^ j) w₀ n, hz1, hw1]; ring
  rw [Finset.sum_congr rfl hsummand, ← Finset.mul_sum, rootsOfUnity_geom_zsum hζ (n + 1)]
  unfold monomialTraceCoeff
  by_cases hdvd : (m : ℤ) ∣ (n + 1)
  · rw [if_pos hdvd, if_pos hdvd]
    obtain ⟨k, hk⟩ := hdvd
    -- `w₀^{n+1−m} = w₀^{m(k−1)} = (w₀ᵐ)^{k−1} = z^{k−1}`, the `m` cancels the `1/m`.
    rw [hk, Int.mul_ediv_cancel_left _ (by exact_mod_cast hm.ne')]
    rw [show (m : ℤ) * k - (m : ℤ) = (m : ℤ) * (k - 1) by ring, zpow_mul,
      show k - 1 = -1 + k by ring]
    rw [mul_comm (c * (m : ℂ)⁻¹ * (w₀ ^ (m : ℤ)) ^ (-1 + k)) (m : ℂ)]
    field_simp
  · rw [if_neg hdvd, if_neg hdvd, mul_zero]

/-! ### The full ramified Lemma 3.2 over a finite Laurent principal part

The residue of a meromorphic `1`-form `α = h(w) dw` at `w = 0` sees only finitely many Laurent
coefficients (the principal part).  So the ramified Lemma 3.2 at the level of a **Laurent polynomial**
`h = ∑_{i ∈ ι} c_i wⁿⁱ` already captures the full residue statement: summing the per-monomial closed
forms gives `laurentTraceCoeff`, whose residue at `z = 0` is `∑_{i : n_i = −1} c_i = Res_{w=0}(h)`,
and which equals the honest `m`-sheet sum of `h` (3.1). -/

/-- **The closed-form trace coefficient of a Laurent polynomial** `h = ∑_i c_i wⁿⁱ` (Miranda (3.1)):
the sum of the per-monomial closed forms. -/
noncomputable def laurentTraceCoeff {ι : Type*} (s : Finset ι) (c : ι → ℂ) (n : ι → ℤ) (m : ℕ) :
    ℂ → ℂ := fun z => ∑ i ∈ s, monomialTraceCoeff (c i) (n i) m z

/-- Each closed-form monomial trace coefficient is meromorphic at `0` (it is a single Laurent
monomial there), so the residue of a finite sum splits termwise (`resAt_finsum`). -/
theorem meromorphicAt_monomialTraceCoeff (c : ℂ) (n : ℤ) (m : ℕ) :
    MeromorphicAt (monomialTraceCoeff c n m) 0 := by
  unfold monomialTraceCoeff
  by_cases hdvd : (m : ℤ) ∣ (n + 1)
  · simp only [hdvd, if_true]
    have : (fun z : ℂ => c * z ^ ((n + 1) / (m : ℤ) - 1))
        = (fun z => c * (z - 0) ^ ((n + 1) / (m : ℤ) - 1)) := by funext z; rw [sub_zero]
    rw [this]
    exact (MeromorphicAt.const c 0).mul
      ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow _)
  · simp only [hdvd, if_false]; exact analyticAt_const.meromorphicAt

/-- **The closed-form Laurent trace coefficient is meromorphic at `0`** (fact (A), closed-form level):
a finite sum of single Laurent monomials in `z`.  This is the meromorphy half of the ramified Lemma
3.2 — the downstairs trace `Tr_m h` of a Laurent polynomial `h` is meromorphic at the branch value
`z = 0`, the ramified analogue of `meromorphicAt_traceCoeff_fibreTrace`. -/
theorem meromorphicAt_laurentTraceCoeff {ι : Type*} (s : Finset ι) (c : ι → ℂ) (n : ι → ℤ) (m : ℕ) :
    MeromorphicAt (laurentTraceCoeff s c n m) 0 := by
  classical
  rw [show laurentTraceCoeff s c n m = fun z => ∑ i ∈ s, monomialTraceCoeff (c i) (n i) m z from rfl]
  exact MeromorphicAt.fun_sum (fun i _ => meromorphicAt_monomialTraceCoeff (c i) (n i) m)

/-- **Ramified Lemma 3.2 over a Laurent polynomial — the residue identity.**  For `h = ∑_i c_i wⁿⁱ`,
the residue at `z = 0` of the ramified trace equals the upstairs residue of `h`:

> `Res_{z=0}(Tr_m h) = ∑_{i ∈ s} (if n_i = −1 then c_i else 0) = Res_{w=0}(h)`.

This is `resAt_monomialTraceCoeff` summed over the monomials (`resAt_finsum`), then
`resAt_laurentMonomial` on the upstairs side.  Captures the full residue content for any meromorphic
`α` (its principal part is such a Laurent polynomial). -/
theorem resAt_laurentTraceCoeff {ι : Type*} (s : Finset ι) (c : ι → ℂ) (n : ι → ℤ) {m : ℕ}
    (hm : 0 < m) :
    resAt (laurentTraceCoeff s c n m) 0
      = resAt (fun w => ∑ i ∈ s, c i * (w - 0) ^ n i) 0 := by
  classical
  -- LHS: residue of a finite sum splits termwise; each term is the monomial trace residue.
  rw [show laurentTraceCoeff s c n m = fun z => ∑ i ∈ s, monomialTraceCoeff (c i) (n i) m z from rfl,
    LaurentForm.resAt_finsum s (fun i z => monomialTraceCoeff (c i) (n i) m z)
      (fun i _ => meromorphicAt_monomialTraceCoeff (c i) (n i) m)]
  -- RHS: residue of a finite sum of Laurent monomials splits termwise too.
  rw [LaurentForm.resAt_finsum s (fun i w => c i * (w - 0) ^ n i)
      (fun i _ => (MeromorphicAt.const (c i) 0).mul
        ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow (n i)))]
  exact Finset.sum_congr rfl (fun i _ => resAt_monomialTraceCoeff (c i) (n i) hm)

/-- **(3.1) over a Laurent polynomial (soundness).**  The closed-form trace coefficient of
`h = ∑_i c_i wⁿⁱ` equals the honest `m`-sheet sum of `h` at `z = w₀ᵐ` (`w₀ ≠ 0`):

> `∑_{j<m} (∑_i c_i (ζ^j w₀)^{n_i}) · (ζ^j · (1/m) w₀^{1−m}) = laurentTraceCoeff s c n m (w₀ᵐ)`.

The inner `∑_i …` is `h(ζ^j w₀)`, so the LHS is exactly `∑_j h(ζ^j w₀)·(sheet-j Jacobian)` — the
genuine `m`-sheet trace of `h·dw`.  Swapping the order of summation and applying
`monomialTraceCoeff_eq_sheetSum` per monomial. -/
theorem laurentTraceCoeff_eq_sheetSum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (n : ι → ℤ)
    {m : ℕ} (hm : 0 < m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (w₀ : ℂ) (hw₀ : w₀ ≠ 0) :
    (∑ j ∈ range m, (∑ i ∈ s, c i * (ζ ^ j * w₀) ^ n i)
        * (ζ ^ j * ((m : ℂ)⁻¹ * w₀ ^ (1 - (m : ℤ)))))
      = laurentTraceCoeff s c n m (w₀ ^ (m : ℤ)) := by
  unfold laurentTraceCoeff
  -- distribute the sheet-`j` Jacobian into the inner sum, then swap `∑_j ∑_i = ∑_i ∑_j`.
  rw [show (∑ j ∈ range m, (∑ i ∈ s, c i * (ζ ^ j * w₀) ^ n i)
        * (ζ ^ j * ((m : ℂ)⁻¹ * w₀ ^ (1 - (m : ℤ)))))
      = ∑ j ∈ range m, ∑ i ∈ s,
          c i * (ζ ^ j * w₀) ^ n i * (ζ ^ j * ((m : ℂ)⁻¹ * w₀ ^ (1 - (m : ℤ)))) from by
    refine Finset.sum_congr rfl (fun j _ => ?_); rw [Finset.sum_mul]]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl
    (fun i _ => monomialTraceCoeff_eq_sheetSum hm hζ (c i) (n i) w₀ hw₀)

end Jacobians.RamifiedTrace
