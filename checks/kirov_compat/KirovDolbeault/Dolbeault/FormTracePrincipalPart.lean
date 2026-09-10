/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

/-!
# Principal-part extraction for a meromorphic coefficient (Gate A, §VIII.3 step 2)

The global trace `Tr_F α` is, in the value chart, a single coefficient function `T : ℂ → ℂ` that is
`MeromorphicAt` at each of the finitely-many exceptional values (the finite pole-values).  Miranda
§VIII.3 step 2 extracts its **principal parts** — the finitely-many negative Laurent coefficients at
each pole — and subtracts them to leave a *global holomorphic* remainder.

Mathlib has **no principal-part API** for `MeromorphicAt`.  This file builds the extraction at the
level of a single coefficient function `ℂ → ℂ`:

* the **negative-power tail** `negTail c b N z := ∑_{k=1}^{N} b k · (z − c) ^ (−k)` (a polynomial in
  `(z − c)⁻¹` — the shape of a `LaurentForm`'s principal part at one centre);
* the **single-point extraction** `exists_principalPart_meromorphicAt`: for `MeromorphicAt h c` there
  is `N : ℕ` and coefficients `b` such that `h − negTail c b N` is `AnalyticAt c` — i.e. the pole is
  removed.

The construction follows the standard Laurent-coefficient peeling, driven by Mathlib's
`meromorphicOrderAt`: `(z − c)^N • h` has nonnegative order when `−N ≤ order h`, hence is analytic;
its Taylor coefficients up to `N − 1` are exactly the principal-part coefficients, and subtracting
them leaves an analytic remainder.

These are clean standalone building blocks (no geometric input) feeding the `GlobalTrace.L` /
`GlobalTrace.hentire` fields of `FormTraceGlobalAssemble`.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`; rationality on `ℂℙ¹`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Filter Topology

namespace Jacobians.Dolbeault.FormTracePrincipalPart

/-- The **negative-power Laurent tail** at a centre `c`: `∑_{k=1}^{N} b k · (z − c) ^ (−k : ℤ)`.
This is the principal part of a meromorphic coefficient at a pole of order `≤ N` — a polynomial in
`(z − c)⁻¹`, the shape of a single centre's contribution to a `LaurentForm`. -/
noncomputable def negTail (c : ℂ) (b : ℕ → ℂ) (N : ℕ) : ℂ → ℂ :=
  fun z => ∑ k ∈ Finset.Icc 1 N, b k * (z - c) ^ (-(k : ℤ))

/-! ### The order of `(z − c)^N • h`

Scaling a meromorphic `h` at `c` by `(z − c)^N` raises its order by `N`.  When `−N ≤ order h` the
scaled function has nonnegative order, hence converges at `c`, hence (junk-repaired) is analytic. -/

/-- **Order arithmetic for the `(z − c)^N` scaling.**  `meromorphicOrderAt ((z−c)^N • h) c
= N + meromorphicOrderAt h c`.  Specialises `meromorphicOrderAt_smul` with
`meromorphicOrderAt_pow_id_sub_const`. -/
theorem meromorphicOrderAt_pow_sub_smul {h : ℂ → ℂ} {c : ℂ} (hh : MeromorphicAt h c) (N : ℕ) :
    meromorphicOrderAt (fun z => (z - c) ^ N • h z) c = (N : WithTop ℤ) + meromorphicOrderAt h c := by
  have hpow : MeromorphicAt (fun z => (z - c) ^ N) c := by fun_prop
  rw [show (fun z => (z - c) ^ N • h z) = (fun z => (z - c) ^ N) • h from rfl,
    meromorphicOrderAt_smul hpow hh]
  congr 1
  exact meromorphicOrderAt_pow_id_sub_const

/-! ### Single-step Taylor division for an analytic function

The cornerstone of principal-part extraction: an analytic `G` at `c` can be written `G(z) = G(c) +
(z − c)·G₁(z)` with `G₁` analytic at `c`.  (The difference `G − G(c)` vanishes at `c`, so it has
analytic order `≥ 1`; the `(z − c)¹ • analytic` factorisation is `AnalyticAt.analyticOrderAt_ne_top`,
with the degenerate "`G` locally constant" case handled directly.) -/

/-- **Single-step Taylor division.**  For `G` analytic at `c`, there is an analytic `G₁` at `c` with
`G z = G c + (z − c) • G₁ z` for all `z` near `c`. -/
theorem exists_analyticAt_taylor_step {G : ℂ → ℂ} {c : ℂ} (hG : AnalyticAt ℂ G c) :
    ∃ G₁ : ℂ → ℂ, AnalyticAt ℂ G₁ c ∧ ∀ᶠ z in 𝓝 c, G z = G c + (z - c) • G₁ z := by
  -- Work with the difference `D z = G z - G c`, which vanishes at `c`.
  set D : ℂ → ℂ := fun z => G z - G c with hD
  have hDan : AnalyticAt ℂ D c := hG.sub analyticAt_const
  by_cases hconst : ∀ᶠ z in 𝓝 c, D z = 0
  · -- `G` is locally constant: take `G₁ = 0`.
    refine ⟨fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [hconst] with z hz
    have hgc : G z = G c := sub_eq_zero.mp hz
    simp [hgc]
  · -- `D` is not locally zero: `analyticOrderAt D c ≠ ⊤`, and `D c = 0` forces order `≥ 1`.
    have hne : analyticOrderAt D c ≠ ⊤ := fun h => hconst (analyticOrderAt_eq_top.1 h)
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (hDan.analyticOrderAt_ne_top).1 hne
    set k := analyticOrderNatAt D c with hk
    -- `D c = 0`, so the order `k ≥ 1` (else `D c = g c ≠ 0`).
    have hDc : D c = 0 := by simp [hD]
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · exfalso
        have := hg_eq.self_of_nhds
        rw [hk0] at this
        simp only [pow_zero, one_smul] at this
        rw [hDc] at this
        exact hg_ne this.symm
      · exact hk0
    -- `G₁ := (z − c)^(k−1) • g` is analytic, and `(z−c)^k • g = (z−c) • G₁`.
    refine ⟨fun z => (z - c) ^ (k - 1) • g z, ?_, ?_⟩
    · exact ((analyticAt_id.sub analyticAt_const).pow _).smul hg_an
    · filter_upwards [hg_eq] with z hz
      have hDz : G z - G c = (z - c) ^ k • g z := hz
      have hkpow : (z - c) ^ k = (z - c) * (z - c) ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have : G z = G c + (z - c) ^ k • g z := by rw [← hDz]; ring
      rw [this, hkpow]
      simp only [smul_eq_mul]
      ring

/-- **Iterated Taylor division (finite Taylor expansion with analytic remainder).**  For `G` analytic
at `c` and any `N : ℕ`, there are coefficients `a : ℕ → ℂ` and an analytic remainder `R` with
`G z = (∑_{j<N} a j · (z − c)^j) + (z − c)^N • R z` for all `z` near `c`.  Proved by induction on `N`
via `exists_analyticAt_taylor_step` (each step peels off one Taylor coefficient). -/
theorem exists_analyticAt_taylorPoly {G : ℂ → ℂ} {c : ℂ} (hG : AnalyticAt ℂ G c) (N : ℕ) :
    ∃ (a : ℕ → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R c ∧
      ∀ᶠ z in 𝓝 c, G z = (∑ j ∈ Finset.range N, a j * (z - c) ^ j) + (z - c) ^ N • R z := by
  induction N with
  | zero =>
    refine ⟨fun _ => 0, G, hG, ?_⟩
    filter_upwards with z
    simp
  | succ N ih =>
    obtain ⟨a, R, hR_an, hR_eq⟩ := ih
    -- Peel one more term off the remainder `R`.
    obtain ⟨R₁, hR₁_an, hR₁_eq⟩ := exists_analyticAt_taylor_step hR_an
    -- New coefficient: `a` extended by `R c` at index `N`.
    refine ⟨Function.update a N (R c), R₁, hR₁_an, ?_⟩
    filter_upwards [hR_eq, hR₁_eq] with z hz hz₁
    rw [hz, hz₁]
    -- `∑_{j<N+1} a' j (z−c)^j + (z−c)^{N+1}•R₁ = ∑_{j<N} a j (z−c)^j + (z−c)^N•(R c + (z−c)•R₁)`.
    rw [Finset.sum_range_succ]
    have hsum_eq : (∑ j ∈ Finset.range N, Function.update a N (R c) j * (z - c) ^ j)
        = ∑ j ∈ Finset.range N, a j * (z - c) ^ j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Function.update_of_ne (by exact Nat.ne_of_lt (Finset.mem_range.mp hj))]
    rw [hsum_eq, Function.update_self]
    simp only [smul_eq_mul]
    ring

/-! ### The negative-power tail as a reindexed Taylor head

The principal part of `(z − c)^{-N}·g` is `∑_{j<N} a_j (z − c)^{j−N}`, which reindexes (`k = N − j`)
to the `negTail` form `∑_{k=1}^{N} a_{N−k} (z − c)^{−k}`. -/

/-- **Reindexing the Taylor head into a negative-power tail.**
`∑_{j<N} a j · (z − c) ^ (j − N : ℤ) = negTail c (fun k => a (N − k)) N z`. -/
theorem sum_taylorHead_eq_negTail (c : ℂ) (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (∑ j ∈ Finset.range N, a j * (z - c) ^ ((j : ℤ) - N))
      = negTail c (fun k => a (N - k)) N z := by
  rw [negTail]
  -- Reindex RHS `Icc 1 N` by `k = j + 1` onto `range N`, and LHS by `j ↦ N − 1 − j`.
  rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext x; simp,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  rw [← Finset.sum_range_reflect (fun j => a j * (z - c) ^ ((j : ℤ) - N)) N]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjN : j < N := Finset.mem_range.mp hj
  -- LHS (reflected) term at `j`: `a (N − 1 − j)·(z−c)^((N−1−j) − N)`;
  -- RHS term at `j`: `a (N − (1 + j))·(z−c)^(−(1 + j))`.
  rw [show N - 1 - j = N - (1 + j) by omega]
  congr 1
  rw [show ((N - (1 + j) : ℕ) : ℤ) = (N : ℤ) - (1 + j) by omega]
  push_cast
  ring_nf

/-! ### The single-point principal-part extraction (the §VIII.3 step-2 atom)

Assembling everything: a meromorphic coefficient `h` at `c` decomposes, on a punctured neighbourhood,
as `negTail c b N + R` with `R` analytic at `c` — the principal part `negTail` carries the pole, the
remainder `R` is holomorphic. -/

/-- **Single-point principal-part extraction.**  For a coefficient `h` that is `MeromorphicAt c`,
there are a degree `N : ℕ`, principal-part coefficients `b : ℕ → ℂ`, and an analytic remainder `R`
(`AnalyticAt ℂ R c`) such that on a punctured neighbourhood of `c`,
`h z = negTail c b N z + R z`.  (When `h` has no pole at `c`, `N = 0` and `negTail ≡ 0`, so `h` simply
agrees with the analytic `R` off `c`.)  This is Miranda §VIII.3 step 2 at one centre — Mathlib has no
principal-part API, so it is built from `meromorphicOrderAt_eq_int_iff` (the `(z−c)^n • g`
factorisation) + the iterated Taylor division `exists_analyticAt_taylorPoly`. -/
theorem exists_principalPart_meromorphicAt {h : ℂ → ℂ} {c : ℂ} (hh : MeromorphicAt h c) :
    ∃ (N : ℕ) (b : ℕ → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R c ∧
      h =ᶠ[𝓝[≠] c] fun z => negTail c b N z + R z := by
  -- Split on the order of `h` at `c`.
  by_cases hord : 0 ≤ meromorphicOrderAt h c
  · -- No pole: `h` agrees with an analytic function off `c`; empty principal part.
    cases hcase : meromorphicOrderAt h c with
    | top =>
      -- `h ≡ 0` off `c`.
      refine ⟨0, fun _ => 0, fun _ => 0, analyticAt_const, ?_⟩
      filter_upwards [meromorphicOrderAt_eq_top_iff.1 hcase] with z hz
      simp [negTail, hz]
    | coe n =>
      have hn0 : 0 ≤ n := by rw [hcase] at hord; exact_mod_cast hord
      obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hh).1 hcase
      lift n to ℕ using hn0 with m hm
      refine ⟨0, fun _ => 0, fun z => (z - c) ^ m • g z, ?_, ?_⟩
      · exact ((analyticAt_id.sub analyticAt_const).pow _).smul hg_an
      · filter_upwards [hg_eq] with z hz
        simp only [negTail]
        rw [hz]
        simp
  · -- Genuine pole: `order = -(N : ℤ)` for some `N ≥ 1`.
    push Not at hord
    have hne_top : meromorphicOrderAt h c ≠ ⊤ := by
      intro h'; rw [h'] at hord; exact (not_lt.2 le_top) hord
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne_top
    have hn_neg : n < 0 := by rw [← hn] at hord; exact_mod_cast hord
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hh).1 hn.symm
    -- `N := -n ≥ 1`.
    set N := (-n).toNat with hN
    have hNn : (N : ℤ) = -n := by rw [hN, Int.toNat_of_nonneg (by omega)]
    -- Taylor-expand `g` to degree `N`.
    obtain ⟨a, R, hR_an, hR_eq⟩ := exists_analyticAt_taylorPoly hg_an N
    refine ⟨N, fun k => a (N - k), R, hR_an, ?_⟩
    -- On `𝓝[≠] c`: `h z = (z−c)^n • g z = (z−c)^(−N) • (Taylor head + (z−c)^N R) = negTail + R`.
    have hR_eqNE : g =ᶠ[𝓝[≠] c]
        fun z => (∑ j ∈ Finset.range N, a j * (z - c) ^ j) + (z - c) ^ N • R z :=
      hR_eq.filter_mono nhdsWithin_le_nhds
    filter_upwards [hg_eq, hR_eqNE, self_mem_nhdsWithin] with z hz hzR hzc
    have hzc' : z - c ≠ 0 := sub_ne_zero.mpr (by simpa using hzc)
    rw [hz, hzR, ← sum_taylorHead_eq_negTail c a N z]
    -- `(z−c)^n • (S + (z−c)^N • R) = (∑ a j (z−c)^(j−N)) + R`, using `n = −N`.
    rw [smul_add, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← mul_assoc, mul_comm ((z - c) ^ n) (a j), mul_assoc, ← zpow_natCast (z - c) j,
        ← zpow_add₀ hzc']
      congr 2
      omega
    · rw [← mul_assoc, ← zpow_natCast (z - c) N, ← zpow_add₀ hzc']
      rw [show n + (N : ℤ) = 0 by omega]
      simp

/-! ### A negative-power tail at a different centre is analytic

A `negTail` centred at `c'` is analytic at any other point `c ≠ c'` (its only pole is at `c'`). -/

/-- **A `negTail` is analytic away from its centre.**  `negTail c' b N` is `AnalyticAt c` for `c ≠ c'`
(its only singularity is the pole at `c'`). -/
theorem analyticAt_negTail_of_ne {c c' : ℂ} (b : ℕ → ℂ) (N : ℕ) (hne : c ≠ c') :
    AnalyticAt ℂ (negTail c' b N) c := by
  show AnalyticAt ℂ (fun z => ∑ k ∈ Finset.Icc 1 N, b k * (z - c') ^ (-(k : ℤ))) c
  refine Finset.analyticAt_fun_sum _ (fun k _ => ?_)
  refine analyticAt_const.mul ?_
  have hbase : AnalyticAt ℂ (fun z : ℂ => z - c') c := analyticAt_id.sub analyticAt_const
  exact hbase.zpow (sub_ne_zero.mpr hne)

/-! ### Multi-point finite principal-part subtraction (assembly-ready)

For finitely many centres `S : Finset ℂ`, with `h` meromorphic at every `c ∈ S`, there is a single
function `P` — a finite sum of `negTail`s, one per centre — such that `h − P` is **analytic at every
`c ∈ S`** (the principal part at each centre is subtracted, removing the pole; the tails at the other
centres are analytic at `c`).  This is the finite-pole half of Miranda §VIII.3 step 2/3 (subtract all
finite principal parts to leave a remainder holomorphic at every finite pole). -/

/-- **Multi-point finite principal-part subtraction.**  Given a finite centre set `S` and a coefficient
`h` that is `MeromorphicAt` at every `c ∈ S`, there is a function `P` (a finite sum of `negTail`s, one
per centre — so `P` is itself analytic away from `S`) such that `h − P` is `AnalyticAt c` for every
`c ∈ S` (germ-equal off `c` to an analytic function, with the pole removed).  More precisely we return,
per centre, the degree/coefficients and the global subtrahend `P`, with `h − P` analytic at each
centre. -/
theorem exists_finitePrincipalPart {h : ℂ → ℂ} {S : Finset ℂ}
    (hh : ∀ c ∈ S, MeromorphicAt h c) :
    ∃ P : ℂ → ℂ, (∀ c ∉ S, AnalyticAt ℂ P c) ∧
      ∀ c ∈ S, ∃ R : ℂ → ℂ, AnalyticAt ℂ R c ∧ (h - P) =ᶠ[𝓝[≠] c] R := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨fun _ => 0, fun c _ => analyticAt_const, fun c hc => absurd hc (Finset.notMem_empty c)⟩
  | insert c₀ S hc₀ ih =>
    -- Extract the principal part of `h` at the new centre `c₀`.
    obtain ⟨N, b, R₀, hR₀_an, hR₀_eq⟩ :=
      exists_principalPart_meromorphicAt (hh c₀ (Finset.mem_insert_self c₀ S))
    -- Recurse on `S` (each `c ∈ S` is still a meromorphic point of `h`).
    obtain ⟨P, hP_an, hP_centres⟩ :=
      ih (fun c hc => hh c (Finset.mem_insert_of_mem hc))
    refine ⟨fun z => negTail c₀ b N z + P z, ?_, ?_⟩
    · -- `negTail c₀ b N + P` is analytic away from `insert c₀ S`.
      intro c hc
      rw [Finset.mem_insert, not_or] at hc
      exact (analyticAt_negTail_of_ne (c := c) (c' := c₀) b N hc.1).add (hP_an c hc.2)
    · -- `h − (negTail c₀ + P)` is analytic at every centre of `insert c₀ S`.
      intro c hc
      rw [Finset.mem_insert] at hc
      rcases hc with heq | hcS
      · -- At `c₀` (`c = c₀`): `h − negTail c₀ b N` is analytic (`R₀`); subtracting the
        -- off-centre-analytic `P` keeps it analytic.
        subst heq
        refine ⟨fun z => R₀ z - P z, hR₀_an.sub (hP_an c hc₀), ?_⟩
        filter_upwards [hR₀_eq] with z hz
        simp only [Pi.sub_apply]
        rw [show h z - (negTail c b N z + P z) = (h z - negTail c b N z) - P z by ring, hz]
        ring
      · -- At `c ∈ S` (so `c ≠ c₀`): `h − P` is analytic (`R`); subtracting the off-centre-analytic
        -- `negTail c₀` keeps it analytic.
        obtain ⟨R, hR_an, hR_eq⟩ := hP_centres c hcS
        have hne : c ≠ c₀ := fun h => hc₀ (h ▸ hcS)
        refine ⟨fun z => R z - negTail c₀ b N z, hR_an.sub (analyticAt_negTail_of_ne b N hne), ?_⟩
        filter_upwards [hR_eq] with z hz
        simp only [Pi.sub_apply] at hz ⊢
        rw [show h z - (negTail c₀ b N z + P z) = (h z - P z) - negTail c₀ b N z by ring, hz]

/-! ### The global finite `hentire` bridge

Assembling the multi-point subtraction into a **global analyticity** statement.  If `h` is analytic
off a finite set `C` and meromorphic at each `c ∈ C`, then after subtracting the finite principal part
`P` the remainder `h − P` is analytic off `C` and *germ-analytic* (`=ᶠ[𝓝[≠] c] (analytic)`) at each
`c ∈ C`.  The promotion to a **full** `AnalyticAt c` (the shape of `GlobalTrace.hentire`) holds exactly
when `h − P` is additionally continuous at each `c ∈ C` (the junk-value is the analytic-continuation
value); we record that as the explicit hypothesis `hcont`, isolating the junk-freeness condition that
the global trace construction must supply. -/

/-- **The global finite `hentire` bridge.**  Let `h` be analytic at every point off a finite set `C`
(`hoff`), meromorphic at every `c ∈ C` (`hmero`), and such that, after the finite principal-part
subtraction `P` (from `exists_finitePrincipalPart`), `h − P` is **continuous at every `c ∈ C`**
(`hcont` — the junk-free condition).  Then there is a finite principal part `P` with `h − P`
`AnalyticOnNhd ℂ … Set.univ` (entire) — the finite half of `GlobalTrace.hentire`.

The continuity hypothesis is the precise, irreducible junk-value requirement: a meromorphic `h` whose
*pole is removed* by `P` has a removable singularity at each `c ∈ C`, and `MeromorphicAt.analyticAt`
upgrades "meromorphic + continuous" to "analytic".  The global trace `T` built from the geometric
pushforward is junk-free by construction, so `hcont` is automatic there. -/
theorem exists_entire_of_finitePoles {h : ℂ → ℂ} {C : Finset ℂ}
    (hoff : ∀ c ∉ C, AnalyticAt ℂ h c) (hmero : ∀ c ∈ C, MeromorphicAt h c) :
    ∃ P : ℂ → ℂ, (∀ c ∉ C, AnalyticAt ℂ P c) ∧
      (∀ c ∈ C, ∃ R : ℂ → ℂ, AnalyticAt ℂ R c ∧ (h - P) =ᶠ[𝓝[≠] c] R) ∧
      ((∀ c ∈ C, ContinuousAt (h - P) c) → AnalyticOnNhd ℂ (h - P) Set.univ) := by
  classical
  obtain ⟨P, hP_an, hP_centres⟩ := exists_finitePrincipalPart hmero
  refine ⟨P, hP_an, hP_centres, fun hcont z _ => ?_⟩
  by_cases hzC : z ∈ C
  · -- At a centre: meromorphic (pole removed) + continuous ⟹ analytic.
    obtain ⟨R, hR_an, hR_eq⟩ := hP_centres z hzC
    -- `h − P` is meromorphic at `z` (`h` meromorphic, `P` analytic since... P meromorphic at z too).
    -- `h − P =ᶠ[𝓝[≠]z] R` (analytic ⟹ meromorphic), so `h − P` is meromorphic at `z`.
    have hmeroHP : MeromorphicAt (h - P) z := hR_an.meromorphicAt.congr hR_eq.symm
    exact hmeroHP.analyticAt (hcont z hzC)
  · -- Off `C`: `h` analytic and `P` analytic.
    exact (hoff z hzC).sub (hP_an z hzC)

end Jacobians.Dolbeault.FormTracePrincipalPart
