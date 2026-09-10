/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.SymmetricFunctionDescent
import KirovDolbeault.Dolbeault.FormTracePrincipalPart
import KirovDolbeault.Dolbeault.TailSerre
import KirovDolbeault.Dolbeault.TailFrameWitness

/-!
# The unweighted symmetric descent with residue bookkeeping (T lane)

The plain-value-trace mirror of `Jacobians.SymmetricDescent.analyticAt_weightedSymSum_descent`:
for the **unweighted** `m`-sheet sum the roots-of-unity collapse keeps the indices `m ∣ n`
(power-sum weight `ζ^{j·n}`, no `+1` shift), so

> `∑_{j<m} Q(ζʲ·u) = G(uᵐ)`  (`Q` analytic at `0`, `G` analytic at `0`),

with `G(v) = m·∑'ₖ a_{m·k}·vᵏ`.  On top of it, the **meromorphic descent**
`meromorphicAt_symSum_descent`: for `ψ` meromorphic at `0` the unweighted `m`-sheet sum
descends through `(·)^m` to a function `H` meromorphic at `0` whose residue is the depth-`m`
normalization

> `planarCoeff (−1) H 0 = m · planarCoeff (−m) ψ 0`

— the sphere-side half of the ramified-cluster Lemma 3.2, matching the X-side
`planarCoeff_neg_one_branch` (`ResidueAtom.lean`).  The principal part contributes the finite
tail `∑_{m ∣ k} m·b_k·v^{−k/m}` (per-monomial collapse `∑_j ζ^{−jk} = m·[m ∣ k]`), the analytic
remainder descends by the analytic statement, and only the `k = m` tail term hits depth `−1`.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), §VIII.3.
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §5.
* `Jacobians.SymmetricFunctionDescent` (the weighted mirror, proof pattern reused verbatim).
-/

noncomputable section

open Complex Filter Topology Finset
open scoped NNReal ENNReal

namespace Jacobians.Dolbeault.FrameTraceWall

open FormalMultilinearSeries Jacobians.SymmetricDescent Jacobians.Dolbeault
  Jacobians.Dolbeault.FormTracePrincipalPart

/-! ## The arithmetic-progression index map `k ↦ m·k` -/

/-- The reindex map `k ↦ m·k` is injective (for `m > 0`). -/
theorem mulIdx_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (fun k : ℕ => m * k) := by
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left hm hab

/-- `n` lies in the range of `k ↦ m·k` iff `m ∣ n`. -/
theorem mem_range_mulIdx_iff (m n : ℕ) :
    n ∈ Set.range (fun k : ℕ => m * k) ↔ m ∣ n := by
  constructor
  · rintro ⟨k, rfl⟩
    exact Dvd.intro k rfl
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

/-! ## The unweighted symmetric-sum HasSum identity -/

/-- For `u` near `0`, the unweighted `m`-sheet sum HasSum form: `∑_{j<m} Q(ζʲ·u)` is the sum of
the series `n ↦ (∑_{j<m} ζ^{j·n})·uⁿ·pf.coeff n`. -/
theorem hasSum_plainSymSum_aux {Q : ℂ → ℂ} {pf : FormalMultilinearSeries ℂ ℂ ℂ}
    (hpf : HasFPowerSeriesAt Q pf 0) (m : ℕ) (ζ : ℂ) :
    ∀ᶠ u in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => (∑ j ∈ Finset.range m, (ζ ^ j) ^ ((n : ℤ))) * u ^ n * pf.coeff n)
        (∑ j ∈ Finset.range m, Q (ζ ^ j * u)) := by
  rw [hasFPowerSeriesAt_iff] at hpf
  have hev : ∀ᶠ u in 𝓝 (0 : ℂ), ∀ j ∈ Finset.range m,
      HasSum (fun n => (ζ ^ j * u) ^ n • pf.coeff n) (Q (ζ ^ j * u)) := by
    rw [eventually_all_finset]
    intro j _
    have hcont : Tendsto (fun u : ℂ => ζ ^ j * u) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun u : ℂ => ζ ^ j * u) := continuous_const.mul continuous_id
      simpa using hc.tendsto 0
    have := hcont.eventually hpf
    filter_upwards [this] with u hu
    simpa using hu
  filter_upwards [hev] with u hu
  have hperj : ∀ j ∈ Finset.range m,
      HasSum (fun n : ℕ => ((ζ ^ j) ^ ((n : ℤ))) * u ^ n * pf.coeff n) (Q (ζ ^ j * u)) := by
    intro j hj
    refine (hu j hj).congr_fun ?_
    intro n
    rw [smul_eq_mul, zpow_natCast, mul_pow]
  have hsum := hasSum_sum hperj
  refine hsum.congr_fun ?_
  intro n
  rw [Finset.sum_mul, Finset.sum_mul]

/-! ## The analytic descent -/

/-- **The unweighted symmetric-sum descent.**  For an analytic germ `Q` at `0`, `m > 0`, and a
primitive `m`-th root of unity `ζ`, there is an analytic germ `G` at `0` with

> `∑_{j<m} Q(ζʲ·u) = G(uᵐ)`   (for `u` near `0`).

(`G(v) = m·∑'ₖ a_{m·k}·vᵏ`, the divisible-subsequence series.) -/
theorem analyticAt_plainSymSum_descent {Q : ℂ → ℂ} (hQ : AnalyticAt ℂ Q 0) {m : ℕ} (hm : 0 < m)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      ∀ᶠ u in 𝓝 (0 : ℂ), (∑ j ∈ Finset.range m, Q (ζ ^ j * u)) = G (u ^ m) := by
  obtain ⟨pf, hpf⟩ := hQ
  set c : ℕ → ℂ := fun k => pf.coeff (m * k) with hc
  refine ⟨fun v => (m : ℂ) * ofScalarsSum (E := ℂ) c v, ?_, ?_⟩
  · have hrad : 0 < pf.radius := by
      obtain ⟨r, hr⟩ := hpf; exact lt_of_lt_of_le hr.r_pos hr.r_le
    have := analyticAt_ofScalars_subseq pf hrad hm 0
    simp only [Nat.add_zero] at this
    exact (analyticAt_const (v := (m : ℂ))).mul this
  · have hradc : 0 < (ofScalars ℂ c).radius := by
      obtain ⟨ρ, hρ0, hρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
        (show (0 : ℝ≥0∞) < pf.radius by
          obtain ⟨r, hr⟩ := hpf; exact lt_of_lt_of_le hr.r_pos hr.r_le)
      have hle := le_radius_ofScalars_subseq pf hm 0 hρ
      simp only [Nat.add_zero] at hle
      refine lt_of_lt_of_le ?_ hle
      have hρ0' : (0 : ℝ≥0) < ρ := by exact_mod_cast hρ0
      rw [← ENNReal.coe_pow]
      exact_mod_cast pow_pos hρ0' m
    have hpow : ∀ᶠ u in 𝓝 (0 : ℂ), (‖u ^ m‖₊ : ℝ≥0∞) < (ofScalars ℂ c).radius := by
      have htend : Tendsto (fun u : ℂ => (‖u ^ m‖₊ : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
        have hcont : Continuous (fun u : ℂ => (‖u ^ m‖₊ : ℝ≥0∞)) :=
          (ENNReal.continuous_coe).comp (continuous_nnnorm.comp (continuous_pow m))
        have h0 := hcont.tendsto 0
        simpa [zero_pow hm.ne'] using h0
      exact htend.eventually (eventually_lt_nhds hradc)
    filter_upwards [hasSum_plainSymSum_aux hpf m ζ, hpow] with u hu hupow
    -- collapse the coefficient by the roots-of-unity power sum
    have hcollapse : ∀ n : ℕ,
        (∑ j ∈ Finset.range m, (ζ ^ j) ^ ((n : ℤ))) * u ^ n * pf.coeff n
          = (if (m : ℤ) ∣ (n : ℤ) then (m : ℂ) else 0) * u ^ n * pf.coeff n := by
      intro n
      rw [Jacobians.RamifiedTrace.rootsOfUnity_geom_zsum hζ ((n : ℤ))]
    rw [show (fun n : ℕ => (∑ j ∈ Finset.range m, (ζ ^ j) ^ ((n : ℤ))) * u ^ n * pf.coeff n)
          = (fun n : ℕ => (if (m : ℤ) ∣ (n : ℤ) then (m : ℂ) else 0) * u ^ n * pf.coeff n)
        from funext hcollapse] at hu
    set F : ℕ → ℂ := fun n => (if (m : ℤ) ∣ (n : ℤ) then (m : ℂ) else 0) * u ^ n * pf.coeff n
      with hF
    have hdvd_iff : ∀ n : ℕ, ((m : ℤ) ∣ (n : ℤ)) ↔ (m ∣ n) := fun n => Int.natCast_dvd_natCast
    have hzero : ∀ n ∉ Set.range (fun k : ℕ => m * k), F n = 0 := by
      intro n hn
      have hnotdvd : ¬ (m : ℤ) ∣ (n : ℤ) := by
        rw [hdvd_iff n, ← mem_range_mulIdx_iff]
        exact hn
      simp [hF, hnotdvd]
    have hreindex : HasSum (F ∘ (fun k : ℕ => m * k))
        (∑ j ∈ Finset.range m, Q (ζ ^ j * u)) :=
      ((mulIdx_injective hm).hasSum_iff hzero).mpr hu
    have hFcomp : ∀ k : ℕ, (F ∘ (fun k : ℕ => m * k)) k = (m : ℂ) * (c k • (u ^ m) ^ k) := by
      intro k
      simp only [Function.comp, hF, hc]
      have hdvd : (m : ℤ) ∣ ((m * k : ℕ) : ℤ) := by
        rw [hdvd_iff]
        exact Dvd.intro k rfl
      rw [if_pos hdvd, smul_eq_mul, ← pow_mul]
      ring
    rw [show (F ∘ (fun k : ℕ => m * k)) = (fun k => (m : ℂ) * (c k • (u ^ m) ^ k))
        from funext hFcomp] at hreindex
    have hG : HasSum (fun k => c k • (u ^ m) ^ k) (ofScalarsSum (E := ℂ) c (u ^ m)) :=
      hasSum_ofScalarsSum_of_lt_radius c hupow
    exact hreindex.unique (hG.mul_left (m : ℂ))

/-! ## The principal-part collapse

The per-monomial roots-of-unity collapse for the negative tail: only the depths `m ∣ k`
survive, contributing `m·b_k·(uᵐ)^{−k/m}`. -/

/-- **The descended tail at the centre `c₀`**: `v ↦ ∑_{k ∈ Icc 1 N, m ∣ k} m·b_k·(v−c₀)^{−k/m}`. -/
def descTail (c₀ : ℂ) (m : ℕ) (b : ℕ → ℂ) (N : ℕ) : ℂ → ℂ :=
  fun v => ∑ k ∈ (Finset.Icc 1 N).filter (fun k => m ∣ k),
    ((m : ℂ) * b k) * (v - c₀) ^ (-((k / m : ℕ) : ℤ))

theorem meromorphicAt_descTail (c₀ : ℂ) (m : ℕ) (b : ℕ → ℂ) (N : ℕ) :
    MeromorphicAt (descTail c₀ m b N) c₀ := by
  apply MeromorphicAt.fun_sum
  intro k _
  exact (MeromorphicAt.const _ c₀).mul (meromorphicAt_zpow_self c₀ (-((k / m : ℕ) : ℤ)))

/-- **The tail collapse**: for `u ≠ 0`, the unweighted `m`-sheet sum of the negative tail is
the descended tail at `uᵐ`. -/
theorem negTail_plainSymSum (c₀ : ℂ) (b : ℕ → ℂ) (N : ℕ) {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (u : ℂ) :
    ∑ j ∈ Finset.range m, negTail 0 b N (ζ ^ j * u) = descTail c₀ m b N (c₀ + u ^ m) := by
  classical
  -- expand and swap the two finite sums
  have hexp : ∑ j ∈ Finset.range m, negTail 0 b N (ζ ^ j * u)
      = ∑ k ∈ Finset.Icc 1 N, (∑ j ∈ Finset.range m, (ζ ^ j) ^ (-(k : ℤ))) *
          (b k * u ^ (-(k : ℤ))) := by
    simp only [negTail]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_zero, mul_zpow]
    ring
  rw [hexp]
  -- collapse each depth by the roots-of-unity power sum
  have hcollapse : ∀ k ∈ Finset.Icc 1 N,
      (∑ j ∈ Finset.range m, (ζ ^ j) ^ (-(k : ℤ))) * (b k * u ^ (-(k : ℤ)))
        = (if (m : ℤ) ∣ (-(k : ℤ)) then (m : ℂ) else 0) * (b k * u ^ (-(k : ℤ))) := by
    intro k _
    rw [Jacobians.RamifiedTrace.rootsOfUnity_geom_zsum hζ (-(k : ℤ))]
  rw [Finset.sum_congr rfl hcollapse]
  -- kill the non-divisible depths, rewrite the divisible ones
  have hdvd_iff : ∀ k : ℕ, ((m : ℤ) ∣ (-(k : ℤ))) ↔ (m ∣ k) := by
    intro k
    rw [Int.dvd_neg, Int.natCast_dvd_natCast]
  have hsplit : ∑ k ∈ Finset.Icc 1 N,
      (if (m : ℤ) ∣ (-(k : ℤ)) then (m : ℂ) else 0) * (b k * u ^ (-(k : ℤ)))
        = ∑ k ∈ (Finset.Icc 1 N).filter (fun k => m ∣ k),
            (m : ℂ) * (b k * u ^ (-(k : ℤ))) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : m ∣ k
    · rw [if_pos ((hdvd_iff k).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((hdvd_iff k).mp hc)), if_neg h]
      ring
  rw [hsplit]
  simp only [descTail]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hdvd : m ∣ k := (Finset.mem_filter.mp hk).2
  have hku : u ^ (-(k : ℤ)) = (c₀ + u ^ m - c₀) ^ (-((k / m : ℕ) : ℤ)) := by
    rw [add_sub_cancel_left, ← zpow_natCast u m, ← zpow_mul]
    congr 1
    obtain ⟨k', rfl⟩ := hdvd
    rw [Nat.mul_div_cancel_left k' hm]
    push_cast
    ring
  rw [hku]
  ring

/-- The residue read of the descended tail: only the depth-`m` term hits `−1`. -/
theorem planarCoeff_neg_one_descTail (c₀ : ℂ) (m : ℕ) (hm : 0 < m) (b : ℕ → ℂ) (N : ℕ) :
    planarCoeff (-1) (descTail c₀ m b N) c₀ = if m ≤ N then (m : ℂ) * b m else 0 := by
  classical
  unfold descTail
  rw [planarCoeff_finset_sum ((Finset.Icc 1 N).filter (fun k => m ∣ k))
    (fun k v => ((m : ℂ) * b k) * (v - c₀) ^ (-((k / m : ℕ) : ℤ))) (-1) c₀
    (fun k _ => (MeromorphicAt.const ((m : ℂ) * b k) c₀).mul
      (meromorphicAt_zpow_self c₀ (-((k / m : ℕ) : ℤ))))]
  have hterm : ∀ k ∈ (Finset.Icc 1 N).filter (fun k => m ∣ k),
      planarCoeff (-1) (fun v => ((m : ℂ) * b k) * (v - c₀) ^ (-((k / m : ℕ) : ℤ))) c₀
        = if k = m then (m : ℂ) * b m else 0 := by
    intro k hk
    obtain ⟨hkIcc, hdvd⟩ := Finset.mem_filter.mp hk
    rw [planarCoeff_monomial]
    by_cases hkm : k = m
    · subst hkm
      rw [if_pos rfl, if_pos]
      rw [Nat.div_self hm]
      norm_num
    · rw [if_neg hkm, if_neg]
      intro hc
      -- `−1 = −(k/m)` forces `k/m = 1`, i.e. `k = m` (as `m ∣ k`)
      have h1 : ((k / m : ℕ) : ℤ) = 1 := by omega
      have h2 : k / m = 1 := by exact_mod_cast h1
      obtain ⟨k', rfl⟩ := hdvd
      rw [Nat.mul_div_cancel_left k' hm] at h2
      subst h2
      exact hkm (by ring)
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ m (fun _ => (m : ℂ) * b m)]
  by_cases hmN : m ≤ N
  · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm, hmN⟩, dvd_refl m⟩), if_pos hmN]
  · rw [if_neg (fun hc => hmN (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).2), if_neg hmN]

/-! ## The meromorphic descent with residue bookkeeping -/

/-- **The meromorphic unweighted symmetric descent.**  For `ψ` meromorphic at `0`, `m > 0`, and
`ζ` a primitive `m`-th root of unity, the unweighted `m`-sheet sum descends through `(·)^m`:
there is `H` meromorphic at `0` with

> `∑_{j<m} ψ(ζʲ·u) = H(uᵐ)`  (for `u ≠ 0` near `0`),  and
> `planarCoeff (−1) H 0 = m · planarCoeff (−m) ψ 0`

(the sphere-side ramified-cluster residue normalization, matching the X-side
`planarCoeff_neg_one_branch`). -/
theorem meromorphicAt_plainSymSum_descent (c₀ : ℂ) {ψ : ℂ → ℂ} (hψ : MeromorphicAt ψ 0) {m : ℕ}
    (hm : 0 < m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) :
    ∃ H : ℂ → ℂ, MeromorphicAt H c₀ ∧
      (∀ᶠ u in 𝓝[≠] (0 : ℂ), (∑ j ∈ Finset.range m, ψ (ζ ^ j * u)) = H (c₀ + u ^ m)) ∧
      planarCoeff (-1) H c₀ = (m : ℂ) * planarCoeff (-(m : ℤ)) ψ 0 := by
  classical
  obtain ⟨N, b, R, hR_an, hψ_eq⟩ := exists_principalPart_meromorphicAt hψ
  obtain ⟨G, hG_an, hG_eq⟩ := analyticAt_plainSymSum_descent hR_an hm hζ
  have hshift_an : AnalyticAt ℂ (fun z : ℂ => G (z - c₀)) c₀ := by
    have hsub : AnalyticAt ℂ (fun z : ℂ => z - c₀) c₀ := analyticAt_id.sub analyticAt_const
    have hcomp := AnalyticAt.comp (g := G) (f := fun z : ℂ => z - c₀) (x := c₀)
      (by simpa using hG_an) hsub
    simpa [Function.comp] using hcomp
  refine ⟨descTail c₀ m b N + fun z => G (z - c₀),
    (meromorphicAt_descTail c₀ m b N).add hshift_an.meromorphicAt, ?_, ?_⟩
  · -- the descent identity on the punctured neighbourhood
    have hper : ∀ j ∈ Finset.range m, ∀ᶠ u in 𝓝[≠] (0 : ℂ),
        ψ (ζ ^ j * u) = negTail 0 b N (ζ ^ j * u) + R (ζ ^ j * u) := by
      intro j hj
      have hζj : (ζ : ℂ) ^ j ≠ 0 :=
        pow_ne_zero j (hζ.ne_zero (by rintro rfl; simp at hj))
      have htend : Tendsto (fun u : ℂ => ζ ^ j * u) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · have hc : Tendsto (fun u : ℂ => ζ ^ j * u) (𝓝 0) (𝓝 0) := by
            simpa using (continuous_const.mul continuous_id).tendsto (0 : ℂ)
          exact hc.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with u hu
          exact Set.mem_compl_singleton_iff.mpr (mul_ne_zero hζj hu)
      exact htend.eventually hψ_eq
    have hall : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ∀ j ∈ Finset.range m,
        ψ (ζ ^ j * u) = negTail 0 b N (ζ ^ j * u) + R (ζ ^ j * u) :=
      (eventually_all_finset _).mpr hper
    have hG' : ∀ᶠ u in 𝓝[≠] (0 : ℂ),
        (∑ j ∈ Finset.range m, R (ζ ^ j * u)) = G (u ^ m) :=
      hG_eq.filter_mono nhdsWithin_le_nhds
    filter_upwards [hall, hG'] with u hu hGu
    rw [Finset.sum_congr rfl hu, Finset.sum_add_distrib,
      negTail_plainSymSum c₀ b N hm hζ u, hGu]
    show _ = descTail c₀ m b N (c₀ + u ^ m) + G (c₀ + u ^ m - c₀)
    rw [add_sub_cancel_left]
  · -- the residue bookkeeping
    rw [planarCoeff_add (meromorphicAt_descTail c₀ m b N) hshift_an.meromorphicAt,
      planarCoeff_neg_one_descTail c₀ m hm b N]
    have hG0 : planarCoeff (-1) (fun z => G (z - c₀)) c₀ = 0 :=
      planarCoeff_eq_zero_of_lt_order
        (lt_of_lt_of_le (by exact_mod_cast (by norm_num : (-1 : ℤ) < 0))
          hshift_an.meromorphicOrderAt_nonneg) hshift_an.meromorphicAt
    have hmero_tail : MeromorphicAt (negTail 0 b N) 0 := by
      apply MeromorphicAt.fun_sum
      intro k _
      exact (MeromorphicAt.const (b k) 0).mul (meromorphicAt_zpow_self 0 (-(k : ℤ)))
    have hψm : planarCoeff (-(m : ℤ)) ψ 0 = if m ≤ N then b m else 0 := by
      rw [planarCoeff_congr hψ_eq (-(m : ℤ)),
        show (fun z => negTail 0 b N z + R z) = negTail 0 b N + R from rfl,
        planarCoeff_add hmero_tail hR_an.meromorphicAt]
      have hR0 : planarCoeff (-(m : ℤ)) R 0 = 0 := by
        refine planarCoeff_eq_zero_of_lt_order ?_ hR_an.meromorphicAt
        refine lt_of_lt_of_le ?_ hR_an.meromorphicOrderAt_nonneg
        exact_mod_cast (by omega : -(m : ℤ) < 0)
      have htail : planarCoeff (-(m : ℤ)) (negTail 0 b N) 0 = if m ≤ N then b m else 0 := by
        rw [show negTail 0 b N
            = fun z => ∑ k ∈ Finset.Icc 1 N, b k * (z - 0) ^ (-(k : ℤ)) from rfl,
          planarCoeff_finset_sum (Finset.Icc 1 N)
            (fun k z => b k * (z - 0) ^ (-(k : ℤ))) (-(m : ℤ)) 0
            (fun k _ => (MeromorphicAt.const (b k) 0).mul
              (meromorphicAt_zpow_self 0 (-(k : ℤ))))]
        have hterm : ∀ k ∈ Finset.Icc 1 N,
            planarCoeff (-(m : ℤ)) (fun z => b k * (z - 0) ^ (-(k : ℤ))) 0
              = if k = m then b m else 0 := by
          intro k _
          rw [planarCoeff_monomial]
          by_cases hkm : k = m
          · subst hkm
            rw [if_pos rfl, if_pos rfl]
          · rw [if_neg (fun hc => hkm (by omega : k = m)), if_neg hkm]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ m (fun _ => b m)]
        by_cases hmN : m ≤ N
        · rw [if_pos (Finset.mem_Icc.mpr ⟨hm, hmN⟩), if_pos hmN]
        · rw [if_neg (fun hc => hmN (Finset.mem_Icc.mp hc).2), if_neg hmN]
      rw [hR0, htail, add_zero]
    rw [hψm, hG0, add_zero]
    by_cases hmN : m ≤ N
    · rw [if_pos hmN, if_pos hmN]
    · rw [if_neg hmN, if_neg hmN]
      ring

end Jacobians.Dolbeault.FrameTraceWall

end
