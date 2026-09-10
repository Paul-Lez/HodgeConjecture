/-
  Dolbeault ladder — **Forster 13.2**: `∂̄`-solvability on an *open* disk.

  This is the single missing analytic engine for the Čech finiteness node.  The repo already has:

    * `DbarDisk.dbar_solvable_of_compactSupport` (Forster 13.1, Cauchy transform), and
    * `DbarDiskCohomology.dbar_solvable_ball` — solving `∂̄u = g` on a ball, but only for a
      **globally** smooth datum `g`.

  Forster 13.2 removes the global-smoothness requirement: it solves `∂̄u = g` on an open disk for a
  datum `g` smooth on the *open disk only*.  This is exactly what the genuine disk-acyclicity
  `H¹(disk, 𝒪) = 0` (Forster 13.4 — required by Leray's theorem 12.8) needs: there the datum is the
  glued `∂̄(smooth split)`, smooth on the union's chart-image ball but not globally, leaving no room
  for a cutoff bump.

  **Proof (Forster p.106, exhaustion).**  Exhaust `ball c R` by `ball c ρₙ`, `ρₙ ↑ R`.  Cutoffs `χₙ`
  (`= 1` on `closedBall c ρₙ`, supported in `ball c ρₙ₊₁ ⋐ ball c R`) make `χₙ·g` globally smooth with
  compact support, so 13.1 gives `fₙ` with `∂̄fₙ = χₙ·g = g` on `ball c ρₙ`.  Inductively correct
  `f̃ₙ` by a holomorphic polynomial `Pₙ` (Taylor partial sum of the holomorphic `fₙ₊₁ − f̃ₙ`) so that
  `‖f̃ₙ₊₁ − f̃ₙ‖ ≤ 2⁻ⁿ` on `closedBall c ρₙ`; the limit `u` converges locally uniformly, is smooth, and
  the holomorphic corrections preserve `∂̄u = g`.

  Mathlib ingredients (all confirmed present): `DifferentiableOn.hasFPowerSeriesOnBall`,
  `HasFPowerSeriesOnBall.tendstoUniformlyOn'` (partial sums = polynomials → `f` uniformly on
  subdisks), `TendstoLocallyUniformlyOn.differentiableOn` (locally-uniform limit of holomorphic is
  holomorphic), `ContDiffBump`.
-/
import KirovDolbeault.Dolbeault.DbarDiskCohomology

open Complex Metric Filter Topology
open scoped NNReal ENNReal

-- The transparency option resolves the `IsScalarTower ℝ ℂ ℂ` diamond (the documented `Module ℝ`
-- clash) so `restrictScalars`/`ContDiff.restrict_scalars` from `ℂ` to `ℝ` elaborate; the repo's other
-- Dolbeault files set the same option.
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault
namespace DbarOpenDisk

/-! ### Keystone lemmas (proven) -/

/-- Power-series partial sums (centred at `c`) are entire — they are polynomials. -/
theorem diff_partialSum (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) (c : ℂ) :
    Differentiable ℂ (fun y => p.partialSum n (y - c)) := by
  unfold FormalMultilinearSeries.partialSum
  apply Differentiable.fun_sum
  intro k _
  have hcmm : ContDiff ℂ (⊤ : ℕ∞) (p k) := (p k).contDiff
  exact (hcmm.differentiable (by norm_num)).comp (by fun_prop)

/-- **Runge/Taylor approximation on a closed subdisk.**  A function holomorphic on `ball c R'` is,
on any closed subdisk `closedBall c r` (`r < R'`), uniformly approximated to within `ε` by an *entire*
function (a Taylor partial sum). -/
theorem exists_holo_approx (φ : ℂ → ℂ) (c : ℂ) (R' : ℝ)
    (hφ : DifferentiableOn ℂ φ (ball c R')) (r : ℝ) (hr0 : 0 ≤ r) (hrR : r < R')
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧ ∀ z ∈ closedBall c r, ‖φ z - P z‖ ≤ ε := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  have hs0 : 0 < s := hr0.trans_lt hrs
  set R₀ : ℝ≥0 := s.toNNReal with hR₀
  have hR₀pos : 0 < R₀ := Real.toNNReal_pos.mpr hs0
  have hR₀coe : (R₀ : ℝ) = s := Real.coe_toNNReal s hs0.le
  have hsub : closedBall c (R₀ : ℝ) ⊆ ball c R' := by
    rw [hR₀coe]; exact closedBall_subset_ball hsR
  have hball := (hφ.mono hsub).hasFPowerSeriesOnBall hR₀pos
  set r' : ℝ≥0 := ((r + s) / 2).toNNReal with hr'
  have hr'coe : (r' : ℝ) = (r + s) / 2 := Real.coe_toNNReal _ (by positivity)
  have hr'lt : (r' : ℝ≥0∞) < (R₀ : ℝ≥0∞) := by
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hr'coe, hR₀coe]; linarith
  have htu := hball.tendstoUniformlyOn' hr'lt
  rw [Metric.tendstoUniformlyOn_iff] at htu
  obtain ⟨N, hN⟩ := (htu ε hε).exists
  refine ⟨fun y => (cauchyPowerSeries φ c R₀).partialSum N (y - c), diff_partialSum _ _ _, ?_⟩
  intro z hz
  have hzin : z ∈ ball c (r' : ℝ) := by
    rw [mem_ball, hr'coe]; rw [mem_closedBall] at hz; linarith
  have := hN z hzin
  rw [dist_eq_norm] at this
  exact this.le

/-- **Cutoff × open-disk-smooth datum is globally smooth.**  If `g` is smooth on the open set `U`,
`ψ` is globally smooth, and `tsupport ψ ⊆ U`, then `ψ·g` is globally smooth (it is `ψ·g` on `U` and
`0` off `tsupport ψ`). -/
theorem contDiff_cutoff_mul {g ψ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsupp : tsupport ψ ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hψ.contDiffAt.mul (hg.contDiffAt (hU.mem_nhds hx))
  · have hxs : x ∉ tsupport ψ := fun h => hx (hsupp h)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hxs] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]

/-- `∂̄` is subtractive at a point where both functions are real-differentiable. -/
theorem dbar_sub {f h : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) :
    DbarDisk.dbar (fun x => f x - h x) z = DbarDisk.dbar f z - DbarDisk.dbar h z := by
  unfold DbarDisk.dbar
  rw [fderiv_fun_sub hf hh]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-- `∂̄` is additive at a point where both functions are real-differentiable. -/
theorem dbar_add {f h : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) :
    DbarDisk.dbar (fun x => f x + h x) z = DbarDisk.dbar f z + DbarDisk.dbar h z := by
  unfold DbarDisk.dbar
  rw [fderiv_fun_add hf hh]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- An entire function is `ℝ`-smooth (holomorphic ⟹ `ℝ`-analytic ⟹ `C^∞`). -/
theorem entire_contDiffR {P : ℂ → ℂ} (hP : Differentiable ℂ P) : ContDiff ℝ (⊤ : ℕ∞) P := by
  have hC : AnalyticOnNhd ℂ P Set.univ := hP.differentiableOn.analyticOnNhd isOpen_univ
  exact (hC.restrictScalars (𝕜 := ℝ)).contDiff

/-- A holomorphic function on an open set is `ℝ`-smooth there. -/
theorem holo_contDiffOnR {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    ContDiffOn ℝ (⊤ : ℕ∞) f s :=
  ((hf.analyticOnNhd hs).restrictScalars (𝕜 := ℝ)).contDiffOn hs.uniqueDiffOn

/-! ### Exhaustion radii and the per-ball solve -/

/-- The exhaustion radii `ρₙ = R(1 − 2⁻⁽ⁿ⁺¹⁾) ↑ R`. -/
noncomputable def rho (R : ℝ) (n : ℕ) : ℝ := R * (1 - (1 / 2) ^ (n + 1))

/-- The exhaustion radii are positive, strictly increasing, bounded by `R`, and tend to `R`. -/
theorem rho_props {R : ℝ} (hR : 0 < R) :
    (∀ n, 0 < rho R n) ∧ StrictMono (rho R) ∧ (∀ n, rho R n < R) ∧
      Tendsto (rho R) atTop (nhds R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have h1 : (1 / 2 : ℝ) ^ (n + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    have : (0 : ℝ) < 1 - (1 / 2) ^ (n + 1) := by linarith
    rw [rho]; positivity
  · intro a b hab
    have : (1 / 2 : ℝ) ^ (b + 1) < (1 / 2) ^ (a + 1) :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
    simp only [rho]; nlinarith
  · intro n
    have h1 : (0 : ℝ) < (1 / 2) ^ (n + 1) := by positivity
    simp only [rho]; nlinarith
  · have h1 : Tendsto (fun n => (1 / 2 : ℝ) ^ (n + 1)) atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)
    have h2 := (tendsto_const_nhds (x := R)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub h1)
    have hrw : rho R = fun n => R * (1 - (1 / 2) ^ (n + 1)) := rfl
    rw [hrw]; simpa using h2

/-- **The per-ball solve.** With the open-disk datum `g`, solve `∂̄u = g` on `ball c a` for radii
`0 < a < b < R`: cut off `g` by a bump (`= 1` on `closedBall c a`, supported in `closedBall c b ⊆
ball c R`) so `χ·g` is globally smooth with compact support, then apply Forster 13.1. -/
theorem solve_on_ball (c : ℂ) {R : ℝ} {g : ℂ → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (ball c R))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hbR : b < R) :
    ∃ u : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) u ∧ ∀ z ∈ ball c a, DbarDisk.dbar u z = g z := by
  set χ : ContDiffBump c := { rIn := a, rOut := b, rIn_pos := ha, rIn_lt_rOut := hab } with hχ
  set χℂ : ℂ → ℂ := fun z => ((χ z : ℝ) : ℂ) with hχℂ
  obtain ⟨hχℂ_smooth, hχℂ_supp⟩ := DbarLocal.contDiff_hasCompactSupport_ofReal_contDiffBump χ
  have htsupp : tsupport χℂ ⊆ ball c R := by
    have h1 : tsupport χℂ ⊆ tsupport (fun z => (χ z : ℝ)) := by
      apply closure_mono; intro z hz
      simp only [Function.mem_support, hχℂ, ne_eq] at hz ⊢
      intro h0; exact hz (by rw [h0]; rfl)
    exact (χ.tsupport_eq ▸ h1).trans (closedBall_subset_ball hbR)
  have hG_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun z => χℂ z * g z) :=
    contDiff_cutoff_mul isOpen_ball hg hχℂ_smooth htsupp
  have hG_supp : HasCompactSupport (fun z => χℂ z * g z) := hχℂ_supp.mul_right
  obtain ⟨u, hu_smooth, hu_dbar⟩ := DbarDisk.dbar_solvable_of_compactSupport hG_smooth hG_supp
  refine ⟨u, hu_smooth, fun z hz => ?_⟩
  rw [hu_dbar z]
  show ((χ z : ℝ) : ℂ) * g z = g z
  rw [χ.one_of_mem_closedBall (ball_subset_closedBall hz)]
  simp only [Complex.ofReal_one, one_mul]

/-! ### Forster 13.2 — the main theorem -/

/-- **Forster 13.2 — `∂̄`-solvability on an open disk.**  For `g` smooth on the *open* ball
`ball c R`, there is `u` smooth on `ball c R` with `∂̄u = g` there.  Unlike
`DbarDiskCohomology.dbar_solvable_ball`, the datum need not be globally smooth — this is the version
required by genuine disk-acyclicity (Forster 13.4 / Leray 12.8). -/
theorem dbar_solvable_open_disk (c : ℂ) {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (ball c R)) :
    ∃ u : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u (ball c R) ∧
      ∀ z ∈ ball c R, DbarDisk.dbar u z = g z := by
  obtain ⟨ρpos, ρmono, ρltR, ρtend⟩ := rho_props hR
  set ρ := rho R with hρ
  -- **Base case.**  Solve on `ball c (ρ 1)`.
  obtain ⟨φ0, hφ0_smooth, hφ0_dbar⟩ :=
    solve_on_ball c hg (a := ρ 1) (b := ρ 2) (ρpos 1) (ρmono (by norm_num)) (ρltR 2)
  -- **Step.**  Correct a solution on `ball c (ρ (n+1))` to one on `ball c (ρ (n+2))`, controlling the
  -- change on `closedBall c (ρ n)` by `2⁻ⁿ` via a holomorphic (Taylor) correction.
  have step : ∀ (n : ℕ) (φ : ℂ → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ →
      (∀ z ∈ ball c (ρ (n + 1)), DbarDisk.dbar φ z = g z) →
      ∃ φ' : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ' ∧
        (∀ z ∈ ball c (ρ (n + 2)), DbarDisk.dbar φ' z = g z) ∧
        ∀ z ∈ closedBall c (ρ n), ‖φ' z - φ z‖ ≤ (1 / 2) ^ n := by
    intro n φ hφ_smooth hφ_dbar
    obtain ⟨f, hf_smooth, hf_dbar⟩ :=
      solve_on_ball c hg (a := ρ (n + 2)) (b := ρ (n + 3)) (ρpos _) (ρmono (by omega)) (ρltR _)
    have hfφ_holo : DifferentiableOn ℂ (fun z => f z - φ z) (ball c (ρ (n + 1))) := by
      intro z hz
      have hdb : DbarDisk.dbar (fun x => f x - φ x) z = 0 := by
        rw [dbar_sub (hf_smooth.differentiable (by norm_num) z)
              (hφ_smooth.differentiable (by norm_num) z),
          hf_dbar z (ball_subset_ball (ρmono (by omega)).le hz), hφ_dbar z hz, sub_self]
      exact (DbarDiskCohomology.differentiableAt_of_dbar_eq_zero (hf_smooth.sub hφ_smooth)
        hdb).differentiableWithinAt
    obtain ⟨P, hP_diff, hP_approx⟩ :=
      exists_holo_approx (fun z => f z - φ z) c (ρ (n + 1)) hfφ_holo (ρ n) (ρpos n).le
        (ρmono (by omega)) ((1 / 2) ^ n) (by positivity)
    refine ⟨fun z => f z - P z, hf_smooth.sub (entire_contDiffR hP_diff), ?_, ?_⟩
    · intro z hz
      rw [dbar_sub (hf_smooth.differentiable (by norm_num) z)
          ((entire_contDiffR hP_diff).differentiable (by norm_num) z),
        hf_dbar z hz, DbarDisk.dbar_eq_zero_of_differentiableAt (hP_diff z), sub_zero]
    · intro z hz
      have heq : f z - P z - φ z = f z - φ z - P z := by ring
      rw [heq]; exact hP_approx z hz
  -- **Build the corrected sequence** `φₙ` by recursion (`choose!` removes the proof-dependence).
  choose! nxt hnxt_smooth hnxt_dbar hnxt_bd using step
  set seq : ℕ → ℂ → ℂ := fun n => Nat.rec φ0 (fun k φ => nxt k φ) n with hseqdef
  have hseq0 : seq 0 = φ0 := rfl
  have hseqS : ∀ n, seq (n + 1) = nxt n (seq n) := fun n => rfl
  have hseq_inv : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (seq n) ∧
      ∀ z ∈ ball c (ρ (n + 1)), DbarDisk.dbar (seq n) z = g z := by
    intro n
    induction n with
    | zero => exact ⟨hφ0_smooth, hφ0_dbar⟩
    | succ k ih =>
      rw [hseqS k]
      exact ⟨hnxt_smooth k (seq k) ih.1 ih.2, hnxt_dbar k (seq k) ih.1 ih.2⟩
  have hseq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (seq n) := fun n => (hseq_inv n).1
  have hseq_dbar : ∀ n, ∀ z ∈ ball c (ρ (n + 1)), DbarDisk.dbar (seq n) z = g z :=
    fun n => (hseq_inv n).2
  have hseq_bd : ∀ n, ∀ z ∈ closedBall c (ρ n), ‖seq (n + 1) z - seq n z‖ ≤ (1 / 2) ^ n := by
    intro n; rw [hseqS n]; exact hnxt_bd n (seq n) (hseq_smooth n) (hseq_dbar n)
  -- **Differences.**  `D k = φₖ₊₁ − φₖ`; each is holomorphic on `ball c (ρ (k+1))`.
  set D : ℕ → ℂ → ℂ := fun k z => seq (k + 1) z - seq k z with hD
  have hDholo : ∀ k, DifferentiableOn ℂ (D k) (ball c (ρ (k + 1))) := by
    intro k z hz
    have hdb : DbarDisk.dbar (D k) z = 0 := by
      have h := dbar_sub (hseq_smooth (k + 1) |>.differentiable (by norm_num) z)
        (hseq_smooth k |>.differentiable (by norm_num) z)
      rw [show D k = (fun x => seq (k + 1) x - seq k x) from rfl, h,
        hseq_dbar (k + 1) z (ball_subset_ball (ρmono (by omega)).le hz), hseq_dbar k z hz, sub_self]
    exact (DbarDiskCohomology.differentiableAt_of_dbar_eq_zero
      ((hseq_smooth (k + 1)).sub (hseq_smooth k)) hdb).differentiableWithinAt
  -- **Pointwise bound** of the shifted differences on `closedBall c (ρ m)`.
  have hDbd : ∀ m k, ∀ z ∈ closedBall c (ρ m), ‖D (k + m) z‖ ≤ (1 / 2) ^ (k + m) := by
    intro m k z hz
    exact hseq_bd (k + m) z (closedBall_subset_closedBall (ρmono.le_iff_le.mpr (by omega)) hz)
  have hgeom : ∀ m, Summable (fun k => (1 / 2 : ℝ) ^ (k + m)) := by
    intro m; simp_rw [pow_add]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  -- **Summability** of the difference series at points of `ball c R`.
  have hsummable : ∀ z ∈ ball c R, Summable (fun k => D k z) := by
    intro z hz
    obtain ⟨m, hm⟩ := (ρtend.eventually (Ioi_mem_nhds (mem_ball.mp hz))).exists
    rw [← summable_nat_add_iff m]
    refine Summable.of_norm_bounded (hgeom m) (fun k => ?_)
    exact hDbd m k z (mem_closedBall.mpr (le_of_lt hm))
  -- **The tail series** `T m = ∑' k, D (k+m)` is holomorphic on `ball c (ρ m)` (M-test +
  -- locally-uniform limit of holomorphic partial sums).
  set T : ℕ → ℂ → ℂ := fun m z => ∑' k, D (k + m) z with hT
  have hTm_holo : ∀ m, DifferentiableOn ℂ (T m) (ball c (ρ m)) := by
    intro m
    have hMtest := tendstoUniformlyOn_tsum (hgeom m)
      (s := closedBall c (ρ m)) (fun k z hz => hDbd m k z hz)
    have hlu : TendstoLocallyUniformlyOn (fun t z => ∑ k ∈ t, D (k + m) z) (T m) atTop
        (ball c (ρ m)) :=
      (hMtest.mono ball_subset_closedBall).tendstoLocallyUniformlyOn
    refine hlu.differentiableOn (Filter.Eventually.of_forall (fun t => ?_)) isOpen_ball
    exact DifferentiableOn.fun_sum (fun k _ =>
      (hDholo (k + m)).mono (ball_subset_ball (ρmono.le_iff_le.mpr (by omega))))
  -- **Local representation** `u = seq m + T m` on `ball c (ρ m)` (telescope + tsum split).
  have hrepr : ∀ m, ∀ w ∈ ball c (ρ m), seq 0 w + ∑' k, D k w = seq m w + T m w := by
    intro m w hw
    have hsw : Summable (fun k => D k w) := hsummable w (ball_subset_ball (ρltR m).le hw)
    have h1 : ∑' k, D k w = (∑ i ∈ Finset.range m, D i w) + ∑' k, D (k + m) w :=
      (hsw.sum_add_tsum_nat_add m).symm
    have h2 : ∑ i ∈ Finset.range m, D i w = seq m w - seq 0 w :=
      Finset.sum_range_sub (fun k => seq k w) m
    rw [h1, h2]
    show seq 0 w + ((seq m w - seq 0 w) + T m w) = seq m w + T m w
    ring
  -- **The candidate solution** `u = seq 0 + ∑' D`.
  refine ⟨fun z => seq 0 z + ∑' k, D k z, ?_, ?_⟩
  · -- `ContDiffOn`: locally `u = seq m + T m`, both `ℝ`-smooth.
    intro z hz
    obtain ⟨m, hm⟩ := (ρtend.eventually (Ioi_mem_nhds (mem_ball.mp hz))).exists
    have hzm : z ∈ ball c (ρ m) := mem_ball.mpr hm
    have heq : (fun w => seq 0 w + ∑' k, D k w) =ᶠ[𝓝 z] (fun w => seq m w + T m w) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hzm) (hrepr m)
    have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => seq m w + T m w) z :=
      (hseq_smooth m).contDiffAt.add
        ((holo_contDiffOnR isOpen_ball (hTm_holo m)).contDiffAt (isOpen_ball.mem_nhds hzm))
    exact (hcd.congr_of_eventuallyEq heq).contDiffWithinAt
  · -- The `∂̄` equation: locally `∂̄u = ∂̄(seq m) + ∂̄(T m) = g + 0`.
    intro z hz
    obtain ⟨m, hm⟩ := (ρtend.eventually (Ioi_mem_nhds (mem_ball.mp hz))).exists
    have hzm : z ∈ ball c (ρ m) := mem_ball.mpr hm
    have heq : (fun w => seq 0 w + ∑' k, D k w) =ᶠ[𝓝 z] (fun w => seq m w + T m w) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hzm) (hrepr m)
    have hTm_diffC : DifferentiableAt ℂ (T m) z := (hTm_holo m z hzm).differentiableAt
      (isOpen_ball.mem_nhds hzm)
    have hcongr : DbarDisk.dbar (fun w => seq 0 w + ∑' k, D k w) z
        = DbarDisk.dbar (fun w => seq m w + T m w) z := by
      simp only [DbarDisk.dbar, heq.fderiv_eq]
    rw [hcongr, dbar_add ((hseq_smooth m).differentiable (by norm_num) z)
        (hTm_diffC.restrictScalars ℝ), DbarDisk.dbar_eq_zero_of_differentiableAt hTm_diffC,
      add_zero, hseq_dbar m z (ball_subset_ball (ρmono (by omega)).le hzm)]

end DbarOpenDisk
end Jacobians.Dolbeault
