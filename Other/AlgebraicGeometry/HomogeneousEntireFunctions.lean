/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.PolynomialGrowthLiouville
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Entire homogeneous functions on `ℂ^{N+1}` are homogeneous forms

A global holomorphic section of `𝒪(m)` on `ℙᴺ(ℂ)` is the same thing as a holomorphic function on
the punctured cone `ℂ^{N+1} ∖ {0}` that is homogeneous of degree `m`.  This file proves the
function-level half of the comparison `H⁰(ℙᴺ(ℂ)^an, 𝒪(m)^an) = H⁰(ℙᴺ, 𝒪(m))` for `m ≥ 0`: an
*entire* function on `ℂ^{N+1}` which is homogeneous of degree `m` is the evaluation of a
homogeneous polynomial of degree `m`, and conversely.

The growth hypothesis of `Complex.PolynomialGrowth.exists_mvPolynomial_eq_of_growth` is supplied
by compactness of the unit sphere, and the low-order Taylor coefficients are killed by the same
Cauchy estimate run with a *small* radius.
-/

@[expose] public noncomputable section

open scoped Nat
open Set Metric Finset
open scoped ContDiff

namespace Complex.PolynomialGrowth

/-! ### Cauchy estimates at small radius -/

/-- Cauchy's estimates at small radius: if an entire function on `ℂⁿ` is bounded by `C · ‖z‖ᵐ`,
its Taylor coefficients of order `< m` along every complex line vanish. -/
theorem iteratedDeriv_line_eq_zero_of_lt {n m k : ℕ} {f : (Fin n → ℂ) → ℂ} {C : ℝ}
    (hf : Differentiable ℂ f) (hC0 : 0 ≤ C) (hC : ∀ w, ‖f w‖ ≤ C * ‖w‖ ^ m)
    (z : Fin n → ℂ) (hk : k < m) :
    iteratedDeriv k (fun t : ℂ ↦ f (t • z)) 0 = 0 := by
  have hsmul : Differentiable ℂ fun t : ℂ ↦ t • z := by fun_prop
  have hline : Differentiable ℂ fun t : ℂ ↦ f (t • z) := hf.comp hsmul
  set B : ℝ := (k ! : ℝ) * (C * ‖z‖ ^ m) with hBdef
  have hB : 0 ≤ B := by positivity
  have hbound : ∀ R : ℝ, 0 < R → R ≤ 1 →
      ‖iteratedDeriv k (fun t : ℂ ↦ f (t • z)) 0‖ ≤ B * R := by
    intro R hR0 hR1
    have hcauchy : ‖iteratedDeriv k (fun t : ℂ ↦ f (t • z)) 0‖ ≤
        (k ! : ℝ) * (C * (R * ‖z‖) ^ m) / R ^ k := by
      refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR0
        hline.diffContOnCl ?_
      intro t ht
      have htR : ‖t‖ = R := by simpa [mem_sphere_iff_norm] using ht
      have hnorm : ‖t • z‖ = R * ‖z‖ := by rw [norm_smul, htR]
      simpa [hnorm] using hC (t • z)
    refine hcauchy.trans ?_
    have hsplit : R ^ m = R ^ (m - k) * R ^ k := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : k ≤ m)]
    have hkey : (k ! : ℝ) * (C * (R * ‖z‖) ^ m) / R ^ k = B * R ^ (m - k) := by
      rw [mul_pow, hBdef, hsplit]
      field_simp
    rw [hkey]
    refine mul_le_mul_of_nonneg_left ?_ hB
    calc R ^ (m - k) ≤ R ^ 1 := pow_le_pow_of_le_one hR0.le hR1 (by omega)
      _ = R := pow_one R
  have hzero : ‖iteratedDeriv k (fun t : ℂ ↦ f (t • z)) 0‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hBpos : (0 : ℝ) < B + 1 := by linarith
    set R : ℝ := min 1 (ε / (B + 1)) with hRdef
    have hR0 : 0 < R := lt_min zero_lt_one (div_pos hε hBpos)
    have hR1 : R ≤ 1 := min_le_left _ _
    refine (hbound R hR0 hR1).trans ?_
    rw [zero_add]
    calc B * R ≤ B * (ε / (B + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hB
      _ ≤ ε := by
          rw [mul_div_assoc'] at *
          rw [div_le_iff₀ hBpos]
          nlinarith
  simpa using norm_le_zero_iff.mp hzero

/-! ### Homogeneous functions are bounded by a power of the norm -/

/-- A continuous function on `ℂ^{N+1}` homogeneous of degree `m` satisfies `‖F x‖ ≤ C ‖x‖ᵐ`,
with `C` a bound for `F` on the unit sphere. -/
theorem exists_bound_of_homogeneous {N m : ℕ} {F : (Fin (N + 1) → ℂ) → ℂ}
    (hcont : Continuous F)
    (hhom : ∀ (t : ℂ) (x : Fin (N + 1) → ℂ), F (t • x) = t ^ m * F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖F x‖ ≤ C * ‖x‖ ^ m := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_sphere (0 : Fin (N + 1) → ℂ) 1).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C₀ 0, le_max_right _ _, fun x ↦ ?_⟩
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hsphere : ∀ u : Fin (N + 1) → ℂ, ‖u‖ = 1 → ‖F u‖ ≤ C := by
    intro u hu
    exact (hC₀ u (by simpa [mem_sphere_iff_norm] using hu)).trans (le_max_left _ _)
  rcases eq_or_ne x 0 with rfl | hx
  · have he : ‖(fun _ : Fin (N + 1) ↦ (1 : ℂ))‖ = 1 := by
      simp
    have h0 : F 0 = (0 : ℂ) ^ m * F (fun _ : Fin (N + 1) ↦ (1 : ℂ)) := by
      have h := hhom 0 (fun _ : Fin (N + 1) ↦ (1 : ℂ))
      simp only [zero_smul] at h
      exact h
    have hFe : ‖F (fun _ : Fin (N + 1) ↦ (1 : ℂ))‖ ≤ C := hsphere _ he
    rw [h0, norm_mul, norm_pow]
    simp only [norm_zero, norm_zero]
    have hnn : (0 : ℝ) ≤ (0 : ℝ) ^ m := by positivity
    nlinarith [hnn, hFe, norm_nonneg (F (fun _ : Fin (N + 1) ↦ (1 : ℂ)))]
  · have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hu : ‖((‖x‖ : ℂ))⁻¹ • x‖ = 1 := by
      rw [norm_smul]
      simp [hxn]
    have hxeq : ((‖x‖ : ℂ)) • ((‖x‖ : ℂ)⁻¹ • x) = x := by
      rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hxn), one_smul]
    have hFx : F x = (‖x‖ : ℂ) ^ m * F ((‖x‖ : ℂ)⁻¹ • x) := by
      conv_lhs => rw [← hxeq]
      exact hhom _ _
    rw [hFx, norm_mul, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hsphere _ hu) (by positivity)

/-! ### The main comparison -/

/-- **Entire homogeneous functions are homogeneous forms.**  This is the function-level
statement `H⁰(ℙᴺ(ℂ)^an, 𝒪(m)^an) = H⁰(ℙᴺ, 𝒪(m))` for `m ≥ 0`: an entire function on the
coordinate cone `ℂ^{N+1}` that is homogeneous of degree `m` is given by a homogeneous polynomial
of degree `m`. -/
theorem exists_isHomogeneous_eq_of_homogeneous {N m : ℕ} {F : (Fin (N + 1) → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F univ)
    (hhom : ∀ (t : ℂ) (x : Fin (N + 1) → ℂ), F (t • x) = t ^ m * F x) :
    ∃ Q : MvPolynomial (Fin (N + 1)) ℂ, Q.IsHomogeneous m ∧
      ∀ x, MvPolynomial.eval x Q = F x := by
  have hcd : ContDiff ℂ ω F := contDiffOn_univ.mp hF.contDiffOn_of_completeSpace
  have hdiff : Differentiable ℂ F := hcd.differentiable (by simp)
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_homogeneous hdiff.continuous hhom
  have hCgrowth : ∀ w : Fin (N + 1) → ℂ, ‖F w‖ ≤ C * (1 + ‖w‖) ^ m := by
    intro w
    refine (hC w).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    exact pow_le_pow_left₀ (norm_nonneg w) (by linarith) m
  obtain ⟨Q, hQhom, hQeval⟩ :=
    exists_isHomogeneous_eval_eq_diag (n := N + 1) (k := m)
      ((m ! : ℂ)⁻¹ • iteratedFDeriv ℂ m F 0)
  refine ⟨Q, hQhom, fun x ↦ ?_⟩
  have hsmul : Differentiable ℂ fun t : ℂ ↦ t • x := by fun_prop
  have hline : Differentiable ℂ fun t : ℂ ↦ F (t • x) := hdiff.comp hsmul
  have hsum := Complex.hasSum_taylorSeries_of_entire hline 0 1
  have hvanish : ∀ k, k ≠ m →
      (k ! : ℂ)⁻¹ • ((1 : ℂ) - 0) ^ k • iteratedDeriv k (fun t : ℂ ↦ F (t • x)) 0 = 0 := by
    intro k hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [iteratedDeriv_line_eq_zero_of_lt hdiff hC0 hC x hlt]; simp
    · rw [iteratedDeriv_line_eq_zero hdiff hCgrowth x hgt]; simp
  have heq := hsum.unique (hasSum_single m hvanish)
  rw [show F ((1 : ℂ) • x) = F x by rw [one_smul]] at heq
  rw [heq, hQeval x, iteratedDeriv_line_eq_iteratedFDeriv hcd x]
  simp

/-- The converse: a homogeneous polynomial of degree `m` is entire and homogeneous of degree
`m`. -/
theorem eval_smul_of_isHomogeneous {N m : ℕ} {Q : MvPolynomial (Fin (N + 1)) ℂ}
    (hQ : Q.IsHomogeneous m) (t : ℂ) (x : Fin (N + 1) → ℂ) :
    MvPolynomial.eval (t • x) Q = t ^ m * MvPolynomial.eval x Q := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdeg : ∑ i : Fin (N + 1), d i = m := by
    have h := hQ.degree_eq_sum_deg_support hd
    rw [h]
    exact (Finset.sum_subset (Finset.subset_univ _)
      fun i _ hi ↦ Finsupp.notMem_support_iff.mp hi).symm
  have hprod : ∏ i : Fin (N + 1), (t • x) i ^ (d i) =
      t ^ m * ∏ i : Fin (N + 1), x i ^ (d i) := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  rw [hprod]
  ring

/-- **Characterisation of entire homogeneous functions.**  On the coordinate cone `ℂ^{N+1}`, the
entire functions homogeneous of degree `m` are exactly the degree-`m` forms.  This is the
function-level form of `H⁰(ℙᴺ(ℂ)^an, 𝒪(m)^an) = H⁰(ℙᴺ, 𝒪(m))` for `m ≥ 0`. -/
theorem analyticOnNhd_homogeneous_iff {N m : ℕ} {F : (Fin (N + 1) → ℂ) → ℂ} :
    (AnalyticOnNhd ℂ F univ ∧ ∀ (t : ℂ) (x : Fin (N + 1) → ℂ), F (t • x) = t ^ m * F x) ↔
      ∃ Q : MvPolynomial (Fin (N + 1)) ℂ, Q.IsHomogeneous m ∧
        ∀ x, MvPolynomial.eval x Q = F x := by
  constructor
  · rintro ⟨hF, hhom⟩
    exact exists_isHomogeneous_eq_of_homogeneous hF hhom
  · rintro ⟨Q, hQ, hQeval⟩
    have hfun : F = fun x : Fin (N + 1) → ℂ ↦ MvPolynomial.eval x Q := by
      funext x; exact (hQeval x).symm
    subst hfun
    exact ⟨analyticOnNhd_eval Q, fun t x ↦ eval_smul_of_isHomogeneous hQ t x⟩

/-! ### Negative degrees -/

/-- An *entire* function on `ℂ^{N+1}` that is homogeneous of a strictly negative degree
vanishes identically: letting the scaling parameter tend to `0` forces the value to be `0`.

Note that this is **not** by itself the vanishing `H⁰(ℙᴺ(ℂ)^an, 𝒪(-k)^an) = 0`: a section of a
negative twist is homogeneous on the *punctured* cone and need not extend over the origin, so the
sheaf-level vanishing additionally needs a Riemann/Hartogs extension theorem (for `N ≥ 1`) or a
direct cocycle argument.  For `N = 0` the sheaf-level vanishing is false, since `ℙ⁰` is a point. -/
theorem eq_zero_of_homogeneous_neg {N k : ℕ} {F : (Fin (N + 1) → ℂ) → ℂ}
    (hcont : Continuous F) (hk : 0 < k)
    (hhom : ∀ t : ℂ, t ≠ 0 → ∀ x : Fin (N + 1) → ℂ, t ^ k * F (t • x) = F x) (x) :
    F x = 0 := by
  have hsmul : Continuous fun t : ℂ ↦ F (t • x) := hcont.comp (by fun_prop)
  have hcontmul : ContinuousAt (fun t : ℂ ↦ t ^ k * F (t • x)) 0 :=
    ((continuous_pow k).continuousAt).mul hsmul.continuousAt
  have hlim : Filter.Tendsto (fun t : ℂ ↦ t ^ k * F (t • x))
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 0) := by
    have h := hcontmul.continuousWithinAt (s := {(0 : ℂ)}ᶜ)
    simpa [zero_pow hk.ne'] using h.tendsto
  have hconst : Filter.Tendsto (fun t : ℂ ↦ t ^ k * F (t • x))
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (F x)) := by
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := F x))
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hhom t ht x).symm
  exact tendsto_nhds_unique hconst hlim

end Complex.PolynomialGrowth
