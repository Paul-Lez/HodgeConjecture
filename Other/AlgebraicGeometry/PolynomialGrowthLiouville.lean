/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Liouville's theorem with polynomial growth, in several complex variables

This file proves the multivariable generalisation of Liouville's theorem that is the analytic
heart of the `H⁰` half of projective GAGA for twists of the structure sheaf: an entire function
on `ℂⁿ` whose growth is bounded by `C · (1 + ‖z‖)ᵐ` is a polynomial of total degree at most `m`.
-/

@[expose] public noncomputable section

open scoped Nat
open Set Metric Finset
open scoped ContDiff Manifold

namespace Complex.PolynomialGrowth

/-! ### Homogeneous parts coming from continuous multilinear maps -/

/-- The diagonal restriction of a continuous multilinear map on `k` copies of `ℂⁿ` is given by a
homogeneous polynomial of degree `k`. -/
theorem exists_isHomogeneous_eval_eq_diag {n k : ℕ}
    (T : ContinuousMultilinearMap ℂ (fun _ : Fin k => Fin n → ℂ) ℂ) :
    ∃ P : MvPolynomial (Fin n) ℂ, P.IsHomogeneous k ∧
      ∀ z : Fin n → ℂ, MvPolynomial.eval z P = T fun _ ↦ z := by
  classical
  refine ⟨∑ c : Fin k → Fin n, MvPolynomial.C (T fun j ↦ Pi.single (c j) 1) *
      ∏ j : Fin k, MvPolynomial.X (c j), ?_, ?_⟩
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun c _ ↦ ?_
    refine MvPolynomial.IsHomogeneous.C_mul ?_ _
    have := MvPolynomial.IsHomogeneous.prod (R := ℂ) (σ := Fin n) Finset.univ
      (fun j : Fin k ↦ MvPolynomial.X (c j)) (fun _ ↦ 1)
      (fun j _ ↦ MvPolynomial.isHomogeneous_X ℂ (c j))
    simpa using this
  · intro z
    have hz : (fun _ : Fin k ↦ z) = fun _ : Fin k ↦ ∑ i : Fin n, z i • Pi.single i (1 : ℂ) := by
      funext _
      funext i
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    rw [hz]
    rw [show (T fun _ : Fin k ↦ ∑ i : Fin n, z i • Pi.single i (1 : ℂ)) =
        T.toMultilinearMap fun _ : Fin k ↦ ∑ i : Fin n, z i • Pi.single i (1 : ℂ) from rfl,
      MultilinearMap.map_sum]
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_prod,
      MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [show (T.toMultilinearMap fun j ↦ z (c j) • Pi.single (c j) (1 : ℂ)) =
        (∏ j : Fin k, z (c j)) • T.toMultilinearMap fun j ↦ Pi.single (c j) (1 : ℂ) from
      MultilinearMap.map_smul_univ _ _ _]
    simp [mul_comm]

/-! ### Cauchy estimates along complex lines -/

/-- If an entire function on `ℂⁿ` grows at most like `C · (1 + ‖z‖)ᵐ`, then along every complex
line through the origin all its one-variable Taylor coefficients of order `> m` vanish. -/
theorem iteratedDeriv_line_eq_zero {n m k : ℕ} {f : (Fin n → ℂ) → ℂ} {C : ℝ}
    (hf : Differentiable ℂ f) (hC : ∀ w, ‖f w‖ ≤ C * (1 + ‖w‖) ^ m)
    (z : Fin n → ℂ) (hk : m < k) :
    iteratedDeriv k (fun t : ℂ ↦ f (t • z)) 0 = 0 := by
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg (f 0)).trans (hC 0)
    simpa using this
  have hsmul : Differentiable ℂ fun t : ℂ ↦ t • z := by fun_prop
  have hline : Differentiable ℂ fun t : ℂ ↦ f (t • z) := hf.comp hsmul
  set B : ℝ := (k ! : ℝ) * (C * (1 + ‖z‖) ^ m) with hBdef
  have hB : 0 ≤ B := by positivity
  have hbound : ∀ R : ℝ, 1 ≤ R →
      ‖iteratedDeriv k (fun t : ℂ ↦ f (t • z)) 0‖ ≤ B / R := by
    intro R hR
    have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
    have hcauchy : ‖iteratedDeriv k (fun t : ℂ ↦ f (t • z)) 0‖ ≤
        (k ! : ℝ) * (C * (1 + R * ‖z‖) ^ m) / R ^ k := by
      refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR0
        hline.diffContOnCl ?_
      intro t ht
      have htR : ‖t‖ = R := by simpa [mem_sphere_iff_norm] using ht
      have : ‖t • z‖ = R * ‖z‖ := by rw [norm_smul, htR]
      simpa [this] using hC (t • z)
    refine hcauchy.trans ?_
    have hstep : (1 + R * ‖z‖) ^ m ≤ R ^ m * (1 + ‖z‖) ^ m := by
      have h1 : 1 + R * ‖z‖ ≤ R * (1 + ‖z‖) := by nlinarith [norm_nonneg z]
      calc (1 + R * ‖z‖) ^ m ≤ (R * (1 + ‖z‖)) ^ m :=
            pow_le_pow_left₀ (by positivity) h1 m
        _ = R ^ m * (1 + ‖z‖) ^ m := by rw [mul_pow]
    have hnum : (k ! : ℝ) * (C * (1 + R * ‖z‖) ^ m) ≤ B * R ^ m := by
      have : C * (1 + R * ‖z‖) ^ m ≤ C * (R ^ m * (1 + ‖z‖) ^ m) :=
        mul_le_mul_of_nonneg_left hstep hC0
      calc (k ! : ℝ) * (C * (1 + R * ‖z‖) ^ m)
          ≤ (k ! : ℝ) * (C * (R ^ m * (1 + ‖z‖) ^ m)) := by
            exact mul_le_mul_of_nonneg_left this (by positivity)
        _ = B * R ^ m := by rw [hBdef]; ring
    have hRk : R ^ m * R ≤ R ^ k := by
      have : R ^ (m + 1) ≤ R ^ k := pow_le_pow_right₀ hR hk
      simpa [pow_succ] using this
    rw [div_le_div_iff₀ (by positivity) hR0]
    calc (k ! : ℝ) * (C * (1 + R * ‖z‖) ^ m) * R ≤ B * R ^ m * R :=
          mul_le_mul_of_nonneg_right hnum hR0.le
      _ = B * (R ^ m * R) := by ring
      _ ≤ B * R ^ k := mul_le_mul_of_nonneg_left hRk hB
  have hzero : ‖iteratedDeriv k (fun t : ℂ ↦ f (t • z)) 0‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hR : (1 : ℝ) ≤ 1 + B / ε := le_add_of_nonneg_right (div_nonneg hB hε.le)
    refine (hbound (1 + B / ε) hR).trans ?_
    rw [zero_add, div_le_iff₀ (by linarith)]
    have : ε * (1 + B / ε) = ε + B := by field_simp
    rw [this]
    linarith
  simpa using norm_le_zero_iff.mp hzero

/-! ### Identification of the line derivatives with the iterated derivatives -/

/-- The `k`-th derivative at the origin of the restriction of `f` to the complex line through `z`
is the `k`-th iterated derivative of `f` at the origin evaluated on the diagonal `(z, …, z)`. -/
theorem iteratedDeriv_line_eq_iteratedFDeriv {n k : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : ContDiff ℂ ω f) (z : Fin n → ℂ) :
    iteratedDeriv k (fun t : ℂ ↦ f (t • z)) 0 = iteratedFDeriv ℂ k f 0 fun _ ↦ z := by
  set L : ℂ →L[ℂ] (Fin n → ℂ) := (ContinuousLinearMap.id ℂ ℂ).smulRight z with hL
  have hfun : (fun t : ℂ ↦ f (t • z)) = f ∘ L := rfl
  rw [iteratedDeriv_eq_iteratedFDeriv, hfun,
    L.iteratedFDeriv_comp_right hf 0 (le_top : (k : WithTop ℕ∞) ≤ ω)]
  simp [hL]

/-! ### Liouville's theorem with polynomial growth -/

/-- **Polynomial-growth Liouville theorem, homogeneous form.**  An entire function on `ℂⁿ`
bounded by `C · (1 + ‖z‖)ᵐ` is the sum of `m + 1` homogeneous polynomial functions, the `k`-th
being the `k`-th diagonal Taylor term at the origin. -/
theorem exists_isHomogeneous_sum_eq {n m : ℕ} {f : (Fin n → ℂ) → ℂ} {C : ℝ}
    (hf : AnalyticOnNhd ℂ f univ) (hC : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ P : ℕ → MvPolynomial (Fin n) ℂ, (∀ k, (P k).IsHomogeneous k) ∧
      ∀ z, ∑ k ∈ Finset.range (m + 1), MvPolynomial.eval z (P k) = f z := by
  have hcd : ContDiff ℂ ω f := contDiffOn_univ.mp hf.contDiffOn_of_completeSpace
  have hdiff : Differentiable ℂ f := hcd.differentiable (by simp)
  choose P hPhom hPeval using fun k : ℕ ↦
    exists_isHomogeneous_eval_eq_diag (n := n) (k := k)
      ((k ! : ℂ)⁻¹ • iteratedFDeriv ℂ k f 0)
  refine ⟨P, hPhom, fun z ↦ ?_⟩
  have hsmul : Differentiable ℂ fun t : ℂ ↦ t • z := by fun_prop
  have hline : Differentiable ℂ fun t : ℂ ↦ f (t • z) := hdiff.comp hsmul
  have hsum := Complex.hasSum_taylorSeries_of_entire hline 0 1
  have hvanish : ∀ k ∉ Finset.range (m + 1),
      (k ! : ℂ)⁻¹ • ((1 : ℂ) - 0) ^ k • iteratedDeriv k (fun t : ℂ ↦ f (t • z)) 0 = 0 := by
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hk
    rw [iteratedDeriv_line_eq_zero hdiff hC z hk]
    simp
  have heq := hsum.unique (hasSum_sum_of_ne_finset_zero hvanish)
  rw [show f ((1 : ℂ) • z) = f z by rw [one_smul]] at heq
  rw [heq]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hPeval k z, iteratedDeriv_line_eq_iteratedFDeriv hcd z]
  simp

/-- **Liouville's theorem with polynomial growth in several complex variables.**  An entire
function on `ℂⁿ` whose growth is bounded by `C · (1 + ‖z‖)ᵐ` is a polynomial function of total
degree at most `m`.  This is the analytic input to the `H⁰` comparison for twists of the
structure sheaf of complex projective space. -/
theorem exists_mvPolynomial_eq_of_growth {n m : ℕ} {f : (Fin n → ℂ) → ℂ} {C : ℝ}
    (hf : AnalyticOnNhd ℂ f univ) (hC : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ P : MvPolynomial (Fin n) ℂ, P.totalDegree ≤ m ∧ ∀ z, MvPolynomial.eval z P = f z := by
  obtain ⟨P, hPhom, hPsum⟩ := exists_isHomogeneous_sum_eq hf hC
  refine ⟨∑ k ∈ Finset.range (m + 1), P k, ?_, fun z ↦ ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun k hk ↦ ?_
    exact (hPhom k).totalDegree_le.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  · rw [map_sum]
    exact hPsum z

/-- The degree-zero case is the classical Liouville theorem: a bounded entire function on `ℂⁿ`
is constant. -/
theorem exists_eq_const_of_bounded_of_analytic {n : ℕ} {f : (Fin n → ℂ) → ℂ} {C : ℝ}
    (hf : AnalyticOnNhd ℂ f univ) (hC : ∀ z, ‖f z‖ ≤ C) :
    ∃ c : ℂ, ∀ z, f z = c := by
  obtain ⟨P, hP, hPeval⟩ :=
    exists_mvPolynomial_eq_of_growth (m := 0) hf (by simpa using hC)
  refine ⟨MvPolynomial.eval 0 P, fun z ↦ ?_⟩
  rw [← hPeval z]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, P = MvPolynomial.C c :=
    ⟨_, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hP)⟩
  rw [hc]
  simp

/-! ### The converse: polynomial functions are entire of polynomial growth -/

/-- A polynomial function on `ℂⁿ` is entire. -/
theorem analyticOnNhd_eval {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    AnalyticOnNhd ℂ (fun z : Fin n → ℂ ↦ MvPolynomial.eval z P) univ := by
  refine MvPolynomial.induction_on
    (motive := fun Q : MvPolynomial (Fin n) ℂ ↦
      AnalyticOnNhd ℂ (fun z : Fin n → ℂ ↦ MvPolynomial.eval z Q) univ)
    P (fun a ↦ ?_) (fun p q hp hq ↦ ?_) (fun p i hp ↦ ?_)
  · simpa using analyticOnNhd_const (𝕜 := ℂ) (v := a) (s := (univ : Set (Fin n → ℂ)))
  · have hsplit : (fun z : Fin n → ℂ ↦ MvPolynomial.eval z (p + q)) =
        (fun z : Fin n → ℂ ↦ MvPolynomial.eval z p) +
          fun z : Fin n → ℂ ↦ MvPolynomial.eval z q := by
      funext z; simp
    rw [hsplit]
    exact hp.add hq
  · have hproj : AnalyticOnNhd ℂ (fun z : Fin n → ℂ ↦ z i) univ := fun x _ ↦
      ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ)).analyticAt x
    have hsplit : (fun z : Fin n → ℂ ↦ MvPolynomial.eval z (p * MvPolynomial.X i)) =
        (fun z : Fin n → ℂ ↦ MvPolynomial.eval z p) * fun z : Fin n → ℂ ↦ z i := by
      funext z; simp
    rw [hsplit]
    exact hp.mul hproj

/-- A polynomial function on `ℂⁿ` grows at most like a constant times `(1 + ‖z‖)` to the total
degree. -/
theorem norm_eval_le_of_totalDegree {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (z : Fin n → ℂ) :
    ‖MvPolynomial.eval z P‖ ≤
      (∑ d ∈ P.support, ‖MvPolynomial.coeff d P‖) * (1 + ‖z‖) ^ P.totalDegree := by
  have hz : (1 : ℝ) ≤ 1 + ‖z‖ := by simp [norm_nonneg]
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd ↦ ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hprod : ‖∏ i : Fin n, z i ^ (d i)‖ = ∏ i : Fin n, ‖z i‖ ^ (d i) := by
    simp [norm_prod, norm_pow]
  rw [hprod]
  have hle : ∏ i : Fin n, ‖z i‖ ^ (d i) ≤ ∏ i : Fin n, (1 + ‖z‖) ^ (d i) :=
    Finset.prod_le_prod (fun i _ ↦ by positivity)
      (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _)
        (by simpa using (norm_le_pi_norm z i).trans (by linarith)) _)
  refine hle.trans ?_
  rw [Finset.prod_pow_eq_pow_sum]
  refine pow_le_pow_right₀ hz ?_
  have hsupp : ∑ i ∈ d.support, d i = ∑ i : Fin n, d i :=
    Finset.sum_subset (Finset.subset_univ _)
      (fun i _ hi ↦ Finsupp.notMem_support_iff.mp hi)
  have := MvPolynomial.le_totalDegree (p := P) (s := d) hd
  rw [Finsupp.sum] at this
  omega

/-- **Characterisation of entire functions of polynomial growth on `ℂⁿ`.**  They are exactly the
polynomial functions of total degree at most `m`. -/
theorem analyticOnNhd_and_growth_iff {n m : ℕ} {f : (Fin n → ℂ) → ℂ} :
    (AnalyticOnNhd ℂ f univ ∧ ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ m) ↔
      ∃ P : MvPolynomial (Fin n) ℂ, P.totalDegree ≤ m ∧ ∀ z, MvPolynomial.eval z P = f z := by
  constructor
  · rintro ⟨hf, C, hC⟩
    exact exists_mvPolynomial_eq_of_growth hf hC
  · rintro ⟨P, hdeg, hP⟩
    have hfun : f = fun z : Fin n → ℂ ↦ MvPolynomial.eval z P := by
      funext z; exact (hP z).symm
    subst hfun
    refine ⟨analyticOnNhd_eval P, ∑ d ∈ P.support, ‖MvPolynomial.coeff d P‖, fun z ↦ ?_⟩
    have hz : (1 : ℝ) ≤ 1 + ‖z‖ := by simp [norm_nonneg]
    refine (norm_eval_le_of_totalDegree P z).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz hdeg)
      (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

/-! ### The form used by the repository's holomorphic function sheaf -/

/-- The polynomial-growth Liouville theorem in the manifold idiom used by
`holomorphicFunctionSheaf`: a `C^ω` function on the model space `Fin n → ℂ` of polynomial growth
of order `m` is a polynomial function of total degree at most `m`. -/
theorem exists_mvPolynomial_eq_of_contMDiff_of_growth {n m : ℕ} {f : (Fin n → ℂ) → ℂ} {C : ℝ}
    (hf : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω f)
    (hC : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ P : MvPolynomial (Fin n) ℂ, P.totalDegree ≤ m ∧ ∀ z, MvPolynomial.eval z P = f z :=
  exists_mvPolynomial_eq_of_growth
    (contDiff_omega_iff_analyticOnNhd.mp (contMDiff_iff_contDiff.mp hf)) hC

/-! ### Growth from homogeneity and compactness

The polynomial growth hypothesis is what a global holomorphic section of `𝒪(m)` on complex
projective space supplies: writing the section in homogeneous coordinates gives a function on
`ℂ^{N+1}` homogeneous of degree `m`, bounded on the unit sphere by compactness; restricting to
the affine chart `x₀ = 1` then has growth of order `m`. -/

/-- A degree-`m` homogeneous function bounded on the unit sphere has growth of order `m` on the
affine chart `x₀ = 1`. -/
theorem norm_cons_le_of_homogeneous_of_bounded_sphere {N m : ℕ} {F : (Fin (N + 1) → ℂ) → ℂ}
    {C : ℝ} (hsphere : ∀ x : Fin (N + 1) → ℂ, ‖x‖ = 1 → ‖F x‖ ≤ C)
    (hhom : ∀ (t : ℂ) (x : Fin (N + 1) → ℂ), F (t • x) = t ^ m * F x) (z : Fin N → ℂ) :
    ‖F (Fin.cons 1 z)‖ ≤ C * (1 + ‖z‖) ^ m := by
  set x : Fin (N + 1) → ℂ := Fin.cons 1 z with hx
  have hx0 : (1 : ℝ) ≤ ‖x‖ := by
    have := norm_le_pi_norm x 0
    simpa [hx] using this
  have hxne : ‖x‖ ≠ 0 := by positivity
  have hxle : ‖x‖ ≤ 1 + ‖z‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [hx, norm_nonneg]
    · have := norm_le_pi_norm z j
      simp only [hx, Fin.cons_succ]
      linarith
  have hu : ‖(‖x‖ : ℂ)⁻¹ • x‖ = 1 := by
    rw [norm_smul]
    simp [hxne]
  have hxeq : ((‖x‖ : ℂ)) • ((‖x‖ : ℂ)⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hxne), one_smul]
  have hFx : F x = (‖x‖ : ℂ) ^ m * F ((‖x‖ : ℂ)⁻¹ • x) := by
    conv_lhs => rw [← hxeq]
    exact hhom _ _
  have hbound : ‖F ((‖x‖ : ℂ)⁻¹ • x)‖ ≤ C := hsphere _ hu
  calc ‖F x‖ = ‖x‖ ^ m * ‖F ((‖x‖ : ℂ)⁻¹ • x)‖ := by
        rw [hFx, norm_mul, norm_pow]
        simp
    _ ≤ (1 + ‖z‖) ^ m * C := by
        refine mul_le_mul (pow_le_pow_left₀ (by positivity) hxle m) hbound (norm_nonneg _)
          (by positivity)
    _ = C * (1 + ‖z‖) ^ m := by ring

/-- **The `H⁰` shape of GAGA for `𝒪(m)` on `ℙᴺ`, at the level of functions.**  A function on
`ℂ^{N+1}` that is homogeneous of degree `m`, bounded on the unit sphere, and entire in the affine
chart `x₀ = 1`, restricts on that chart to a polynomial of total degree at most `m`. -/
theorem exists_mvPolynomial_eq_of_homogeneous_of_bounded_sphere {N m : ℕ}
    {F : (Fin (N + 1) → ℂ) → ℂ} {C : ℝ}
    (hsphere : ∀ x : Fin (N + 1) → ℂ, ‖x‖ = 1 → ‖F x‖ ≤ C)
    (hhom : ∀ (t : ℂ) (x : Fin (N + 1) → ℂ), F (t • x) = t ^ m * F x)
    (hchart : AnalyticOnNhd ℂ (fun z : Fin N → ℂ ↦ F (Fin.cons 1 z)) univ) :
    ∃ P : MvPolynomial (Fin N) ℂ, P.totalDegree ≤ m ∧
      ∀ z, MvPolynomial.eval z P = F (Fin.cons 1 z) :=
  exists_mvPolynomial_eq_of_growth hchart
    (norm_cons_le_of_homogeneous_of_bounded_sphere hsphere hhom)

end Complex.PolynomialGrowth
