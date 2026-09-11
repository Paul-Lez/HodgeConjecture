/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Polynomial.MahlerMeasure

/-!
# Polynomial growth of coefficients of monic factors

For a monic polynomial with coefficients polynomial in a complex parameter, all monic factors
of all specializations satisfy one coefficient-growth bound. Mignotte's inequality bounds a
factor coefficient using the Mahler measure of the original polynomial, and that measure is
bounded by the sum of the coefficient norms. This estimate requires no continuity in the
choice of factor.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Polynomial

/-- A coefficient of a monic divisor is bounded by the coefficient sum of the dividend. -/
theorem norm_coeff_le_of_monic_dvd {p q : Polynomial ℂ} (hp : p.Monic) (hq : q.Monic)
    (hqp : q ∣ p) (i : ℕ) :
    ‖q.coeff i‖ ≤ 2 ^ p.natDegree * (∑ j ∈ range (p.natDegree + 1), ‖p.coeff j‖) := by
  obtain ⟨r, hr⟩ := hqp
  have hrm : r.Monic := hq.of_mul_monic_left (hr ▸ hp)
  have hr1 : 1 ≤ r.mahlerMeasure :=
    one_le_mahlerMeasure_of_one_le_norm_leadingCoeff (by simp [hrm.leadingCoeff])
  have hc := norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure i q r hr1
  rw [← hr] at hc
  calc
    ‖q.coeff i‖ ≤ (q.natDegree.choose i : ℝ) * p.mahlerMeasure := hc
    _ ≤ 2 ^ p.natDegree * p.mahlerMeasure := by
      apply mul_le_mul_of_nonneg_right _ p.mahlerMeasure_nonneg
      exact_mod_cast (Nat.choose_le_two_pow q.natDegree i).trans
        (Nat.pow_le_pow_right (by omega) (natDegree_le_of_dvd ⟨r, hr⟩ hp.ne_zero))
    _ ≤ 2 ^ p.natDegree * (∑ j ∈ range (p.natDegree + 1), ‖p.coeff j‖) := by
      gcongr
      exact p.mahlerMeasure_le_sum_norm_coeff.trans_eq (p.sum_over_range (by simp))

/-- Polynomial evaluation has growth bounded by its degree and the sum of coefficient norms. -/
theorem norm_eval_le_sum_norm_coeff_mul (p : Polynomial ℂ) (z : ℂ) :
    ‖p.eval z‖ ≤ (∑ j ∈ range (p.natDegree + 1), ‖p.coeff j‖) *
      (1 + ‖z‖) ^ p.natDegree := by
  rw [eval_eq_sum_range]
  calc
    ‖∑ j ∈ range (p.natDegree + 1), p.coeff j * z ^ j‖ ≤
        ∑ j ∈ range (p.natDegree + 1), ‖p.coeff j * z ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range (p.natDegree + 1), ‖p.coeff j‖ * (1 + ‖z‖) ^ p.natDegree := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul, norm_pow]
      gcongr
      exact (pow_le_pow_left₀ (norm_nonneg z) (by linarith) j).trans
        (pow_le_pow_right₀ (by linarith [norm_nonneg z]) (by simpa using Nat.le_of_lt_succ (mem_range.mp hj)))
    _ = _ := by rw [sum_mul]

/-- Coefficients of all monic factors of a monic polynomial family obey one polynomial-growth
bound, independent of the factor and coefficient index. -/
theorem exists_monic_factor_coeff_growth (p : Polynomial (Polynomial ℂ)) (hp : p.Monic) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (z : ℂ) (q : Polynomial ℂ), q.Monic →
      q ∣ p.map (Polynomial.evalRingHom z) → ∀ i,
      ‖q.coeff i‖ ≤ C * (1 + ‖z‖) ^ N := by
  let a : ℕ → ℝ := fun i => ∑ j ∈ range ((p.coeff i).natDegree + 1), ‖(p.coeff i).coeff j‖
  let N := (range (p.natDegree + 1)).sup fun i => (p.coeff i).natDegree
  refine ⟨2 ^ p.natDegree * ∑ i ∈ range (p.natDegree + 1), a i, N, by positivity, ?_⟩
  intro z q hq hd i
  have hh := norm_coeff_le_of_monic_dvd (hp.map (Polynomial.evalRingHom z)) hq hd i
  rw [hp.natDegree_map] at hh
  simp only [coeff_map, coe_evalRingHom] at hh
  calc
    ‖q.coeff i‖ ≤ 2 ^ p.natDegree * ∑ j ∈ range (p.natDegree + 1),
        ‖(p.coeff j).eval z‖ := hh
    _ ≤ 2 ^ p.natDegree * ∑ j ∈ range (p.natDegree + 1), a j * (1 + ‖z‖) ^ N := by
      gcongr with j hj
      apply (norm_eval_le_sum_norm_coeff_mul (p.coeff j) z).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ a j)
      exact pow_le_pow_right₀ (by linarith [norm_nonneg z]) (Finset.le_sup (f := fun i =>
        (p.coeff i).natDegree) hj)
    _ = _ := by rw [← sum_mul, mul_assoc]


/-- Multivariable polynomial evaluation is bounded by coefficient mass and total degree. -/
theorem norm_mvPolynomial_eval_le (n : ℕ) (a : MvPolynomial (Fin n) ℂ) (z : Fin n → ℂ) :
    ‖MvPolynomial.eval z a‖ ≤
      (∑ s ∈ a.support, ‖a.coeff s‖) * (1 + ‖z‖) ^ a.totalDegree := by
  rw [MvPolynomial.eval_eq]
  calc
    ‖∑ s ∈ a.support, a.coeff s * ∏ i ∈ s.support, z i ^ s i‖ ≤
        ∑ s ∈ a.support, ‖a.coeff s * ∏ i ∈ s.support, z i ^ s i‖ := norm_sum_le _ _
    _ ≤ ∑ s ∈ a.support, ‖a.coeff s‖ * (1 + ‖z‖) ^ a.totalDegree := by
      apply sum_le_sum
      intro s hs
      rw [norm_mul, norm_prod]
      simp_rw [norm_pow]
      gcongr
      calc
        ∏ i ∈ s.support, ‖z i‖ ^ s i ≤
            ∏ i ∈ s.support, (1 + ‖z‖) ^ s i := by
          gcongr with i hi
          exact (norm_le_pi_norm z i).trans (by linarith [norm_nonneg z])
        _ = (1 + ‖z‖) ^ (s.sum fun _ e ↦ e) := by
          simp [Finsupp.sum, Finset.prod_pow_eq_pow_sum]
        _ ≤ (1 + ‖z‖) ^ a.totalDegree :=
          pow_le_pow_right₀ (by linarith [norm_nonneg z]) (MvPolynomial.le_totalDegree hs)
    _ = _ := by rw [sum_mul]


/-- Uniform polynomial growth for monic factors of a multivariable polynomial family. -/
theorem exists_monic_factor_coeff_mvPolynomial_growth {n : ℕ}
    (p : Polynomial (MvPolynomial (Fin n) ℂ)) (hp : p.Monic) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (z : Fin n → ℂ) (q : Polynomial ℂ), q.Monic →
      q ∣ p.map (MvPolynomial.eval z) → ∀ i,
      ‖q.coeff i‖ ≤ C * (1 + ‖z‖) ^ N := by
  let a : ℕ → ℝ := fun i ↦ ∑ s ∈ (p.coeff i).support, ‖(p.coeff i).coeff s‖
  let N := (range (p.natDegree + 1)).sup fun i ↦ (p.coeff i).totalDegree
  refine ⟨2 ^ p.natDegree * ∑ i ∈ range (p.natDegree + 1), a i, N, by positivity, ?_⟩
  intro z q hq hd i
  have hh := norm_coeff_le_of_monic_dvd (hp.map (MvPolynomial.eval z)) hq hd i
  rw [hp.natDegree_map] at hh
  simp only [coeff_map] at hh
  calc
    ‖q.coeff i‖ ≤ 2 ^ p.natDegree * ∑ j ∈ range (p.natDegree + 1),
        ‖MvPolynomial.eval z (p.coeff j)‖ := hh
    _ ≤ 2 ^ p.natDegree * ∑ j ∈ range (p.natDegree + 1),
        a j * (1 + ‖z‖) ^ N := by
      gcongr with j hj
      apply (norm_mvPolynomial_eval_le n (p.coeff j) z).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ a j)
      exact pow_le_pow_right₀ (by linarith [norm_nonneg z])
        (Finset.le_sup (f := fun i ↦ (p.coeff i).totalDegree) hj)
    _ = _ := by rw [← sum_mul, mul_assoc]

end Polynomial
