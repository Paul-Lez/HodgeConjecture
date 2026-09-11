/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Entire functions of polynomial growth

Cauchy's estimates force Taylor coefficients above the growth degree to vanish.
Consequently an entire function with a global polynomial growth bound is a polynomial.
-/

public section

open Filter Metric Polynomial
open scoped Topology

namespace Complex

/-- Derivatives above the degree of a polynomial growth bound vanish at the origin. -/
theorem iteratedDeriv_zero_of_polynomial_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C) {N n : ℕ}
    (hgrowth : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N) (hn : N < n) :
    iteratedDeriv n f 0 = 0 := by
  apply norm_le_zero_iff.mp
  have hlim : Tendsto (fun R : ℝ => (n.factorial * C * 2 ^ N) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hRpos : 0 < R := by positivity
  calc
    ‖iteratedDeriv n f 0‖ ≤ n.factorial * (C * (1 + R) ^ N) / R ^ n :=
      norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hRpos hf.diffContOnCl
        (fun z hz => by simpa only [mem_sphere_zero_iff_norm.mp hz] using hgrowth z)
    _ ≤ n.factorial * (C * (2 * R) ^ N) / R ^ (N + 1) := by
      apply div_le_div₀ (by positivity)
      · gcongr
        linarith
      · positivity
      · exact pow_le_pow_right₀ hR hn
    _ = (n.factorial * C * 2 ^ N) / R := by
      rw [mul_pow, pow_succ]
      field_simp

/-- An entire complex function with growth of degree at most `N` is a polynomial
of degree at most `N`. -/
theorem exists_polynomial_of_polynomial_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ p : ℂ[X], p.natDegree ≤ N ∧ ∀ z, p.eval z = f z := by
  let p : ℂ[X] := ∑ n ∈ Finset.range (N + 1),
    monomial n ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0)
  refine ⟨p, ?_, ?_⟩
  · apply natDegree_sum_le_of_forall_le
    intro n hn
    exact (natDegree_monomial_le _).trans (by simpa using Finset.mem_range.mp hn)
  · intro z
    have htail (n : ℕ) (hn : n ∉ Finset.range (N + 1)) :
        (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * (z - 0) ^ n = 0 := by
      rw [iteratedDeriv_zero_of_polynomial_growth hf hC hgrowth (by simpa using hn)]
      simp
    rw [← taylorSeries_eq_of_entire' 0 z hf, tsum_eq_sum htail]
    simp [p, eval_finsetSum, eval_monomial]

private lemma norm_fin_cons_le {n : ℕ} (t : ℂ) (y : Fin n → ℂ) :
    ‖(Fin.cons t y : Fin (n + 1) → ℂ)‖ ≤ ‖t‖ + ‖y‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using (norm_le_pi_norm y j).trans (le_add_of_nonneg_left (norm_nonneg t))

private lemma growth_fin_cons {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℂ} {C : ℝ}
    (hC : 0 ≤ C) {N : ℕ} (h : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N)
    (t : ℂ) (y : Fin n → ℂ) :
    ‖f (Fin.cons t y)‖ ≤ (C * (1 + ‖t‖) ^ N) * (1 + ‖y‖) ^ N := by
  calc
    ‖f (Fin.cons t y)‖ ≤ C * (1 + ‖(Fin.cons t y : Fin (n + 1) → ℂ)‖) ^ N := h _
    _ ≤ C * ((1 + ‖t‖) * (1 + ‖y‖)) ^ N := by
      gcongr
      have := norm_fin_cons_le t y
      have := mul_nonneg (norm_nonneg t) (norm_nonneg y)
      nlinarith
    _ = _ := by rw [mul_pow, mul_assoc]

/-- An entire function of finitely many complex variables with polynomial growth is a
multivariate polynomial. The proof uses interpolation, so needs no mixed derivative API. -/
theorem exists_mvPolynomial_of_polynomial_growth {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ p : MvPolynomial (Fin n) ℂ, ∀ z, MvPolynomial.eval z p = f z := by
  classical
  induction n generalizing C with
  | zero =>
    refine ⟨MvPolynomial.C (f 0), fun z => ?_⟩
    simp only [MvPolynomial.eval_C]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    have hslice (t : ℂ) : Differentiable ℂ (fun y : Fin n → ℂ => f (Fin.cons t y)) := by
      apply hf.comp
      apply differentiable_pi.mpr
      intro i
      exact Fin.cases (by simp)
        (fun j => by simpa using differentiable_apply j) i
    have hpoly (i : Fin (N + 1)) : ∃ p : MvPolynomial (Fin n) ℂ,
        ∀ y, MvPolynomial.eval y p = f (Fin.cons (i : ℂ) y) :=
      ih (hslice (i : ℂ)) (by positivity) (growth_fin_cons hC hgrowth (i : ℂ))
    choose p hp using hpoly
    let nodes : Fin (N + 1) → ℂ := fun i => (i : ℂ)
    have hinj : Set.InjOn nodes (Finset.univ : Finset (Fin (N + 1))) := by
      intro a _ b _ hab
      apply Fin.ext
      dsimp [nodes] at hab
      exact_mod_cast hab
    let basis (i : Fin (N + 1)) : MvPolynomial (Fin (n + 1)) ℂ :=
      (Lagrange.basis Finset.univ nodes i).eval₂ MvPolynomial.C (MvPolynomial.X 0)
    refine ⟨∑ i, MvPolynomial.rename Fin.succ (p i) * basis i, fun z => ?_⟩
    have hline : Differentiable ℂ (fun t => f (Fin.cons t (fun j : Fin n => z j.succ))) := by
      apply hf.comp
      apply differentiable_pi.mpr
      intro i
      exact Fin.cases (by simp)
        (fun j => by simp) i
    obtain ⟨q, hqdeg, hq⟩ := exists_polynomial_of_polynomial_growth hline
      (C := C * (1 + ‖fun j : Fin n => z j.succ‖) ^ N) (by positivity) N (fun t => by
        convert growth_fin_cons hC hgrowth t (fun j : Fin n => z j.succ) using 1
        ring)
    have hqinterp := Lagrange.eq_interpolate (f := q) hinj
      (show q.degree < ((Finset.univ : Finset (Fin (N + 1))).card : WithBot ℕ) from
        lt_of_le_of_lt (degree_le_natDegree) (by
          simp only [Finset.card_univ, Fintype.card_fin]
          exact_mod_cast Nat.lt_succ_of_le hqdeg))
    have heval := congrArg (Polynomial.eval (z 0)) hqinterp
    rw [hq] at heval
    have hzcons : Fin.cons (z 0) (fun j : Fin n => z j.succ) = z := by
      ext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hzcons] at heval
    rw [heval, Lagrange.interpolate_apply, eval_finsetSum]
    simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_rename,
      Function.comp_def, hp, Polynomial.eval_mul, Polynomial.eval_C, hq]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp [basis, Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum, map_sum]

end Complex
