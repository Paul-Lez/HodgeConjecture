/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.MvPolynomialHomogenisation
public import Other.AlgebraicGeometry.HomogeneousEntireFunctions
public import Other.AlgebraicGeometry.ProjectiveChartHolomorphic
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# `H⁰(ℙᴺ, 𝒪(m))` at the level of chart functions

Putting together the three halves proved so far:

* an entire function on `ℂᴺ` of polynomial growth of order `m` is a polynomial of total degree at
  most `m` (`Complex.PolynomialGrowth.exists_mvPolynomial_eq_of_growth`);
* such polynomials are exactly the dehomogenisations of degree-`m` forms in `N + 1` variables
  (`Other.ProjectiveChart.existsUnique_isHomogeneous_deh_eq`);
* a holomorphic function on `ℙᴺ(ℂ)^an` pulls back along a homogeneous chart to an entire function
  on `ℂᴺ` (`ComplexProjectiveSpace.analyticOnNhd_comp_chartPoint`).

The result is the `H⁰` comparison for `𝒪(m)`, `m ≥ 0`, in the form that a sheaf-level statement
would be reduced to: a holomorphic function on a chart with growth of order `m` *is* the chart
expression of a unique degree-`m` form.
-/

@[expose] public noncomputable section

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Manifold ContDiff

namespace Other.ProjectiveChart

/-- An entire function on `ℂᴺ` with polynomial growth of order `m` is the chart expression of a
degree-`m` form in `N + 1` variables, uniquely so. -/
theorem existsUnique_isHomogeneous_of_growth {N m : ℕ} (i : Fin (N + 1))
    {f : (Fin N → ℂ) → ℂ} {C : ℝ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hC : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃! Q : MvPolynomial (Fin (N + 1)) ℂ, Q.IsHomogeneous m ∧
      ∀ z : Fin N → ℂ, MvPolynomial.eval z (deh ℂ i Q) = f z := by
  obtain ⟨P, hPdeg, hPeval⟩ :=
    Complex.PolynomialGrowth.exists_mvPolynomial_eq_of_growth hf hC
  obtain ⟨Q, ⟨hQhom, hQdeh⟩, hQuniq⟩ := existsUnique_isHomogeneous_deh_eq ℂ i m hPdeg
  refine ⟨Q, ⟨hQhom, fun z ↦ by rw [hQdeh]; exact hPeval z⟩, ?_⟩
  rintro Q' ⟨hQ'hom, hQ'eval⟩
  refine hQuniq Q' ⟨hQ'hom, ?_⟩
  refine MvPolynomial.funext fun z ↦ ?_
  rw [hQ'eval z, hPeval z]

/-- The converse: the chart expression of a degree-`m` form is entire with growth of order `m`. -/
theorem analyticOnNhd_and_growth_of_isHomogeneous {N m : ℕ} (i : Fin (N + 1))
    {Q : MvPolynomial (Fin (N + 1)) ℂ} (hQ : Q.IsHomogeneous m) :
    AnalyticOnNhd ℂ (fun z : Fin N → ℂ ↦ MvPolynomial.eval z (deh ℂ i Q)) Set.univ ∧
      ∃ C : ℝ, ∀ z : Fin N → ℂ,
        ‖MvPolynomial.eval z (deh ℂ i Q)‖ ≤ C * (1 + ‖z‖) ^ m := by
  refine ⟨Complex.PolynomialGrowth.analyticOnNhd_eval _, ?_⟩
  refine ⟨∑ d ∈ (deh ℂ i Q).support, ‖MvPolynomial.coeff d (deh ℂ i Q)‖, fun z ↦ ?_⟩
  have hz : (1 : ℝ) ≤ 1 + ‖z‖ := by simp [norm_nonneg]
  refine (Complex.PolynomialGrowth.norm_eval_le_of_totalDegree (deh ℂ i Q) z).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hz (totalDegree_deh_le ℂ i hQ))
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

/-- **The `H⁰` comparison for `𝒪(m)` on `ℙᴺ`, at the level of chart functions.**  A holomorphic
function on `ℙᴺ(ℂ)^an` whose expression in the `i`-th homogeneous chart has growth of order `m`
is the chart expression of a unique degree-`m` form. -/
theorem existsUnique_isHomogeneous_of_chart_growth (N : ℕ) (i : Fin (N + 1)) {m : ℕ} {C : ℝ}
    {g : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ))) → ℂ}
    (hg : ContMDiff 𝓘(ℂ, Fin N → ℂ) 𝓘(ℂ, ℂ) ω g)
    (hC : ∀ z : Fin N → ℂ,
      ‖g (ComplexProjectiveSpace.projectivizationToComplexPoint
        (ComplexProjectiveSpace.chartPoint i z))‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃! Q : MvPolynomial (Fin (N + 1)) ℂ, Q.IsHomogeneous m ∧
      ∀ z : Fin N → ℂ, MvPolynomial.eval z (deh ℂ i Q) =
        g (ComplexProjectiveSpace.projectivizationToComplexPoint
          (ComplexProjectiveSpace.chartPoint i z)) :=
  existsUnique_isHomogeneous_of_growth i
    (ComplexProjectiveSpace.analyticOnNhd_comp_chartPoint N i hg) hC

end Other.ProjectiveChart
