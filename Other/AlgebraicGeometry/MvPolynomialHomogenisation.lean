/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveChartIso

/-!
# Homogenisation: degree-`m` forms are the polynomials of total degree at most `m`

Dehomogenisation `deh i` substitutes `Xᵢ ↦ 1` and `X_{i.succAbove j} ↦ Yⱼ`.  This file proves that
it restricts to a bijection from the degree-`m` homogeneous forms in `N + 1` variables onto the
polynomials of total degree at most `m` in `N` variables, the inverse being homogenisation.

This is the algebraic half of `H⁰(ℙᴺ, 𝒪(m)) =` degree-`m` forms: combined with
`Complex.PolynomialGrowth.exists_mvPolynomial_eq_of_growth` it identifies the chart description of
a section of `𝒪(m)` with a homogeneous form.  Mathlib has homogeneous components but no
homogenisation.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Other.ProjectiveChart

section Homogenisation

variable (R : Type*) [CommRing R] {N : ℕ}

/-! ### Exponents -/

/-- The exponent vector obtained by deleting the `i`-th entry. -/
def restrictExponent (i : Fin (N + 1)) (α : Fin (N + 1) →₀ ℕ) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j ↦ α (i.succAbove j)

@[simp]
theorem restrictExponent_apply (i : Fin (N + 1)) (α : Fin (N + 1) →₀ ℕ) (j : Fin N) :
    restrictExponent i α j = α (i.succAbove j) := rfl

/-- The exponent vector of the degree-`m` homogenisation of a monomial. -/
def homExponent (i : Fin (N + 1)) (m : ℕ) (d : Fin N →₀ ℕ) : Fin (N + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (i.insertNth (m - d.degree) (⇑d))

@[simp]
theorem homExponent_apply_self (i : Fin (N + 1)) (m : ℕ) (d : Fin N →₀ ℕ) :
    homExponent i m d i = m - d.degree := by
  simp [homExponent]

@[simp]
theorem homExponent_apply_succAbove (i : Fin (N + 1)) (m : ℕ) (d : Fin N →₀ ℕ) (j : Fin N) :
    homExponent i m d (i.succAbove j) = d j := by
  simp [homExponent]

@[simp]
theorem restrictExponent_homExponent (i : Fin (N + 1)) (m : ℕ) (d : Fin N →₀ ℕ) :
    restrictExponent i (homExponent i m d) = d := by
  ext j
  simp

/-- The degree of an exponent vector splits off its `i`-th entry. -/
theorem degree_eq_add_restrictExponent (i : Fin (N + 1)) (α : Fin (N + 1) →₀ ℕ) :
    α.degree = α i + (restrictExponent i α).degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succAbove _ i]
  simp

theorem degree_homExponent (i : Fin (N + 1)) {m : ℕ} {d : Fin N →₀ ℕ} (hd : d.degree ≤ m) :
    (homExponent i m d).degree = m := by
  rw [degree_eq_add_restrictExponent i, restrictExponent_homExponent, homExponent_apply_self]
  omega

/-- On exponents of a fixed degree, deleting the `i`-th entry is injective. -/
theorem restrictExponent_injOn (i : Fin (N + 1)) {m : ℕ} {α β : Fin (N + 1) →₀ ℕ}
    (hα : α.degree = m) (hβ : β.degree = m)
    (h : restrictExponent i α = restrictExponent i β) : α = β := by
  have hi : α i = β i := by
    have hα' := degree_eq_add_restrictExponent i α
    have hβ' := degree_eq_add_restrictExponent i β
    rw [h] at hα'
    omega
  ext k
  refine Fin.succAboveCases i hi (fun j ↦ ?_) k
  exact congrArg (fun γ : Fin N →₀ ℕ ↦ γ j) h

/-! ### Homogenisation -/

/-- Dehomogenisation sends a monomial to the monomial on the restricted exponent. -/
theorem deh_monomial (i : Fin (N + 1)) (α : Fin (N + 1) →₀ ℕ) (c : R) :
    deh R i (monomial α c) = monomial (restrictExponent i α) c := by
  rw [deh, coe_eval₂Hom, eval₂_monomial,
    Finsupp.prod_fintype _ _ (fun k ↦ pow_zero _), Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, one_pow, one_mul]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun k ↦ pow_zero _)]
  simp

/-- The degree-`m` homogenisation of a polynomial in `N` variables. -/
def homogenise (i : Fin (N + 1)) (m : ℕ) (P : MvPolynomial (Fin N) R) :
    MvPolynomial (Fin (N + 1)) R :=
  ∑ d ∈ P.support, monomial (homExponent i m d) (coeff d P)

/-- Dehomogenising a homogenisation recovers the original polynomial. -/
@[simp]
theorem deh_homogenise (i : Fin (N + 1)) (m : ℕ) (P : MvPolynomial (Fin N) R) :
    deh R i (homogenise R i m P) = P := by
  rw [homogenise, map_sum]
  simp only [deh_monomial, restrictExponent_homExponent]
  exact support_sum_monomial_coeff P

/-- The homogenisation of a polynomial of total degree at most `m` is a degree-`m` form. -/
theorem isHomogeneous_homogenise (i : Fin (N + 1)) {m : ℕ} {P : MvPolynomial (Fin N) R}
    (hP : P.totalDegree ≤ m) : (homogenise R i m P).IsHomogeneous m := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun d hd ↦ ?_
  refine isHomogeneous_monomial _ (degree_homExponent i ?_)
  have h := MvPolynomial.le_totalDegree hd
  rw [Finsupp.degree_apply]
  exact le_trans h hP

/-- On a degree-`m` form, dehomogenisation preserves the coefficients. -/
theorem coeff_deh_of_isHomogeneous (i : Fin (N + 1)) {m : ℕ}
    {Q : MvPolynomial (Fin (N + 1)) R} (hQ : Q.IsHomogeneous m)
    {β : Fin (N + 1) →₀ ℕ} (hβ : β ∈ Q.support) :
    coeff (restrictExponent i β) (deh R i Q) = coeff β Q := by
  have hdeg : ∀ α ∈ Q.support, (α : Fin (N + 1) →₀ ℕ).degree = m := by
    intro α hα
    rw [Finsupp.degree_apply]
    exact (hQ.degree_eq_sum_deg_support hα).symm
  conv_lhs => rw [← support_sum_monomial_coeff Q]
  rw [map_sum, coeff_sum]
  simp only [deh_monomial, coeff_monomial]
  rw [Finset.sum_eq_single β]
  · simp
  · intro α hα hne
    refine if_neg fun hcontra ↦ hne ?_
    exact restrictExponent_injOn i (hdeg α hα) (hdeg β hβ) hcontra
  · intro h'
    exact absurd hβ h'

/-- Dehomogenisation is injective on degree-`m` forms. -/
theorem eq_zero_of_deh_eq_zero (i : Fin (N + 1)) {m : ℕ}
    {Q : MvPolynomial (Fin (N + 1)) R} (hQ : Q.IsHomogeneous m) (h : deh R i Q = 0) :
    Q = 0 := by
  ext β
  by_cases hβ : β ∈ Q.support
  · have := coeff_deh_of_isHomogeneous R i hQ hβ
    rw [h] at this
    simpa using this.symm
  · simpa using MvPolynomial.notMem_support_iff.mp hβ

/-- **Degree-`m` forms in `N + 1` variables are exactly the polynomials of total degree at most
`m` in `N` variables.**  Dehomogenisation is the bijection, homogenisation its inverse. -/
theorem existsUnique_isHomogeneous_deh_eq (i : Fin (N + 1)) (m : ℕ)
    {P : MvPolynomial (Fin N) R} (hP : P.totalDegree ≤ m) :
    ∃! Q : MvPolynomial (Fin (N + 1)) R, Q.IsHomogeneous m ∧ deh R i Q = P := by
  refine ⟨homogenise R i m P, ⟨isHomogeneous_homogenise R i hP, deh_homogenise R i m P⟩, ?_⟩
  rintro Q ⟨hQhom, hQdeh⟩
  have hsub : (Q - homogenise R i m P).IsHomogeneous m :=
    hQhom.sub (isHomogeneous_homogenise R i hP)
  have hzero : deh R i (Q - homogenise R i m P) = 0 := by
    rw [map_sub, hQdeh, deh_homogenise, sub_self]
  have := eq_zero_of_deh_eq_zero R i hsub hzero
  linear_combination (norm := ring_nf) this

/-- The total degree of a dehomogenisation is at most the degree of the form. -/
theorem totalDegree_deh_le (i : Fin (N + 1)) {m : ℕ}
    {Q : MvPolynomial (Fin (N + 1)) R} (hQ : Q.IsHomogeneous m) :
    (deh R i Q).totalDegree ≤ m := by
  conv_lhs => rw [← support_sum_monomial_coeff Q]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun α hα ↦ ?_
  rw [deh_monomial]
  refine le_trans (MvPolynomial.totalDegree_monomial_le _ _) ?_
  have hdeg : Finsupp.degree (α : Fin (N + 1) →₀ ℕ) = m := by
    rw [Finsupp.degree_apply]
    exact (hQ.degree_eq_sum_deg_support hα).symm
  have hsplit := degree_eq_add_restrictExponent i α
  have hle : Finsupp.degree (restrictExponent i α) ≤ m := by omega
  simpa [Finsupp.sum, Finsupp.degree_apply] using hle

end Homogenisation

end Other.ProjectiveChart
