/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytic.ParametricCircleIntegral
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# The Weierstrass preparation theorem

We state the Weierstrass preparation theorem: a holomorphic function on a neighbourhood of the
origin in `ℂ^{n+1}` which does not vanish identically on the last coordinate axis factors, near
the origin, as a unit times a Weierstrass polynomial.

## Main definitions

- `IsWeierstrassPolynomial`: a monic polynomial whose lower coefficients vanish at the origin.
- `LocalOkaRing.fromPolynomial`: a polynomial over the germs in `n` variables, viewed as a germ
  in `n + 1` variables.
- `Polynomial.toOkaRing`: a polynomial over `OkaRing U` viewed as a holomorphic function on the
  cylinder `U.extend'` over `U`.
- `OkaRing.germ`: the Taylor series of a holomorphic function at a point of its domain.
- `OkaRing.germPoly`: the coefficientwise germ of a polynomial over `OkaRing U` at a point of
  the cylinder over `U`, Taylor expanded in the polynomial variable.

## Main results

Besides the statement of the local Weierstrass division theorem
(`localweierstrass_division`) and the proof of the local Weierstrass preparation theorem
from it (`localweierstrass_preparation`, via division by the generic Weierstrass polynomial
and the analytic implicit function theorem `exists_analyticAt_implicit`), this file develops
the dictionary between functions and germs used to reduce Oka's coherence lemma to them:

- `OkaRing.germ_toOkaRing`: the germ of the function attached to a polynomial is the germ
  polynomial, viewed as a germ via `LocalOkaRing.fromPolynomial`.
- `OkaRing.exists_restrict_eq_of_germ_eq`, `LocalOkaRing.exists_okaRing_germ`,
  `OkaRing.exists_isUnit_restrict`: germs detect local equality, are realized by functions on
  neighbourhoods, and detect local invertibility.
- `LocalOkaRing.exists_isWeierstrassPolynomial_realize` and
  `LocalOkaRing.exists_poly_germPoly`: realizations of germ polynomials by polynomials over
  the holomorphic functions on a neighbourhood.
- `Polynomial.exists_map_restrict_eq_zero`: a polynomial in the last variable whose attached
  function vanishes near a point of the cylinder vanishes coefficientwise near the base point.
- `MvPowerSeries.Represents.homogeneous_eval_eq_zero`, `MvPowerSeries.exists_direction`,
  `lineEquiv`: choice of a linear change of coordinates making finitely many nonzero germs
  general in the last variable.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open Finsupp in
theorem MvPowerSeries.mem_span_X_of_constantCoeff_eq_zero
    {σ : Type*} [Finite σ] [LinearOrder σ] {φ : MvPowerSeries σ ℂ}
    (hφ : MvPowerSeries.constantCoeff φ = 0) :
    φ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ ℂ)) := by
  classical
  haveI := Fintype.ofFinite σ
  rw [Ideal.mem_span_range_iff_exists_fun]
  set g : σ → MvPowerSeries σ ℂ :=
    fun i ↦ (fun e ↦ if ∀ j, j < i → e j = 0 then coeff (e + single i 1) φ else 0) with hg
  refine ⟨g, ?_⟩
  ext d
  rw [map_sum]
  have key : ∀ i : σ, coeff d (g i * X i)
      = if single i 1 ≤ d then (if ∀ j, j < i → d j = 0 then coeff d φ else 0) else 0 := by
    intro i
    rw [X_def, coeff_mul_monomial, mul_one]
    by_cases hle : single i 1 ≤ d
    · rw [if_pos hle, if_pos hle, hg, MvPowerSeries.coeff_apply]
      dsimp only
      rw [tsub_add_cancel_of_le hle]
      refine if_congr (forall_congr' fun j ↦ imp_congr_right fun hj ↦ ?_) rfl rfl
      simp [Finsupp.tsub_apply, ne_of_gt hj]
    · rw [if_neg hle, if_neg hle]
  rw [Finset.sum_congr rfl fun i _ ↦ key i]
  simp_rw [← ite_and]
  by_cases hd : d = 0
  · subst hd
    rw [coeff_zero_eq_constantCoeff, hφ]
    refine Finset.sum_eq_zero fun i _ ↦ if_neg fun h ↦ ?_
    have h1 := Finsupp.single_le_iff.mp h.1
    simp only [Finsupp.coe_zero, Pi.zero_apply] at h1
    omega
  · have hne : d.support.Nonempty := Finsupp.support_nonempty_iff.mpr hd
    have hmem : d.support.min' hne ∈ d.support := Finset.min'_mem _ hne
    have hpos : 1 ≤ d (d.support.min' hne) :=
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hmem)
    rw [Finset.sum_eq_single (d.support.min' hne)]
    · have hcond : single (d.support.min' hne) 1 ≤ d ∧
          (∀ j, j < d.support.min' hne → d j = 0) := by
        refine ⟨Finsupp.single_le_iff.mpr hpos, fun j hj ↦ ?_⟩
        by_contra hdj
        exact absurd (Finset.min'_le _ j (Finsupp.mem_support_iff.mpr hdj)) (not_le.mpr hj)
      rw [if_pos hcond]
    · intro i _ hi
      refine if_neg fun h ↦ ?_
      have hisupp : i ∈ d.support :=
        Finsupp.mem_support_iff.mpr (by have := Finsupp.single_le_iff.mp h.1; omega)
      have hlt : d.support.min' hne < i :=
        lt_of_le_of_ne (Finset.min'_le _ i hisupp) (Ne.symm hi)
      exact absurd (h.2 _ hlt) (Nat.one_le_iff_ne_zero.mp hpos)
    · intro h; exact absurd (Finset.mem_univ _) h

open MvPowerSeries in
theorem MvPowerSeries.maximalIdeal_eq_span_X {σ : Type*} [Finite σ] [LinearOrder σ] :
    IsLocalRing.maximalIdeal (MvPowerSeries σ ℂ)
      = Ideal.span (Set.range (X : σ → MvPowerSeries σ ℂ)) := by
  apply le_antisymm
  · intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    refine mem_span_X_of_constantCoeff_eq_zero ?_
    by_contra hc
    exact hx (isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hc))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 := isUnit_iff_constantCoeff.mp hu
    rw [constantCoeff_X] at h0
    exact not_isUnit_zero h0

/-- **The formal power series ring is complete for its maximal-adic topology.**

No order on `σ` is assumed: `MvPowerSeries.maximalIdeal_eq_span_X` needs one to pick a smallest
variable occurring in a monomial, but its *statement* does not mention the order, so any linear
order will do and a finite type has one. -/
instance instIsAdicCompleteMaximalIdealMvPowerSeries {σ : Type*} [Finite σ] :
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries σ ℂ)) (MvPowerSeries σ ℂ) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  letI : LinearOrder σ := LinearOrder.lift' e e.injective
  rw [MvPowerSeries.maximalIdeal_eq_span_X]
  infer_instance

open Polynomial in
theorem exists_diffQuotient
    {R : Type*} [CommRing R] [Nontrivial R]
    (q : R[X]) (hq : q ≠ 0) (c : R) :
    ∃ Q : R[X], Q.degree < q.degree ∧ q - C (q.eval c) = (X - C c) * Q := by
  refine ⟨q /ₘ (X - C c), ?_, ?_⟩
  · refine degree_divByMonic_lt q (X - C c) hq ?_
    rw [degree_X_sub_C]
    exact_mod_cast Nat.zero_lt_one
  · have h := modByMonic_add_div q (X - C c)
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    exact (eq_sub_of_add_eq' h).symm

open Polynomial in
/-- Divided difference: `p(c) - p(t) = (c - t) * (p /ₘ (X - C c))(t)`. -/
theorem eval_sub_eval_eq_mul_divByMonic {R : Type*} [CommRing R] (p : R[X]) (c t : R) :
    p.eval c - p.eval t = (c - t) * (p /ₘ (X - C c)).eval t := by
  have h := modByMonic_add_div p (X - C c)
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  have h2 := congrArg (Polynomial.eval t) h
  simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X] at h2
  linear_combination h2

open Finset Polynomial in
/-- Divided-difference identity for a finite power sum with leading coefficient one. -/
theorem sum_pow_sub_sum_pow_eq (d : ℕ) (c : ℕ → ℂ) (hcd : c d = 1) (ζ t : ℂ) :
    (∑ j ∈ range (d + 1), c j * ζ ^ j) - (∑ j ∈ range (d + 1), c j * t ^ j)
      = (ζ - t) * ∑ i ∈ range d, t ^ i *
          ∑ j ∈ Icc (i + 1) d, ζ ^ (j - 1 - i) * c j := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0; simp
  set p : ℂ[X] := ∑ j ∈ range (d + 1), C (c j) * X ^ j with hp
  have hcoeff : ∀ k, p.coeff k = if k ≤ d then c k else 0 := by
    intro k
    rw [hp, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (range (d + 1)) k c]
    simp
  have hle : p.natDegree ≤ d :=
    natDegree_le_iff_coeff_eq_zero.mpr (fun k hk ↦ by rw [hcoeff k, if_neg (by omega)])
  have hnd : p.natDegree = d := by
    refine natDegree_eq_of_le_of_coeff_ne_zero hle ?_
    rw [hcoeff d, if_pos le_rfl, hcd]
    exact one_ne_zero
  have heval : ∀ s : ℂ, p.eval s = ∑ j ∈ range (d + 1), c j * s ^ j := by
    intro s
    rw [hp, eval_finsetSum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    simp
  have hdeg : (p /ₘ (X - C ζ)).natDegree < d := by
    rw [natDegree_divByMonic p (monic_X_sub_C ζ), natDegree_X_sub_C, hnd]
    omega
  have hkey := eval_sub_eval_eq_mul_divByMonic p ζ t
  rw [heval, heval] at hkey
  rw [hkey, eval_eq_sum_range' hdeg]
  congr 1
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [coeff_divByMonic_X_sub_C p ζ i, hnd, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj ↦ ?_)
  have hexp : j - 1 - i = j - (i + 1) := by omega
  rw [hcoeff j, if_pos (Finset.mem_Icc.mp hj).2, hexp]
  ring

namespace MvPowerSeries
section Curry

/-! ### Currying a power series in a sum of variables

A formal power series in the variables `σ ⊕ τ` is the same thing as a power series in `σ`
whose coefficients are power series in `τ`: on coefficients this is nothing but
`Finsupp.sumFinsuppEquivProdFinsupp`, which splits an exponent on `σ ⊕ τ` into its `σ`-part
and its `τ`-part. `curry` and `uncurry` are the two directions and `curryEquiv` packages them
as a ring equivalence; `finSuccRingEquiv` specialises it to
`ℂ⟦x₁, …, x_{n+1}⟧ ≃+* (ℂ⟦x₁, …, x_n⟧)⟦X⟧`, singling out the last variable.

Nothing in this section is used elsewhere in the project: the Weierstrass theorems below reach
the same "one distinguished variable" viewpoint through `LocalOkaRing.fromPolynomial` and
`Polynomial` rather than through `PowerSeries`. It is general `MvPowerSeries` API in a Mathlib
namespace and a Mathlib upstreaming candidate, which is why it is documented and kept rather
than made `private`.
-/

variable {σ τ R : Type*} [CommSemiring R]

/-- A power series in the variables `σ ⊕ τ`, read as a power series in `σ` with coefficients
power series in `τ`. Its `(dσ, dτ)`-coefficient is the coefficient of the exponent on `σ ⊕ τ`
assembled from `dσ` and `dτ`. Inverse to `uncurry`; packaged as a ring equivalence in
`curryEquiv`. -/
noncomputable def curry (f : MvPowerSeries (σ ⊕ τ) R) : MvPowerSeries σ (MvPowerSeries τ R) :=
  fun dσ dτ ↦ coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (dσ, dτ)) f

/-- A power series in `σ` with coefficients power series in `τ`, read as a power series in the
variables `σ ⊕ τ`. Inverse to `curry`. -/
noncomputable def uncurry (g : MvPowerSeries σ (MvPowerSeries τ R)) : MvPowerSeries (σ ⊕ τ) R :=
  fun d ↦ coeff (Finsupp.sumFinsuppEquivProdFinsupp d).2
              (coeff (Finsupp.sumFinsuppEquivProdFinsupp d).1 g)

@[simp] lemma coeff_curry (f : MvPowerSeries (σ ⊕ τ) R) (dσ : σ →₀ ℕ) (dτ : τ →₀ ℕ) :
    coeff dτ (coeff dσ (curry f)) =
      coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (dσ, dτ)) f := rfl

@[simp] lemma coeff_uncurry (g : MvPowerSeries σ (MvPowerSeries τ R)) (d : σ ⊕ τ →₀ ℕ) :
    coeff d (uncurry g) =
      coeff (Finsupp.sumFinsuppEquivProdFinsupp d).2
        (coeff (Finsupp.sumFinsuppEquivProdFinsupp d).1 g) := rfl

lemma uncurry_curry (f : MvPowerSeries (σ ⊕ τ) R) : uncurry (curry f) = f := by
  ext d
  rw [coeff_uncurry, coeff_curry, Prod.mk.eta, Equiv.symm_apply_apply]

lemma curry_uncurry (g : MvPowerSeries σ (MvPowerSeries τ R)) : curry (uncurry g) = g := by
  ext dσ dτ
  rw [coeff_curry, coeff_uncurry, Equiv.apply_symm_apply]

@[simp] lemma curry_add (f g : MvPowerSeries (σ ⊕ τ) R) :
    curry (f + g) = curry f + curry g := by
  ext dσ dτ
  simp [map_add]

@[simp] lemma curry_zero : curry (0 : MvPowerSeries (σ ⊕ τ) R) = 0 := by
  ext dσ dτ
  simp

lemma curry_one : curry (1 : MvPowerSeries (σ ⊕ τ) R) = 1 := by
  classical
  have he0 : Finsupp.sumFinsuppEquivProdFinsupp (0 : σ ⊕ τ →₀ ℕ) = (0, 0) := by
    apply Prod.ext <;> ext x <;> simp
  ext dσ dτ
  rw [coeff_curry, coeff_one]
  have key : (Finsupp.sumFinsuppEquivProdFinsupp.symm (dσ, dτ) = (0 : σ ⊕ τ →₀ ℕ))
      ↔ (dσ = 0 ∧ dτ = 0) := by
    rw [Equiv.symm_apply_eq, he0, Prod.mk.injEq]
  simp only [key]
  by_cases h : dσ = 0 ∧ dτ = 0
  · obtain ⟨h1, h2⟩ := h; subst h1; subst h2; simp
  · rw [if_neg h]
    rcases not_and_or.mp h with h' | h'
    · simp [coeff_one, if_neg h']
    · by_cases hσ : dσ = 0
      · subst hσ; simp [coeff_one, if_neg h']
      · simp [coeff_one, if_neg hσ]

lemma symm_prod_eq_sumElim (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    Finsupp.sumFinsuppEquivProdFinsupp.symm (a, b) = Finsupp.sumElim a b := by
  ext x
  cases x with
  | inl x => simp
  | inr x => simp

lemma curry_mul (f g : MvPowerSeries (σ ⊕ τ) R) : curry (f * g) = curry f * curry g := by
  classical
  ext dσ dτ
  have hL : coeff dτ (coeff dσ (curry (f * g)))
      = ∑ q ∈ (Finset.antidiagonal dσ) ×ˢ (Finset.antidiagonal dτ),
          coeff (Finsupp.sumElim q.1.1 q.2.1) f * coeff (Finsupp.sumElim q.1.2 q.2.2) g := by
    rw [coeff_curry, symm_prod_eq_sumElim, coeff_mul,
      ← Finsupp.image_sumElim_product_antidiagonal,
      Finset.sum_image (by
        rintro ⟨⟨x, y⟩, z, w⟩ _ ⟨⟨x', y'⟩, z', w'⟩ _ hEq
        simp only [Prod.mk.injEq] at hEq
        obtain ⟨h1, h2⟩ := hEq
        have hx : x = x' := by ext a; simpa using DFunLike.congr_fun h1 (Sum.inl a)
        have hz : z = z' := by ext a; simpa using DFunLike.congr_fun h1 (Sum.inr a)
        have hy : y = y' := by ext a; simpa using DFunLike.congr_fun h2 (Sum.inl a)
        have hw : w = w' := by ext a; simpa using DFunLike.congr_fun h2 (Sum.inr a)
        subst hx; subst hy; subst hz; subst hw; rfl)]
  have hR : coeff dτ (coeff dσ (curry f * curry g))
      = ∑ q ∈ (Finset.antidiagonal dσ) ×ˢ (Finset.antidiagonal dτ),
          coeff (Finsupp.sumElim q.1.1 q.2.1) f * coeff (Finsupp.sumElim q.1.2 q.2.2) g := by
    rw [coeff_mul, map_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun pσ _ ↦ ?_
    rw [coeff_mul]
    refine Finset.sum_congr rfl fun pτ _ ↦ ?_
    rw [coeff_curry, coeff_curry, symm_prod_eq_sumElim, symm_prod_eq_sumElim]
  rw [hL, hR]

/-- `curry` and `uncurry` as a ring equivalence
`R⟦σ ⊕ τ⟧ ≃+* (R⟦τ⟧)⟦σ⟧`. -/
noncomputable def curryEquiv : MvPowerSeries (σ ⊕ τ) R ≃+* MvPowerSeries σ (MvPowerSeries τ R) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
  map_add' := curry_add
  map_mul' := curry_mul

/-- `Fin (n + 1)` split as its last element and the rest, in the form `Unit ⊕ Fin n` that
`curryEquiv` consumes: `Fin.last n` goes to `Sum.inl ()` and `Fin.castSucc j` to `Sum.inr j`.

This differs from `finSumFinEquiv` and `Fin.consEquiv` in singling out the **last** variable,
which is the one the Weierstrass theorems distinguish. -/
def finLastEquivSum (n : ℕ) : Fin (n + 1) ≃ Unit ⊕ Fin n where
  toFun i := Fin.lastCases (Sum.inl ()) Sum.inr i
  invFun x := Sum.elim (fun _ ↦ Fin.last n) Fin.castSucc x
  left_inv i := by
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp
  right_inv x := by
    cases x with
    | inl u => simp
    | inr j => simp

/-- Power series in `n + 1` variables, read as power series in the last variable with
coefficients power series in the first `n`: `ℂ⟦x₁, …, x_{n+1}⟧ ≃+* (ℂ⟦x₁, …, x_n⟧)⟦X⟧`.

This is `curryEquiv` along `finLastEquivSum`, and it is the change of viewpoint that makes the
Weierstrass division and preparation theorems statements about a polynomial ring in one
variable. -/
noncomputable def finSuccRingEquiv (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) ℂ ≃+* PowerSeries (MvPowerSeries (Fin n) ℂ) :=
  (MvPowerSeries.renameEquiv (R := ℂ) (finLastEquivSum n)).toRingEquiv.trans
    (curryEquiv (σ := Unit) (τ := Fin n) (R := ℂ))

end Curry
end MvPowerSeries

namespace MvPowerSeries

lemma summableAt_X {ι : Type*} (i : ι) (x : ι → ℂ) :
    (X i : MvPowerSeries ι ℂ).SummableAt x := by
  classical
  refine summable_of_ne_finset_zero (s := {Finsupp.single i 1}) fun d hd ↦ ?_
  rw [Finset.mem_singleton] at hd
  rw [term, coeff_X, if_neg hd, zero_mul, norm_zero]

lemma locallyConvergent_X {ι : Type*} (i : ι) :
    (X i : MvPowerSeries ι ℂ).LocallyConvergent :=
  .of_forall fun x ↦ summableAt_X i x

lemma eval_X {ι : Type*} (i : ι) (x : ι → ℂ) :
    (X i : MvPowerSeries ι ℂ).eval x = x i := by
  classical
  rw [eval, tsum_eq_single (Finsupp.single i 1) ?_]
  · rw [term, coeff_X, if_pos rfl, one_mul, evalMonomial, Finsupp.prod_single_index] <;> simp
  · intro d hd
    rw [term, coeff_X, if_neg hd, zero_mul]

lemma eval_add_of_summableAt {ι : Type*} {P Q : MvPowerSeries ι ℂ} {x : ι → ℂ}
    (hP : P.SummableAt x) (hQ : Q.SummableAt x) :
    (P + Q).eval x = P.eval x + Q.eval x := by
  have hfun : (P + Q).term x = fun d ↦ P.term x d + Q.term x d :=
    funext fun d ↦ term_add P Q x d
  refine (hP.add hQ).hasSum.unique ?_
  rw [hfun]
  exact hP.hasSum.add hQ.hasSum

lemma eval_mul_of_summableAt {ι : Type*} {P Q : MvPowerSeries ι ℂ} {x : ι → ℂ}
    (hP : P.SummableAt x) (hQ : Q.SummableAt x) :
    (P * Q).eval x = P.eval x * Q.eval x := by
  classical
  have hFsum : Summable fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ P.term x p.1 * Q.term x p.2 := by
    refine Summable.of_norm ?_
    simpa [norm_mul] using
      Summable.mul_of_nonneg hP hQ (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hF : HasSum (fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ P.term x p.1 * Q.term x p.2)
      (P.eval x * Q.eval x) := hP.hasSum.mul hQ.hasSum hFsum
  have hσ := (antidiagonalSigmaEquiv ι).hasSum_iff.mpr hF
  have hfib : ∀ d : ι →₀ ℕ,
      HasSum (fun c : {p : (ι →₀ ℕ) × (ι →₀ ℕ) //
          p ∈ Finset.HasAntidiagonal.antidiagonal d} ↦ P.term x c.1.1 * Q.term x c.1.2)
        ((P * Q).term x d) := by
    intro d
    rw [term_mul, ← Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal d)
      (fun p ↦ P.term x p.1 * Q.term x p.2)]
    exact hasSum_fintype _
  exact ((hσ.sigma hfib).unique (hP.mul hQ).hasSum).symm

lemma summableAt_zero {ι : Type*} (x : ι → ℂ) : (0 : MvPowerSeries ι ℂ).SummableAt x := by
  simpa using summableAt_algebraMap 0 x

lemma summableAt_one {ι : Type*} (x : ι → ℂ) : (1 : MvPowerSeries ι ℂ).SummableAt x := by
  simpa using summableAt_algebraMap 1 x

lemma eval_algebraMap {ι : Type*} (c : ℂ) (x : ι → ℂ) :
    (algebraMap ℂ (MvPowerSeries ι ℂ) c).eval x = c := by
  classical
  rw [eval, tsum_eq_single 0 (fun d hd ↦ term_algebraMap_of_ne_zero c x hd),
    term_algebraMap_zero]

lemma eval_of_zero {ι : Type*} (x : ι → ℂ) : (0 : MvPowerSeries ι ℂ).eval x = 0 := by
  simpa using eval_algebraMap 0 x

lemma eval_one {ι : Type*} (x : ι → ℂ) : (1 : MvPowerSeries ι ℂ).eval x = 1 := by
  simpa using eval_algebraMap 1 x

lemma SummableAt.sum {ι κ : Type*} {x : ι → ℂ} {s : Finset κ} {P : κ → MvPowerSeries ι ℂ} :
    (∀ k ∈ s, (P k).SummableAt x) → (∑ k ∈ s, P k).SummableAt x := by
  classical
  induction s using Finset.induction with
  | empty => intro _; simpa using summableAt_zero x
  | insert k s hk ih =>
      intro h
      rw [Finset.sum_insert hk]
      exact (h k (by simp)).add (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

lemma eval_sum_of_summableAt {ι κ : Type*} {x : ι → ℂ} {s : Finset κ}
    {P : κ → MvPowerSeries ι ℂ} :
    (∀ k ∈ s, (P k).SummableAt x) → (∑ k ∈ s, P k).eval x = ∑ k ∈ s, (P k).eval x := by
  classical
  induction s using Finset.induction with
  | empty => intro _; simp [eval_of_zero]
  | insert k s hk ih =>
      intro h
      have hs : ∀ j ∈ s, (P j).SummableAt x := fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hk, Finset.sum_insert hk,
        eval_add_of_summableAt (h k (by simp)) (SummableAt.sum hs), ih hs]

lemma SummableAt.pow {ι : Type*} {P : MvPowerSeries ι ℂ} {x : ι → ℂ} (h : P.SummableAt x) :
    ∀ m : ℕ, (P ^ m).SummableAt x
  | 0 => by simpa using summableAt_one x
  | m + 1 => by rw [pow_succ]; exact (SummableAt.pow h m).mul h

lemma eval_pow_of_summableAt {ι : Type*} {P : MvPowerSeries ι ℂ} {x : ι → ℂ}
    (h : P.SummableAt x) :
    ∀ m : ℕ, (P ^ m).eval x = P.eval x ^ m
  | 0 => by simpa using eval_one x
  | m + 1 => by
      rw [pow_succ, pow_succ, eval_mul_of_summableAt (h.pow m) h, eval_pow_of_summableAt h m]

lemma summableAt_zero_pt {ι : Type*} (P : MvPowerSeries ι ℂ) :
    P.SummableAt (0 : ι → ℂ) := by
  classical
  refine summable_of_ne_finset_zero (s := {0}) fun d hd ↦ ?_
  rw [Finset.mem_singleton] at hd
  rw [term, evalMonomial_eq_zero hd, mul_zero, norm_zero]

end MvPowerSeries

variable {n : ℕ}

/-- The last coordinate `x_{n+1}` as a germ at the origin in `n + 1` variables: the
distinguished variable of the Weierstrass theorems, and the one variable not in the image of
`LocalOkaRing.incl`. Local convergence is `MvPowerSeries.locallyConvergent_X`. -/
noncomputable def LocalOkaRing.lastVar : LocalOkaRing (Fin (n + 1)) :=
  ⟨MvPowerSeries.X (Fin.last n), MvPowerSeries.locallyConvergent_X _⟩

namespace MvPowerSeries
open Filter Topology

variable {σ τ : Type*}

lemma evalMonomial_mapDomain (e : σ ↪ τ) (d : σ →₀ ℕ) (x : τ → ℂ) :
    evalMonomial (Finsupp.mapDomain e d) x = evalMonomial d (x ∘ e) :=
  Finsupp.prod_mapDomain_index_inj e.injective

lemma term_rename (e : σ ↪ τ) [TendstoCofinite (e : σ → τ)]
    (P : MvPowerSeries σ ℂ) (x : τ → ℂ) (d : σ →₀ ℕ) :
    (rename (e : σ → τ) P).term x (Finsupp.mapDomain e d) = P.term (x ∘ e) d := by
  rw [term, term, ← Finsupp.embDomain_eq_mapDomain, coeff_embDomain_rename,
    Finsupp.embDomain_eq_mapDomain, evalMonomial_mapDomain]

lemma eval_rename (e : σ ↪ τ) [TendstoCofinite (e : σ → τ)]
    (P : MvPowerSeries σ ℂ) (x : τ → ℂ) :
    (rename (e : σ → τ) P).eval x = P.eval (x ∘ e) := by
  have hzero : Function.support (fun d' ↦ (rename (e : σ → τ) P).term x d') ⊆
      Set.range (Finsupp.mapDomain (e : σ → τ)) := by
    intro d' hd'
    by_contra h
    apply hd'
    change (rename (e : σ → τ) P).term x d' = 0
    rw [term, coeff_rename_eq_zero _ _ h, zero_mul]
  rw [eval, eval, ← Function.Injective.tsum_eq
    (Finsupp.mapDomain_injective e.injective) hzero]
  exact tsum_congr fun d ↦ term_rename e P x d

lemma SummableAt.rename (e : σ ↪ τ) [TendstoCofinite (e : σ → τ)]
    {P : MvPowerSeries σ ℂ} {x : τ → ℂ} (h : P.SummableAt (x ∘ e)) :
    (rename (e : σ → τ) P).SummableAt x := by
  refine (Function.Injective.summable_iff
    (g := fun d : σ →₀ ℕ ↦ Finsupp.mapDomain (e : σ → τ) d)
    (Finsupp.mapDomain_injective e.injective) ?_).mp ?_
  · intro d' hd'
    rw [term, coeff_rename_eq_zero _ _ hd', zero_mul, norm_zero]
  · simpa [SummableAt, Function.comp_def, term_rename] using h

lemma LocallyConvergent.rename (e : σ ↪ τ) [TendstoCofinite (e : σ → τ)]
    {P : MvPowerSeries σ ℂ} (hP : P.LocallyConvergent) :
    (rename (e : σ → τ) P).LocallyConvergent := by
  have hc : Tendsto (fun x : τ → ℂ ↦ x ∘ (e : σ → τ)) (𝓝 0) (𝓝 0) :=
    (continuous_pi fun i ↦ continuous_apply (e i)).tendsto' 0 0 rfl
  filter_upwards [hc.eventually hP] with x hx using SummableAt.rename e hx

end MvPowerSeries

instance : Filter.TendstoCofinite (Fin.castSuccEmb : Fin n → Fin (n + 1)) :=
  Filter.tendstoCofinite_of_finite _

/-- A germ at the origin in `n` variables, read as a germ in `n + 1` variables not involving
the last one: renaming along `Fin.castSuccEmb`, as a morphism of `ℂ`-algebras.

Together with `LocalOkaRing.lastVar` this presents `LocalOkaRing (Fin (n + 1))` over
`LocalOkaRing (Fin n)`, which is what the induction on the number of variables needs. Local
convergence is preserved because renaming along an embedding only reindexes the variables
(`MvPowerSeries.LocallyConvergent.rename`). -/
noncomputable def LocalOkaRing.incl :
    LocalOkaRing (Fin n) →ₐ[ℂ] LocalOkaRing (Fin (n + 1)) :=
  ((MvPowerSeries.rename (Fin.castSuccEmb : Fin n → Fin (n + 1))).comp
      (localOkaSubring (Fin n)).val).codRestrict _
    (fun P ↦ MvPowerSeries.LocallyConvergent.rename _ P.2)

open Polynomial TopologicalSpace

variable {n : ℕ}

/-- A local Weierstrass polynomial is a monic polynomial whose coefficients below the leading
one vanish at the origin. -/
structure IsLocalWeierstrassPolynomial
  (P : (MvPowerSeries (Fin n) ℂ)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) :
  MvPowerSeries.constantCoeff (P.coeff i) = 0

section FromPolynomial

namespace MvPowerSeries

/-- A power series in `n` variables representing `F` represents, as a power series in `n + 1`
variables, the pullback of `F` along the projection to the first `n` coordinates. -/
lemma Represents.rename_castSucc {P : MvPowerSeries (Fin n) ℂ} {F : (Fin n → ℂ) → ℂ}
    (hP : P.Represents F) :
    (rename (Fin.castSuccEmb : Fin n → Fin (n + 1)) P).Represents
      (fun x ↦ F (Fin.init x)) := by
  have hcont : Continuous (Fin.init : (Fin (n + 1) → ℂ) → (Fin n → ℂ)) :=
    continuous_pi fun i ↦ continuous_apply i.castSucc
  filter_upwards [(hcont.tendsto 0).eventually hP] with x hx
  have hinj : Function.Injective
      (Finsupp.mapDomain (M := ℕ) (Fin.castSuccEmb : Fin n → Fin (n + 1))) :=
    Finsupp.mapDomain_injective Fin.castSuccEmb.injective
  have hvanish : ∀ d ∉ Set.range
      (Finsupp.mapDomain (M := ℕ) (Fin.castSuccEmb : Fin n → Fin (n + 1))),
      (rename (Fin.castSuccEmb : Fin n → Fin (n + 1)) P).term x d = 0 := fun d hd ↦ by
    rw [term, coeff_rename_eq_zero _ _ hd, zero_mul]
  refine (Function.Injective.hasSum_iff hinj hvanish).mp ?_
  have hfun : (rename (Fin.castSuccEmb : Fin n → Fin (n + 1)) P).term x ∘
      Finsupp.mapDomain (Fin.castSuccEmb : Fin n → Fin (n + 1)) = P.term (Fin.init x) :=
    funext fun d ↦ term_rename Fin.castSuccEmb P x d
  rw [hfun]
  exact hx

variable {ι : Type*}

/-- The power series `X i` represents the `i`-th coordinate function. -/
lemma represents_X (i : ι) : (X i : MvPowerSeries ι ℂ).Represents (fun x ↦ x i) := by
  classical
  refine .of_forall fun x ↦ ?_
  have h : ∀ d ≠ Finsupp.single i 1, (X i : MvPowerSeries ι ℂ).term x d = 0 := fun d hd ↦ by
    rw [term, coeff_X, if_neg hd, zero_mul]
  have h1 : (X i : MvPowerSeries ι ℂ).term x (Finsupp.single i 1) = x i := by
    rw [term, coeff_X, if_pos rfl, one_mul]
    simp [evalMonomial]
  simpa only [h1] using hasSum_single (f := (X i : MvPowerSeries ι ℂ).term x)
    (Finsupp.single i 1) h

end MvPowerSeries

namespace LocalOkaRing

open MvPowerSeries

@[simp]
lemma coe_incl (P : LocalOkaRing (Fin n)) :
    (incl P : MvPowerSeries (Fin (n + 1)) ℂ) =
      MvPowerSeries.rename (Fin.castSuccEmb : Fin n → Fin (n + 1))
        (P : MvPowerSeries (Fin n) ℂ) :=
  rfl

@[simp]
lemma coe_lastVar :
    ((lastVar : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ) =
      MvPowerSeries.X (Fin.last n) :=
  rfl

end LocalOkaRing

end FromPolynomial

/-- A polynomial over the germs in `n` variables, viewed as a germ in `n + 1` variables. -/
noncomputable def LocalOkaRing.fromPolynomial :
    (LocalOkaRing (Fin n))[X] →ₐ[ℂ] LocalOkaRing (Fin (n + 1)) :=
  Polynomial.aevalTower LocalOkaRing.incl LocalOkaRing.lastVar

namespace LocalOkaRing

@[simp]
lemma fromPolynomial_C (P : LocalOkaRing (Fin n)) :
    fromPolynomial (Polynomial.C P) = incl P :=
  Polynomial.aevalTower_C _ _ _

@[simp]
lemma fromPolynomial_X :
    fromPolynomial (Polynomial.X : (LocalOkaRing (Fin n))[X]) = lastVar :=
  Polynomial.aevalTower_X _ _

/-- The underlying power series of `LocalOkaRing.fromPolynomial Q` is
`MvPowerSeries.fromPolynomial'` applied to the underlying polynomial of power series. -/
lemma coe_fromPolynomial (Q : (LocalOkaRing (Fin n))[X]) :
    (fromPolynomial Q : MvPowerSeries (Fin (n + 1)) ℂ) =
      MvPowerSeries.fromPolynomial'
        (Q.map (Subring.subtype (localOkaSubring (Fin n)).toSubring)) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMemClass.coe_add, hp, hq, Polynomial.map_add, map_add]
  | monomial k a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    rw [map_mul, map_pow, fromPolynomial_C, fromPolynomial_X]
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
    rw [map_mul, map_pow, MvPowerSeries.fromPolynomial'_C, MvPowerSeries.fromPolynomial'_X]
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_incl, coe_lastVar]
    rfl

lemma fromPolynomial_injective :
    Function.Injective (fromPolynomial (n := n)) := by
  intro Q₁ Q₂ h
  have h2 : (fromPolynomial Q₁ : MvPowerSeries (Fin (n + 1)) ℂ) = fromPolynomial Q₂ :=
    congrArg Subtype.val h
  rw [coe_fromPolynomial, coe_fromPolynomial] at h2
  exact Polynomial.map_injective _ (fun a b hab ↦ Subtype.ext hab)
    (MvPowerSeries.fromPolynomial'_injective h2)

end LocalOkaRing

lemma LocalOkaRing.eval_incl (a : LocalOkaRing (Fin n)) (z : Fin (n + 1) → ℂ) :
    ((incl a : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval z
      = (a : MvPowerSeries (Fin n) ℂ).eval (fun j ↦ z j.castSucc) := by
  change (MvPowerSeries.rename (Fin.castSuccEmb : Fin n → Fin (n + 1))
      (a : MvPowerSeries (Fin n) ℂ)).eval z = _
  rw [MvPowerSeries.eval_rename]
  rfl

lemma LocalOkaRing.eval_lastVar (z : Fin (n + 1) → ℂ) :
    ((lastVar : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval z
      = z (Fin.last n) :=
  MvPowerSeries.eval_X _ _

lemma LocalOkaRing.fromPolynomial_eq_sum (q : (LocalOkaRing (Fin n))[X]) :
    fromPolynomial q
      = ∑ i ∈ Finset.range (q.natDegree + 1), incl (q.coeff i) * lastVar ^ i := by
  rw [fromPolynomial]
  exact Polynomial.eval₂_eq_sum_range _ _

lemma LocalOkaRing.summableAt_incl (a : LocalOkaRing (Fin n)) (z : Fin (n + 1) → ℂ)
    (ha : (a : MvPowerSeries (Fin n) ℂ).SummableAt (fun j ↦ z j.castSucc)) :
    ((incl a : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).SummableAt z := by
  change (MvPowerSeries.rename (Fin.castSuccEmb : Fin n → Fin (n + 1))
      (a : MvPowerSeries (Fin n) ℂ)).SummableAt z
  exact MvPowerSeries.SummableAt.rename _ ha

lemma LocalOkaRing.eval_fromPolynomial (q : (LocalOkaRing (Fin n))[X]) (z : Fin (n + 1) → ℂ)
    (hz : ∀ i, ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt
      (fun j ↦ z j.castSucc)) :
    ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval z
      = ∑ i ∈ Finset.range (q.natDegree + 1),
          ((q.coeff i : MvPowerSeries (Fin n) ℂ).eval (fun j ↦ z j.castSucc))
            * z (Fin.last n) ^ i := by
  classical
  have hX : (MvPowerSeries.X (Fin.last n) : MvPowerSeries (Fin (n + 1)) ℂ).SummableAt z :=
    MvPowerSeries.summableAt_X _ z
  have hcast : ((∑ i ∈ Finset.range (q.natDegree + 1),
        incl (q.coeff i) * lastVar ^ i : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ)
      = ∑ i ∈ Finset.range (q.natDegree + 1),
          ((incl (q.coeff i) : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)
            * (MvPowerSeries.X (Fin.last n) : MvPowerSeries (Fin (n + 1)) ℂ) ^ i := by
    push_cast
    rfl
  have hsum : ∀ i ∈ Finset.range (q.natDegree + 1),
      (((incl (q.coeff i) : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)
        * (MvPowerSeries.X (Fin.last n) : MvPowerSeries (Fin (n + 1)) ℂ) ^ i).SummableAt z :=
    fun i _ ↦ (summableAt_incl _ z (hz i)).mul (hX.pow i)
  rw [fromPolynomial_eq_sum, hcast, MvPowerSeries.eval_sum_of_summableAt hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [MvPowerSeries.eval_mul_of_summableAt (summableAt_incl _ z (hz i)) (hX.pow i),
    MvPowerSeries.eval_pow_of_summableAt hX, eval_incl, MvPowerSeries.eval_X]

lemma LocalOkaRing.eval_fromPolynomial_axis (q : (LocalOkaRing (Fin n))[X]) (w : ℂ) :
    ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval
        (Fin.snoc (0 : Fin n → ℂ) w : Fin (n + 1) → ℂ)
      = ∑ i ∈ Finset.range (q.natDegree + 1),
          MvPowerSeries.constantCoeff (q.coeff i : MvPowerSeries (Fin n) ℂ) * w ^ i := by
  have hpt : (fun j : Fin n ↦ (Fin.snoc (0 : Fin n → ℂ) w : Fin (n + 1) → ℂ) j.castSucc) = 0 := by
    funext j; simp [Fin.snoc_castSucc]
  rw [eval_fromPolynomial q (Fin.snoc (0 : Fin n → ℂ) w : Fin (n + 1) → ℂ)
    (fun i ↦ by rw [hpt]; exact MvPowerSeries.summableAt_zero_pt _)]
  simp only [Fin.snoc_last]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hpt, MvPowerSeries.eval_zero]

lemma LocalOkaRing.eval_fromPolynomial_axis_weierstrass
    (q : (LocalOkaRing (Fin n))[X])
    (hq : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q)) (w : ℂ) :
    ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval
        (Fin.snoc (0 : Fin n → ℂ) w : Fin (n + 1) → ℂ)
      = w ^ q.natDegree := by
  classical
  have hinj : Function.Injective (localOkaSubring (Fin n)).val.toRingHom :=
    Subtype.val_injective
  set Q := Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q with hQ
  have hqne : q ≠ 0 := fun h ↦ hq.monic.ne_zero (by rw [hQ, h, Polynomial.map_zero])
  have hdeg : Q.natDegree = q.natDegree := natDegree_map_eq_of_injective hinj q
  have hcoeff : ∀ i, MvPowerSeries.constantCoeff (q.coeff i : MvPowerSeries (Fin n) ℂ)
      = MvPowerSeries.constantCoeff (Q.coeff i) := fun i ↦ by rw [hQ, Polynomial.coeff_map]; rfl
  rw [eval_fromPolynomial_axis,
    Finset.sum_eq_single_of_mem q.natDegree (Finset.self_mem_range_succ q.natDegree)]
  · have hlead :
        MvPowerSeries.constantCoeff (q.coeff q.natDegree : MvPowerSeries (Fin n) ℂ) = 1 := by
      rw [hcoeff, ← hdeg, hq.monic.coeff_natDegree, map_one]
    rw [hlead, one_mul]
  · intro i hi hine
    have hilt : i < q.natDegree := by
      have := Finset.mem_range.mp hi; omega
    have hidQ : (i : WithBot ℕ) < Q.degree := by
      rw [hQ, degree_map_eq_of_injective hinj, Polynomial.degree_eq_natDegree hqne]
      exact_mod_cast hilt
    rw [hcoeff, hq.apply_zero i hidQ, zero_mul]

lemma LocalOkaRing.eventually_summableAt_coeffs (q : (LocalOkaRing (Fin n))[X]) :
    ∀ᶠ z' : Fin n → ℂ in nhds 0,
      ∀ i ∈ Finset.range (q.natDegree + 1),
        ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt z' := by
  rw [Filter.eventually_all_finset]
  intro i _
  exact (q.coeff i).locallyConvergent

lemma LocalOkaRing.eval_coeff_natDegree
    (q : (LocalOkaRing (Fin n))[X])
    (hq : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q)) (z' : Fin n → ℂ) :
    ((q.coeff q.natDegree : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z' = 1 := by
  have hinj : Function.Injective (localOkaSubring (Fin n)).val.toRingHom :=
    Subtype.val_injective
  have hcoeff1 : q.coeff q.natDegree = 1 := by
    apply hinj
    have h1 : (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q).coeff q.natDegree = 1 := by
      rw [← natDegree_map_eq_of_injective hinj q]
      exact hq.monic.coeff_natDegree
    rw [map_one, ← Polynomial.coeff_map]
    exact h1
  rw [hcoeff1, show ((1 : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ) = 1 by simp]
  exact MvPowerSeries.eval_one z'

lemma LocalOkaRing.eventually_error_lt
    (q : (LocalOkaRing (Fin n))[X])
    (hq : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z' : Fin n → ℂ in nhds 0,
      ∑ i ∈ Finset.range q.natDegree,
          ‖((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z'‖ * ε ^ i
        < ε ^ q.natDegree := by
  have hinj : Function.Injective (localOkaSubring (Fin n)).val.toRingHom :=
    Subtype.val_injective
  have hqne : q ≠ 0 := fun h ↦ hq.monic.ne_zero (by rw [h, Polynomial.map_zero])
  have hci0 : ∀ i ∈ Finset.range q.natDegree,
      ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval 0 = 0 := by
    intro i hi
    have hilt : i < q.natDegree := Finset.mem_range.mp hi
    have hidQ : (i : WithBot ℕ)
        < (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q).degree := by
      rw [degree_map_eq_of_injective hinj, Polynomial.degree_eq_natDegree hqne]
      exact_mod_cast hilt
    rw [MvPowerSeries.eval_zero]
    have hthis := hq.apply_zero i hidQ
    rwa [Polynomial.coeff_map] at hthis
  have htend : Filter.Tendsto
      (fun z' : Fin n → ℂ ↦ ∑ i ∈ Finset.range q.natDegree,
          ‖((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z'‖ * ε ^ i)
      (nhds 0) (nhds 0) := by
    have hsum0 : (0 : ℝ) = ∑ i ∈ Finset.range q.natDegree,
        ‖((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval (0 : Fin n → ℂ)‖
          * ε ^ i := by
      refine (Finset.sum_eq_zero fun i hi ↦ ?_).symm
      rw [hci0 i hi, norm_zero, zero_mul]
    rw [hsum0]
    refine tendsto_finsetSum _ fun i _ ↦ ?_
    exact Filter.Tendsto.mul_const _
      ((q.coeff i).locallyConvergent.analyticAt.continuousAt.norm)
  exact htend.eventually (gt_mem_nhds (pow_pos hε _))

lemma LocalOkaRing.eventually_fromPolynomial_ne_zero
    (q : (LocalOkaRing (Fin n))[X])
    (hq : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z' : Fin n → ℂ in nhds 0,
      ∀ w : ℂ, ‖w‖ = ε →
        ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval
            (Fin.snoc z' w : Fin (n + 1) → ℂ) ≠ 0 := by
  filter_upwards [eventually_summableAt_coeffs q, eventually_error_lt q hq hε]
    with z' hsummable herror w hw
  have hpt : (fun j : Fin n ↦ (Fin.snoc z' w : Fin (n + 1) → ℂ) j.castSucc) = z' := by
    funext j; simp [Fin.snoc_castSucc]
  have hz : ∀ i, ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt
      (fun j : Fin n ↦ (Fin.snoc z' w : Fin (n + 1) → ℂ) j.castSucc) := by
    intro i
    rw [hpt]
    by_cases hi : i ≤ q.natDegree
    · exact hsummable i (Finset.mem_range.mpr (by omega))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simpa using MvPowerSeries.summableAt_zero z'
  have hval : ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc z' w : Fin (n + 1) → ℂ)
      = ∑ i ∈ Finset.range (q.natDegree + 1),
          ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z' * w ^ i := by
    rw [eval_fromPolynomial q (Fin.snoc z' w : Fin (n + 1) → ℂ) hz]
    simp only [Fin.snoc_last, hpt]
  set S := ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
      MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc z' w : Fin (n + 1) → ℂ) with hS
  have hSdecomp : S = w ^ q.natDegree + ∑ i ∈ Finset.range q.natDegree,
      ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z' * w ^ i := by
    rw [hval, Finset.sum_range_succ, eval_coeff_natDegree q hq z', one_mul, add_comm]
  set T := ∑ i ∈ Finset.range q.natDegree,
      ((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z' * w ^ i with hT
  have hTbound : ‖T‖ ≤ ∑ i ∈ Finset.range q.natDegree,
      ‖((q.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval z'‖ * ε ^ i := by
    rw [hT]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ le_of_eq ?_)
    rw [norm_mul, norm_pow, hw]
  have hlow : (0 : ℝ) < ‖S‖ := by
    have h2 : ‖(w : ℂ) ^ q.natDegree‖ ≤ ‖S‖ + ‖T‖ := by
      have he : (w : ℂ) ^ q.natDegree = S - T := by rw [hSdecomp]; ring
      rw [he]; exact norm_sub_le S T
    have h1 : ‖(w : ℂ) ^ q.natDegree‖ = ε ^ q.natDegree := by rw [norm_pow, hw]
    have hTlt : ‖T‖ < ε ^ q.natDegree := lt_of_le_of_lt hTbound herror
    rw [h1] at h2
    linarith
  intro hzero
  rw [hzero, norm_zero] at hlow
  exact lt_irrefl 0 hlow

/-- The value of `fromPolynomial q` along a `Fin.snoc` slice. -/
lemma LocalOkaRing.eval_fromPolynomial_snoc (q : (LocalOkaRing (Fin n))[X]) (w : Fin n → ℂ)
    (hwc : ∀ j, ((q.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt w)
    (s : ℂ) :
    ((fromPolynomial q : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval
        (Fin.snoc w s)
      = ∑ j ∈ Finset.range (q.natDegree + 1),
          ((q.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval w * s ^ j := by
  have hsnocc : (fun j : Fin n ↦ (Fin.snoc w s : Fin (n + 1) → ℂ) j.castSucc) = w := by
    funext j; simp [Fin.snoc_castSucc]
  rw [eval_fromPolynomial q (Fin.snoc w s) (fun i ↦ by rw [hsnocc]; exact hwc i)]
  simp only [Fin.snoc_last, hsnocc]

/-- Evaluation of `fromPolynomial b` along a slice, with the sum taken over any range
containing the degree of `b`. -/
lemma LocalOkaRing.eval_fromPolynomial_snoc_range (b : (LocalOkaRing (Fin n))[X]) (m : ℕ)
    (hbm : b.degree < (m : WithBot ℕ)) (w : Fin n → ℂ)
    (hwc : ∀ j, ((b.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt w)
    (s : ℂ) :
    ((LocalOkaRing.fromPolynomial b : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w s)
      = ∑ j ∈ Finset.range m,
          ((b.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval w * s ^ j := by
  rw [LocalOkaRing.eval_fromPolynomial_snoc b w hwc s]
  by_cases hb0 : b = 0
  · subst hb0
    simp [MvPowerSeries.eval_of_zero]
  · have hnd : b.natDegree < m := (Polynomial.natDegree_lt_iff_degree_lt hb0).mpr hbm
    refine Finset.sum_subset (fun j hj ↦ ?_) (fun j _ hj ↦ ?_)
    · rw [Finset.mem_range] at hj ⊢
      omega
    · rw [Finset.mem_range, not_lt] at hj
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), ZeroMemClass.coe_zero,
        MvPowerSeries.eval_of_zero, zero_mul]

/-- The pointwise algebraic identity behind Weierstrass division. -/
lemma div_sub_div_add_sum_eq {d : ℕ} (F Qz Qt ζ t : ℂ) (E : ℕ → ℂ)
    (hQz : Qz ≠ 0) (hne : ζ - t ≠ 0)
    (hE : Qz - Qt = (ζ - t) * ∑ i ∈ Finset.range d, t ^ i * E i) :
    F / (ζ - t)
      = Qt * (F / (Qz * (ζ - t))) + ∑ i ∈ Finset.range d, t ^ i * (F / Qz * E i) := by
  have hsumeq : (∑ i ∈ Finset.range d, t ^ i * (F / Qz * E i))
      = F / Qz * ∑ i ∈ Finset.range d, t ^ i * E i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ by ring)
  rw [hsumeq]
  field_simp
  linear_combination F * hE

/-- The Weierstrass division integrand identity, pointwise on the circle. -/
lemma localweierstrass_integrand_eqOn
    (q : (LocalOkaRing (Fin n))[X])
    (hq : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q))
    (f : LocalOkaRing (Fin (n + 1)))
    (δ ε : ℝ)
    (hq0 : ∀ z : Fin (n + 1) → ℂ, (∀ i : Fin n, ‖z i.castSucc‖ ≤ δ) → ‖z (Fin.last n)‖ = ε →
      ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).eval z ≠ 0)
    (w : Fin n → ℂ) (hwδ : ∀ i, ‖w i‖ ≤ δ)
    (hwc : ∀ j, ((q.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt w)
    (t : ℂ) (ht : ‖t‖ < ε) :
    Set.EqOn
      (fun ζ : ℂ ↦ (ζ - t)⁻¹ • (f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ))
      (fun ζ : ℂ ↦
        ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
            MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w t) *
          ((f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) /
            (((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
              MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) * (ζ - t)))
        + ∑ i ∈ Finset.range q.natDegree, t ^ i *
            ((f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) /
              ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
                MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) *
              (∑ j ∈ Finset.Icc (i + 1) q.natDegree,
                ζ ^ (j - 1 - i) *
                  ((q.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval w)))
      (Metric.sphere 0 ε) := by
  intro ζ hζ
  have hζn : ‖ζ‖ = ε := mem_sphere_zero_iff_norm.mp hζ
  have hQz : ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
      MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) ≠ 0 := by
    refine hq0 _ (fun i ↦ ?_) ?_
    · simp only [Fin.snoc_castSucc]
      exact hwδ i
    · simpa only [Fin.snoc_last] using hζn
  have hne : ζ - t ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h, hζn] at ht
    exact lt_irrefl _ ht
  have hcd : ((q.coeff q.natDegree : LocalOkaRing (Fin n)) :
      MvPowerSeries (Fin n) ℂ).eval w = 1 := LocalOkaRing.eval_coeff_natDegree q hq w
  have hE := sum_pow_sub_sum_pow_eq q.natDegree
    (fun j ↦ ((q.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval w) hcd ζ t
  rw [← LocalOkaRing.eval_fromPolynomial_snoc q w hwc ζ,
    ← LocalOkaRing.eval_fromPolynomial_snoc q w hwc t] at hE
  simp only [smul_eq_mul, inv_mul_eq_div]
  exact div_sub_div_add_sum_eq _ _ _ ζ t _ hQz hne hE

/-- The Weierstrass division integral identity. -/
lemma localweierstrass_division_lemma_four
    (q : (LocalOkaRing (Fin n))[X])
    (hq : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q))
    (f : LocalOkaRing (Fin (n + 1)))
    (δ : ℝ) (ε : ℝ) (he : ε > 0) (r : ℝ) (hεr : ε < r)
    (hf : (f : MvPowerSeries (Fin (n + 1)) ℂ).SummableAt (fun _ ↦ (r : ℂ)))
    (hq' : ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
      MvPowerSeries (Fin (n + 1)) ℂ).SummableAt (fun _ ↦ (r : ℂ)))
    (hq0 : ∀ z : Fin (n + 1) → ℂ, (∀ i : Fin n, ‖z i.castSucc‖ ≤ δ) → ‖z (Fin.last n)‖ = ε →
      ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).eval z ≠ 0)
    (w : Fin n → ℂ) (hwδ : ∀ i, ‖w i‖ ≤ δ) (hwε : ‖w‖ < ε)
    (hwc : ∀ j, ((q.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt w)
    (t : ℂ) (ht : ‖t‖ < ε) :
    (f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w t)
      = ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∮ ζ in C(0, ε),
              (f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) /
                (((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
                  MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) * (ζ - t)))
          * ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
              MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w t)
        + ∑ i ∈ Finset.range q.natDegree, t ^ i *
            ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
              ∮ ζ in C(0, ε),
                (f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) /
                  ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
                    MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) *
                  (∑ j ∈ Finset.Icc (i + 1) q.natDegree,
                    ζ ^ (j - 1 - i) *
                      ((q.coeff j : LocalOkaRing (Fin n)) :
                        MvPowerSeries (Fin n) ℂ).eval w)) := by
  classical
  have hr0 : (0 : ℝ) < r := lt_trans he hεr
  have hwi : ∀ i, ‖w i‖ ≤ ε := fun i ↦ le_of_lt (lt_of_le_of_lt (norm_le_pi_norm w i) hwε)
  have hzr : ∀ ζ : ℂ, ‖ζ‖ ≤ ε → ‖(Fin.snoc w ζ : Fin (n + 1) → ℂ)‖ < r := fun ζ hζ ↦
    lt_of_le_of_lt (norm_snoc_le hwi hζ) hεr
  have hsn : Differentiable ℂ (fun s : ℂ ↦ (Fin.snoc w s : Fin (n + 1) → ℂ)) :=
    differentiable_snoc_last w
  have hmem : ∀ ζ : ℂ, ζ ∈ Metric.closedBall (0 : ℂ) ε → ‖ζ‖ ≤ ε := by
    intro ζ hζ; rwa [Metric.mem_closedBall, dist_zero_right] at hζ
  have hFd : ∀ ζ : ℂ, ‖ζ‖ ≤ ε → DifferentiableAt ℂ
      (fun s : ℂ ↦ (f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w s)) ζ := by
    intro ζ hζ
    have h := (MvPowerSeries.analyticAt_eval_of_summableAt_const hr0 hf
      (hzr ζ hζ)).differentiableAt.comp ζ (hsn ζ)
    simpa [Function.comp_def] using h
  have hQd : ∀ ζ : ℂ, ‖ζ‖ ≤ ε → DifferentiableAt ℂ
      (fun s : ℂ ↦ ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w s)) ζ := by
    intro ζ hζ
    have h := (MvPowerSeries.analyticAt_eval_of_summableAt_const hr0 hq'
      (hzr ζ hζ)).differentiableAt.comp ζ (hsn ζ)
    simpa [Function.comp_def] using h
  have hFcont : ContinuousOn
      (fun s : ℂ ↦ (f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w s))
      (Metric.closedBall 0 ε) := fun ζ hζ ↦
    (hFd ζ (hmem ζ hζ)).continuousAt.continuousWithinAt
  have hQcont : ContinuousOn
      (fun s : ℂ ↦ ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w s))
      (Metric.closedBall 0 ε) := fun ζ hζ ↦
    (hQd ζ (hmem ζ hζ)).continuousAt.continuousWithinAt
  have hFs := hFcont.mono Metric.sphere_subset_closedBall
  have hQs := hQcont.mono Metric.sphere_subset_closedBall
  have hQzne : ∀ ζ ∈ Metric.sphere (0 : ℂ) ε,
      ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) ≠ 0 := by
    intro ζ hζ
    have hζn : ‖ζ‖ = ε := mem_sphere_zero_iff_norm.mp hζ
    refine hq0 _ (fun i ↦ ?_) ?_
    · simp only [Fin.snoc_castSucc]
      exact hwδ i
    · simpa only [Fin.snoc_last] using hζn
  have htne : ∀ ζ ∈ Metric.sphere (0 : ℂ) ε, ζ - t ≠ 0 := by
    intro ζ hζ h
    have hζn : ‖ζ‖ = ε := mem_sphere_zero_iff_norm.mp hζ
    rw [sub_eq_zero] at h
    rw [← h, hζn] at ht
    exact lt_irrefl _ ht
  have hcauchy : ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(0, ε),
      (ζ - t)⁻¹ • (f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ))
      = (f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w t) := by
    refine Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (s := ∅) Set.countable_empty ?_ hFcont ?_
    · rwa [Metric.mem_ball, dist_zero_right]
    · intro x hx
      refine hFd x (le_of_lt ?_)
      have hx1 := hx.1
      rwa [Metric.mem_ball, dist_zero_right] at hx1
  have hint1 : CircleIntegrable (fun ζ : ℂ ↦
      ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
          MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w t) *
        ((f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) /
          (((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
            MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) * (ζ - t)))) 0 ε := by
    refine ContinuousOn.circleIntegrable he.le ?_
    refine continuousOn_const.mul (hFs.div (hQs.mul ?_) ?_)
    · exact (continuous_id.sub continuous_const).continuousOn
    · intro ζ hζ
      exact mul_ne_zero (hQzne ζ hζ) (htne ζ hζ)
  have hint2 : ∀ i ∈ Finset.range q.natDegree, CircleIntegrable (fun ζ : ℂ ↦
      t ^ i * ((f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) /
        ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
          MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) *
        (∑ j ∈ Finset.Icc (i + 1) q.natDegree,
          ζ ^ (j - 1 - i) *
            ((q.coeff j : LocalOkaRing (Fin n)) :
              MvPowerSeries (Fin n) ℂ).eval w))) 0 ε := by
    intro i _
    have hEc : Continuous (fun ζ : ℂ ↦ ∑ j ∈ Finset.Icc (i + 1) q.natDegree,
        ζ ^ (j - 1 - i) *
          ((q.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval w) := by
      apply continuous_finsetSum
      intro j _
      fun_prop
    refine ContinuousOn.circleIntegrable he.le ?_
    exact continuousOn_const.mul ((hFs.div hQs hQzne).mul hEc.continuousOn)
  rw [← hcauchy, circleIntegral.integral_congr he.le
      (localweierstrass_integrand_eqOn q hq f δ ε hq0 w hwδ hwc t ht),
    circleIntegral.integral_add hint1 (CircleIntegrable.fun_sum _ hint2),
    circleIntegral.integral_fun_sum hint2, smul_eq_mul, mul_add]
  congr 1
  · rw [circleIntegral.integral_const_mul]
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [circleIntegral.integral_const_mul]
    ring

lemma localweierstrass_division_lemma_one
      (q : (LocalOkaRing (Fin n))[X])
      (hq : IsLocalWeierstrassPolynomial (Polynomial.map (localOkaSubring _).val.toRingHom q))
      (f : LocalOkaRing (Fin (n + 1))) :
      ∃ (δ : ℝ) (_ : δ > 0) (ε : ℝ) (_ : ε > 0) (r : ℝ) (_ : ε < r),
        (f : MvPowerSeries (Fin (n + 1)) ℂ).SummableAt (fun _ ↦ (r : ℂ)) ∧
        ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
          MvPowerSeries (Fin (n + 1)) ℂ).SummableAt (fun _ ↦ (r : ℂ)) ∧
        ∀ z : Fin (n + 1) → ℂ, (∀ i : Fin n, ‖z i.castSucc‖ ≤ δ) → ‖z (Fin.last n)‖ = ε →
          ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
            MvPowerSeries (Fin (n + 1)) ℂ).eval z ≠ 0 := by
  obtain ⟨ρ₁, hρ₁, hsum₁⟩ := f.locallyConvergent.exists_summableAt_const
  obtain ⟨ρ₂, hρ₂, hsum₂⟩ :=
    (LocalOkaRing.fromPolynomial q :
      LocalOkaRing (Fin (n + 1))).locallyConvergent.exists_summableAt_const
  set r : ℝ := min ρ₁ ρ₂ with hrdef
  have hr : 0 < r := lt_min hρ₁ hρ₂
  have hfr : (f : MvPowerSeries (Fin (n + 1)) ℂ).SummableAt (fun _ ↦ (r : ℂ)) := by
    refine hsum₁.mono (fun i ↦ ?_)
    simp only [Complex.norm_real, Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hρ₁.le]
    exact min_le_left _ _
  have hqr : ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
      MvPowerSeries (Fin (n + 1)) ℂ).SummableAt (fun _ ↦ (r : ℂ)) := by
    refine hsum₂.mono (fun i ↦ ?_)
    simp only [Complex.norm_real, Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hρ₂.le]
    exact min_le_right _ _
  have hε : (0 : ℝ) < r / 2 := by linarith
  have hne := LocalOkaRing.eventually_fromPolynomial_ne_zero q hq hε
  rw [Metric.eventually_nhds_iff] at hne
  obtain ⟨δ₀, hδ₀, hprop⟩ := hne
  refine ⟨δ₀ / 2, by linarith, r / 2, hε, r, by linarith, hfr, hqr, ?_⟩
  intro z hz₁ hz₂
  have hzeq : (Fin.snoc (fun i : Fin n ↦ z i.castSucc) (z (Fin.last n)) :
      Fin (n + 1) → ℂ) = z := by
    funext k
    induction k using Fin.lastCases with
    | last => simp
    | cast j => simp
  have hz'dist : dist (fun i : Fin n ↦ z i.castSucc) (0 : Fin n → ℂ) < δ₀ := by
    rw [dist_pi_lt_iff hδ₀]
    intro i
    simp only [Pi.zero_apply, dist_zero_right]
    have h2 : ‖z i.castSucc‖ ≤ δ₀ / 2 := hz₁ i
    linarith
  have hprop2 := hprop hz'dist (z (Fin.last n)) hz₂
  rwa [hzeq] at hprop2

lemma localweierstrass_division_lemma_two
    (q : (LocalOkaRing (Fin n))[X])
    (_hq : IsLocalWeierstrassPolynomial (Polynomial.map (localOkaSubring _).val.toRingHom q))
    (f : LocalOkaRing (Fin (n + 1)))
    (δ : ℝ) (hd : δ > 0) (ε : ℝ) (he : ε > 0)
    (r : ℝ) (hεr : ε < r)
    (hf : (f : MvPowerSeries (Fin (n + 1)) ℂ).SummableAt (fun _ ↦ (r : ℂ)))
    (hq' : ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).SummableAt (fun _ ↦ (r : ℂ)))
    (hq0 : ∀ z : Fin (n+1) → ℂ, (∀ i : Fin n, ‖z i.castSucc‖ ≤ δ) → ‖z (Fin.last n)‖ = ε →
      ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) :
        MvPowerSeries (Fin (n+1)) ℂ).eval z ≠ 0) :
      ∃ a : LocalOkaRing (Fin (n+1)),
       (a : MvPowerSeries (Fin (n+1)) ℂ).Represents (fun x =>
            (2 * Real.pi * Complex.I : ℂ)⁻¹ *
              ∮ ζ in C(0, ε),
                (f : MvPowerSeries (Fin (n+1)) ℂ).eval (Fin.snoc (Fin.init x) ζ) /
                  (((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) :
                      MvPowerSeries (Fin (n+1)) ℂ).eval (Fin.snoc (Fin.init x) ζ)
                    * (ζ - x (Fin.last n)))) := by
  have hF : AnalyticAt ℂ (fun (x : Fin (n+1) → ℂ) =>
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ ζ in C(0, ε),
          (f : MvPowerSeries (Fin (n+1)) ℂ).eval (Fin.snoc (Fin.init x) ζ) /
            (((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) :
                MvPowerSeries (Fin (n+1)) ℂ).eval (Fin.snoc (Fin.init x) ζ)
              * (ζ - x (Fin.last n)))) 0 := by
    have hr0 : (0 : ℝ) < r := lt_trans he hεr
    set ρ : ℝ := min δ (ε / 2) with hρdef
    have hρ : 0 < ρ := lt_min hd (by linarith)
    have hρδ : ρ ≤ δ := min_le_left _ _
    have hρε : ρ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hcirc : ∀ θ : ℝ, ‖circleMap 0 ε θ‖ = ε := by
      intro θ; simp [norm_circleMap_zero, abs_of_pos he]
    have hdiff : ∀ ζ : ℂ, ‖ζ‖ = ε →
        DifferentiableOn ℂ (fun x : Fin (n+1) → ℂ ↦
          (f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc (Fin.init x) ζ) /
            (((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) :
                MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc (Fin.init x) ζ)
              * (ζ - x (Fin.last n))))
          (Set.univ.pi fun _ : Fin (n+1) ↦ Metric.closedBall (0 : ℂ) ρ) := by
      intro ζ hζ x hx
      have hxi : ∀ i : Fin (n + 1), ‖x i‖ ≤ ρ := by
        intro i
        have h := hx i (Set.mem_univ i)
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      have hz : ‖(Fin.snoc (Fin.init x) ζ : Fin (n+1) → ℂ)‖ < r := by
        refine lt_of_le_of_lt (norm_snocInit_le (fun i ↦ ?_) (le_of_eq hζ)) hεr
        exact le_trans (hxi i.castSucc) hρε.le
      have hsn : DifferentiableAt ℂ
          (fun y : Fin (n+1) → ℂ ↦ (Fin.snoc (Fin.init y) ζ : Fin (n+1) → ℂ)) x :=
        (differentiable_snocInit ζ) x
      have hnum : DifferentiableAt ℂ
          (fun y : Fin (n+1) → ℂ ↦ (f : MvPowerSeries (Fin (n+1)) ℂ).eval
            (Fin.snoc (Fin.init y) ζ)) x := by
        have h := (MvPowerSeries.analyticAt_eval_of_summableAt_const hr0 hf
          hz).differentiableAt.comp x hsn
        simpa [Function.comp_def] using h
      have hden1 : DifferentiableAt ℂ
          (fun y : Fin (n+1) → ℂ ↦ ((LocalOkaRing.fromPolynomial q :
              LocalOkaRing (Fin (n+1))) : MvPowerSeries (Fin (n+1)) ℂ).eval
            (Fin.snoc (Fin.init y) ζ)) x := by
        have h := (MvPowerSeries.analyticAt_eval_of_summableAt_const hr0 hq'
          hz).differentiableAt.comp x hsn
        simpa [Function.comp_def] using h
      have hden2 : DifferentiableAt ℂ
          (fun y : Fin (n+1) → ℂ ↦ ζ - y (Fin.last n)) x :=
        ((differentiable_const ζ).sub (differentiable_apply (𝕜 := ℂ) (Fin.last n))) x
      have hq0' : ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) :
          MvPowerSeries (Fin (n+1)) ℂ).eval (Fin.snoc (Fin.init x) ζ) ≠ 0 := by
        refine hq0 _ (fun i ↦ ?_) ?_
        · simp only [Fin.snoc_castSucc, Fin.init_def]
          exact le_trans (hxi i.castSucc) hρδ
        · simpa only [Fin.snoc_last] using hζ
      have hζx : ζ - x (Fin.last n) ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        have h2 : ‖x (Fin.last n)‖ ≤ ρ := hxi _
        rw [← h, hζ] at h2
        linarith
      have hden : DifferentiableAt ℂ
          (fun y : Fin (n+1) → ℂ ↦ ((LocalOkaRing.fromPolynomial q :
              LocalOkaRing (Fin (n+1))) : MvPowerSeries (Fin (n+1)) ℂ).eval
            (Fin.snoc (Fin.init y) ζ) * (ζ - y (Fin.last n))) x := hden1.mul hden2
      have hdeninv : DifferentiableAt ℂ
          (fun y : Fin (n+1) → ℂ ↦ (((LocalOkaRing.fromPolynomial q :
              LocalOkaRing (Fin (n+1))) : MvPowerSeries (Fin (n+1)) ℂ).eval
            (Fin.snoc (Fin.init y) ζ) * (ζ - y (Fin.last n)))⁻¹) x :=
        hden.inv (mul_ne_zero hq0' hζx)
      have hres : DifferentiableAt ℂ
          (fun y : Fin (n+1) → ℂ ↦ (f : MvPowerSeries (Fin (n+1)) ℂ).eval
              (Fin.snoc (Fin.init y) ζ) /
            (((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) :
                MvPowerSeries (Fin (n+1)) ℂ).eval (Fin.snoc (Fin.init y) ζ)
              * (ζ - y (Fin.last n)))) x := by
        simp_rw [div_eq_mul_inv]
        exact hnum.mul hdeninv
      exact hres.differentiableWithinAt
    have hcont : Continuous fun p :
        (Set.univ.pi fun _ : Fin (n+1) ↦ Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
          (f : MvPowerSeries (Fin (n+1)) ℂ).eval
              (Fin.snoc (Fin.init (p.1 : Fin (n+1) → ℂ)) (circleMap 0 ε p.2)) /
            (((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) :
                MvPowerSeries (Fin (n+1)) ℂ).eval
                (Fin.snoc (Fin.init (p.1 : Fin (n+1) → ℂ)) (circleMap 0 ε p.2))
              * (circleMap 0 ε p.2 - (p.1 : Fin (n+1) → ℂ) (Fin.last n))) := by
      have hΦ := continuous_snocInit_circleMap (m := n) ε
        (Set.univ.pi fun _ : Fin (n+1) ↦ Metric.closedBall (0 : ℂ) ρ)
      have hznorm : ∀ p : (Set.univ.pi fun _ : Fin (n+1) ↦
          Metric.closedBall (0 : ℂ) ρ) × ℝ,
          ‖(Fin.snoc (Fin.init (p.1 : Fin (n+1) → ℂ)) (circleMap 0 ε p.2) :
            Fin (n+1) → ℂ)‖ < r := by
        intro p
        refine lt_of_le_of_lt (norm_snocInit_le (fun i ↦ ?_) (le_of_eq (hcirc p.2))) hεr
        have h := p.1.2 i.castSucc (Set.mem_univ _)
        rw [Metric.mem_closedBall, dist_zero_right] at h
        exact le_trans h hρε.le
      have hnumc : Continuous fun p : (Set.univ.pi fun _ : Fin (n+1) ↦
          Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
          (f : MvPowerSeries (Fin (n+1)) ℂ).eval
            (Fin.snoc (Fin.init (p.1 : Fin (n+1) → ℂ)) (circleMap 0 ε p.2)) := by
        rw [continuous_iff_continuousAt]
        intro p
        have h : ContinuousAt ((f : MvPowerSeries (Fin (n+1)) ℂ).eval ∘
            fun p' : (Set.univ.pi fun _ : Fin (n+1) ↦ Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
              (Fin.snoc (Fin.init (p'.1 : Fin (n+1) → ℂ)) (circleMap 0 ε p'.2) :
                Fin (n+1) → ℂ)) p :=
          ContinuousAt.comp (MvPowerSeries.analyticAt_eval_of_summableAt_const hr0 hf
            (hznorm p)).continuousAt hΦ.continuousAt
        simpa [Function.comp_def] using h
      have hqc : Continuous fun p : (Set.univ.pi fun _ : Fin (n+1) ↦
          Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
          ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n+1))) :
              MvPowerSeries (Fin (n+1)) ℂ).eval
            (Fin.snoc (Fin.init (p.1 : Fin (n+1) → ℂ)) (circleMap 0 ε p.2)) := by
        rw [continuous_iff_continuousAt]
        intro p
        have h : ContinuousAt (((LocalOkaRing.fromPolynomial q :
              LocalOkaRing (Fin (n+1))) : MvPowerSeries (Fin (n+1)) ℂ).eval ∘
            fun p' : (Set.univ.pi fun _ : Fin (n+1) ↦ Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
              (Fin.snoc (Fin.init (p'.1 : Fin (n+1) → ℂ)) (circleMap 0 ε p'.2) :
                Fin (n+1) → ℂ)) p :=
          ContinuousAt.comp (MvPowerSeries.analyticAt_eval_of_summableAt_const hr0 hq'
            (hznorm p)).continuousAt hΦ.continuousAt
        simpa [Function.comp_def] using h
      have hdenc : Continuous fun p : (Set.univ.pi fun _ : Fin (n+1) ↦
          Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
          circleMap 0 ε p.2 - (p.1 : Fin (n+1) → ℂ) (Fin.last n) := by
        refine Continuous.sub ?_ ?_
        · unfold circleMap; fun_prop
        · exact (continuous_apply (Fin.last n)).comp
            (continuous_subtype_val.comp continuous_fst)
      refine hnumc.div (hqc.mul hdenc) (fun p ↦ mul_ne_zero ?_ ?_)
      · refine hq0 _ (fun i ↦ ?_) ?_
        · simp only [Fin.snoc_castSucc, Fin.init_def]
          have h := p.1.2 i.castSucc (Set.mem_univ _)
          rw [Metric.mem_closedBall, dist_zero_right] at h
          exact le_trans h hρδ
        · simpa only [Fin.snoc_last] using hcirc p.2
      · intro h
        rw [sub_eq_zero] at h
        have h2 := p.1.2 (Fin.last n) (Set.mem_univ _)
        rw [Metric.mem_closedBall, dist_zero_right, ← h, hcirc] at h2
        linarith
    exact analyticAt_const.mul (analyticAt_circleIntegral he hρ hdiff hcont)
  obtain ⟨P, hconv, hrep⟩ := MvPowerSeries.exists_represents hF
  exact ⟨⟨P, hconv⟩, hrep⟩

lemma localweierstrass_division_lemma_three
    (q : (LocalOkaRing (Fin n))[X])
    (f : LocalOkaRing (Fin (n + 1)))
    (δ : ℝ) (hd : δ > 0) (ε : ℝ) (he : ε > 0) (r : ℝ) (hεr : ε < r)
    (hf : (f : MvPowerSeries (Fin (n + 1)) ℂ).SummableAt (fun _ ↦ (r : ℂ)))
    (hq' : ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
      MvPowerSeries (Fin (n + 1)) ℂ).SummableAt (fun _ ↦ (r : ℂ)))
    (hq0 : ∀ z : Fin (n + 1) → ℂ, (∀ i : Fin n, ‖z i.castSucc‖ ≤ δ) → ‖z (Fin.last n)‖ = ε →
      ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).eval z ≠ 0)
    (i : ℕ) :
    AnalyticAt ℂ (fun w : Fin n → ℂ ↦
      ∮ ζ in C(0, ε),
        (f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) /
          ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
            MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) *
          (∑ j ∈ Finset.Icc (i + 1) q.natDegree,
            ζ ^ (j - 1 - i) *
              ((q.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).eval w)) 0 := by
  have hr0 : (0 : ℝ) < r := lt_trans he hεr
  obtain ⟨σ, hσ, hcsum⟩ : ∃ σ : ℝ, 0 < σ ∧ ∀ j ∈ Finset.range (q.natDegree + 1),
      ((q.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt
        (fun _ ↦ (σ : ℂ)) := by
    have hc := LocalOkaRing.eventually_summableAt_coeffs q
    rw [Metric.eventually_nhds_iff] at hc
    obtain ⟨σ₀, hσ₀, hprop⟩ := hc
    refine ⟨σ₀ / 2, by linarith, hprop ?_⟩
    rw [dist_pi_lt_iff hσ₀]
    intro k
    simp only [Pi.zero_apply, dist_zero_right, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ σ₀ / 2)]
    linarith
  set ρ : ℝ := min δ (min (ε / 2) (σ / 2)) with hρdef
  have hρ : 0 < ρ := lt_min hd (lt_min (by linarith) (by linarith))
  have hρδ : ρ ≤ δ := min_le_left _ _
  have hρε : ρ < ε :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
  have hρσ : ρ < σ :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
  have hcoeff : ∀ j ∈ Finset.Icc (i + 1) q.natDegree, ∀ w : Fin n → ℂ, ‖w‖ < σ →
      AnalyticAt ℂ ((q.coeff j : LocalOkaRing (Fin n)) :
        MvPowerSeries (Fin n) ℂ).eval w := by
    intro j hj w hw
    refine MvPowerSeries.analyticAt_eval_of_summableAt_const hσ (hcsum j ?_) hw
    rw [Finset.mem_range]
    have h := (Finset.mem_Icc.mp hj).2
    omega
  refine analyticAt_circleIntegral_snoc he hρ hρε hεr
    (fun z hz ↦ MvPowerSeries.analyticAt_eval_of_summableAt_const hr0 hf hz)
    (fun z hz ↦ MvPowerSeries.analyticAt_eval_of_summableAt_const hr0 hq' hz) ?_ ?_ ?_
  · intro w hw ζ hζ
    refine hq0 _ (fun k ↦ ?_) ?_
    · simp only [Fin.snoc_castSucc]
      exact le_trans (hw k) hρδ
    · simpa only [Fin.snoc_last] using hζ
  · intro ζ hζ w hw
    have hwi : ∀ k, ‖w k‖ ≤ ρ := by
      intro k
      have h := hw k (Set.mem_univ k)
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hwn : ‖w‖ < σ :=
      lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hρ.le).mpr hwi) hρσ
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.fun_sum (fun j hj ↦ ?_)
    exact ((hcoeff j hj w hwn).differentiableAt).const_mul _
  · apply continuous_finsetSum
    intro j hj
    refine Continuous.mul ?_ ?_
    · unfold circleMap; fun_prop
    · rw [continuous_iff_continuousAt]
      intro p
      have hwn : ‖(p.1 : Fin n → ℂ)‖ < σ := by
        refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hρ.le).mpr (fun k ↦ ?_)) hρσ
        have h := p.1.2 k (Set.mem_univ _)
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      have h2 : ContinuousAt (((q.coeff j : LocalOkaRing (Fin n)) :
          MvPowerSeries (Fin n) ℂ).eval ∘
          fun p' : (Set.univ.pi fun _ : Fin n ↦ Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
            (p'.1 : Fin n → ℂ)) p :=
        ContinuousAt.comp (hcoeff j hj _ hwn).continuousAt
          (continuous_subtype_val.comp continuous_fst).continuousAt
      simpa [Function.comp_def] using h2

/-! ### Represents and eval helpers -/

namespace MvPowerSeries

variable {ι : Type*}

/-- The sum of a power series representing `F` agrees with `F` near the origin. -/
lemma Represents.eval_eq {P : MvPowerSeries ι ℂ} {F : (ι → ℂ) → ℂ} (hP : P.Represents F) :
    ∀ᶠ x in nhds (0 : ι → ℂ), P.eval x = F x := by
  filter_upwards [hP] with x hx
  rw [eval]
  exact hx.tsum_eq

/-- The value at the origin of a function represented by `P` is the constant term of `P`. -/
lemma Represents.apply_zero {P : MvPowerSeries ι ℂ} {F : (ι → ℂ) → ℂ} (hP : P.Represents F) :
    F 0 = constantCoeff P := by
  rw [← eval_zero P, hP.eval_eq.self_of_nhds]

variable [Fintype ι] [DecidableEq ι]

/-- The sum of a locally convergent power series has the associated formal multilinear series
as a power series expansion at the origin. -/
lemma LocallyConvergent.hasFPowerSeriesAt_eval {P : MvPowerSeries ι ℂ}
    (hP : P.LocallyConvergent) : HasFPowerSeriesAt P.eval (toFPS P) 0 := by
  obtain ⟨ρ, hρ, h⟩ := hP.hasFPowerSeriesOnBall
  exact h.hasFPowerSeriesAt

/-- The partial derivatives at the origin of the sum of a locally convergent power series are
the linear coefficients of the series. -/
lemma LocallyConvergent.fderiv_eval_zero {ι : Type*} [Finite ι] [DecidableEq ι]
    {P : MvPowerSeries ι ℂ} (hP : P.LocallyConvergent) (j : ι) :
    fderiv ℂ P.eval 0 (Pi.single j 1) = coeff (Finsupp.single j 1) P := by
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [hP.hasFPowerSeriesAt_eval.fderiv_eq]
  have h1 : (continuousMultilinearCurryFin1 ℂ (ι → ℂ) ℂ) (toFPS P 1) (Pi.single j 1) =
      toFPS P 1 (fun _ ↦ Pi.single j 1) := rfl
  rw [h1, toFPS_apply_diag]
  have hmem : Finsupp.single j 1 ∈ degFinset ι 1 :=
    mem_degFinset.mpr (by simp [Finsupp.single_apply])
  rw [Finset.sum_eq_single (Finsupp.single j 1)]
  · rw [term]
    have hone : evalMonomial (Finsupp.single j 1) (Pi.single j (1 : ℂ)) = 1 := by
      rw [evalMonomial_eq_prod]
      refine Finset.prod_eq_one fun i _ ↦ ?_
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [Ne.symm hij]
    rw [hone, mul_one]
  · intro e he hne
    rw [term]
    have hzero : evalMonomial e (Pi.single j (1 : ℂ)) = 0 := by
      have hsum : ∑ i, e i = 1 := mem_degFinset.mp he
      have hex : ∃ i, i ≠ j ∧ e i ≠ 0 := by
        by_contra hc
        push Not at hc
        refine hne (Finsupp.ext fun i ↦ ?_)
        rcases eq_or_ne i j with rfl | hij
        · have h2 : ∑ i, e i = e i := Finset.sum_eq_single i
            (fun b _ hb ↦ hc b hb) (fun h ↦ absurd (Finset.mem_univ i) h)
          rw [Finsupp.single_eq_same, ← hsum, h2]
        · rw [hc i hij]
          simp [Ne.symm hij]
      obtain ⟨i, hij, hei⟩ := hex
      rw [evalMonomial_eq_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [Pi.single_eq_of_ne hij, zero_pow hei]
    rw [hzero, mul_zero]
  · intro h
    exact absurd hmem h

end MvPowerSeries

/-! ### Monic polynomials with prescribed lower coefficients -/

section WeierstrassOfCoeffs

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The monic polynomial `X ^ d + ∑ j < d, c j * X ^ j` with prescribed lower coefficients. -/
noncomputable def weierstrassOfCoeffs {d : ℕ} (c : Fin d → R) : R[X] :=
  Polynomial.X ^ d + ∑ j : Fin d, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)

lemma degree_sum_C_mul_X_pow_lt {d : ℕ} (c : Fin d → R) :
    (∑ j : Fin d, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)).degree < (d : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe d)]
  intro j _
  exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (by exact_mod_cast j.isLt)

lemma coeff_sum_C_mul_X_pow_of_lt {d : ℕ} (c : Fin d → R) {k : ℕ} (hk : k < d) :
    (∑ j : Fin d, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)).coeff k = c ⟨k, hk⟩ := by
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (⟨k, hk⟩ : Fin d)]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h ↦ hj (Fin.ext h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma weierstrassOfCoeffs_monic {d : ℕ} (c : Fin d → R) :
    (weierstrassOfCoeffs c).Monic :=
  Polynomial.monic_X_pow_add (degree_sum_C_mul_X_pow_lt c)

lemma weierstrassOfCoeffs_coeff_of_lt {d : ℕ} (c : Fin d → R) {k : ℕ} (hk : k < d) :
    (weierstrassOfCoeffs c).coeff k = c ⟨k, hk⟩ := by
  rw [weierstrassOfCoeffs, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    if_neg (Nat.ne_of_lt hk), zero_add, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin d)]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h ↦ hj (Fin.ext h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma weierstrassOfCoeffs_coeff_self {d : ℕ} (c : Fin d → R) :
    (weierstrassOfCoeffs c).coeff d = 1 := by
  rw [weierstrassOfCoeffs, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl,
    Polynomial.finsetSum_coeff, Finset.sum_eq_zero, add_zero]
  intro j _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    if_neg (fun h ↦ absurd h.symm (Nat.ne_of_lt j.isLt)), mul_zero]

lemma weierstrassOfCoeffs_coeff_of_gt {d : ℕ} (c : Fin d → R) {k : ℕ} (hk : d < k) :
    (weierstrassOfCoeffs c).coeff k = 0 := by
  rw [weierstrassOfCoeffs, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    if_neg (by omega), zero_add, Polynomial.finsetSum_coeff, Finset.sum_eq_zero]
  intro j _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    if_neg (by have := j.isLt; omega), mul_zero]

lemma weierstrassOfCoeffs_degree [Nontrivial R] {d : ℕ} (c : Fin d → R) :
    (weierstrassOfCoeffs c).degree = d := by
  rw [weierstrassOfCoeffs, Polynomial.degree_add_eq_left_of_degree_lt
    (by rw [Polynomial.degree_X_pow]; exact degree_sum_C_mul_X_pow_lt c),
    Polynomial.degree_X_pow]

lemma weierstrassOfCoeffs_natDegree [Nontrivial R] {d : ℕ} (c : Fin d → R) :
    (weierstrassOfCoeffs c).natDegree = d :=
  Polynomial.natDegree_eq_of_degree_eq_some (weierstrassOfCoeffs_degree c)

lemma weierstrassOfCoeffs_map {d : ℕ} (c : Fin d → R) (φ : R →+* S) :
    (weierstrassOfCoeffs c).map φ = weierstrassOfCoeffs (fun j ↦ φ (c j)) := by
  rw [weierstrassOfCoeffs, weierstrassOfCoeffs, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]

end WeierstrassOfCoeffs

/-- The Weierstrass division theorem for germs; uniqueness is omitted. -/
theorem localweierstrass_division
      (q : (LocalOkaRing (Fin n))[X])
      (hq : IsLocalWeierstrassPolynomial
           (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) q))
      (f : LocalOkaRing (Fin (n + 1))) :
      ∃ (a : LocalOkaRing (Fin (n + 1)))
        (b : (LocalOkaRing (Fin (n)))[X]) (_ : b.degree < q.degree),
      f = a * (LocalOkaRing.fromPolynomial q) + (LocalOkaRing.fromPolynomial b) := by
  classical
  have hqm : IsLocalWeierstrassPolynomial
      (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q) := hq
  -- `q` is monic, hence of degree `q.natDegree`
  have hinj : Function.Injective (localOkaSubring (Fin n)).val.toRingHom :=
    Subtype.val_injective
  have hqmonic : q.Monic := by
    have h1 : (Polynomial.map (localOkaSubring (Fin n)).val.toRingHom q).coeff q.natDegree
        = 1 := by
      rw [← natDegree_map_eq_of_injective hinj q]
      exact hqm.monic.coeff_natDegree
    have h2 : q.coeff q.natDegree = 1 := by
      apply hinj
      rw [map_one, ← Polynomial.coeff_map]
      exact h1
    exact h2
  have hqne : q ≠ 0 := hqmonic.ne_zero
  have hqdeg : q.degree = (q.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hqne
  -- radii, summability and nonvanishing on the distinguished torus
  obtain ⟨δ, hδ, ε, hε, r, hεr, hfr, hqr, hq0⟩ :=
    localweierstrass_division_lemma_one q hqm f
  -- the quotient
  obtain ⟨a, hares⟩ :=
    localweierstrass_division_lemma_two q hqm f δ hδ ε hε r hεr hfr hqr hq0
  -- the coefficients of the remainder, as power series
  have hBan : ∀ i : ℕ, AnalyticAt ℂ (fun w : Fin n → ℂ ↦
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ ζ in C(0, ε),
          (f : MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) /
            ((LocalOkaRing.fromPolynomial q : LocalOkaRing (Fin (n + 1))) :
              MvPowerSeries (Fin (n + 1)) ℂ).eval (Fin.snoc w ζ) *
            (∑ j ∈ Finset.Icc (i + 1) q.natDegree,
              ζ ^ (j - 1 - i) *
                ((q.coeff j : LocalOkaRing (Fin n)) :
                  MvPowerSeries (Fin n) ℂ).eval w)) 0 := fun i ↦
    analyticAt_const.mul
      (localweierstrass_division_lemma_three q f δ hδ ε hε r hεr hfr hqr hq0 i)
  choose Bc hBcconv hBcrep using fun i : ℕ ↦ MvPowerSeries.exists_represents (hBan i)
  obtain ⟨bc, hbc⟩ : ∃ bc : Fin q.natDegree → LocalOkaRing (Fin n),
      ∀ j : Fin q.natDegree,
        ((bc j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ) = Bc (j : ℕ) :=
    ⟨fun j ↦ ⟨Bc (j : ℕ), hBcconv (j : ℕ)⟩, fun _ ↦ rfl⟩
  set b : (LocalOkaRing (Fin n))[X] :=
    ∑ j : Fin q.natDegree, Polynomial.C (bc j) * Polynomial.X ^ (j : ℕ) with hbdef
  have hbdeg : b.degree < (q.natDegree : WithBot ℕ) := by
    rw [hbdef]
    exact degree_sum_C_mul_X_pow_lt bc
  have hbcoeff : ∀ i : ℕ, i < q.natDegree →
      ((b.coeff i : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ) = Bc i := by
    intro i hi
    rw [hbdef, coeff_sum_C_mul_X_pow_of_lt bc hi]
    exact hbc ⟨i, hi⟩
  refine ⟨a, b, by rw [hqdeg]; exact hbdeg, ?_⟩
  -- eventual facts near the origin of `ℂ ^ n`, pulled back along `Fin.init`
  have hcontinit : Continuous (Fin.init : (Fin (n + 1) → ℂ) → (Fin n → ℂ)) :=
    continuous_pi fun i ↦ continuous_apply i.castSucc
  have hinit0 : Filter.Tendsto (Fin.init : (Fin (n + 1) → ℂ) → (Fin n → ℂ))
      (nhds 0) (nhds 0) := hcontinit.tendsto' 0 0 rfl
  have hcq : ∀ᶠ w : Fin n → ℂ in nhds 0, ∀ j : ℕ,
      ((q.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt w := by
    filter_upwards [LocalOkaRing.eventually_summableAt_coeffs q] with w hw j
    by_cases hj : j < q.natDegree + 1
    · exact hw j (Finset.mem_range.mpr hj)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), ZeroMemClass.coe_zero]
      exact MvPowerSeries.summableAt_zero w
  have hcb : ∀ᶠ w : Fin n → ℂ in nhds 0, ∀ j : ℕ,
      ((b.coeff j : LocalOkaRing (Fin n)) : MvPowerSeries (Fin n) ℂ).SummableAt w := by
    filter_upwards [LocalOkaRing.eventually_summableAt_coeffs b] with w hw j
    by_cases hj : j < b.natDegree + 1
    · exact hw j (Finset.mem_range.mpr hj)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), ZeroMemClass.coe_zero]
      exact MvPowerSeries.summableAt_zero w
  have hBev := (Filter.eventually_all_finset (Finset.range q.natDegree)).mpr
    (fun i (_ : i ∈ Finset.range q.natDegree) ↦ (hBcrep i).eval_eq)
  have hcqx := hinit0.eventually hcq
  have hcbx := hinit0.eventually hcb
  have hBevx := hinit0.eventually hBev
  have hball : ∀ᶠ x : Fin (n + 1) → ℂ in nhds 0, ‖x‖ < min δ ε :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using lt_min hδ hε)
  -- conclusion via uniqueness of representing power series
  refine LocalOkaRing.ext ?_
  refine MvPowerSeries.Represents.unique f.locallyConvergent.represents_eval ?_
  refine ((a * LocalOkaRing.fromPolynomial q +
    LocalOkaRing.fromPolynomial b).locallyConvergent.represents_eval).congr ?_
  filter_upwards [a.locallyConvergent, (LocalOkaRing.fromPolynomial q).locallyConvergent,
    (LocalOkaRing.fromPolynomial b).locallyConvergent, hares.eval_eq, hcqx, hcbx, hBevx, hball]
    with x hxa hxq hxb hxA hxcq hxcb hxB hxn
  have hxδ : ‖x‖ < δ := lt_of_lt_of_le hxn (min_le_left _ _)
  have hxε : ‖x‖ < ε := lt_of_lt_of_le hxn (min_le_right _ _)
  have hwδ : ∀ i : Fin n, ‖(Fin.init x : Fin n → ℂ) i‖ ≤ δ := by
    intro i
    have h1 : ‖x i.castSucc‖ ≤ ‖x‖ := norm_le_pi_norm x i.castSucc
    simp only [Fin.init_def]
    linarith
  have hwε : ‖(Fin.init x : Fin n → ℂ)‖ < ε := by
    refine lt_of_le_of_lt ?_ hxε
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i ↦ ?_
    simp only [Fin.init_def]
    exact norm_le_pi_norm x i.castSucc
  have ht : ‖x (Fin.last n)‖ < ε :=
    lt_of_le_of_lt (norm_le_pi_norm x (Fin.last n)) hxε
  have hsnoc : (Fin.snoc (Fin.init x) (x (Fin.last n)) : Fin (n + 1) → ℂ) = x :=
    Fin.snoc_init_self x
  have h4 := localweierstrass_division_lemma_four q hqm f δ ε hε r hεr hfr hqr hq0
    (Fin.init x) hwδ hwε hxcq (x (Fin.last n)) ht
  rw [hsnoc] at h4
  have hBb := LocalOkaRing.eval_fromPolynomial_snoc_range b q.natDegree hbdeg
    (Fin.init x) hxcb (x (Fin.last n))
  rw [hsnoc] at hBb
  rw [AddMemClass.coe_add, MulMemClass.coe_mul,
    MvPowerSeries.eval_add_of_summableAt (hxa.mul hxq) hxb,
    MvPowerSeries.eval_mul_of_summableAt hxa hxq, hxA, hBb, h4, add_right_inj]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rw [hbcoeff i hi, hxB i (Finset.mem_range.mpr hi)]
  ring

/-! ### An analytic implicit function theorem -/

section ImplicitFunction

open ContinuousLinearMap

/-- The equivalence between `Fin d` and the last `d` coordinates of `Fin (n + d)`. -/
def finNatAddEquiv (n d : ℕ) : Fin d ≃ {i : Fin (n + d) // ¬ ((i : ℕ) < n)} where
  toFun j := ⟨Fin.natAdd n j, by simp⟩
  invFun i := ⟨((i : Fin (n + d)) : ℕ) - n, by
    have h1 := (i : Fin (n + d)).isLt
    have h2 := i.2
    omega⟩
  left_inv j := by
    ext
    simp
  right_inv i := by
    have h2 := i.2
    ext
    simp
    omega

/-- The analytic implicit function theorem, in the form needed for the Weierstrass
preparation theorem: if `Φ : ℂ^{n+d} → ℂ^d` is analytic at the origin, vanishes there, and
its Jacobian with respect to the last `d` coordinates is invertible, then near the origin
the zero locus of `Φ` contains the graph of an analytic function `s` of the first `n`
coordinates vanishing at the origin. -/
theorem exists_analyticAt_implicit {n d : ℕ} (Φ : (Fin (n + d) → ℂ) → (Fin d → ℂ))
    (hΦ : AnalyticAt ℂ Φ 0) (hΦ0 : Φ 0 = 0)
    (hdet : (Matrix.of fun k j : Fin d ↦
      fderiv ℂ (fun w ↦ Φ w k) 0 (Pi.single (Fin.natAdd n j) 1)).det ≠ 0) :
    ∃ s : (Fin n → ℂ) → (Fin d → ℂ), AnalyticAt ℂ s 0 ∧ s 0 = 0 ∧
      ∀ᶠ y in nhds (0 : Fin n → ℂ), Φ (Fin.append y (s y)) = 0 := by
  classical
  -- the block continuous linear maps
  set πy : (Fin (n + d) → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi (fun j ↦ ContinuousLinearMap.proj (Fin.castAdd d j)) with hπydef
  set eY : (Fin n → ℂ) →L[ℂ] (Fin (n + d) → ℂ) :=
    ContinuousLinearMap.pi
      (Fin.addCases (fun j ↦ ContinuousLinearMap.proj j) (fun _ ↦ 0)) with heYdef
  set eL : (Fin d → ℂ) →L[ℂ] (Fin (n + d) → ℂ) :=
    ContinuousLinearMap.pi
      (Fin.addCases (fun _ ↦ 0) (fun j ↦ ContinuousLinearMap.proj j)) with heLdef
  have heYc : ∀ (u : Fin n → ℂ) (i : Fin n), eY u (Fin.castAdd d i) = u i := by
    intro u i
    simp [heYdef]
  have heYn : ∀ (u : Fin n → ℂ) (j : Fin d), eY u (Fin.natAdd n j) = 0 := by
    intro u j
    simp [heYdef]
  have heLc : ∀ (v : Fin d → ℂ) (i : Fin n), eL v (Fin.castAdd d i) = 0 := by
    intro v i
    simp [heLdef]
  have heLn : ∀ (v : Fin d → ℂ) (j : Fin d), eL v (Fin.natAdd n j) = v j := by
    intro v j
    simp [heLdef]
  have hπyc : ∀ (x : Fin (n + d) → ℂ) (i : Fin n), πy x i = x (Fin.castAdd d i) := by
    intro x i
    simp [hπydef]
  -- the auxiliary map `H (y, λ) = (y, Φ (y, λ))` and its derivative
  set H : (Fin (n + d) → ℂ) → (Fin (n + d) → ℂ) := fun x ↦ eY (πy x) + eL (Φ x) with hHdef
  have hHc : ∀ (x : Fin (n + d) → ℂ) (i : Fin n),
      H x (Fin.castAdd d i) = x (Fin.castAdd d i) := by
    intro x i
    rw [hHdef]
    simp only [Pi.add_apply, heYc, heLc, hπyc, add_zero]
  have hHn : ∀ (x : Fin (n + d) → ℂ) (j : Fin d), H x (Fin.natAdd n j) = Φ x j := by
    intro x j
    rw [hHdef]
    simp only [Pi.add_apply, heYn, heLn, zero_add]
  have hHan : AnalyticAt ℂ H 0 := by
    have h1 : AnalyticAt ℂ (fun x ↦ eY (πy x)) 0 := (eY.comp πy).analyticAt 0
    have h2 : AnalyticAt ℂ (fun x ↦ eL (Φ x)) 0 := (eL.analyticAt _).comp hΦ
    exact h1.add h2
  have hΦdiff : DifferentiableAt ℂ Φ 0 := hΦ.differentiableAt
  set J : (Fin (n + d) → ℂ) →L[ℂ] (Fin d → ℂ) := fderiv ℂ Φ 0 with hJdef
  have hNJ : ∀ k j : Fin d,
      fderiv ℂ (fun w ↦ Φ w k) 0 (Pi.single (Fin.natAdd n j) 1) =
        J (Pi.single (Fin.natAdd n j) 1) k := by
    intro k j
    rw [fderiv_apply hΦdiff k]
    rfl
  set L : (Fin (n + d) → ℂ) →L[ℂ] (Fin (n + d) → ℂ) := eY.comp πy + eL.comp J with hLdef
  have hHd : HasFDerivAt H L 0 := by
    have h1 : HasFDerivAt (fun x ↦ eY (πy x)) (eY.comp πy) 0 := (eY.comp πy).hasFDerivAt
    have h2 : HasFDerivAt (fun x ↦ eL (Φ x)) (eL.comp J) 0 :=
      eL.hasFDerivAt.comp 0 hΦdiff.hasFDerivAt
    exact h1.add h2
  have hLapp : ∀ (v : Fin (n + d) → ℂ), L v = eY (πy v) + eL (J v) := fun v ↦ rfl
  -- the determinant of the derivative
  have hLdetne : L.det ≠ 0 := by
    set A' := LinearMap.toMatrix' (L : (Fin (n + d) → ℂ) →ₗ[ℂ] (Fin (n + d) → ℂ)) with hA'def
    have hA'app : ∀ i j, A' i j = L (Pi.single j 1) i := by
      intro i j
      rw [hA'def, LinearMap.toMatrix'_apply]
      rfl
    have hzero : ∀ i : Fin (n + d), (i : ℕ) < n → ∀ j : Fin (n + d), ¬ ((j : ℕ) < n) →
        A' i j = 0 := by
      intro i hi j hj
      have hieq : Fin.castAdd d ⟨(i : ℕ), hi⟩ = i := Fin.ext rfl
      rw [hA'app, hLapp, Pi.add_apply, ← hieq, heYc, heLc, hπyc, hieq, add_zero]
      refine Pi.single_eq_of_ne (fun h ↦ hj ?_) 1
      rw [← h]
      exact hi
    have hdet2 : A'.det = (Matrix.of fun k j : Fin d ↦
        fderiv ℂ (fun w ↦ Φ w k) 0 (Pi.single (Fin.natAdd n j) 1)).det := by
      rw [Matrix.twoBlockTriangular_det' A' (fun i ↦ (i : ℕ) < n) hzero]
      have hyblock : A'.toSquareBlockProp (fun i ↦ (i : ℕ) < n) = 1 := by
        ext i j
        have hieq : Fin.castAdd d ⟨((i : Fin (n + d)) : ℕ), i.2⟩ = (i : Fin (n + d)) :=
          Fin.ext rfl
        rw [Matrix.toSquareBlockProp_def, Matrix.of_apply]
        rw [hA'app, hLapp, Pi.add_apply, ← hieq, heYc, heLc, hπyc, hieq, add_zero]
        rw [Matrix.one_apply, Pi.single_apply]
        by_cases h : (i : Fin (n + d)) = (j : Fin (n + d))
        · rw [if_pos h, if_pos (Subtype.ext h)]
        · rw [if_neg h, if_neg (fun hc ↦ h (congrArg _ hc))]
      rw [hyblock, Matrix.det_one, one_mul]
      rw [← Matrix.det_submatrix_equiv_self (finNatAddEquiv n d)]
      congr 1
      ext k j
      rw [Matrix.submatrix_apply]
      change A' (Fin.natAdd n k) (Fin.natAdd n j) = _
      rw [hA'app, hLapp, Pi.add_apply, heYn, heLn, zero_add, Matrix.of_apply, hNJ]
    have hLdeteq : L.det = A'.det := by
      rw [hA'def, LinearMap.det_toMatrix']
    rw [hLdeteq, hdet2]
    exact hdet
  -- the local inverse of `H` and its analyticity
  set eqv := L.toContinuousLinearEquivOfDetNeZero hLdetne with heqvdef
  have heqvcoe : (eqv : (Fin (n + d) → ℂ) →L[ℂ] (Fin (n + d) → ℂ)) = L :=
    L.coe_toContinuousLinearEquivOfDetNeZero hLdetne
  have hfd' : fderiv ℂ H 0 = (eqv : (Fin (n + d) → ℂ) →L[ℂ] (Fin (n + d) → ℂ)) := by
    rw [hHd.fderiv, heqvcoe]
  have hstrict : HasStrictFDerivAt H
      (eqv : (Fin (n + d) → ℂ) →L[ℂ] (Fin (n + d) → ℂ)) 0 := by
    have h := hHan.hasStrictFDerivAt
    rwa [hfd'] at h
  set R := HasStrictFDerivAt.toOpenPartialHomeomorph H hstrict with hRdef
  have hRcoe : (R : (Fin (n + d) → ℂ) → (Fin (n + d) → ℂ)) = H :=
    HasStrictFDerivAt.toOpenPartialHomeomorph_coe hstrict
  have hmemsrc : (0 : Fin (n + d) → ℂ) ∈ R.source :=
    HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hstrict
  have hH0 : H 0 = 0 := by
    rw [hHdef]
    simp [hΦ0]
  have hR0 : R 0 = 0 := by
    rw [show R (0 : Fin (n + d) → ℂ) = H 0 from congrFun hRcoe 0, hH0]
  have hsymm0 : R.symm 0 = 0 := by
    have h1 := R.left_inv hmemsrc
    rwa [hR0] at h1
  obtain ⟨p, hp⟩ := hHan
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℂ (Fin (n + d) → ℂ)
      (Fin (n + d) → ℂ)).symm (eqv : (Fin (n + d) → ℂ) →L[ℂ] (Fin (n + d) → ℂ)) := by
    have h2 := hp.fderiv_eq
    rw [hfd'] at h2
    have h3 := congrArg (continuousMultilinearCurryFin1 ℂ (Fin (n + d) → ℂ)
      (Fin (n + d) → ℂ)).symm h2
    rw [LinearIsometryEquiv.symm_apply_apply] at h3
    exact h3.symm
  have hψan : AnalyticAt ℂ (R.symm : (Fin (n + d) → ℂ) → (Fin (n + d) → ℂ)) 0 := by
    have hpR : HasFPowerSeriesAt (R : (Fin (n + d) → ℂ) → (Fin (n + d) → ℂ)) p 0 := by
      rwa [hRcoe]
    have h := R.hasFPowerSeriesAt_symm hmemsrc hpR hp1
    rw [hR0] at h
    exact h.analyticAt
  -- the implicit function
  set s : (Fin n → ℂ) → Fin d → ℂ := fun y j ↦ R.symm (eY y) (Fin.natAdd n j) with hsdef
  have hsan : AnalyticAt ℂ s 0 := by
    refine analyticAt_pi_iff.mpr fun j ↦ ?_
    have h1 : AnalyticAt ℂ (fun y ↦ R.symm (eY y)) 0 := by
      refine AnalyticAt.comp ?_ (eY.analyticAt 0)
      rw [map_zero]
      exact hψan
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + d) ↦ ℂ)
      (Fin.natAdd n j)).analyticAt _).comp h1
  have hs0 : s 0 = 0 := by
    funext j
    rw [hsdef]
    simp only [map_zero, hsymm0, Pi.zero_apply]
  refine ⟨s, hsan, hs0, ?_⟩
  have hRtgt : R.target ∈ nhds (0 : Fin (n + d) → ℂ) := by
    refine R.open_target.mem_nhds ?_
    have h1 := R.map_source hmemsrc
    rwa [hR0] at h1
  have htend : Filter.Tendsto eY (nhds (0 : Fin n → ℂ)) (nhds (0 : Fin (n + d) → ℂ)) := by
    have h := eY.continuous.tendsto 0
    rwa [map_zero] at h
  filter_upwards [htend.eventually hRtgt] with y hy
  have hri : H (R.symm (eY y)) = eY y := by
    have h1 := R.right_inv hy
    rwa [show R (R.symm (eY y)) = H (R.symm (eY y)) from congrFun hRcoe _] at h1
  have hx : ∀ i : Fin n, R.symm (eY y) (Fin.castAdd d i) = y i := by
    intro i
    have h1 := congrFun hri (Fin.castAdd d i)
    rw [hHc, heYc] at h1
    exact h1
  have hΦx : ∀ j : Fin d, Φ (R.symm (eY y)) j = 0 := by
    intro j
    have h1 := congrFun hri (Fin.natAdd n j)
    rw [hHn, heYn] at h1
    exact h1
  have happ : Fin.append y (s y) = R.symm (eY y) := by
    funext i
    induction i using Fin.addCases with
    | left i => rw [Fin.append_left]; exact (hx i).symm
    | right j => rw [Fin.append_right]
  rw [happ]
  funext j
  exact hΦx j

end ImplicitFunction

/-! ### Weierstrass polynomials with germ coefficients vanishing at the origin -/

variable {n : ℕ}

/-- The embedding of `ℂ^{n+1}` into `ℂ^{(n+d)+1}` sending the first `n` coordinates to the
first `n` coordinates and the last coordinate to the last coordinate. -/
def prepEmb (n d : ℕ) : Fin (n + 1) ↪ Fin (n + d + 1) :=
  ⟨Fin.lastCases (Fin.last (n + d)) (fun j ↦ (j.castAdd d).castSucc), by
    intro a b hab
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hab
        have hval := congrArg Fin.val hab
        simp only [Fin.val_last, Fin.val_castSucc, Fin.val_castAdd] at hval
        exact absurd hval (by have := j.isLt; omega)
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hab
        have hval := congrArg Fin.val hab
        simp only [Fin.val_last, Fin.val_castSucc, Fin.val_castAdd] at hval
        exact absurd hval (by have := i.isLt; omega)
      | cast j =>
        simp only [Fin.lastCases_castSucc] at hab
        have hval := congrArg Fin.val hab
        simp only [Fin.val_castSucc, Fin.val_castAdd] at hval
        exact congrArg Fin.castSucc (Fin.ext hval)⟩

instance (n d : ℕ) : Filter.TendstoCofinite (⇑(prepEmb n d)) :=
  Filter.tendstoCofinite_of_finite _

@[simp]
lemma prepEmb_last (n d : ℕ) : prepEmb n d (Fin.last n) = Fin.last (n + d) := by
  simp [prepEmb]

@[simp]
lemma prepEmb_castSucc (n d : ℕ) (j : Fin n) :
    prepEmb n d j.castSucc = (j.castAdd d).castSucc := by
  simp [prepEmb]

/-- The germ of the coordinate function `λ_j` on `ℂ^{n+d}`. -/
noncomputable def lambdaVar (n : ℕ) {d : ℕ} (j : Fin d) : LocalOkaRing (Fin (n + d)) :=
  ⟨MvPowerSeries.X (Fin.natAdd n j), MvPowerSeries.locallyConvergent_X _⟩

@[simp]
lemma coe_lambdaVar (n : ℕ) {d : ℕ} (j : Fin d) :
    ((lambdaVar n j : LocalOkaRing (Fin (n + d))) : MvPowerSeries (Fin (n + d)) ℂ) =
      MvPowerSeries.X (Fin.natAdd n j) :=
  rfl

lemma constantCoeff_lambdaVar (n : ℕ) {d : ℕ} (j : Fin d) :
    LocalOkaRing.constantCoeff (lambdaVar n j) = 0 := by
  rw [LocalOkaRing.constantCoeff_apply, coe_lambdaVar]
  exact MvPowerSeries.constantCoeff_X _

/-- A monic polynomial whose lower coefficients are germs vanishing at the origin is a local
Weierstrass polynomial. -/
lemma isLocalWeierstrassPolynomial_weierstrassOfCoeffs {m d : ℕ}
    (c : Fin d → LocalOkaRing (Fin m)) (hc : ∀ j, LocalOkaRing.constantCoeff (c j) = 0) :
    IsLocalWeierstrassPolynomial ((weierstrassOfCoeffs c).map
      (Subring.subtype (localOkaSubring (Fin m)).toSubring)) := by
  set φ := Subring.subtype (localOkaSubring (Fin m)).toSubring with hφ
  rw [weierstrassOfCoeffs_map]
  refine ⟨weierstrassOfCoeffs_monic _, fun i hi ↦ ?_⟩
  have hi' : i < d := by
    rw [weierstrassOfCoeffs_degree] at hi
    exact_mod_cast hi
  rw [weierstrassOfCoeffs_coeff_of_lt _ hi']
  exact hc ⟨i, hi'⟩

/-! ### Coefficient extraction along the last axis and the `λ`-directions -/

section CoeffExtraction

variable {n d : ℕ}

/-- Restricting the pullback of `P` along `prepEmb` to the last axis restricts `P` to the
last axis. -/
lemma partialEval_rename_prepEmb (P : MvPowerSeries (Fin (n + 1)) ℂ) :
    MvPowerSeries.partialEval (Fin.last (n + d)) (MvPowerSeries.rename (⇑(prepEmb n d)) P) =
      MvPowerSeries.partialEval (Fin.last n) P := by
  refine PowerSeries.ext fun k ↦ ?_
  rw [MvPowerSeries.coeff_partialEval, MvPowerSeries.coeff_partialEval]
  have h1 : Finsupp.single (Fin.last (n + d)) k =
      Finsupp.embDomain (prepEmb n d) (Finsupp.single (Fin.last n) k) := by
    rw [Finsupp.embDomain_single, prepEmb_last]
  rw [h1, MvPowerSeries.coeff_embDomain_rename]

/-- Restricting the function attached to a polynomial over the germ ring to the last axis
evaluates the coefficients at the origin. -/
lemma partialEval_coe_fromPolynomial {m : ℕ} (Q : (LocalOkaRing (Fin m))[X]) :
    MvPowerSeries.partialEval (Fin.last m)
      ((LocalOkaRing.fromPolynomial Q : LocalOkaRing (Fin (m + 1))) :
        MvPowerSeries (Fin (m + 1)) ℂ) =
      ((Q.map (LocalOkaRing.constantCoeff : LocalOkaRing (Fin m) →+* ℂ) : ℂ[X]) :
        PowerSeries ℂ) := by
  refine PowerSeries.ext fun k ↦ ?_
  rw [MvPowerSeries.coeff_partialEval, LocalOkaRing.coe_fromPolynomial]
  have h0 : Finsupp.single (Fin.last m) k =
      Finsupp.mapDomain (Fin.castSucc : Fin m → Fin (m + 1)) 0 +
        Finsupp.single (Fin.last m) k := by
    rw [Finsupp.mapDomain_zero, zero_add]
  rw [h0, MvPowerSeries.coeff_fromPolynomial', Polynomial.coeff_coe, Polynomial.coeff_map,
    Polynomial.coeff_map]
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, LocalOkaRing.constantCoeff_apply]
  rfl

/-- The pullback of a power series along `prepEmb` has no `λ`-linear coefficients. -/
lemma coeff_lambda_rename_prepEmb (P : MvPowerSeries (Fin (n + 1)) ℂ) (j : Fin d) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single ((Fin.natAdd n j).castSucc) 1 +
      Finsupp.single (Fin.last (n + d)) k) (MvPowerSeries.rename (⇑(prepEmb n d)) P) = 0 := by
  refine MvPowerSeries.coeff_rename_eq_zero _ _ ?_
  rintro ⟨e, he⟩
  have hnotmem : (Fin.natAdd n j).castSucc ∉ Set.range (⇑(prepEmb n d)) := by
    rintro ⟨a, ha⟩
    induction a using Fin.lastCases with
    | last =>
      rw [prepEmb_last] at ha
      have hval := congrArg Fin.val ha
      simp only [Fin.val_last, Fin.val_castSucc, Fin.val_natAdd] at hval
      exact absurd hval (by have := j.isLt; omega)
    | cast i =>
      rw [prepEmb_castSucc] at ha
      have hval := congrArg Fin.val ha
      simp only [Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd] at hval
      exact absurd hval (by have := i.isLt; omega)
  have hval := DFunLike.congr_fun he ((Fin.natAdd n j).castSucc)
  rw [Finsupp.mapDomain_notin_range _ _ hnotmem, Finsupp.add_apply,
    Finsupp.single_eq_same] at hval
  omega

lemma castSucc_natAdd_ne_last (j : Fin d) : (Fin.natAdd n j).castSucc ≠ Fin.last (n + d) := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_natAdd, Fin.val_last] at hval
  exact absurd hval (by have := j.isLt; omega)

/-- The `λ`-linear coefficients of the function attached to a polynomial over the germs in
`(y, λ)` are the `λ`-linear coefficients of its coefficients. -/
lemma coeff_lambda_coe_fromPolynomial (Q : (LocalOkaRing (Fin (n + d)))[X]) (j : Fin d)
    (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single ((Fin.natAdd n j).castSucc) 1 +
        Finsupp.single (Fin.last (n + d)) k)
      ((LocalOkaRing.fromPolynomial Q : LocalOkaRing (Fin (n + d + 1))) :
        MvPowerSeries (Fin (n + d + 1)) ℂ) =
      MvPowerSeries.coeff (Finsupp.single (Fin.natAdd n j) 1)
        ((Q.coeff k : LocalOkaRing (Fin (n + d))) : MvPowerSeries (Fin (n + d)) ℂ) := by
  rw [LocalOkaRing.coe_fromPolynomial]
  have h1 : Finsupp.single ((Fin.natAdd n j).castSucc) 1 +
      Finsupp.single (Fin.last (n + d)) k =
      Finsupp.mapDomain (Fin.castSucc : Fin (n + d) → Fin (n + d + 1))
        (Finsupp.single (Fin.natAdd n j) 1) + Finsupp.single (Fin.last (n + d)) k := by
    rw [Finsupp.mapDomain_single]
  rw [h1, MvPowerSeries.coeff_fromPolynomial', Polynomial.coeff_map]
  rfl

/-- The function attached to the generic Weierstrass polynomial, explicitly. -/
lemma coe_fromPolynomial_weierstrassOfCoeffs {m e : ℕ} (c : Fin e → LocalOkaRing (Fin m)) :
    ((LocalOkaRing.fromPolynomial (weierstrassOfCoeffs c) : LocalOkaRing (Fin (m + 1))) :
        MvPowerSeries (Fin (m + 1)) ℂ) =
      MvPowerSeries.X (Fin.last m) ^ e +
        ∑ j : Fin e, MvPowerSeries.rename (Fin.castSuccEmb : Fin m → Fin (m + 1))
          ((c j : LocalOkaRing (Fin m)) : MvPowerSeries (Fin m) ℂ) *
            MvPowerSeries.X (Fin.last m) ^ (j : ℕ) := by
  rw [weierstrassOfCoeffs, map_add, map_pow, map_sum, LocalOkaRing.fromPolynomial_X,
    AddMemClass.coe_add, SubmonoidClass.coe_pow, LocalOkaRing.coe_lastVar,
    AddSubmonoidClass.coe_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, map_pow, LocalOkaRing.fromPolynomial_C, LocalOkaRing.fromPolynomial_X,
    MulMemClass.coe_mul, SubmonoidClass.coe_pow, LocalOkaRing.coe_incl,
    LocalOkaRing.coe_lastVar]

/-- The `λ`-linear coefficients of `A` times the generic Weierstrass polynomial. -/
lemma coeff_lambda_mul_genericWeierstrass (A : MvPowerSeries (Fin (n + d + 1)) ℂ)
    (j : Fin d) (k : ℕ) (hk : k < d) :
    MvPowerSeries.coeff (Finsupp.single ((Fin.natAdd n j).castSucc) 1 +
        Finsupp.single (Fin.last (n + d)) k)
      (A * ((LocalOkaRing.fromPolynomial (weierstrassOfCoeffs (lambdaVar n (d := d))) :
        LocalOkaRing (Fin (n + d + 1))) : MvPowerSeries (Fin (n + d + 1)) ℂ)) =
      if (j : ℕ) ≤ k then
        MvPowerSeries.coeff (Finsupp.single (Fin.last (n + d)) (k - (j : ℕ))) A
      else 0 := by
  classical
  set z : Fin (n + d + 1) := Fin.last (n + d) with hzdef
  set lam : Fin d → Fin (n + d + 1) := fun j' ↦ (Fin.natAdd n j').castSucc with hlamdef
  rw [show Finsupp.single ((Fin.natAdd n j).castSucc) (1 : ℕ) = Finsupp.single (lam j) 1
    from rfl]
  have hlz : ∀ j' : Fin d, lam j' ≠ z := fun j' ↦ castSucc_natAdd_ne_last j'
  have hlam_inj : ∀ j' j'' : Fin d, lam j' = lam j'' → j' = j'' := by
    intro j' j'' h
    have hval := congrArg Fin.val h
    simp only [hlamdef, Fin.val_castSucc, Fin.val_natAdd] at hval
    exact Fin.ext (by omega)
  -- pointwise values of the relevant `Finsupp`s
  have hne : ∀ p q : Fin (n + d + 1), p ≠ q → ∀ b : ℕ, Finsupp.single p b q = 0 := by
    intro p q hpq b
    rw [Finsupp.single_apply, if_neg hpq]
  rw [coe_fromPolynomial_weierstrassOfCoeffs]
  have hren : ∀ j' : Fin d, MvPowerSeries.rename
      (Fin.castSuccEmb : Fin (n + d) → Fin (n + d + 1))
      ((lambdaVar n j' : LocalOkaRing (Fin (n + d))) : MvPowerSeries (Fin (n + d)) ℂ) =
      MvPowerSeries.X (lam j') := by
    intro j'
    rw [coe_lambdaVar, MvPowerSeries.rename_X]
    rfl
  simp only [hren]
  rw [mul_add, Finset.mul_sum, map_add, map_sum]
  have hterm1 : MvPowerSeries.coeff (Finsupp.single (lam j) 1 + Finsupp.single z k)
      (A * MvPowerSeries.X z ^ d) = 0 := by
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_mul_monomial, if_neg]
    intro hle
    rw [Finsupp.single_le_iff, Finsupp.add_apply, hne _ _ (hlz j),
      Finsupp.single_eq_same, zero_add] at hle
    omega
  rw [hterm1, zero_add]
  have hmono : ∀ j' : Fin d, MvPowerSeries.X (lam j') * MvPowerSeries.X z ^ (j' : ℕ) =
      MvPowerSeries.monomial (Finsupp.single (lam j') 1 +
        Finsupp.single z (j' : ℕ)) (1 : ℂ) := by
    intro j'
    rw [MvPowerSeries.X_pow_eq, ← pow_one (MvPowerSeries.X (lam j')),
      MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [Finset.sum_eq_single j]
  · rw [hmono, MvPowerSeries.coeff_mul_monomial]
    by_cases hjk : (j : ℕ) ≤ k
    · have hle : Finsupp.single (lam j) 1 + Finsupp.single z (j : ℕ) ≤
          Finsupp.single (lam j) 1 + Finsupp.single z k := by
        rw [Finsupp.le_def]
        intro a
        rcases eq_or_ne a z with rfl | haz
        · simp only [Finsupp.add_apply, Finsupp.single_eq_same, hne _ _ (hlz j)]
          omega
        · simp only [Finsupp.add_apply, hne _ _ (fun h ↦ haz h.symm)]
          omega
      have hsub : (Finsupp.single (lam j) 1 + Finsupp.single z k) -
          (Finsupp.single (lam j) 1 + Finsupp.single z (j : ℕ)) =
          Finsupp.single z (k - (j : ℕ)) := by
        refine Finsupp.ext fun a ↦ ?_
        rw [Finsupp.tsub_apply]
        rcases eq_or_ne a (lam j) with rfl | hap
        · simp only [Finsupp.add_apply, Finsupp.single_eq_same,
            hne _ _ (Ne.symm (hlz j))]
          omega
        · rcases eq_or_ne a z with rfl | haz
          · simp only [Finsupp.add_apply, Finsupp.single_eq_same, hne _ _ (hlz j)]
            omega
          · simp only [Finsupp.add_apply, hne _ _ (fun h ↦ hap h.symm),
              hne _ _ (fun h ↦ haz h.symm)]
            omega
      rw [if_pos hle, if_pos hjk, hsub, mul_one]
    · rw [if_neg, if_neg hjk]
      intro hle
      rw [Finsupp.le_def] at hle
      have h2 := hle z
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, hne _ _ (hlz j)] at h2
      omega
  · intro j' _ hj'
    rw [hmono, MvPowerSeries.coeff_mul_monomial, if_neg]
    intro hle
    rw [Finsupp.le_def] at hle
    have h2 := hle (lam j')
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, hne _ _ (Ne.symm (hlz j')),
      hne _ _ (fun h ↦ hj' (hlam_inj j j' h).symm)] at h2
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

end CoeffExtraction

/-! ### The preparation theorem from the division theorem -/

section Preparation

variable {n : ℕ}

/-- The Weierstrass preparation theorem for germs; uniqueness is omitted. It is derived
from the Weierstrass division theorem `localweierstrass_division` by dividing the pullback
of `f` to `ℂ^{(n+d)+1}` by the generic Weierstrass polynomial `X^d + ∑ λ_j X^j` over
`ℂ^{n+d}` and eliminating the generic coefficients `λ` with the analytic implicit function
theorem. -/
theorem localweierstrass_preparation
    (f : LocalOkaRing (Fin (n + 1)))
    (hf : (f : MvPowerSeries (Fin (n + 1)) ℂ).IsGeneralIn (.last _)) :
    ∃ (u : LocalOkaRing (Fin (n + 1))) (_ : IsUnit u)
      (g : (LocalOkaRing (Fin (n)))[X])
      (_ : IsLocalWeierstrassPolynomial
           (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) g)),
      f = LocalOkaRing.fromPolynomial g * u := by
  classical
  -- the order of generality
  set F₀ : PowerSeries ℂ := MvPowerSeries.partialEval (Fin.last n)
    (f : MvPowerSeries (Fin (n + 1)) ℂ) with hF₀def
  have hF₀ne : F₀ ≠ 0 := hf
  set d : ℕ := F₀.order.toNat with hddef
  have horder : F₀.order = (d : ℕ∞) :=
    (ENat.coe_toNat (fun hc ↦ hF₀ne (PowerSeries.order_eq_top.mp hc))).symm
  -- division by the generic Weierstrass polynomial
  set q : (LocalOkaRing (Fin (n + d)))[X] := weierstrassOfCoeffs (lambdaVar n (d := d))
    with hqdef
  have hq : IsLocalWeierstrassPolynomial
      (q.map (Subring.subtype (localOkaSubring (Fin (n + d))).toSubring)) :=
    isLocalWeierstrassPolynomial_weierstrassOfCoeffs _ (fun j ↦ constantCoeff_lambdaVar n j)
  obtain ⟨A, B, hBdeg, hdiv⟩ := localweierstrass_division q hq
    (⟨MvPowerSeries.rename (⇑(prepEmb n d)) ↑f,
      MvPowerSeries.LocallyConvergent.rename (prepEmb n d) f.locallyConvergent⟩ :
      LocalOkaRing (Fin (n + d + 1)))
  have hdivc : (MvPowerSeries.rename (⇑(prepEmb n d)) ↑f :
      MvPowerSeries (Fin (n + d + 1)) ℂ) =
      ↑A * ↑(LocalOkaRing.fromPolynomial q) + ↑(LocalOkaRing.fromPolynomial B) := by
    have h1 := congrArg (fun P : LocalOkaRing (Fin (n + d + 1)) ↦
      (P : MvPowerSeries (Fin (n + d + 1)) ℂ)) hdiv
    simp only at h1
    rw [AddMemClass.coe_add, MulMemClass.coe_mul] at h1
    exact h1
  -- restriction to the last axis
  have hq0 : MvPowerSeries.partialEval (Fin.last (n + d))
      (↑(LocalOkaRing.fromPolynomial q) : MvPowerSeries (Fin (n + d + 1)) ℂ) =
      PowerSeries.X ^ d := by
    rw [partialEval_coe_fromPolynomial, hqdef, weierstrassOfCoeffs_map]
    rw [show (fun j : Fin d ↦ LocalOkaRing.constantCoeff (lambdaVar n j)) =
      fun _ ↦ (0 : ℂ) from funext fun j ↦ constantCoeff_lambdaVar n j]
    rw [show weierstrassOfCoeffs (fun _ : Fin d ↦ (0 : ℂ)) = Polynomial.X ^ d by
      rw [weierstrassOfCoeffs]
      simp]
    rw [Polynomial.coe_pow, Polynomial.coe_X]
  have hpe : F₀ = MvPowerSeries.partialEval (Fin.last (n + d))
      (↑A : MvPowerSeries (Fin (n + d + 1)) ℂ) * PowerSeries.X ^ d +
      ((B.map (LocalOkaRing.constantCoeff :
        LocalOkaRing (Fin (n + d)) →+* ℂ) : ℂ[X]) : PowerSeries ℂ) := by
    have h1 := congrArg (MvPowerSeries.partialEval (Fin.last (n + d))) hdivc
    rw [partialEval_rename_prepEmb, map_add, map_mul, hq0,
      partialEval_coe_fromPolynomial] at h1
    exact h1
  set Bbar : ℂ[X] := B.map (LocalOkaRing.constantCoeff :
    LocalOkaRing (Fin (n + d)) →+* ℂ) with hBbardef
  have hqd : q.degree = (d : WithBot ℕ) := weierstrassOfCoeffs_degree _
  have hBd : Bbar.degree < (d : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_map_le) (hqd ▸ hBdeg)
  have hBcoeff0 : ∀ i : ℕ, d ≤ i → B.coeff i = 0 := fun i hi ↦
    Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le (hqd ▸ hBdeg) (by exact_mod_cast hi))
  have hBbar0 : Bbar = 0 := by
    refine Polynomial.ext fun k ↦ ?_
    rw [Polynomial.coeff_zero]
    by_cases hkd : k < d
    · have h2 := congrArg (PowerSeries.coeff k) hpe
      rw [PowerSeries.coeff_of_lt_order k (by rw [horder]; exact_mod_cast hkd)] at h2
      rw [map_add, PowerSeries.coeff_mul_X_pow', if_neg (by omega), zero_add,
        Polynomial.coeff_coe] at h2
      exact h2.symm
    · rw [hBbardef, Polynomial.coeff_map, hBcoeff0 k (by omega), map_zero]
  have hβ : ∀ i : ℕ, LocalOkaRing.constantCoeff (B.coeff i) = 0 := by
    intro i
    have h2 := congrArg (fun p : ℂ[X] ↦ p.coeff i) hBbar0
    simpa [hBbardef, Polynomial.coeff_map] using h2
  -- the constant term of `A` is nonzero
  rw [hBbar0, Polynomial.coe_zero, add_zero] at hpe
  set α : PowerSeries ℂ := MvPowerSeries.partialEval (Fin.last (n + d))
    (↑A : MvPowerSeries (Fin (n + d + 1)) ℂ) with hαdef
  have hα : MvPowerSeries.constantCoeff (↑A : MvPowerSeries (Fin (n + d + 1)) ℂ) =
      PowerSeries.coeff d F₀ := by
    have h2 := congrArg (PowerSeries.coeff d) hpe
    rw [PowerSeries.coeff_mul_X_pow', if_pos (le_refl d), Nat.sub_self] at h2
    rw [← MvPowerSeries.constantCoeff_partialEval, ← hαdef,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h2.symm
  have hαne : MvPowerSeries.constantCoeff (↑A : MvPowerSeries (Fin (n + d + 1)) ℂ) ≠ 0 := by
    rw [hα, hddef]
    exact PowerSeries.coeff_order hF₀ne
  -- the matrix of `λ`-linear coefficients of the remainder
  have hMeq : ∀ k j : Fin d,
      MvPowerSeries.coeff (Finsupp.single (Fin.natAdd n j) 1)
        ((B.coeff (k : ℕ) : LocalOkaRing (Fin (n + d))) : MvPowerSeries (Fin (n + d)) ℂ) =
      -(if (j : ℕ) ≤ (k : ℕ) then PowerSeries.coeff ((k : ℕ) - (j : ℕ)) α else 0) := by
    intro k j
    have h2 := congrArg (MvPowerSeries.coeff
      (Finsupp.single ((Fin.natAdd n j).castSucc) 1 +
        Finsupp.single (Fin.last (n + d)) (k : ℕ))) hdivc
    rw [coeff_lambda_rename_prepEmb, map_add,
      coeff_lambda_mul_genericWeierstrass _ _ _ k.isLt,
      coeff_lambda_coe_fromPolynomial] at h2
    have h3 : MvPowerSeries.coeff
        (Finsupp.single (Fin.last (n + d)) ((k : ℕ) - (j : ℕ)))
        (↑A : MvPowerSeries (Fin (n + d + 1)) ℂ) =
        PowerSeries.coeff ((k : ℕ) - (j : ℕ)) α := by
      rw [hαdef, MvPowerSeries.coeff_partialEval]
    rw [h3] at h2
    linear_combination -h2
  -- the analytic implicit function theorem
  set Φ : (Fin (n + d) → ℂ) → (Fin d → ℂ) := fun w k ↦
    ((B.coeff (k : ℕ) : LocalOkaRing (Fin (n + d))) : MvPowerSeries (Fin (n + d)) ℂ).eval w
    with hΦdef
  have hΦan : AnalyticAt ℂ Φ 0 :=
    analyticAt_pi_iff.mpr fun k ↦ (B.coeff (k : ℕ)).locallyConvergent.analyticAt
  have hΦ0 : Φ 0 = 0 := by
    funext k
    rw [hΦdef]
    change ((B.coeff (k : ℕ) : LocalOkaRing (Fin (n + d))) :
      MvPowerSeries (Fin (n + d)) ℂ).eval 0 = (0 : Fin d → ℂ) k
    rw [MvPowerSeries.eval_zero, Pi.zero_apply]
    have h2 := hβ (k : ℕ)
    rwa [LocalOkaRing.constantCoeff_apply] at h2
  have hdet : (Matrix.of fun k j : Fin d ↦
      fderiv ℂ (fun w ↦ Φ w k) 0 (Pi.single (Fin.natAdd n j) 1)).det ≠ 0 := by
    have hM : (Matrix.of fun k j : Fin d ↦
        fderiv ℂ (fun w ↦ Φ w k) 0 (Pi.single (Fin.natAdd n j) 1)) =
        Matrix.of fun k j : Fin d ↦
          -(if (j : ℕ) ≤ (k : ℕ) then PowerSeries.coeff ((k : ℕ) - (j : ℕ)) α else 0) := by
      ext k j
      rw [Matrix.of_apply, Matrix.of_apply, ← hMeq k j]
      exact (B.coeff (k : ℕ)).locallyConvergent.fderiv_eval_zero _
    rw [hM]
    have htri : Matrix.BlockTriangular (Matrix.of fun k j : Fin d ↦
        -(if (j : ℕ) ≤ (k : ℕ) then PowerSeries.coeff ((k : ℕ) - (j : ℕ)) α else 0))
        OrderDual.toDual := by
      intro k j hkj
      have hkj' : k < j := hkj
      rw [Matrix.of_apply, if_neg (by rw [Fin.lt_def] at hkj'; omega), neg_zero]
    rw [Matrix.det_of_lowerTriangular _ htri]
    have hdiag : ∀ k : Fin d, (Matrix.of fun k j : Fin d ↦
        -(if (j : ℕ) ≤ (k : ℕ) then PowerSeries.coeff ((k : ℕ) - (j : ℕ)) α else 0)) k k =
        -(PowerSeries.coeff 0 α) := by
      intro k
      rw [Matrix.of_apply, if_pos (le_refl _), Nat.sub_self]
    rw [Finset.prod_congr rfl (fun k _ ↦ hdiag k), Finset.prod_const]
    refine pow_ne_zero _ (neg_ne_zero.mpr ?_)
    rw [hαdef, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.constantCoeff_partialEval]
    exact hαne
  obtain ⟨s, hsan, hs0, hsz⟩ := exists_analyticAt_implicit Φ hΦan hΦ0 hdet
  -- the coefficients of the Weierstrass polynomial
  have hs_coord : ∀ j : Fin d, AnalyticAt ℂ (fun y ↦ s y j) 0 := fun j ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) j).analyticAt _).comp hsan
  choose S hSconv hSrep using fun j : Fin d ↦ MvPowerSeries.exists_represents (hs_coord j)
  set sg : Fin d → LocalOkaRing (Fin n) := fun j ↦ ⟨S j, hSconv j⟩ with hsgdef
  have hsg0 : ∀ j, LocalOkaRing.constantCoeff (sg j) = 0 := by
    intro j
    rw [LocalOkaRing.constantCoeff_apply]
    change MvPowerSeries.constantCoeff (S j) = 0
    have h2 : s 0 j = MvPowerSeries.constantCoeff (S j) := (hSrep j).apply_zero
    rw [← h2, hs0, Pi.zero_apply]
  set g : (LocalOkaRing (Fin n))[X] := weierstrassOfCoeffs sg with hgdef
  -- the substitution `τ (y, z) = (y, s y, z)`
  set τ : (Fin (n + 1) → ℂ) → (Fin (n + d + 1) → ℂ) := fun x ↦
    Fin.snoc (Fin.append (Fin.init x) (s (Fin.init x))) (x (Fin.last n)) with hτdef
  have hτ0 : τ 0 = 0 := by
    funext i
    simp only [hτdef]
    have hinit : Fin.init (0 : Fin (n + 1) → ℂ) = 0 := funext fun j ↦ rfl
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      rfl
    | cast i =>
      rw [Fin.snoc_castSucc]
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_left, hinit]
        rfl
      | right j =>
        rw [Fin.append_right, hinit, hs0]
        rfl
  have hτan : AnalyticAt ℂ τ 0 := by
    refine (analyticAt_pi_iff
      (f := fun (i : Fin (n + d + 1)) (x : Fin (n + 1) → ℂ) ↦ τ x i)).mpr fun i ↦ ?_
    induction i using Fin.lastCases with
    | last =>
      have heq : (fun x : Fin (n + 1) → ℂ ↦ τ x (Fin.last (n + d))) =
          fun x : Fin (n + 1) → ℂ ↦ x (Fin.last n) := by
        funext x
        simp only [hτdef]
        rw [Fin.snoc_last]
      rw [heq]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ)
        (Fin.last n)).analyticAt 0
    | cast i =>
      induction i using Fin.addCases with
      | left i =>
        have heq2 : (fun x : Fin (n + 1) → ℂ ↦ τ x (Fin.castAdd d i).castSucc) =
            fun x : Fin (n + 1) → ℂ ↦ x i.castSucc := by
          funext x
          simp only [hτdef]
          rw [Fin.snoc_castSucc, Fin.append_left]
          rfl
        rw [heq2]
        exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ)
          i.castSucc).analyticAt 0
      | right j =>
        set πinit : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
          ContinuousLinearMap.pi
            (fun i ↦ ContinuousLinearMap.proj i.castSucc) with hπinitdef
        have heq2 : (fun x : Fin (n + 1) → ℂ ↦ τ x (Fin.natAdd n j).castSucc) =
            fun x : Fin (n + 1) → ℂ ↦ (fun y ↦ s y j) (πinit x) := by
          funext x
          simp only [hτdef]
          rw [Fin.snoc_castSucc, Fin.append_right]
          rfl
        rw [heq2]
        have h3 : AnalyticAt ℂ ((fun y ↦ s y j) ∘ ⇑πinit) 0 := by
          refine AnalyticAt.comp ?_ (πinit.analyticAt 0)
          rw [map_zero]
          exact hs_coord j
        exact h3
  -- the unit
  have hAan : AnalyticAt ℂ (fun x ↦
      (↑A : MvPowerSeries (Fin (n + d + 1)) ℂ).eval (τ x)) 0 := by
    have h : AnalyticAt ℂ
        ((↑A : MvPowerSeries (Fin (n + d + 1)) ℂ).eval ∘ τ) 0 := by
      refine AnalyticAt.comp ?_ hτan
      rw [hτ0]
      exact A.locallyConvergent.analyticAt
    exact h
  obtain ⟨U, hUconv, hUrep⟩ := MvPowerSeries.exists_represents hAan
  set u : LocalOkaRing (Fin (n + 1)) := ⟨U, hUconv⟩ with hudef
  have huunit : IsUnit u := by
    rw [LocalOkaRing.isUnit_iff, LocalOkaRing.constantCoeff_apply]
    change MvPowerSeries.constantCoeff U ≠ 0
    rw [← hUrep.apply_zero]
    show (↑A : MvPowerSeries (Fin (n + d + 1)) ℂ).eval (τ 0) ≠ 0
    rw [hτ0, MvPowerSeries.eval_zero]
    exact hαne
  refine ⟨u, huunit, g, isLocalWeierstrassPolynomial_weierstrassOfCoeffs sg hsg0, ?_⟩
  -- continuity facts
  have htend_τ : Filter.Tendsto τ (nhds 0) (nhds (0 : Fin (n + d + 1) → ℂ)) := by
    have h := hτan.continuousAt
    rwa [ContinuousAt, hτ0] at h
  have htend_init : Filter.Tendsto (fun x : Fin (n + 1) → ℂ ↦ Fin.init x)
      (nhds 0) (nhds (0 : Fin n → ℂ)) := by
    have hcont : Continuous (fun x : Fin (n + 1) → ℂ ↦ Fin.init x) :=
      continuous_pi fun j ↦ continuous_apply j.castSucc
    have h := hcont.tendsto 0
    rwa [show Fin.init (0 : Fin (n + 1) → ℂ) = 0 from funext fun j ↦ rfl] at h
  have hw' : ∀ x : Fin (n + 1) → ℂ, (fun j : Fin (n + d) ↦ τ x j.castSucc) =
      Fin.append (Fin.init x) (s (Fin.init x)) := by
    intro x
    funext j
    simp only [hτdef]
    exact Fin.snoc_castSucc _ _ j
  have htend_w' : Filter.Tendsto (fun x : Fin (n + 1) → ℂ ↦
      (fun j : Fin (n + d) ↦ τ x j.castSucc)) (nhds 0) (nhds (0 : Fin (n + d) → ℂ)) := by
    have hcont : Continuous (fun w : Fin (n + d + 1) → ℂ ↦
        (fun j : Fin (n + d) ↦ w j.castSucc)) :=
      continuous_pi fun j ↦ continuous_apply j.castSucc
    have h := (hcont.tendsto 0).comp htend_τ
    rwa [show (fun j : Fin (n + d) ↦ (0 : Fin (n + d + 1) → ℂ) j.castSucc) = 0
      from funext fun j ↦ rfl] at h
  -- evaluation of the generic Weierstrass polynomial along `τ`
  have hqeval : ∀ x : Fin (n + 1) → ℂ,
      (↑(LocalOkaRing.fromPolynomial q) : MvPowerSeries (Fin (n + d + 1)) ℂ).eval (τ x) =
        x (Fin.last n) ^ d + ∑ j : Fin d, s (Fin.init x) j * x (Fin.last n) ^ (j : ℕ) := by
    intro x
    have hz : ∀ i : ℕ,
        ((q.coeff i : LocalOkaRing (Fin (n + d))) :
          MvPowerSeries (Fin (n + d)) ℂ).SummableAt (fun j ↦ τ x j.castSucc) := by
      intro i
      rcases lt_trichotomy i d with h | h | h
      · rw [hqdef, weierstrassOfCoeffs_coeff_of_lt _ h, coe_lambdaVar]
        exact MvPowerSeries.summableAt_X _ _
      · rw [hqdef, h, weierstrassOfCoeffs_coeff_self, OneMemClass.coe_one]
        exact MvPowerSeries.summableAt_one _
      · rw [hqdef, weierstrassOfCoeffs_coeff_of_gt _ h, ZeroMemClass.coe_zero]
        exact MvPowerSeries.summableAt_zero _
    rw [LocalOkaRing.eval_fromPolynomial q (τ x) hz]
    have hτlast : τ x (Fin.last (n + d)) = x (Fin.last n) := by
      simp only [hτdef]
      exact Fin.snoc_last _ _
    have hnatdeg : q.natDegree = d := weierstrassOfCoeffs_natDegree _
    rw [hnatdeg, Finset.sum_range_succ, hτlast]
    rw [hqdef, weierstrassOfCoeffs_coeff_self, OneMemClass.coe_one,
      MvPowerSeries.eval_one, one_mul]
    rw [add_comm]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [weierstrassOfCoeffs_coeff_of_lt _ j.isLt]
    congr 1
    rw [show (⟨(j : ℕ), j.isLt⟩ : Fin d) = j from Fin.ext rfl, coe_lambdaVar,
      MvPowerSeries.eval_X]
    rw [show τ x (Fin.natAdd n j).castSucc =
        Fin.append (Fin.init x) (s (Fin.init x)) (Fin.natAdd n j) from
      congrFun (hw' x) (Fin.natAdd n j), Fin.append_right]
  -- the remainder vanishes along the graph of `s`
  have hBeval : ∀ᶠ x in nhds (0 : Fin (n + 1) → ℂ),
      (↑(LocalOkaRing.fromPolynomial B) : MvPowerSeries (Fin (n + d + 1)) ℂ).eval (τ x) =
        0 := by
    have hBsum : ∀ᶠ x in nhds (0 : Fin (n + 1) → ℂ), ∀ i ∈ Finset.range (B.natDegree + 1),
        ((B.coeff i : LocalOkaRing (Fin (n + d))) :
          MvPowerSeries (Fin (n + d)) ℂ).SummableAt (fun j ↦ τ x j.castSucc) := by
      rw [Filter.eventually_all_finset]
      intro i _
      exact htend_w'.eventually (B.coeff i).locallyConvergent
    filter_upwards [hBsum, htend_init.eventually hsz] with x hx hzero
    have hz : ∀ i : ℕ,
        ((B.coeff i : LocalOkaRing (Fin (n + d))) :
          MvPowerSeries (Fin (n + d)) ℂ).SummableAt (fun j ↦ τ x j.castSucc) := by
      intro i
      by_cases hi : i ∈ Finset.range (B.natDegree + 1)
      · exact hx i hi
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
          simp only [Finset.mem_range] at hi
          omega), ZeroMemClass.coe_zero]
        exact MvPowerSeries.summableAt_zero _
    rw [LocalOkaRing.eval_fromPolynomial B (τ x) hz]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rcases lt_or_ge i d with hid | hid
    · have h2 : ((B.coeff i : LocalOkaRing (Fin (n + d))) :
          MvPowerSeries (Fin (n + d)) ℂ).eval (fun j ↦ τ x j.castSucc) = 0 := by
        rw [hw' x]
        have h3 := congrFun hzero (⟨i, hid⟩ : Fin d)
        rw [Pi.zero_apply] at h3
        exact h3
      rw [h2, zero_mul]
    · rw [hBcoeff0 i hid, ZeroMemClass.coe_zero, MvPowerSeries.eval_of_zero, zero_mul]
  -- evaluation of the Weierstrass polynomial `g`
  have hgeval : ∀ᶠ x in nhds (0 : Fin (n + 1) → ℂ),
      (↑(LocalOkaRing.fromPolynomial g) : MvPowerSeries (Fin (n + 1)) ℂ).eval x =
        x (Fin.last n) ^ d + ∑ j : Fin d, s (Fin.init x) j * x (Fin.last n) ^ (j : ℕ) := by
    have hgsum : ∀ᶠ x in nhds (0 : Fin (n + 1) → ℂ), ∀ j : Fin d,
        (S j).SummableAt (Fin.init x) := by
      rw [Filter.eventually_all]
      intro j
      exact htend_init.eventually (hSconv j)
    have hgrep : ∀ᶠ x in nhds (0 : Fin (n + 1) → ℂ), ∀ j : Fin d,
        (S j).eval (Fin.init x) = s (Fin.init x) j := by
      rw [Filter.eventually_all]
      intro j
      exact htend_init.eventually (hSrep j).eval_eq
    filter_upwards [hgsum, hgrep] with x hx hrep
    have hz : ∀ i : ℕ,
        ((g.coeff i : LocalOkaRing (Fin n)) :
          MvPowerSeries (Fin n) ℂ).SummableAt (fun j ↦ x j.castSucc) := by
      intro i
      rcases lt_trichotomy i d with h | h | h
      · rw [hgdef, weierstrassOfCoeffs_coeff_of_lt _ h]
        exact hx _
      · rw [hgdef, h, weierstrassOfCoeffs_coeff_self, OneMemClass.coe_one]
        exact MvPowerSeries.summableAt_one _
      · rw [hgdef, weierstrassOfCoeffs_coeff_of_gt _ h, ZeroMemClass.coe_zero]
        exact MvPowerSeries.summableAt_zero _
    rw [LocalOkaRing.eval_fromPolynomial g x hz]
    have hnatdeg : g.natDegree = d := weierstrassOfCoeffs_natDegree _
    rw [hnatdeg, Finset.sum_range_succ]
    rw [hgdef, weierstrassOfCoeffs_coeff_self, OneMemClass.coe_one,
      MvPowerSeries.eval_one, one_mul]
    rw [add_comm]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [weierstrassOfCoeffs_coeff_of_lt _ j.isLt]
    congr 1
    rw [show (⟨(j : ℕ), j.isLt⟩ : Fin d) = j from Fin.ext rfl]
    change (S j).eval (fun j' ↦ x j'.castSucc) = s (Fin.init x) j
    exact hrep j
  -- the division identity, evaluated
  have hev1 : ∀ᶠ w in nhds (0 : Fin (n + d + 1) → ℂ),
      (↑f : MvPowerSeries (Fin (n + 1)) ℂ).eval (w ∘ ⇑(prepEmb n d)) =
        (↑A : MvPowerSeries (Fin (n + d + 1)) ℂ).eval w *
          (↑(LocalOkaRing.fromPolynomial q) :
            MvPowerSeries (Fin (n + d + 1)) ℂ).eval w +
          (↑(LocalOkaRing.fromPolynomial B) :
            MvPowerSeries (Fin (n + d + 1)) ℂ).eval w := by
    filter_upwards [A.locallyConvergent, (LocalOkaRing.fromPolynomial q).locallyConvergent,
      (LocalOkaRing.fromPolynomial B).locallyConvergent] with w hwA hwq hwB
    rw [← MvPowerSeries.eval_rename (prepEmb n d), hdivc,
      MvPowerSeries.eval_add_of_summableAt (hwA.mul hwq) hwB,
      MvPowerSeries.eval_mul_of_summableAt hwA hwq]
  -- `τ` composed with the embedding is the identity
  have hτe : ∀ x : Fin (n + 1) → ℂ, (τ x) ∘ ⇑(prepEmb n d) = x := by
    intro x
    funext i
    rw [Function.comp_apply]
    induction i using Fin.lastCases with
    | last =>
      rw [prepEmb_last]
      simp only [hτdef]
      exact Fin.snoc_last _ _
    | cast i =>
      rw [prepEmb_castSucc]
      simp only [hτdef]
      rw [Fin.snoc_castSucc, Fin.append_left]
      rfl
  -- conclusion via uniqueness of representing power series
  refine LocalOkaRing.ext ?_
  refine MvPowerSeries.Represents.unique f.locallyConvergent.represents_eval ?_
  refine ((LocalOkaRing.fromPolynomial g * u).locallyConvergent.represents_eval).congr ?_
  have hueval : ∀ᶠ x in nhds (0 : Fin (n + 1) → ℂ),
      (↑u : MvPowerSeries (Fin (n + 1)) ℂ).eval x =
        (↑A : MvPowerSeries (Fin (n + d + 1)) ℂ).eval (τ x) :=
    hUrep.eval_eq
  filter_upwards [(LocalOkaRing.fromPolynomial g).locallyConvergent, u.locallyConvergent,
    htend_τ.eventually hev1, hBeval, hgeval, hueval] with x hxg hxu h1 hB0 hg1 hu1
  rw [MulMemClass.coe_mul, MvPowerSeries.eval_mul_of_summableAt hxg hxu]
  rw [hτe x] at h1
  rw [h1, hB0, add_zero, hqeval x, hg1, hu1]
  ring

end Preparation

section ToOkaRing

/-!
### Polynomials as holomorphic functions on a cylinder

A polynomial `P` over `OkaRing U` is interpreted as the holomorphic function
`(z, w) ↦ ∑ i, (P.coeff i) z * w ^ i` on the cylinder `U.extend'` over `U`. Formally,
`Polynomial.toOkaRing` is evaluation at the last coordinate function, with coefficients pulled
back along the projection to the first `n` coordinates.
-/

/-- The projection of `ℂ^{n + 1}` to the first `n` coordinates, as a continuous linear map. -/
noncomputable def finInitCLM : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.castSucc

@[simp]
lemma finInitCLM_apply (x : Fin (n + 1) → ℂ) : finInitCLM x = Fin.init x :=
  rfl

/-- Pullback of holomorphic functions along the projection of the cylinder over `U` to `U`. -/
noncomputable def OkaRing.pullbackInit (U : Opens (Fin n → ℂ)) :
    OkaRing U →ₐ[ℂ] OkaRing U.extend' where
  toFun f := OkaRing.mk (fun y ↦ f.toFun _ ⟨Fin.init y.1, Opens.mem_extend'.mp y.2⟩)
    (OkaAnalytic.comp_continuousLinearMap finInitCLM
      (fun _ hy ↦ Opens.mem_extend'.mp hy) f.2)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
lemma OkaRing.pullbackInit_toFun {U : Opens (Fin n → ℂ)} (f : OkaRing U)
    (y : U.extend') :
    (OkaRing.pullbackInit U f).toFun _ y = f.toFun _ ⟨Fin.init y.1, Opens.mem_extend'.mp y.2⟩ :=
  rfl

/-- The last coordinate, as a holomorphic function on the cylinder over `U`. -/
noncomputable def OkaRing.lastVar (U : Opens (Fin n → ℂ)) : OkaRing U.extend' :=
  OkaRing.mk (fun y ↦ y.1 (Fin.last n))
    (okaAnalytic_restrict fun x _ ↦
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ)
        (Fin.last n)).analyticAt x)

@[simp]
lemma OkaRing.lastVar_toFun (U : Opens (Fin n → ℂ)) (y : U.extend') :
    (OkaRing.lastVar U).toFun _ y = y.1 (Fin.last n) :=
  rfl

/-- A polynomial with coefficients holomorphic functions on `U`, viewed as the holomorphic
function `(z, w) ↦ ∑ i, (P.coeff i) z * w ^ i` on the cylinder over `U`. -/
noncomputable
def Polynomial.toOkaRing (U : Opens (Fin n → ℂ)) :
    (OkaRing U)[X] →ₐ[ℂ] OkaRing U.extend' :=
  Polynomial.eval₂AlgHom (OkaRing.pullbackInit U) (OkaRing.lastVar U) fun _ ↦ Commute.all _ _

@[simp]
lemma Polynomial.toOkaRing_C (U : Opens (Fin n → ℂ)) (f : OkaRing U) :
    Polynomial.toOkaRing U (Polynomial.C f) = OkaRing.pullbackInit U f :=
  Polynomial.eval₂_C _ _

@[simp]
lemma Polynomial.toOkaRing_X (U : Opens (Fin n → ℂ)) :
    Polynomial.toOkaRing U (Polynomial.X : (OkaRing U)[X]) = OkaRing.lastVar U :=
  Polynomial.eval₂_X _ _

/-- Transporting the evaluation of a holomorphic function along an equality of points. -/
lemma OkaRing.evalHom_congr {U : Opens (Fin n → ℂ)} {x y : Fin n → ℂ} (hx : x ∈ U)
    (hy : y ∈ U) (h : x = y) (f : OkaRing U) :
    OkaRing.evalHom hx f = OkaRing.evalHom hy f := by
  subst h
  rfl

/-- The value of `Polynomial.toOkaRing U P` at a point of the cylinder is obtained by
evaluating the coefficients at the base point and the resulting polynomial at the last
coordinate. -/
lemma OkaRing.evalHom_toOkaRing {U : Opens (Fin n → ℂ)} {y : Fin (n + 1) → ℂ}
    (hy : y ∈ U.extend') (P : (OkaRing U)[X]) :
    OkaRing.evalHom hy (Polynomial.toOkaRing U P) =
      Polynomial.eval₂ (OkaRing.evalHom (Opens.mem_extend'.mp hy)) (y (Fin.last n)) P := by
  have key : (OkaRing.evalHom hy).comp (Polynomial.toOkaRing U).toRingHom =
      Polynomial.eval₂RingHom (OkaRing.evalHom (Opens.mem_extend'.mp hy)) (y (Fin.last n)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.toOkaRing_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rfl
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.toOkaRing_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  have := congrArg (fun Φ ↦ Φ P) key
  simpa using this

/-- Interpreting polynomials as functions on the cylinder commutes with restriction. -/
lemma Polynomial.toOkaRing_map_restrict {U W : Opens (Fin n → ℂ)} (h : W ≤ U)
    (P : (OkaRing U)[X]) :
    Polynomial.toOkaRing W (P.map (OkaRing.restrict h).toRingHom) =
      OkaRing.restrict (TopologicalSpace.Opens.extend'_mono h) (Polynomial.toOkaRing U P) := by
  apply OkaRing.ext
  funext z
  have h1 := OkaRing.evalHom_toOkaRing z.2 (P.map (OkaRing.restrict h).toRingHom)
  have h2 := OkaRing.evalHom_toOkaRing ((TopologicalSpace.Opens.extend'_mono h) z.2) P
  rw [Polynomial.eval₂_map] at h1
  have hcomp : (OkaRing.evalHom (Opens.mem_extend'.mp z.2)).comp
      (OkaRing.restrict h).toRingHom =
      OkaRing.evalHom (Opens.mem_extend'.mp (TopologicalSpace.Opens.extend'_mono h z.2)) :=
    RingHom.ext fun a ↦ rfl
  rw [hcomp] at h1
  calc (Polynomial.toOkaRing W (P.map (OkaRing.restrict h).toRingHom)).toFun _ z
      = OkaRing.evalHom z.2 (Polynomial.toOkaRing W (P.map (OkaRing.restrict h).toRingHom)) :=
        rfl
    _ = OkaRing.evalHom (TopologicalSpace.Opens.extend'_mono h z.2)
          (Polynomial.toOkaRing U P) := by rw [h1, h2]
    _ = (OkaRing.restrict (TopologicalSpace.Opens.extend'_mono h)
          (Polynomial.toOkaRing U P)).toFun _ z := rfl

end ToOkaRing















variable {n : ℕ} (U : Opens (Fin n → ℂ))

/-- A Weierstrass polynomial is a monic polynomial whose coefficients below the leading one
vanish at the origin. -/
structure IsWeierstrassPolynomial (P : (OkaRing U)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) : (P.coeff i).toGlobalFun _ 0 = 0

section Germ

/-!
### Germs of holomorphic functions at arbitrary points

`OkaRing.germ hy` sends a holomorphic function on `U` to its Taylor series at the point
`y ∈ U`, i.e. to the Taylor series at the origin of the translated function. The germ map is
local in every respect: two functions with the same germ agree on a neighbourhood, every germ
is realized by a function on a neighbourhood, and a function whose germ is a unit is invertible
near the point.
-/

open MvPowerSeries

namespace OkaRing

variable {ι : Type*} [Fintype ι] {U : Opens (ι → ℂ)} {y : ι → ℂ}

/-- The Taylor series of a holomorphic function at a point `y` of its domain. -/
noncomputable def germ (hy : y ∈ U) : OkaRing U →ₐ[ℂ] LocalOkaRing ι :=
  (toLocalOkaRingHom (U.shift y) (by simpa using hy)).comp
    (shift U y : OkaRing U ≃ₐ[ℂ] OkaRing (U.shift y)).toAlgHom

/-- Near the origin, the translate of `f` by `y` agrees with `z ↦ f (z + y)`. -/
lemma shift_toGlobalFun_eventuallyEq (hy : y ∈ U) (f : OkaRing U) :
    (shift U y f).toGlobalFun _ =ᶠ[nhds (0 : ι → ℂ)] fun z ↦ f.toGlobalFun _ (z + y) := by
  filter_upwards [(U.shift y).isOpen.mem_nhds (show (0 : ι → ℂ) ∈ U.shift y by simpa using hy)]
    with z hz
  rw [(shift U y f).toGlobalFun_apply hz, f.toGlobalFun_apply (show z + y ∈ U from hz)]
  rfl

/-- The germ of `f` at `y` sums to `z ↦ f (z + y)` near the origin. -/
lemma germ_represents (hy : y ∈ U) (f : OkaRing U) :
    ((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ).Represents
      (fun z ↦ f.toGlobalFun _ (z + y)) :=
  (toLocalOkaRing_represents (show (0 : ι → ℂ) ∈ U.shift y by simpa using hy)
    ((shift U y : OkaRing U ≃ₐ[ℂ] OkaRing (U.shift y)) f)).congr
    (shift_toGlobalFun_eventuallyEq hy f)

/-- The germ of `f` at `y` is the unique locally convergent power series summing to
`z ↦ f (z + y)` near the origin. -/
lemma germ_eq_of_represents {P : LocalOkaRing ι} (hy : y ∈ U) {f : OkaRing U}
    (h : (P : MvPowerSeries ι ℂ).Represents (fun z ↦ f.toGlobalFun _ (z + y))) :
    germ hy f = P :=
  toLocalOkaRing_eq_of_represents
    (h0 := show (0 : ι → ℂ) ∈ U.shift y by simpa using hy)
    (h.congr (shift_toGlobalFun_eventuallyEq hy f).symm)

/-- At the origin, the germ is the Taylor series at the origin. -/
lemma germ_zero_mem (h0 : (0 : ι → ℂ) ∈ U) (f : OkaRing U) :
    germ h0 f = toLocalOkaRingHom U h0 f := by
  refine germ_eq_of_represents h0 ?_
  have h : (fun z ↦ f.toGlobalFun _ (z + 0)) = f.toGlobalFun _ := by
    funext z
    rw [add_zero]
  rw [h]
  exact toLocalOkaRing_represents h0 f

/-- Taking germs commutes with restriction. -/
@[simp]
lemma germ_restrict {V : Opens (ι → ℂ)} (hVU : V ≤ U) (hy : y ∈ V) (f : OkaRing U) :
    germ hy (restrict hVU f) = germ (hVU hy) f := by
  refine germ_eq_of_represents hy ?_
  refine (germ_represents (hVU hy) f).congr ?_
  filter_upwards [(V.shift y).isOpen.mem_nhds
    (show (0 : ι → ℂ) ∈ V.shift y by simpa using hy)] with z hz
  rw [f.toGlobalFun_apply (show z + y ∈ U from hVU hz),
    (restrict hVU f).toGlobalFun_apply (show z + y ∈ V from hz)]
  rfl

/-- The germ of a translated function is the germ at the translated point. -/
lemma germ_shift (v : ι → ℂ) {z : ι → ℂ} (hz : z ∈ U) (hy : y ∈ U.shift v)
    (hyz : y + v = z) (f : OkaRing U) :
    germ hy (shift U v f) = germ hz f := by
  subst hyz
  refine germ_eq_of_represents hy ?_
  refine (germ_represents (show y + v ∈ U from hy) f).congr ?_
  filter_upwards [((U.shift v).shift y).isOpen.mem_nhds
    (show (0 : ι → ℂ) ∈ (U.shift v).shift y by simpa using hy)] with w hw
  have hw' : w + y ∈ U.shift v := hw
  have hw'' : w + (y + v) ∈ U := by
    have h8 : (w + y) + v ∈ U := hw'
    rwa [add_assoc] at h8
  rw [f.toGlobalFun_apply hw'', (shift U v f).toGlobalFun_apply hw']
  change f.toFun _ ⟨w + (y + v), hw''⟩ = f.toFun _ ⟨(w + y) + v, hw'⟩
  congr 1
  exact Subtype.ext (add_assoc w y v).symm

/-- The constant term of the germ at `y` is the value at `y`. -/
lemma constantCoeff_germ (hy : y ∈ U) (f : OkaRing U) :
    LocalOkaRing.constantCoeff (germ hy f) = evalHom hy f := by
  have h1 : HasSum (((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ).term 0)
      (f.toGlobalFun _ (0 + y)) :=
    Filter.Eventually.self_of_nhds
      (p := fun z ↦ HasSum (((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ).term z)
        (f.toGlobalFun _ (z + y))) (germ_represents hy f)
  have h2 : HasSum (((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ).term 0)
      (MvPowerSeries.constantCoeff ((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ)) := by
    have h3 := hasSum_single
      (f := ((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ).term 0) 0
      (fun d hd ↦ by rw [term, evalMonomial_eq_zero hd, mul_zero])
    simpa only [term, evalMonomial_zero, mul_one, coeff_zero_eq_constantCoeff] using h3
  have h4 := h2.unique h1
  rw [LocalOkaRing.constantCoeff_apply, h4, zero_add, f.toGlobalFun_apply hy]
  rfl

/-- A function whose germ at `y` vanishes vanishes on a neighbourhood of `y`. -/
lemma exists_restrict_eq_zero (hy : y ∈ U) {f : OkaRing U} (h : germ hy f = 0) :
    ∃ (W : Opens (ι → ℂ)) (hWU : W ≤ U), y ∈ W ∧ restrict hWU f = 0 := by
  have hrep := germ_represents hy f
  rw [h, ZeroMemClass.coe_zero] at hrep
  have hzero : ∀ᶠ z in nhds (0 : ι → ℂ), f.toGlobalFun _ (z + y) = 0 := by
    filter_upwards [hrep] with z hz
    have h5 : HasSum ((0 : MvPowerSeries ι ℂ).term z) (0 : ℂ) := by
      have : (0 : MvPowerSeries ι ℂ).term z = fun _ ↦ (0 : ℂ) := funext fun d ↦ term_zero z d
      rw [this]
      exact hasSum_zero
    exact hz.unique h5
  obtain ⟨t, hts, htopen, ht0⟩ := mem_nhds_iff.mp hzero
  refine ⟨U ⊓ ⟨(fun z ↦ z - y) ⁻¹' t, htopen.preimage (continuous_id.sub continuous_const)⟩,
    inf_le_left, ⟨hy, by simpa using ht0⟩, ?_⟩
  apply OkaRing.ext
  funext z
  obtain ⟨hzU, hzt⟩ := z.2
  have h6 : f.toGlobalFun _ ((z.1 - y) + y) = 0 := hts hzt
  rw [sub_add_cancel, f.toGlobalFun_apply hzU] at h6
  exact h6

/-- Two functions with the same germ at `y` agree on a neighbourhood of `y`. -/
lemma exists_restrict_eq_of_germ_eq (hy : y ∈ U) {f g : OkaRing U}
    (h : germ hy f = germ hy g) :
    ∃ (W : Opens (ι → ℂ)) (hWU : W ≤ U), y ∈ W ∧ restrict hWU f = restrict hWU g := by
  obtain ⟨W, hWU, hyW, hz⟩ := exists_restrict_eq_zero hy (f := f - g)
    (by rw [map_sub, h, sub_self])
  rw [map_sub, sub_eq_zero] at hz
  exact ⟨W, hWU, hyW, hz⟩

/-- A nowhere vanishing holomorphic function is invertible. -/
lemma isUnit_of_forall_ne_zero {f : OkaRing U} (h : ∀ z : U, f.toFun _ z ≠ 0) :
    IsUnit f := by
  have hg : ∀ x ∈ U, AnalyticAt ℂ (fun w ↦ (f.toGlobalFun _ w)⁻¹) x := fun x hx ↦
    (f.analyticAt_toGlobalFun hx).inv (by rw [f.toGlobalFun_apply hx]; exact h ⟨x, hx⟩)
  have hmul : f * OkaRing.mk _ (okaAnalytic_restrict hg) = 1 := by
    apply OkaRing.ext
    funext z
    change f.toFun _ z * (f.toGlobalFun _ z.1)⁻¹ = 1
    rw [f.toGlobalFun_apply z.2]
    exact mul_inv_cancel₀ (h z)
  exact IsUnit.of_mul_eq_one _ hmul

/-- The ring of holomorphic functions on a nonempty open set is nontrivial. -/
lemma nontrivial (hy : y ∈ U) : Nontrivial (OkaRing U) :=
  ⟨⟨1, 0, fun hc ↦ one_ne_zero (α := ℂ) (by
    have h1 := congrArg (evalHom hy) hc
    rwa [map_one, map_zero] at h1)⟩⟩

/-- A function whose germ at `y` is invertible is invertible on a neighbourhood of `y`. -/
lemma exists_isUnit_restrict (hy : y ∈ U) {f : OkaRing U} (h : IsUnit (germ hy f)) :
    ∃ (W : Opens (ι → ℂ)) (hWU : W ≤ U), y ∈ W ∧ IsUnit (restrict hWU f) := by
  rw [LocalOkaRing.isUnit_iff, constantCoeff_germ] at h
  have hcont : ContinuousAt (f.toGlobalFun _) y := (f.analyticAt_toGlobalFun hy).continuousAt
  have hne : f.toGlobalFun _ y ≠ 0 := by
    rw [f.toGlobalFun_apply hy]
    exact h
  obtain ⟨t, hts, htopen, hyt⟩ := mem_nhds_iff.mp (hcont.eventually_ne hne)
  refine ⟨U ⊓ ⟨t, htopen⟩, inf_le_left, ⟨hy, hyt⟩, ?_⟩
  refine isUnit_of_forall_ne_zero fun z ↦ ?_
  have h7 : f.toGlobalFun _ z.1 ≠ 0 := hts z.2.2
  rw [f.toGlobalFun_apply z.2.1] at h7
  exact h7

end OkaRing

end Germ

section GermPoly

/-!
### Germs of polynomial functions on a cylinder

The germ at a point `(y', w)` of the cylinder `V.extend'` of the function attached to a
polynomial `Q` over `OkaRing V` is again polynomial: it is obtained by taking germs of the
coefficients at `y'` and Taylor expanding at `w` in the polynomial variable. This is the
content of `OkaRing.germ_toOkaRing`, which links `Polynomial.toOkaRing` with
`LocalOkaRing.fromPolynomial`.
-/

open MvPowerSeries

/-- Membership in a finite infimum of open sets. -/
lemma TopologicalSpace.Opens.mem_finset_inf {X α : Type*} [TopologicalSpace X] {s : Finset α}
    {f : α → Opens X} {x : X} : x ∈ s.inf f ↔ ∀ i ∈ s, x ∈ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact h1
      · exact ih.mp h2 i hi
    · intro h
      exact ⟨h a (Finset.mem_insert_self a s), ih.mpr fun i hi ↦
        h i (Finset.mem_insert_of_mem hi)⟩

namespace OkaRing

variable {n : ℕ} {V : Opens (Fin n → ℂ)} {y' : Fin n → ℂ}

/-- Taylor expansion of a polynomial over `OkaRing V` at the point `(y', w)` of the cylinder:
take germs of the coefficients at `y'` and expand the polynomial variable at `w`. -/
noncomputable def germPoly (hy' : y' ∈ V) (w : ℂ) :
    (OkaRing V)[X] →ₐ[ℂ] (LocalOkaRing (Fin n))[X] :=
  ((Polynomial.aeval
      (Polynomial.X + Polynomial.C (algebraMap ℂ (LocalOkaRing (Fin n)) w))).restrictScalars
    ℂ).comp (Polynomial.mapAlgHom (germ hy'))

lemma germPoly_apply (hy' : y' ∈ V) (w : ℂ) (Q : (OkaRing V)[X]) :
    germPoly hy' w Q = (Q.map (germ hy').toRingHom).comp
      (Polynomial.X + Polynomial.C (algebraMap ℂ (LocalOkaRing (Fin n)) w)) := by
  rw [germPoly, AlgHom.comp_apply, AlgHom.restrictScalars_apply, Polynomial.aeval_def,
    Polynomial.comp, Polynomial.algebraMap_eq]
  rfl

/-- `OkaRing.germPoly` as a Taylor expansion. -/
lemma germPoly_eq_taylor (hy' : y' ∈ V) (w : ℂ) (Q : (OkaRing V)[X]) :
    germPoly hy' w Q = Polynomial.taylor (algebraMap ℂ (LocalOkaRing (Fin n)) w)
      (Q.map (germ hy').toRingHom) := by
  rw [germPoly_apply, Polynomial.taylor_apply]

/-- At a point with vanishing last coordinate, `OkaRing.germPoly` is just the coefficientwise
germ. -/
lemma germPoly_zero (hy' : y' ∈ V) (Q : (OkaRing V)[X]) :
    germPoly hy' 0 Q = Q.map (germ hy').toRingHom := by
  rw [germPoly_eq_taylor, map_zero, Polynomial.taylor_zero]

lemma monic_germPoly (hy' : y' ∈ V) (w : ℂ) {Q : (OkaRing V)[X]} (hQ : Q.Monic) :
    (germPoly hy' w Q).Monic := by
  rw [germPoly_apply]
  exact (hQ.map _).comp_X_add_C _

lemma natDegree_germPoly_le (hy' : y' ∈ V) (w : ℂ) (Q : (OkaRing V)[X]) :
    (germPoly hy' w Q).natDegree ≤ Q.natDegree := by
  rw [germPoly_eq_taylor, Polynomial.natDegree_taylor]
  exact Polynomial.natDegree_map_le

/-- The germ of the pullback of `f` is the image of the germ of `f` under the inclusion of
germ rings. -/
lemma germ_pullbackInit {y : Fin (n + 1) → ℂ} (hy : y ∈ V.extend') (f : OkaRing V) :
    germ hy (pullbackInit V f) =
      LocalOkaRing.incl (germ (Opens.mem_extend'.mp hy) f) := by
  refine germ_eq_of_represents hy ?_
  have h1 : ((LocalOkaRing.incl (germ (Opens.mem_extend'.mp hy) f) :
      LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).Represents
      (fun x ↦ f.toGlobalFun _ (Fin.init x + Fin.init y)) := by
    rw [LocalOkaRing.coe_incl]
    exact Represents.rename_castSucc (germ_represents (Opens.mem_extend'.mp hy) f)
  refine h1.congr ?_
  have hcont : Continuous (fun x : Fin (n + 1) → ℂ ↦ x + y) :=
    continuous_id.add continuous_const
  filter_upwards [IsOpen.mem_nhds (V.extend'.isOpen.preimage hcont)
    (show ((0 : Fin (n + 1) → ℂ) + y) ∈ V.extend' by rwa [zero_add])] with x hx
  have hx' : Fin.init (x + y) ∈ V := Opens.mem_extend'.mp hx
  rw [f.toGlobalFun_apply (show Fin.init x + Fin.init y ∈ V from hx'),
    (pullbackInit V f).toGlobalFun_apply hx]
  rfl

/-- The germ of the last coordinate function at `y` is `X_last + y_last`. -/
lemma germ_lastVar {y : Fin (n + 1) → ℂ} (hy : y ∈ V.extend') :
    germ hy (lastVar V) =
      LocalOkaRing.lastVar + algebraMap ℂ (LocalOkaRing (Fin (n + 1))) (y (Fin.last n)) := by
  refine germ_eq_of_represents hy ?_
  have h1 : ((LocalOkaRing.lastVar +
      algebraMap ℂ (LocalOkaRing (Fin (n + 1))) (y (Fin.last n)) : LocalOkaRing (Fin (n + 1))) :
      MvPowerSeries (Fin (n + 1)) ℂ).Represents
      ((fun z ↦ z (Fin.last n)) + Function.const _ (y (Fin.last n))) := by
    have h2 := (represents_X (ι := Fin (n + 1)) (Fin.last n)).add
      (represents_algebraMap (ι := Fin (n + 1)) (y (Fin.last n)))
    rw [AddMemClass.coe_add, LocalOkaRing.coe_lastVar]
    exact h2
  refine h1.congr ?_
  have hcont : Continuous (fun x : Fin (n + 1) → ℂ ↦ x + y) :=
    continuous_id.add continuous_const
  filter_upwards [IsOpen.mem_nhds (V.extend'.isOpen.preimage hcont)
    (show ((0 : Fin (n + 1) → ℂ) + y) ∈ V.extend' by rwa [zero_add])] with z hz
  rw [(lastVar V).toGlobalFun_apply hz]
  rfl

/-- Key compatibility: the germ at `y` of the function attached to a polynomial `Q` is the
polynomial germ `OkaRing.germPoly` of `Q`, viewed as a germ via
`LocalOkaRing.fromPolynomial`. -/
theorem germ_toOkaRing {y : Fin (n + 1) → ℂ} (hy : y ∈ V.extend') (Q : (OkaRing V)[X]) :
    germ hy (Polynomial.toOkaRing V Q) =
      LocalOkaRing.fromPolynomial
        (germPoly (Opens.mem_extend'.mp hy) (y (Fin.last n)) Q) := by
  have key : (germ hy).toRingHom.comp (Polynomial.toOkaRing V).toRingHom =
      LocalOkaRing.fromPolynomial.toRingHom.comp
        (germPoly (Opens.mem_extend'.mp hy) (y (Fin.last n))).toRingHom := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · have hL : germ hy (Polynomial.toOkaRing V (Polynomial.C a)) =
          LocalOkaRing.incl (germ (Opens.mem_extend'.mp hy) a) := by
        rw [Polynomial.toOkaRing_C]
        exact germ_pullbackInit hy a
      have hR : LocalOkaRing.fromPolynomial
          (germPoly (Opens.mem_extend'.mp hy) (y (Fin.last n)) (Polynomial.C a)) =
          LocalOkaRing.incl (germ (Opens.mem_extend'.mp hy) a) := by
        rw [germPoly_apply, Polynomial.map_C, Polynomial.C_comp,
          LocalOkaRing.fromPolynomial_C]
        rfl
      simpa using hL.trans hR.symm
    · have hL : germ hy (Polynomial.toOkaRing V Polynomial.X) =
          LocalOkaRing.lastVar +
            algebraMap ℂ (LocalOkaRing (Fin (n + 1))) (y (Fin.last n)) := by
        rw [Polynomial.toOkaRing_X]
        exact germ_lastVar hy
      have hR : LocalOkaRing.fromPolynomial
          (germPoly (Opens.mem_extend'.mp hy) (y (Fin.last n)) Polynomial.X) =
          LocalOkaRing.lastVar +
            algebraMap ℂ (LocalOkaRing (Fin (n + 1))) (y (Fin.last n)) := by
        rw [germPoly_apply, Polynomial.map_X, Polynomial.X_comp, map_add,
          LocalOkaRing.fromPolynomial_X, LocalOkaRing.fromPolynomial_C]
        rw [AlgHom.commutes]
      simpa using hL.trans hR.symm
  have h9 := congrArg (fun Φ : (OkaRing V)[X] →+* LocalOkaRing (Fin (n + 1)) ↦ Φ Q) key
  simpa using h9

end OkaRing

namespace LocalOkaRing

open OkaRing TopologicalSpace

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Every germ is realized by a holomorphic function on a neighbourhood of any prescribed
point. -/
lemma exists_okaRing_germ (P : LocalOkaRing ι) (y : ι → ℂ) :
    ∃ (W : Opens (ι → ℂ)) (hy : y ∈ W) (f : OkaRing W), OkaRing.germ hy f = P := by
  obtain ⟨U, h0, f₀, hf₀⟩ := LocalOkaRing.exists_okaRing P
  refine ⟨U.shift (-y), by simpa using h0, shift U (-y) f₀, ?_⟩
  rw [germ_shift (-y) h0 (by simpa using h0) (add_neg_cancel y) f₀, germ_zero_mem h0]
  exact hf₀

/-- Every polynomial over the germ ring is realized, coefficientwise, by a polynomial over the
holomorphic functions on a neighbourhood of any prescribed point. -/
lemma exists_poly_map_germ (g : (LocalOkaRing (Fin n))[X]) (y' : Fin n → ℂ) :
    ∃ (V : Opens (Fin n → ℂ)) (hy' : y' ∈ V) (Q : (OkaRing V)[X]),
      Q.map (OkaRing.germ hy').toRingHom = g ∧ Q.natDegree ≤ g.natDegree := by
  classical
  choose W hyW fc hfc using fun j : ℕ ↦ LocalOkaRing.exists_okaRing_germ (g.coeff j) y'
  set d := g.natDegree with hd
  set V : Opens (Fin n → ℂ) := (Finset.range (d + 1)).inf W with hV
  have hy' : y' ∈ V := Opens.mem_finset_inf.mpr fun j _ ↦ hyW j
  have hle : ∀ j, j ∈ Finset.range (d + 1) → V ≤ W j := fun j hj ↦ Finset.inf_le hj
  set c : ℕ → OkaRing V := fun j ↦
    if h : j ∈ Finset.range (d + 1) then OkaRing.restrict (hle j h) (fc j) else 0 with hc
  have hgerm : ∀ j ∈ Finset.range (d + 1), OkaRing.germ hy' (c j) = g.coeff j := by
    intro j hj
    rw [hc]
    simp only [dif_pos hj]
    rw [germ_restrict (hle j hj) hy' (fc j)]
    exact hfc j
  set Q : (OkaRing V)[X] :=
    ∑ j ∈ Finset.range (d + 1), Polynomial.C (c j) * Polynomial.X ^ j with hQ
  have hcoeff : ∀ k, Q.coeff k = if k ∈ Finset.range (d + 1) then c k else 0 := by
    intro k
    rw [hQ, Polynomial.finsetSum_coeff]
    have h1 : ∀ j ∈ Finset.range (d + 1),
        (Polynomial.C (c j) * Polynomial.X ^ j).coeff k = if j = k then c j else 0 := by
      intro j _
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      rcases eq_or_ne j k with rfl | hjk
      · simp
      · rw [if_neg (Ne.symm hjk), mul_zero, if_neg hjk]
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' (Finset.range (d + 1)) k c]
  have hQdeg : Q.natDegree ≤ d := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
    rw [hcoeff]
    rw [if_neg (by simp; omega)]
  refine ⟨V, hy', Q, ?_, hQdeg⟩
  refine Polynomial.ext fun k ↦ ?_
  rw [Polynomial.coeff_map, hcoeff]
  by_cases hk : k ∈ Finset.range (d + 1)
  · rw [if_pos hk]
    exact hgerm k hk
  · rw [if_neg hk, map_zero]
    refine (Polynomial.coeff_eq_zero_of_natDegree_lt ?_).symm
    simp only [Finset.mem_range] at hk
    omega

/-- Monic refinement of `LocalOkaRing.exists_poly_map_germ`. -/
lemma exists_poly_map_germ_monic {g : (LocalOkaRing (Fin n))[X]} (hg : g.Monic)
    (y' : Fin n → ℂ) :
    ∃ (V : Opens (Fin n → ℂ)) (hy' : y' ∈ V) (Q : (OkaRing V)[X]),
      Q.map (OkaRing.germ hy').toRingHom = g ∧ Q.Monic ∧ Q.natDegree = g.natDegree := by
  obtain ⟨V, hy', Q₀, hmap, hdeg⟩ := exists_poly_map_germ g y'
  haveI : Nontrivial (OkaRing V) := OkaRing.nontrivial hy'
  set d := g.natDegree with hd
  set Q : (OkaRing V)[X] :=
    Q₀ + Polynomial.C (1 - Q₀.coeff d) * Polynomial.X ^ d with hQ
  have hcoeffd : Q.coeff d = 1 := by
    rw [hQ, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl,
      mul_one]
    ring
  have hQdeg : Q.natDegree ≤ d := by
    refine Polynomial.natDegree_add_le_of_degree_le hdeg ?_
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hmonic : Q.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one d hQdeg hcoeffd
  have hcd : (OkaRing.germ hy').toRingHom (Q₀.coeff d) = 1 := by
    have h3 := congrArg (fun p ↦ p.coeff d) hmap
    simp only [Polynomial.coeff_map] at h3
    rw [h3]
    exact hg
  refine ⟨V, hy', Q, ?_, hmonic, ?_⟩
  · rw [hQ, Polynomial.map_add, hmap, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, map_sub, map_one, hcd, sub_self, Polynomial.C_0, zero_mul, add_zero]
  · refine le_antisymm hQdeg ?_
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeffd]; exact one_ne_zero)

open Polynomial in
/-- A local Weierstrass polynomial is the coefficientwise germ at the origin of a Weierstrass
polynomial over the holomorphic functions on a neighbourhood of the origin. -/
lemma exists_isWeierstrassPolynomial_realize {g : (LocalOkaRing (Fin n))[X]}
    (hg : IsLocalWeierstrassPolynomial
      (g.map (Subring.subtype (localOkaSubring (Fin n)).toSubring))) :
    ∃ (V : Opens (Fin n → ℂ)) (h0 : (0 : Fin n → ℂ) ∈ V) (Q : (OkaRing V)[X]),
      Q.map (OkaRing.germ h0).toRingHom = g ∧ IsWeierstrassPolynomial V Q := by
  have hinj : Function.Injective (Subring.subtype (localOkaSubring (Fin n)).toSubring) :=
    fun a b hab ↦ Subtype.ext hab
  have hgmonic : g.Monic := (Function.Injective.monic_map_iff hinj).mpr hg.monic
  obtain ⟨V, h0, Q, hmap, hQmonic, hQdeg⟩ := exists_poly_map_germ_monic hgmonic 0
  refine ⟨V, h0, Q, hmap, hQmonic, ?_⟩
  intro i hi
  have hi' : i < Q.natDegree := by
    have h1 := lt_of_lt_of_le hi Polynomial.degree_le_natDegree
    exact_mod_cast h1
  have hdeg2 : (i : WithBot ℕ) <
      (g.map (Subring.subtype (localOkaSubring (Fin n)).toSubring)).degree := by
    rw [Polynomial.degree_map_eq_of_injective hinj,
      Polynomial.degree_eq_natDegree hgmonic.ne_zero]
    exact_mod_cast hQdeg ▸ hi'
  have hzero := hg.apply_zero i hdeg2
  rw [Polynomial.coeff_map] at hzero
  have hgi : OkaRing.germ h0 (Q.coeff i) = g.coeff i := by
    have := congrArg (fun p ↦ p.coeff i) hmap
    simpa using this
  rw [(Q.coeff i).toGlobalFun_apply h0]
  have h5 : LocalOkaRing.constantCoeff (OkaRing.germ h0 (Q.coeff i)) =
      OkaRing.evalHom h0 (Q.coeff i) := OkaRing.constantCoeff_germ h0 (Q.coeff i)
  rw [hgi] at h5
  rw [show (Q.coeff i).toFun _ ⟨0, h0⟩ = OkaRing.evalHom h0 (Q.coeff i) from rfl, ← h5]
  exact hzero

end LocalOkaRing

end GermPoly

section Slice

/-- If the holomorphic function attached to a polynomial `P` vanishes near a point of the
cylinder, then the coefficients of `P` vanish on a neighbourhood of the base point: a
polynomial in the last variable vanishing on an open set vanishes coefficientwise. -/
lemma Polynomial.exists_map_restrict_eq_zero {V : Opens (Fin n → ℂ)} (P : (OkaRing V)[X])
    {W : Opens (Fin (n + 1) → ℂ)} (hWV : W ≤ V.extend') {y : Fin (n + 1) → ℂ} (hy : y ∈ W)
    (h : OkaRing.restrict hWV (Polynomial.toOkaRing V P) = 0) :
    ∃ (V' : Opens (Fin n → ℂ)) (hV' : V' ≤ V), Fin.init y ∈ V' ∧
      P.map (OkaRing.restrict hV').toRingHom = 0 := by
  classical
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp W.isOpen y hy
  set u' : Fin (n + 1) → Set ℂ := fun i ↦ if i ∈ I then u i else Set.univ with hu'
  have hu'open : ∀ i, IsOpen (u' i) := fun i ↦ by
    rw [hu']
    dsimp only
    split
    · exact (hu i ‹_›).1
    · exact isOpen_univ
  have hyu' : ∀ i, y i ∈ u' i := fun i ↦ by
    rw [hu']
    dsimp only
    split
    · exact (hu i ‹_›).2
    · trivial
  have hpi : ∀ x : Fin (n + 1) → ℂ, (∀ i, x i ∈ u' i) → x ∈ W := by
    intro x hx
    refine hsub fun i hi ↦ ?_
    have h1 := hx i
    rw [hu'] at h1
    dsimp only at h1
    rwa [if_pos (by simpa using hi)] at h1
  set B : Opens (Fin n → ℂ) := ⟨Set.pi Set.univ (fun i : Fin n ↦ u' i.castSucc),
    isOpen_set_pi Set.finite_univ fun i _ ↦ hu'open _⟩ with hB
  refine ⟨V ⊓ B, inf_le_left, ⟨Opens.mem_extend'.mp (hWV hy), fun i _ ↦ hyu' _⟩, ?_⟩
  refine Polynomial.ext fun k ↦ ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  apply OkaRing.ext
  funext z
  have hzV : z.1 ∈ V := z.2.1
  have hzB : ∀ i : Fin n, z.1 i ∈ u' i.castSucc := fun i ↦ z.2.2 i (Set.mem_univ i)
  -- the one variable polynomial at the base point `z`
  set pz : ℂ[X] := P.map (OkaRing.evalHom hzV) with hpz
  have hroots : ∀ ζ ∈ u' (Fin.last n), pz.IsRoot ζ := by
    intro ζ hζ
    have hxW : Fin.snoc z.1 ζ ∈ W := by
      refine hpi _ fun i ↦ ?_
      induction i using Fin.lastCases with
      | last => rwa [Fin.snoc_last]
      | cast j => rw [Fin.snoc_castSucc]; exact hzB j
    have h0 : OkaRing.evalHom hxW (OkaRing.restrict hWV (Polynomial.toOkaRing V P)) = 0 := by
      rw [h, map_zero]
    rw [OkaRing.evalHom_restrict, OkaRing.evalHom_toOkaRing (hWV hxW)] at h0
    have hpt : Fin.init (Fin.snoc z.1 ζ : Fin (n + 1) → ℂ) = z.1 := by simp
    have hcast : Polynomial.eval₂
        (OkaRing.evalHom (Opens.mem_extend'.mp (hWV hxW)))
        ((Fin.snoc z.1 ζ : Fin (n + 1) → ℂ) (Fin.last n)) P =
        Polynomial.eval₂ (OkaRing.evalHom hzV) ζ P := by
      have hhom : OkaRing.evalHom (U := V) (Opens.mem_extend'.mp (hWV hxW)) =
          OkaRing.evalHom hzV :=
        RingHom.ext fun a ↦ OkaRing.evalHom_congr _ _ hpt a
      rw [hhom, Fin.snoc_last]
    rw [hcast, Polynomial.eval₂_eq_eval_map] at h0
    exact h0
  have hinf : Set.Infinite (u' (Fin.last n)) :=
    infinite_of_mem_nhds (y (Fin.last n))
      ((hu'open (Fin.last n)).mem_nhds (hyu' (Fin.last n)))
  have hpz0 : pz = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot pz (hinf.mono fun ζ hζ ↦ hroots ζ hζ)
  have hck : OkaRing.evalHom hzV (P.coeff k) = 0 := by
    have h2 := congrArg (fun p : ℂ[X] ↦ p.coeff k) hpz0
    simpa [hpz] using h2
  exact hck

end Slice

section LineDirection

/-!
### Choosing a good direction

Given finitely many nonzero germs at the origin, there is a direction `v`, not orthogonal to
the last coordinate axis, along which no germ vanishes identically. After the linear change of
coordinates `lineEquiv` this makes all the germs general in the last variable.
-/

open MvPowerSeries

variable {ι : Type*} [Fintype ι]

/-- If the function represented by `P` vanishes along the line spanned by `v` near the origin,
all homogeneous parts of `P` vanish at `v`. -/
theorem MvPowerSeries.Represents.homogeneous_eval_eq_zero [DecidableEq ι]
    {P : MvPowerSeries ι ℂ} {F : (ι → ℂ) → ℂ} (hP : P.Represents F) (v : ι → ℂ)
    (hv : ∀ᶠ t : ℂ in nhds 0, F (t • v) = 0) (k : ℕ) :
    ∑ d ∈ degFinset ι k, coeff d P * evalMonomial d v = 0 := by
  have hconv := hP.locallyConvergent
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hP.and hconv)
  set ρ : ℝ := ε / 2 with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hmem : ∀ x : ι → ℂ, ‖x‖ ≤ ρ → HasSum (P.term x) (F x) ∧ P.SummableAt x := by
    intro x hx
    refine hball ?_
    rw [mem_ball_zero_iff]
    calc ‖x‖ ≤ ρ := hx
      _ < ε := by rw [hρdef]; linarith
  set l : ℝ := ρ / (‖v‖ + 1) with hl
  have hl0 : 0 < l := by positivity
  set y₀ : ι → ℂ := (l : ℂ) • v with hy₀
  have hy₀ρ : ‖y₀‖ ≤ ρ := by
    rw [hy₀, norm_smul, Complex.norm_real, Real.norm_of_nonneg hl0.le, hl,
      div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg v, hρ0]
  -- the coefficients of the one variable restriction to the line through `y₀`
  set a : ℕ → ℂ := fun m ↦ ∑ d ∈ degFinset ι m, coeff d P * evalMonomial d y₀ with ha
  have ha0 : ∀ m, a m = 0 := by
    refine eq_zero_of_hasSum_zero (C := ∑' d, ‖P.term y₀ d‖) (fun m ↦ ?_) ?_
    · calc ‖a m‖ ≤ ∑ d ∈ degFinset ι m, ‖P.term y₀ d‖ := by
            rw [ha]
            exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun d _ ↦ rfl))
        _ ≤ ∑' d, ‖P.term y₀ d‖ :=
            le_hasSum (hasSum_degree_norm (hmem y₀ hy₀ρ).2) m fun _ _ ↦
              Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    · have hcont : Filter.Tendsto (fun t : ℂ ↦ t * (l : ℂ)) (nhds 0) (nhds 0) := by
        have h1 : Continuous (fun t : ℂ ↦ t * (l : ℂ)) := continuous_id.mul continuous_const
        have h2 := h1.tendsto 0
        rwa [zero_mul] at h2
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos, hcont.eventually hv] with t ht htl
      rw [mem_ball_zero_iff] at ht
      have hty : ‖t • y₀‖ ≤ ρ := by
        rw [norm_smul]
        calc ‖t‖ * ‖y₀‖ ≤ 1 * ρ :=
              mul_le_mul ht.le hy₀ρ (norm_nonneg _) zero_le_one
          _ = ρ := one_mul ρ
      have hFty : F (t • y₀) = 0 := by
        have h3 : t • y₀ = (t * (l : ℂ)) • v := by rw [hy₀, smul_smul]
        rw [h3]
        exact htl
      have h4 := hasSum_degree (hmem (t • y₀) hty).1
      rw [hFty] at h4
      have hfun : (fun m ↦ ∑ d ∈ degFinset ι m, P.term (t • y₀) d) =
          fun m ↦ a m * t ^ m := by
        funext m
        rw [ha, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d hd ↦ ?_
        rw [term, evalMonomial_smul, mem_degFinset.mp hd]
        ring
      rwa [hfun] at h4
  -- homogeneity in the scaling factor `l`
  have hk := ha0 k
  simp only [ha] at hk
  have h5 : ∑ d ∈ degFinset ι k, coeff d P * evalMonomial d y₀ =
      (l : ℂ) ^ k * ∑ d ∈ degFinset ι k, coeff d P * evalMonomial d v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [hy₀, evalMonomial_smul, mem_degFinset.mp hd]
    ring
  rw [h5] at hk
  exact (mul_eq_zero.mp hk).resolve_left
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hl0.ne'))

/-- Finitely many nonzero power series admit a common direction `v`, transverse to the
hyperplane of the first `n` coordinates, at which some homogeneous part of each of them does
not vanish. -/
theorem MvPowerSeries.exists_direction {p : ℕ}
    (P : Fin p → MvPowerSeries (Fin (n + 1)) ℂ) (hP : ∀ i, P i ≠ 0) :
    ∃ v : Fin (n + 1) → ℂ, v (Fin.last n) ≠ 0 ∧
      ∀ i, ∃ k, ∑ d ∈ degFinset (Fin (n + 1)) k, coeff d (P i) * evalMonomial d v ≠ 0 := by
  classical
  have hex : ∀ i, ∃ d, coeff d (P i) ≠ 0 := fun i ↦ by
    by_contra hc
    push Not at hc
    exact hP i (MvPowerSeries.ext fun d ↦ by rw [hc d, map_zero])
  choose D hD using hex
  set k : Fin p → ℕ := fun i ↦ ∑ j, D i j with hk
  set hpol : Fin p → MvPolynomial (Fin (n + 1)) ℂ := fun i ↦
    ∑ e ∈ degFinset (Fin (n + 1)) (k i), MvPolynomial.monomial e (coeff e (P i)) with hhp
  have hh : ∀ i, hpol i ≠ 0 := by
    intro i hzero
    have h3 := congrArg (MvPolynomial.coeff (D i)) hzero
    rw [hhp] at h3
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
      MvPolynomial.coeff_zero] at h3
    rw [Finset.sum_ite_eq' (degFinset (Fin (n + 1)) (k i)) (D i)
      (fun e ↦ coeff e (P i))] at h3
    rw [if_pos (self_mem_degFinset (D i))] at h3
    exact hD i h3
  set q : MvPolynomial (Fin (n + 1)) ℂ := MvPolynomial.X (Fin.last n) * ∏ i, hpol i with hq
  have hq0 : q ≠ 0 :=
    mul_ne_zero (MvPolynomial.X_ne_zero _) (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hh i)
  obtain ⟨v, hv⟩ : ∃ v, MvPolynomial.eval v q ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hq0 (MvPolynomial.funext fun v ↦ by rw [hc v, map_zero])
  rw [hq, map_mul, MvPolynomial.eval_X, map_prod] at hv
  have hvlast : v (Fin.last n) ≠ 0 := left_ne_zero_of_mul hv
  have hvh : ∀ i, MvPolynomial.eval v (hpol i) ≠ 0 := fun i ↦
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hv) i (Finset.mem_univ i)
  refine ⟨v, hvlast, fun i ↦ ⟨k i, ?_⟩⟩
  have heval : MvPolynomial.eval v (hpol i) =
      ∑ e ∈ degFinset (Fin (n + 1)) (k i), coeff e (P i) * evalMonomial e v := by
    rw [hhp]
    dsimp only
    rw [map_sum]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [MvPolynomial.eval_monomial]
    rfl
  rw [← heval]
  exact hvh i

/-- If the partial evaluation of `P` along the `i`-th axis vanishes, so does the represented
function along that axis, near the origin. -/
theorem MvPowerSeries.Represents.eventually_axis_eq_zero {ι : Type*} [Finite ι] [DecidableEq ι]
    {P : MvPowerSeries ι ℂ}
    {F : (ι → ℂ) → ℂ} (hP : P.Represents F) (i : ι) (h : partialEval i P = 0) :
    ∀ᶠ t : ℂ in nhds 0, F (t • Pi.single i 1) = 0 := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have htend : Filter.Tendsto (fun t : ℂ ↦ t • Pi.single i (1 : ℂ)) (nhds 0) (nhds 0) := by
    have h1 : Continuous (fun t : ℂ ↦ t • Pi.single i (1 : ℂ)) :=
      continuous_id.smul continuous_const
    have h2 := h1.tendsto 0
    rwa [zero_smul] at h2
  filter_upwards [htend.eventually hP] with t ht
  have hvan : ∀ d ∉ Set.range (fun m : ℕ ↦ Finsupp.single i m),
      P.term (t • Pi.single i (1 : ℂ)) d = 0 := by
    intro d hd
    have hj : ∃ j, j ≠ i ∧ d j ≠ 0 := by
      by_contra hc
      push Not at hc
      refine hd ⟨d i, ?_⟩
      change Finsupp.single i (d i) = d
      refine Finsupp.ext fun j ↦ ?_
      rcases eq_or_ne j i with rfl | hj
      · rw [Finsupp.single_eq_same]
      · rw [Finsupp.single_apply, if_neg fun hij ↦ hj hij.symm]
        exact (hc j hj).symm
    obtain ⟨j, hji, hdj⟩ := hj
    rw [term]
    have hev : evalMonomial d (t • Pi.single i (1 : ℂ)) = 0 := by
      rw [evalMonomial_eq_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [Pi.smul_apply, Pi.single_eq_of_ne hji, smul_zero]
      exact zero_pow hdj
    rw [hev, mul_zero]
  have h2 := (Function.Injective.hasSum_iff (Finsupp.single_injective i) hvan).mpr ht
  have hfun : P.term (t • Pi.single i (1 : ℂ)) ∘ (fun m : ℕ ↦ Finsupp.single i m) =
      fun _ ↦ (0 : ℂ) := by
    funext m
    rw [Function.comp_apply, term]
    have hc : coeff (Finsupp.single i m) P = 0 := by
      have h3 := congrArg (PowerSeries.coeff m) h
      rwa [coeff_partialEval, map_zero] at h3
    rw [hc, zero_mul]
  rw [hfun] at h2
  exact (h2.unique hasSum_zero).symm ▸ rfl

/-- A linear automorphism of `ℂ^{n+1}` whose inverse maps the last coordinate axis onto the
line spanned by a vector `v` with `v_last ≠ 0`. -/
noncomputable def lineEquiv (v : Fin (n + 1) → ℂ) (hv : v (Fin.last n) ≠ 0) :
    (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ) := by
  refine (LinearEquiv.ofLinear
    (LinearMap.id - (LinearMap.proj (Fin.last n)).smulRight
      ((v (Fin.last n))⁻¹ • (v - Pi.single (Fin.last n) 1)))
    (LinearMap.id + (LinearMap.proj (Fin.last n)).smulRight (v - Pi.single (Fin.last n) 1))
    ?_ ?_).toContinuousLinearEquiv
  · -- τ ∘ σ = id
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    have hlast : (x + x (Fin.last n) • (v - Pi.single (Fin.last n) (1 : ℂ)) :
        Fin (n + 1) → ℂ) (Fin.last n) = x (Fin.last n) * v (Fin.last n) := by
      rw [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, smul_eq_mul]
      ring
    rw [hlast, smul_smul]
    have hcoeff : x (Fin.last n) * v (Fin.last n) * (v (Fin.last n))⁻¹ = x (Fin.last n) := by
      field_simp
    rw [hcoeff, add_sub_cancel_right]
  · -- σ ∘ τ = id
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    have hlast : (x - x (Fin.last n) •
        ((v (Fin.last n))⁻¹ • (v - Pi.single (Fin.last n) (1 : ℂ))) :
        Fin (n + 1) → ℂ) (Fin.last n) = x (Fin.last n) * (v (Fin.last n))⁻¹ := by
      rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same,
        smul_eq_mul, smul_eq_mul]
      field_simp
      ring
    rw [hlast, smul_smul, sub_add_cancel]

/-- The inverse of `lineEquiv` sends the last coordinate axis to the line spanned by `v`. -/
lemma lineEquiv_symm_smul_single (v : Fin (n + 1) → ℂ) (hv : v (Fin.last n) ≠ 0) (t : ℂ) :
    (lineEquiv v hv).symm (t • Pi.single (Fin.last n) 1) = t • v := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  change t • Pi.single (Fin.last n) (1 : ℂ) =
    t • v - (t • v) (Fin.last n) • ((v (Fin.last n))⁻¹ • (v - Pi.single (Fin.last n) (1 : ℂ)))
  rw [Pi.smul_apply, smul_eq_mul, smul_smul, mul_assoc, mul_inv_cancel₀ hv, mul_one,
    smul_sub, sub_sub_cancel]

end LineDirection

section GermPolyMore

open MvPowerSeries

variable {n : ℕ}

/-- Being a member of `Polynomial.degreeLT R d` bounds the `natDegree` when `0 < d`. -/
lemma Polynomial.natDegree_lt_of_mem_degreeLT {R : Type*} [CommRing R] {d : ℕ} (hd : 0 < d)
    {g : R[X]} (hg : g ∈ Polynomial.degreeLT R d) : g.natDegree < d := by
  rcases eq_or_ne g 0 with rfl | hg0
  · simpa using hd
  · exact (Polynomial.natDegree_lt_iff_degree_lt hg0).mpr (Polynomial.mem_degreeLT.mp hg)

namespace OkaRing

variable {V : Opens (Fin n → ℂ)} {y' : Fin n → ℂ}

/-- Taking polynomial germs commutes with restriction of the coefficients. -/
lemma germPoly_map_restrict {V' : Opens (Fin n → ℂ)} (h : V' ≤ V) (hy' : y' ∈ V') (w : ℂ)
    (R : (OkaRing V)[X]) :
    germPoly hy' w (R.map (restrict h).toRingHom) = germPoly (h hy') w R := by
  rw [germPoly_eq_taylor, germPoly_eq_taylor, Polynomial.map_map]
  have hcomp : (germ hy').toRingHom.comp (restrict h).toRingHom = (germ (h hy')).toRingHom :=
    RingHom.ext fun a ↦ germ_restrict h hy' a
  rw [hcomp]

end OkaRing

namespace LocalOkaRing

open OkaRing

/-- Every polynomial over the germ ring arises as the polynomial germ, at any prescribed point
of the cylinder, of a polynomial over the holomorphic functions near the base point. -/
lemma exists_poly_germPoly (g : (LocalOkaRing (Fin n))[X]) (y' : Fin n → ℂ) (w : ℂ) :
    ∃ (V' : Opens (Fin n → ℂ)) (hy' : y' ∈ V') (R : (OkaRing V')[X]),
      OkaRing.germPoly hy' w R = g ∧ R.natDegree ≤ g.natDegree := by
  obtain ⟨V', hy', R, hmap, hdeg⟩ :=
    exists_poly_map_germ
      (Polynomial.taylor (-(algebraMap ℂ (LocalOkaRing (Fin n)) w)) g) y'
  refine ⟨V', hy', R, ?_, by rwa [Polynomial.natDegree_taylor] at hdeg⟩
  rw [OkaRing.germPoly_eq_taylor, hmap, Polynomial.taylor_taylor, add_neg_cancel,
    Polynomial.taylor_zero]

end LocalOkaRing

/-- Weierstrass polynomials restrict to Weierstrass polynomials. -/
lemma IsWeierstrassPolynomial.map_restrict {V V' : Opens (Fin n → ℂ)} (h : V' ≤ V)
    (h0 : (0 : Fin n → ℂ) ∈ V') {Q : (OkaRing V)[X]} (hQ : IsWeierstrassPolynomial V Q) :
    IsWeierstrassPolynomial V' (Q.map (OkaRing.restrict h).toRingHom) := by
  haveI : Nontrivial (OkaRing V') := OkaRing.nontrivial h0
  haveI : Nontrivial (OkaRing V) := OkaRing.nontrivial (h h0)
  have hdeg : (Q.map (OkaRing.restrict h).toRingHom).degree = Q.degree := by
    rw [Polynomial.degree_eq_natDegree
        (hQ.monic.map (OkaRing.restrict h).toRingHom).ne_zero,
      Polynomial.degree_eq_natDegree hQ.monic.ne_zero,
      hQ.monic.natDegree_map]
  refine ⟨hQ.monic.map _, fun j hj ↦ ?_⟩
  rw [hdeg] at hj
  have hzero := hQ.apply_zero j hj
  rw [(Q.coeff j).toGlobalFun_apply (h h0)] at hzero
  rw [Polynomial.coeff_map, OkaRing.toGlobalFun_apply _ h0]
  exact hzero

end GermPolyMore

end
