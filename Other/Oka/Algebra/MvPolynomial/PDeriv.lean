/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Other.Oka.Algebra.MvPolynomial.Taylor

/-!
# The linear Taylor coefficients of a multivariate polynomial are its partial derivatives

Material for `Mathlib/Algebra/MvPolynomial/PDeriv.lean`; see `README.md` on the mirror tree.

`Other/Oka/Algebra/MvPolynomial/Taylor.lean` shifts the variables ; `MvPolynomial.taylorAlgHom z` is
`p ↦ p(x + z)` ; and its module docstring says the coefficients of the image are the Taylor
coefficients of `p` at `z`. It states that for the constant term
(`MvPolynomial.constantCoeff_taylorAlgHom`) and cannot state it for any other, because a Taylor
coefficient beyond the constant one is a derivative and `MvPolynomial.pderiv` is not in that
file's import closure. This file is the degree-one case, and it is a separate file for exactly
that reason: `Mathlib.Algebra.MvPolynomial.PDeriv` costs **118 Mathlib modules** against
`Mathlib/Algebra/MvPolynomial/Eval.lean`'s closure, which is what
`Other/Oka/Algebra/MvPolynomial/Taylor.lean` imports, and **0** against
`Mathlib/Algebra/MvPolynomial/PDeriv.lean`'s own, which is what this file mirrors ;
both measured with `scripts/import_cost.py`. The mirror layering therefore matches the layering
an upstreamed pair of files would have.

## Main results

- `MvPolynomial.coeff_single_one_taylorAlgHom`: **the coefficient of `xᵢ` in `p(x + z)` is
  `∂p/∂xᵢ` evaluated at `z`.**

## What is not here

**No higher Taylor coefficient.** The coefficient at `Finsupp.single i k` is `∂ᵏp/∂xᵢᵏ` at `z`
divided by `k!`, which needs the base ring to have the factorials invertible and is a different
statement; and the coefficient at a general exponent is a mixed partial. Only the degree-one case
is used, by `LocalOkaRing.coeff_single_one_ofMvPolynomial` in `Other/Oka/Polynomial/Germ.lean`, and it
is the only one that needs no hypothesis on `R` at all.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- **The linear Taylor coefficient is the partial derivative**: the coefficient of `xᵢ` in
`p(x + z)` is `∂p/∂xᵢ` evaluated at `z`.

Both sides are additive in `p` and agree on constants, so the content is the multiplication step,
and there `MvPolynomial.coeff_mul_X'` splits on whether the variable being multiplied in is `i`:
if it is, the surviving coefficient is the constant term of `p(x + z)`, which is
`MvPolynomial.constantCoeff_taylorAlgHom`, and it matches the term
`MvPolynomial.pderiv_X_self` contributes on the other side; if it is not, both extra terms
vanish. The induction is `MvPolynomial.induction_on`, so no monomial expansion appears.

`MvPolynomial.coeff_mul_X'` decides membership in a `Finsupp.support`, so the proof opens
`classical`; the statement needs no `DecidableEq σ` and the `unusedDecidableInType` linter is
what says so. -/
theorem coeff_single_one_taylorAlgHom (z : σ → R) (i : σ) (p : MvPolynomial σ R) :
    coeff (Finsupp.single i 1) (taylorAlgHom z p) = eval z (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [taylorAlgHom_C, coeff_C, pderiv_C, map_zero]
      exact if_neg fun h ↦ by simpa using h.symm
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      rw [map_mul, taylorAlgHom_X, mul_add, coeff_add, coeff_mul_X', mul_comm _ (C (z j)),
        coeff_C_mul, hp, pderiv_mul, map_add, eval_mul, eval_mul, eval_X]
      by_cases h : j = i
      · subst h
        rw [if_pos (by simp), tsub_self, ← constantCoeff_eq, constantCoeff_taylorAlgHom,
          pderiv_X_self, map_one]
        ring
      · rw [if_neg (by simpa using h), pderiv_X_of_ne h, map_zero]
        ring

end MvPolynomial

end
