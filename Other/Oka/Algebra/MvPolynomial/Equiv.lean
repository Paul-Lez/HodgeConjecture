/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Evaluating through `MvPolynomial.optionEquivLeft`

`MvPolynomial.optionEquivLeft R σ`, the algebra equivalence
`MvPolynomial (Option σ) R ≃ₐ[R] Polynomial (MvPolynomial σ R)`, makes
the variable `none` the polynomial variable and the variables `some s` the coefficients. This file
adds the one lemma that says what that does to evaluation: evaluating at a point of
`Option σ → R` is evaluating the coefficients at its restriction along `some` and then evaluating
the resulting one-variable polynomial at its value on `none`.

`Mathlib/Algebra/MvPolynomial/Equiv.lean` has this for `MvPolynomial.finSuccEquiv`
(`MvPolynomial.eval_eq_eval_mv_eval'`) and not for the `Option` equivalence it is built from, so
a caller whose splitting of the variables is not `Fin.cons` cannot use it. The proof here is the
proof of that lemma with `Fin.cases` replaced by `Option.rec`.

## Main results

- `MvPolynomial.eval_eq_eval_optionEquivLeft`: **evaluating at a point of `Option σ → R` is
  evaluating the coefficients along `some` and the resulting one-variable polynomial at the
  value on `none`.**
-/

@[expose] public section

namespace MvPolynomial

variable {R : Type*} [CommSemiring R] {σ : Type*}

/-- **Evaluation through `MvPolynomial.optionEquivLeft`**: the variables `some s` are evaluated
into the coefficients and the variable `none` into the polynomial variable.

This is `MvPolynomial.eval_eq_eval_mv_eval'` for the `Option` splitting rather than the
`Fin.cons` one. -/
theorem eval_eq_eval_optionEquivLeft (x : Option σ → R) (p : MvPolynomial (Option σ) R) :
    eval x p =
      Polynomial.eval (x none)
        (Polynomial.map (eval (x ∘ some)) (optionEquivLeft R σ p)) := by
  let φ : Polynomial (MvPolynomial σ R) →ₐ[R] Polynomial R :=
    { Polynomial.mapRingHom (eval (x ∘ some)) with
      commutes' := fun r ↦ by
        convert! Polynomial.map_C (eval (x ∘ some))
        exact (eval_C _).symm }
  change aeval x p = (Polynomial.aeval (x none)).comp (φ.comp (optionEquivLeft R σ).toAlgHom) p
  congr 2
  apply MvPolynomial.algHom_ext
  rintro (_ | s) <;> simp [φ]

end MvPolynomial

end
