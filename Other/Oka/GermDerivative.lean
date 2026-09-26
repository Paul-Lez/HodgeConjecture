/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Weierstrass

/-!
# The linear coefficients of a germ are the partial derivatives at the point

`OkaRing.germ hy f` is the Taylor series of a holomorphic function `f` at a point `y` of its
domain (`Other/Oka/Weierstrass.lean`). This file identifies its coefficient at `Finsupp.single j 1`
with the derivative of `f` at `y` in the `j`-th coordinate direction ;
`fderiv ℂ (f.toGlobalFun U) y (Pi.single j 1)`.

**This is for an arbitrary holomorphic function**, and that is the point.
`Other/Oka/AnalyticSpace/SimpleZeroPolynomial.lean` identifies the same coefficient with
`MvPolynomial.pderiv` when the germ comes from a polynomial, and `Other/Oka/Regular.lean`'s
§*Why the hypothesis is stated with `PowerSeries.order` and not with a derivative* records that
what the tree has for a general germ is a *number at a point*. This is that number, produced from
`f` rather than from a polynomial presenting it.

## What the proof is

Three steps and no analysis of its own:

* `MvPowerSeries.LocallyConvergent.fderiv_eval_zero` (`Other/Oka/Weierstrass.lean`) says the linear
  coefficients of a locally convergent series are the partial derivatives *of its sum, at the
  origin*, and every germ satisfies its hypothesis because `LocalOkaRing ι` is by definition the
  locally convergent series (`LocalOkaRing.locallyConvergent`);
* `OkaRing.germ_represents` says that sum is `z ↦ f (z + y)` near the origin, so the two have the
  same derivative there (`Filter.EventuallyEq.fderiv_eq`);
* `fderiv_comp_add_right` moves the derivative of `z ↦ f (z + y)` at `0` to the derivative of `f`
  at `y`.

## Main results

- `OkaRing.coeff_single_one_germ`: **the coefficient of `X j` in the Taylor series of `f` at `y`
  is `fderiv ℂ (f.toGlobalFun U) y (Pi.single j 1)`.**
- `OkaRing.toGlobalFun_eq_evalHom`: the extension by zero evaluated at a point of the domain is
  the evaluation homomorphism there, which is the spelling every consumer of the above needs,
  since the sheaf-theoretic statements evaluate a section rather than a global function.

## What is not here

* **No derivative of a germ as a germ.** The right-hand side is a complex number, not an element
  of `LocalOkaRing ι`; there is still no operator `∂/∂X j : LocalOkaRing ι → LocalOkaRing ι`, and
  so "`∂f/∂X j` is a unit at the point" is still not expressible. `Other/Oka/Regular.lean` says so and
  is not falsified by this file.
* **No higher coefficients.** Only the coefficients at `Finsupp.single j 1`; nothing about
  `Finsupp.single j 2` or about mixed terms, which would be higher derivatives divided by
  factorials.
* **No statement quantified over `LocalOkaRing ι`.** The result below is about `OkaRing.germ` and
  quantifies over the holomorphic function `f`; whether every element of `LocalOkaRing ι` is such
  a germ is a surjectivity statement this file neither uses nor proves.
-/

@[expose] public section

open TopologicalSpace MvPowerSeries

noncomputable section

namespace OkaRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Opens (ι → ℂ)} {y : ι → ℂ}

omit [DecidableEq ι] in
/-- **The extension by zero of a holomorphic function, at a point of its domain, is the value of
the evaluation homomorphism there.** Both sides are `f.toFun _ ⟨y, hy⟩`; this is
`OkaRing.toGlobalFun_apply` said in the spelling the sheaf-theoretic statements use. -/
theorem toGlobalFun_eq_evalHom (f : OkaRing U) (hy : y ∈ U) :
    f.toGlobalFun U y = OkaRing.evalHom hy f :=
  OkaRing.toGlobalFun_apply f hy

/-- **The linear coefficient of the germ at `y` is the derivative at `y` in that direction.**

The germ sums to `z ↦ f (z + y)` near the origin, so its linear coefficients are the partial
derivatives of that translate at the origin, which are the partial derivatives of `f` at `y`. -/
theorem coeff_single_one_germ (hy : y ∈ U) (f : OkaRing U) (j : ι) :
    MvPowerSeries.coeff (Finsupp.single j 1)
        ((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ) =
      fderiv ℂ (f.toGlobalFun U) y (Pi.single j 1) := by
  set P : MvPowerSeries ι ℂ := ((germ hy f : LocalOkaRing ι) : MvPowerSeries ι ℂ) with hP
  have hconv : P.LocallyConvergent := (germ hy f).locallyConvergent
  have hEq : P.eval =ᶠ[nhds (0 : ι → ℂ)] fun z ↦ f.toGlobalFun U (z + y) :=
    hconv.represents_eval.eventuallyEq (germ_represents hy f)
  rw [← hconv.fderiv_eval_zero j, hEq.fderiv_eq, fderiv_comp_add_right]
  simp

end OkaRing

end
