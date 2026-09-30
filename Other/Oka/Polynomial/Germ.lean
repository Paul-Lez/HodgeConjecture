/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Algebra.MvPolynomial.PDeriv
public import Other.Oka.MaximalIdeal
public import Other.Oka.Polynomial
public import Other.Oka.Weierstrass

/-!
# Germs of polynomial functions

The germ at a point `y ∈ ℂ^ι` of the holomorphic function defined by a polynomial, as a
`ℂ`-algebra map `MvPolynomial ι ℂ →ₐ[ℂ] LocalOkaRing ι`.

This is separated from `Other/Oka/Polynomial.lean` because `OkaRing.germ` lives in
`Other/Oka/Weierstrass.lean`, and "a polynomial function is holomorphic" should not depend on
Weierstrass theory.

`Other/Oka/MaximalIdeal.lean` is imported for `LocalOkaRing.coord` alone, which
`LocalOkaRing.ofMvPolynomial_zero_X` names. `Other/Oka/Analytification/Flatness.lean` used to hold that
declaration and its corollary, and said in terms that it did so *"only because the proof names
`LocalOkaRing.coord`, which lives in `Other/Oka/MaximalIdeal.lean` and is not in that file's import
closure"*. That was true; the obstacle it names is **one** `Oka` module and **zero** Mathlib
modules, since `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic` is already reached through
`Other/Oka/Weierstrass.lean`. Paying it here is what lets
`LocalOkaRing.coeff_single_one_ofMvPolynomial` be stated beside `LocalOkaRing.ofMvPolynomial`
rather than behind `Oka.Completion` and `Oka.RingTheory.Flat.Descent`, which the germ-of-a-
polynomial line has no other reason to import.

The consumer of `LocalOkaRing.coeff_single_one_ofMvPolynomial` is
`Other/Oka/AnalyticSpace/SimpleZeroPolynomial.lean`, which restates
`ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_coeff` and its three siblings with the
coefficient replaced by `MvPolynomial.pderiv`.

## Main definitions

- `LocalOkaRing.ofMvPolynomial y`: the germ at `y` of the holomorphic function defined by a
  polynomial.

## Main results

- `LocalOkaRing.constantCoeff_ofMvPolynomial`: the constant term of the germ at `y` is the
  value `MvPolynomial.eval y p`, with `LocalOkaRing.constantCoeff_coe_ofMvPolynomial` its
  `simp` normal form. In particular the germ is a unit exactly when `p` does not vanish at `y`,
  which is what identifies the zero set of a family of polynomials with the points where their
  germs are non-units.
- `LocalOkaRing.coe_ofMvPolynomial_zero`: **at the origin the germ of a polynomial is the
  polynomial**, read as a power series, with `LocalOkaRing.ofMvPolynomial_zero_X` the case of a
  variable that its proof runs on.
- `LocalOkaRing.coeff_single_one_ofMvPolynomial`: **the linear coefficient of the germ at `y` is
  a partial derivative of `p` at `y`.** It is what turns the simple-zero hypothesis of the stalk
  isomorphism of a hypersurface ; one Taylor coefficient of a germ ; into the derivative
  condition a caller holding a polynomial actually has; which statement that is, and where, is in
  the paragraph above and in this declaration's own docstring rather than here, since it is not a
  result of this file.
- `LocalOkaRing.ofMvPolynomial_taylorAlgHom`: **the germ at `y` is the germ at the origin of the
  shifted polynomial** `p(x + y)`. Since `LocalOkaRing ι` is the germ ring at the origin by
  construction, this is what lets a statement about germs at `y` be transported to one about
  germs at the origin, and it is a statement about *polynomials* only in that both sides are
  spelled with `LocalOkaRing.ofMvPolynomial`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open TopologicalSpace

variable {ι : Type*} [Fintype ι]

namespace LocalOkaRing

/-- The germ at `y` of the holomorphic function on `ℂ^ι` defined by a polynomial. -/
noncomputable def ofMvPolynomial (y : ι → ℂ) : MvPolynomial ι ℂ →ₐ[ℂ] LocalOkaRing ι :=
  (OkaRing.germ (U := ⊤) (y := y) trivial).comp (OkaRing.ofMvPolynomial ⊤)

lemma ofMvPolynomial_eq (y : ι → ℂ) (p : MvPolynomial ι ℂ) :
    ofMvPolynomial y p = OkaRing.germ (U := ⊤) (y := y) trivial (OkaRing.ofMvPolynomial ⊤ p) :=
  rfl

/-- The constant term of the germ at `y` of a polynomial is its value at `y`. -/
lemma constantCoeff_ofMvPolynomial (y : ι → ℂ) (p : MvPolynomial ι ℂ) :
    LocalOkaRing.constantCoeff (ofMvPolynomial y p) = MvPolynomial.eval y p := by
  rw [ofMvPolynomial_eq, OkaRing.constantCoeff_germ, OkaRing.evalHom_ofMvPolynomial]

/-- `constantCoeff_ofMvPolynomial` in `simp` normal form.

`LocalOkaRing.constantCoeff_apply` is itself a `simp` lemma, so `simp` rewrites
`LocalOkaRing.constantCoeff P` to `MvPowerSeries.constantCoeff ↑P` before it ever sees
`constantCoeff_ofMvPolynomial`; tagging that lemma `@[simp]` therefore does nothing. This is the
form a goal is actually in by the time `simp` gets there. -/
@[simp]
lemma constantCoeff_coe_ofMvPolynomial (y : ι → ℂ) (p : MvPolynomial ι ℂ) :
    MvPowerSeries.constantCoeff ((ofMvPolynomial y p : LocalOkaRing ι) : MvPowerSeries ι ℂ) =
      MvPolynomial.eval y p := by
  rw [← constantCoeff_apply, constantCoeff_ofMvPolynomial]

/-- The germ at `y` of a polynomial is a unit exactly when the polynomial does not vanish
at `y`. -/
lemma isUnit_ofMvPolynomial_iff (y : ι → ℂ) (p : MvPolynomial ι ℂ) :
    IsUnit (ofMvPolynomial y p) ↔ MvPolynomial.eval y p ≠ 0 := by
  rw [isUnit_iff, constantCoeff_ofMvPolynomial]

/-- **The germ at `y` of a polynomial is the germ at the origin of the polynomial shifted by
`y`.**

The germ at `y` is by definition the Taylor series at the origin of the translate of the
function (`OkaRing.germ`), and translating the *function* attached to `p` is reading the shifted
*polynomial* `p(x + y)` as a function ; which is `MvPolynomial.eval_taylorAlgHom`. So no analysis
is involved: the two ingredients are `OkaRing.germ_shift`, which moves the base point, and
`OkaRing.germ_restrict`, which crosses from `(⊤ : Opens (ι → ℂ)).shift y` back to `⊤`. -/
lemma ofMvPolynomial_taylorAlgHom (y : ι → ℂ) (p : MvPolynomial ι ℂ) :
    ofMvPolynomial (0 : ι → ℂ) (MvPolynomial.taylorAlgHom y p) = ofMvPolynomial y p := by
  have h0 : (0 : ι → ℂ) ∈ (⊤ : Opens (ι → ℂ)).shift y := by simp
  have hshift : OkaRing.shift (⊤ : Opens (ι → ℂ)) y (OkaRing.ofMvPolynomial ⊤ p) =
      OkaRing.ofMvPolynomial ((⊤ : Opens (ι → ℂ)).shift y) (MvPolynomial.taylorAlgHom y p) :=
    Subtype.ext (funext fun w ↦ (MvPolynomial.eval_taylorAlgHom y (w : ι → ℂ) p).symm)
  calc ofMvPolynomial (0 : ι → ℂ) (MvPolynomial.taylorAlgHom y p)
      = OkaRing.germ h0
          (OkaRing.restrict le_top (OkaRing.ofMvPolynomial ⊤ (MvPolynomial.taylorAlgHom y p))) :=
        (OkaRing.germ_restrict le_top h0 _).symm
    _ = OkaRing.germ h0 (OkaRing.shift ⊤ y (OkaRing.ofMvPolynomial ⊤ p)) := by
        rw [OkaRing.restrict_ofMvPolynomial, hshift]
    _ = ofMvPolynomial y p :=
        OkaRing.germ_shift (U := ⊤) y (show y ∈ (⊤ : Opens (ι → ℂ)) from trivial) h0
          (zero_add y) _

/-! ### At the origin, the germ of a polynomial is the polynomial -/

/-- The germ at the origin of the `i`-th coordinate function is the `i`-th coordinate. -/
theorem ofMvPolynomial_zero_X (i : ι) :
    ofMvPolynomial (0 : ι → ℂ) (MvPolynomial.X i) = LocalOkaRing.coord i := by
  refine OkaRing.germ_eq_of_represents (U := ⊤) (y := 0) trivial ?_
  rw [LocalOkaRing.coe_coord]
  refine (MvPowerSeries.represents_X i).congr (Filter.Eventually.of_forall fun z ↦ ?_)
  change z i = (OkaRing.ofMvPolynomial ⊤ (MvPolynomial.X i)).toGlobalFun ⊤ (z + 0)
  rw [OkaRing.toGlobalFun_ofMvPolynomial (U := ⊤) trivial]
  simp

/-- **At the origin, the germ of a polynomial is the polynomial**, read as a power series.

Both sides are `ℂ`-algebra maps out of `MvPolynomial`, so this is `MvPolynomial.algHom_ext` and
the value at a variable. It is what makes the local ring of `𝔸^ι` at the origin, the germ ring
and the formal power series comparable: all three agree on polynomials. -/
theorem coe_ofMvPolynomial_zero (p : MvPolynomial ι ℂ) :
    ((ofMvPolynomial (0 : ι → ℂ) p : LocalOkaRing ι) : MvPowerSeries ι ℂ) =
      (p : MvPowerSeries ι ℂ) := by
  have h : (localOkaSubring ι).val.comp (ofMvPolynomial (0 : ι → ℂ)) =
      MvPolynomial.coeToMvPowerSeries.algHom ℂ := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rw [AlgHom.comp_apply, ofMvPolynomial_zero_X, Subalgebra.val_apply, LocalOkaRing.coe_coord]
    simp
  exact congrArg (fun f : MvPolynomial ι ℂ →ₐ[ℂ] MvPowerSeries ι ℂ ↦ f p) h

/-! ### The linear coefficient of the germ is a partial derivative -/

/-- **The coefficient of `xᵢ` in the germ at `y` of a polynomial is `∂p/∂xᵢ` evaluated at `y`.**

Four rewrites and **no analysis at either end**: the base point moves to the origin by
`LocalOkaRing.ofMvPolynomial_taylorAlgHom`, where the germ *is* the shifted polynomial by
`LocalOkaRing.coe_ofMvPolynomial_zero`; `MvPolynomial.coeff_coe` crosses from the power series to
the polynomial; and `MvPolynomial.coeff_single_one_taylorAlgHom` reads the shifted polynomial's
linear coefficient as a derivative. In particular no derivative operator on `LocalOkaRing` is
constructed or needed, and there is still none ; the derivative here is Mathlib's
`MvPolynomial.pderiv`, on polynomials.

This is what puts the hypothesis of `ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_coeff`
into the form a caller who holds a polynomial actually has; see
`Other/Oka/AnalyticSpace/SimpleZeroPolynomial.lean`. -/
theorem coeff_single_one_ofMvPolynomial (y : ι → ℂ) (i : ι) (p : MvPolynomial ι ℂ) :
    MvPowerSeries.coeff (Finsupp.single i 1)
        ((ofMvPolynomial y p : LocalOkaRing ι) : MvPowerSeries ι ℂ) =
      MvPolynomial.eval y (MvPolynomial.pderiv i p) := by
  rw [← ofMvPolynomial_taylorAlgHom, coe_ofMvPolynomial_zero, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_single_one_taylorAlgHom]

end LocalOkaRing

end
