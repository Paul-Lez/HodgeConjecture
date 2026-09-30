/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Other.Oka.StructureSheaf

/-!
# Polynomials are holomorphic

A polynomial in `ι` complex variables defines a holomorphic function on every open subset of
`ℂ^ι`, and this assignment is a `ℂ`-algebra homomorphism compatible with restriction. This is
the first step of analytification: it is what lets the equations of an affine `ℂ`-scheme be read
as holomorphic functions.

Note that this is *not* `LocalOkaRing.fromPolynomial` of `Other/Oka/LocalOkaRing.lean`, which views a
one-variable polynomial over the germs in `n` variables as a germ in `n + 1` variables. The map
here is the plain one: a polynomial function is holomorphic.

## Main definitions

- `OkaRing.ofMvPolynomial U`: the `ℂ`-algebra map `MvPolynomial ι ℂ →ₐ[ℂ] OkaRing U`.

## Main results

- `MvPolynomial.analyticAt_eval` and `MvPolynomial.analyticOn_eval`: a polynomial function on
  `ℂ^ι` is analytic.
- `OkaRing.evalHom_ofMvPolynomial`: the holomorphic function attached to `p` takes the value
  `MvPolynomial.eval x p` at `x`, which characterises `ofMvPolynomial`.
- `OkaRing.restrict_ofMvPolynomial`: `ofMvPolynomial` is compatible with restriction, i.e. it is
  a map of presheaves of `ℂ`-algebras from the constant presheaf `MvPolynomial ι ℂ`.
-/

@[expose] public section

open TopologicalSpace

variable {ι : Type*} [Fintype ι]

namespace MvPolynomial

/-- Evaluating a polynomial in `ι` complex variables is analytic at every point. -/
theorem analyticAt_eval (p : MvPolynomial ι ℂ) (x : ι → ℂ) :
    AnalyticAt ℂ (fun z : ι → ℂ ↦ MvPolynomial.eval z p) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval_C]
      exact analyticAt_const
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p i hp =>
      have hi : AnalyticAt ℂ (fun z : ι → ℂ ↦ z i) x :=
        (ContinuousLinearMap.proj (R := ℂ) i).analyticAt x
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.mul hi

/-- Evaluating a polynomial in `ι` complex variables is analytic on every set. -/
theorem analyticOn_eval (p : MvPolynomial ι ℂ) (s : Set (ι → ℂ)) :
    AnalyticOn ℂ (fun z : ι → ℂ ↦ MvPolynomial.eval z p) s :=
  fun x _ ↦ (analyticAt_eval p x).analyticWithinAt

end MvPolynomial

namespace OkaRing

variable (U : Opens (ι → ℂ))

/-- The function on `U` defined by a polynomial is holomorphic. -/
theorem okaAnalytic_eval (p : MvPolynomial ι ℂ) :
    OkaAnalytic (fun z : U ↦ MvPolynomial.eval (z : ι → ℂ) p) := by
  refine (MvPolynomial.analyticOn_eval p (U : Set (ι → ℂ))).congr fun x hx ↦ ?_
  exact Subtype.val_injective.extend_apply
    (f := (Subtype.val : U → ι → ℂ)) _ _ ⟨x, hx⟩

/-- A polynomial in `ι` complex variables, viewed as a holomorphic function on `U ⊆ ℂ^ι`.

This is the map that reads the equations of an affine `ℂ`-scheme as holomorphic functions. It
is characterised by `OkaRing.evalHom_ofMvPolynomial`. -/
noncomputable def ofMvPolynomial : MvPolynomial ι ℂ →ₐ[ℂ] OkaRing U where
  toFun p := .mk _ (okaAnalytic_eval U p)
  map_one' := Subtype.ext (funext fun z ↦ map_one (MvPolynomial.eval (z : ι → ℂ)))
  map_mul' p q := Subtype.ext (funext fun z ↦ map_mul (MvPolynomial.eval (z : ι → ℂ)) p q)
  map_zero' := Subtype.ext (funext fun z ↦ map_zero (MvPolynomial.eval (z : ι → ℂ)))
  map_add' p q := Subtype.ext (funext fun z ↦ map_add (MvPolynomial.eval (z : ι → ℂ)) p q)
  commutes' c := Subtype.ext (funext fun z ↦ MvPolynomial.eval_C (f := (z : ι → ℂ)) c)

@[simp]
lemma toFun_ofMvPolynomial (p : MvPolynomial ι ℂ) :
    (ofMvPolynomial U p).toFun U = fun z : U ↦ MvPolynomial.eval (z : ι → ℂ) p :=
  rfl

/-- The holomorphic function attached to `p` takes the value `MvPolynomial.eval x p` at `x`.
Together with `OkaRing.ext` this characterises `OkaRing.ofMvPolynomial`. -/
@[simp]
lemma evalHom_ofMvPolynomial {x : ι → ℂ} (hx : x ∈ U) (p : MvPolynomial ι ℂ) :
    OkaRing.evalHom hx (ofMvPolynomial U p) = MvPolynomial.eval x p :=
  rfl

@[simp]
lemma toGlobalFun_ofMvPolynomial {x : ι → ℂ} (hx : x ∈ U) (p : MvPolynomial ι ℂ) :
    (ofMvPolynomial U p).toGlobalFun U x = MvPolynomial.eval x p :=
  (ofMvPolynomial U p).toGlobalFun_apply hx

/-- Reading a polynomial as a holomorphic function commutes with restriction: `ofMvPolynomial`
is a map of presheaves of `ℂ`-algebras from the constant presheaf with value
`MvPolynomial ι ℂ`. -/
@[simp]
lemma restrict_ofMvPolynomial {U V : Opens (ι → ℂ)} (h : U ≤ V) (p : MvPolynomial ι ℂ) :
    OkaRing.restrict h (ofMvPolynomial V p) = ofMvPolynomial U p :=
  rfl

end OkaRing

end
