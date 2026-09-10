/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.SignTest

/-!
# R3a — the planar Wirtinger chain rule for `∂̄` along a holomorphic map

Lane R rung R3, first half (S3 scoping §4.R3, `docs/planning/S3_FINESHEAF_RES_SCOPING.md`;
campaign `docs/planning/CAMPAIGN_KEYSTONE.md`).  Completes the planar `∂̄` calculus started by
the R0 Leibniz rule `dbar_mul`: this file adds the composition law

  `∂̄(f ∘ φ)(z) = ∂̄f(φ z) · conj φ′(z)`   (`dbar_comp`)

for `φ` holomorphic at `z` and `f` merely `ℝ`-differentiable at `φ z`.

Placement: a separate file rather than an extension of `SignTest.lean`, because `SignTest` is the
frozen R0 sign/normalization **gate** ("cite this, do not re-derive") — R3 calculus layers on top
of it without touching the pinned conventions.  Importing `SignTest` keeps the planar `∂̄`
calculus (`dbar_mul` → `dbar_comp`) linearly ordered for downstream consumers (Glue, R4–R6).

## Why `conj φ′`

`∂̄` is the `dz̄`-component of the real differential.  Precomposition with a holomorphic `φ`
pulls `dz̄` back to `conj φ′ · dz̄`, so `∂̄` of a chart-read function transforms across a
holomorphic transition as a **(0,1)** chart coefficient — factor `conj φ′` exactly.  The
companion factor `φ′` of the `(1,1)` law `OneOneLawAt` (R1) is *not* produced by this chain
rule: it comes from the holomorphic change of the `dz`-slot (the `(1,0)` coefficient family of
`Glue.lean`), and `φ′ · conj φ′ = normSq φ′` reassembles R1's factor.

Proof shape: `fderiv_comp`, plus the fact that the real Fréchet derivative of a holomorphic map
is complex multiplication by `φ′(z)` (`HasDerivAt.complexToReal_fderiv` — the same atom
`DbarDisk.dbar_eq_zero_of_differentiableAt` is built on); the Wirtinger combination
`½(D 1 + i·D i)` is then evaluated by decomposing the (only `ℝ`-linear!) derivative `D` of `f`
over the real basis `1, i`.
-/

open Complex

namespace Jacobians.Dolbeault.FineResidue

open DbarDisk

/-- **Planar Wirtinger chain rule.**  If `φ` is holomorphic at `z` and `f` is (merely)
`ℝ`-differentiable at `φ z`, then

  `∂̄(f ∘ φ)(z) = ∂̄f(φ z) · conj φ′(z)`.

Precomposition with a holomorphic map transforms `∂̄` by the **anti-holomorphic** derivative
factor `conj φ′` — the `(0,1)` (`dz̄`-slot) covariance.  Composition counterpart of the R0
Leibniz rule `dbar_mul`; the analytic half of the `(1,1)` glue law (`Glue.lean`). -/
theorem dbar_comp {f φ : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f (φ z))
    (hφ : DifferentiableAt ℂ φ z) :
    dbar (f ∘ φ) z = dbar f (φ z) * (starRingEnd ℂ) (deriv φ z) := by
  have hφℝ : DifferentiableAt ℝ φ z := hφ.restrictScalars ℝ
  have hcomp : fderiv ℝ (f ∘ φ) z = (fderiv ℝ f (φ z)).comp (fderiv ℝ φ z) :=
    fderiv_comp z hf hφℝ
  -- The real derivative of the holomorphic `φ` is complex multiplication by `φ′(z)`.
  have hφr : fderiv ℝ φ z = deriv φ z • (1 : ℂ →L[ℝ] ℂ) :=
    hφ.hasDerivAt.complexToReal_fderiv.fderiv
  -- The `ℝ`-linear derivative of `f` is determined by its values on the real basis `1, I`.
  have hdec : ∀ a : ℂ, fderiv ℝ f (φ z) a
      = (a.re : ℂ) * fderiv ℝ f (φ z) 1 + (a.im : ℂ) * fderiv ℝ f (φ z) I := by
    intro a
    have ha : a.re • (1 : ℂ) + a.im • I = a := by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
    conv_lhs => rw [← ha]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have hconj : (starRingEnd ℂ) (deriv φ z)
      = ((deriv φ z).re : ℂ) - ((deriv φ z).im : ℂ) * I := by
    simp [Complex.ext_iff]
  unfold DbarDisk.dbar
  rw [hcomp, hφr]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul, mul_one]
  rw [hdec (deriv φ z), hdec (deriv φ z * I), hconj]
  simp only [Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_neg]
  linear_combination (2⁻¹ * ((deriv φ z).im : ℂ) * fderiv ℝ f (φ z) I) * Complex.I_sq

end Jacobians.Dolbeault.FineResidue
