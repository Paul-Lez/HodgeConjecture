/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas

Ported (verbatim, with classic `import` syntax substituted for the Lean module
system) from mrdouglasny/jacobian-challenge, file
`Jacobians/Bridge/ContourDeformation.lean`, which the author in turn ported from
his sibling repository `picard-lefschetz`
(`PicardLefschetz/ContourDeformation.lean`). Both upstream repositories are
licensed under Apache 2.0; the original copyright and attribution are retained
above as required by Apache §4. The only edits are mechanical: the module-system
wrappers (`module` / `public import` / `public section`) were removed and
`public import X` rewritten to `import X` to match this repository's classic
import style. No mathematical content was changed.
-/

import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Ring

/-!
# Chart-local contour deformation

This module is ported from the author's own sibling repository
`picard-lefschetz`, file `PicardLefschetz/ContourDeformation.lean`.

It provides chart-local path-independence for holomorphic 1-forms in one
complex dimension, via Mathlib's Poincaré curve-integral homotopy lemma.
-/

namespace Jacobians.Bridge.ContourDeformation

open Complex MeasureTheory unitInterval

/-- The holomorphic 1-form `ω(z) = f(z) dz` on `ℂ`, with values in
    `ℝ`-linear maps.

    `(holoOneForm f z) v = f z * v`. -/
noncomputable def holoOneForm (f : ℂ → ℂ) : ℂ → (ℂ →L[ℝ] ℂ) :=
  fun z => ContinuousLinearMap.mul ℝ ℂ (f z)

@[simp]
lemma holoOneForm_apply (f : ℂ → ℂ) (z v : ℂ) :
    holoOneForm f z v = f z * v :=
  ContinuousLinearMap.mul_apply' ℝ ℂ (f z) v

/-- For ℂ-differentiable `f`, the Fréchet derivative of `holoOneForm f`
    at `x` is symmetric in its two ℂ arguments: this is the closedness of
    the 1-form `ω = f(z) dz`. -/
lemma holoOneForm_dOmega_symm {t : Set ℂ} (ht : IsOpen t)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f t) :
    ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ (holoOneForm f) t x u v =
      fderivWithin ℝ (holoOneForm f) t x v u := by
  intro x hx u _ v _
  have hxnhd : t ∈ nhds x := ht.mem_nhds hx
  rw [fderivWithin_of_mem_nhds hxnhd]
  have hfℂ : DifferentiableAt ℂ f x := (hf x hx).differentiableAt hxnhd
  have hωℝ : HasFDerivAt (holoOneForm f)
      ((ContinuousLinearMap.mul ℝ ℂ).comp
        ((deriv f x) • (1 : ℂ →L[ℝ] ℂ))) x :=
    (ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt.comp x
      hfℂ.hasDerivAt.complexToReal_fderiv
  rw [hωℝ.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    smul_eq_mul]
  ring

/-- Poincaré curve-integral contour deformation, abstract form. -/
theorem contourDeformation1D_abstract
    {t : Set ℂ}
    {ω : ℂ → (ℂ →L[ℝ] ℂ)}
    (hωdcc : DiffContOnCl ℝ ω t)
    (hsymm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    {a b : ℂ} {γ₁ γ₂ : Path a b}
    (φ : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hφt : ∀ a ∈ Set.Ioo (0 : I) 1, ∀ b ∈ Set.Ioo (0 : I) 1, φ (a, b) ∈ t)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Set.Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x =
    ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x :=
  φ.curveIntegral_add_curveIntegral_eq_of_diffContOnCl hφt hωdcc hsymm hcontdiff

/-- Poincaré curve-integral contour deformation specialised to `holoOneForm f`
    for holomorphic `f`. -/
theorem contourDeformation1D
    {t : Set ℂ} (ht : IsOpen t)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f t)
    (hωdcc : DiffContOnCl ℝ (holoOneForm f) t)
    {a b : ℂ} {γ₁ γ₂ : Path a b}
    (φ : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hφt : ∀ a ∈ Set.Ioo (0 : I) 1, ∀ b ∈ Set.Ioo (0 : I) 1, φ (a, b) ∈ t)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Set.Icc 0 1)) :
    ∫ᶜ x in γ₁, holoOneForm f x + ∫ᶜ x in φ.evalAt 1, holoOneForm f x =
    ∫ᶜ x in γ₂, holoOneForm f x + ∫ᶜ x in φ.evalAt 0, holoOneForm f x :=
  contourDeformation1D_abstract hωdcc (holoOneForm_dOmega_symm ht hf) φ hφt hcontdiff

/-- The side curve integral at `s = 0` along a `Path.Homotopy` vanishes. -/
lemma curveIntegral_pathHomotopy_evalAt_zero_eq_zero
    {a b : ℂ} {γ₁ γ₂ : Path a b} (F : γ₁.Homotopy γ₂)
    (ω : ℂ → (ℂ →L[ℝ] ℂ)) :
    ∫ᶜ x in F.evalAt 0, ω x = 0 := by
  have h0 : F.evalAt (0 : I) =
      (Path.refl a).cast γ₁.source γ₂.source := by
    ext t
    change F.toHomotopy (t, 0) = a
    exact F.source t
  rw [show F.evalAt (0 : I) = (Path.refl a).cast γ₁.source γ₂.source from h0,
      curveIntegral_cast]
  exact curveIntegral_refl ω a

/-- The side curve integral at `s = 1` along a `Path.Homotopy` vanishes. -/
lemma curveIntegral_pathHomotopy_evalAt_one_eq_zero
    {a b : ℂ} {γ₁ γ₂ : Path a b} (F : γ₁.Homotopy γ₂)
    (ω : ℂ → (ℂ →L[ℝ] ℂ)) :
    ∫ᶜ x in F.evalAt 1, ω x = 0 := by
  have h1 : F.evalAt (1 : I) =
      (Path.refl b).cast γ₁.target γ₂.target := by
    ext t
    change F.toHomotopy (t, 1) = b
    exact F.target t
  rw [show F.evalAt (1 : I) = (Path.refl b).cast γ₁.target γ₂.target from h1,
      curveIntegral_cast]
  exact curveIntegral_refl ω b

/-- Endpoint-preserving contour deformation, abstract form. For a
    `Path.Homotopy γ₁ γ₂` whose image stays in `t` on the interior of the
    parameter square, a closed 1-form has equal integrals along `γ₁` and
    `γ₂`. -/
theorem contourDeformation1D_pathHomotopy_abstract
    {t : Set ℂ}
    {ω : ℂ → (ℂ →L[ℝ] ℂ)}
    (hωdcc : DiffContOnCl ℝ ω t)
    (hsymm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    {a b : ℂ} {γ₁ γ₂ : Path a b}
    (F : γ₁.Homotopy γ₂)
    (hFt : ∀ a ∈ Set.Ioo (0 : I) 1, ∀ b ∈ Set.Ioo (0 : I) 1, F (a, b) ∈ t)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (F.toHomotopy.extend xy.1) xy.2)
      (Set.Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x = ∫ᶜ x in γ₂, ω x := by
  have heq :=
    contourDeformation1D_abstract hωdcc hsymm F.toHomotopy hFt hcontdiff
  have h0 := curveIntegral_pathHomotopy_evalAt_zero_eq_zero F ω
  have h1 := curveIntegral_pathHomotopy_evalAt_one_eq_zero F ω
  have hsum0 : ∫ᶜ x in γ₂, ω x + ∫ᶜ x in F.toHomotopy.evalAt 0, ω x =
               ∫ᶜ x in γ₂, ω x := by rw [h0, add_zero]
  have hsum1 : ∫ᶜ x in γ₁, ω x + ∫ᶜ x in F.toHomotopy.evalAt 1, ω x =
               ∫ᶜ x in γ₁, ω x := by rw [h1, add_zero]
  calc ∫ᶜ x in γ₁, ω x = ∫ᶜ x in γ₁, ω x + ∫ᶜ x in F.toHomotopy.evalAt 1, ω x :=
        hsum1.symm
    _ = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in F.toHomotopy.evalAt 0, ω x := heq
    _ = ∫ᶜ x in γ₂, ω x := hsum0

/-- Endpoint-preserving contour deformation specialised to `holoOneForm f` for
    holomorphic `f`. -/
theorem contourDeformation1D_pathHomotopy
    {t : Set ℂ} (ht : IsOpen t)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f t)
    (hωdcc : DiffContOnCl ℝ (holoOneForm f) t)
    {a b : ℂ} {γ₁ γ₂ : Path a b}
    (F : γ₁.Homotopy γ₂)
    (hFt : ∀ a ∈ Set.Ioo (0 : I) 1, ∀ b ∈ Set.Ioo (0 : I) 1, F (a, b) ∈ t)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (F.toHomotopy.extend xy.1) xy.2)
      (Set.Icc 0 1)) :
    ∫ᶜ x in γ₁, holoOneForm f x = ∫ᶜ x in γ₂, holoOneForm f x :=
  contourDeformation1D_pathHomotopy_abstract hωdcc
    (holoOneForm_dOmega_symm ht hf) F hFt hcontdiff

end Jacobians.Bridge.ContourDeformation
