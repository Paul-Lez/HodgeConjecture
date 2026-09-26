/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The Cauchy integral formula on a rectangle

Mathlib proves the Cauchy–Goursat theorem for rectangles
(`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`). We deduce the
Cauchy integral formula: if `f` is continuous on the closed rectangle with lower left corner `a`
and upper right corner `b` and holomorphic on its interior, then for `z` in the interior
`∮_{∂R} (ζ - z)⁻¹ • f ζ dζ = 2πi • f z`.

## Main definitions

- `Complex.rectBoundaryIntegral f a b`: the integral of `f` over the positively oriented boundary
  of the rectangle with corners `a` (lower left) and `b` (upper right), written as the sum of the
  four edge integrals exactly as in `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.
- `Complex.rectBoundary a b`: the boundary of that rectangle.

## Main results

- `Complex.rectBoundaryIntegral_sub_inv`: the winding number of the boundary of a rectangle
  around an interior point is one, i.e. `∮_{∂R} (ζ - z)⁻¹ dζ = 2πi`. Each edge integral is a
  difference of values of a branch of the logarithm.
- `Complex.rectBoundaryIntegral_sub_inv_smul`: the Cauchy integral formula on a rectangle.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval Real Topology

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The integral of `f` over the positively oriented boundary of the rectangle with lower left
corner `a` and upper right corner `b`: bottom edge minus top edge (both traversed from left to
right) plus `I •` right edge minus `I •` left edge (both traversed upwards). -/
noncomputable def rectBoundaryIntegral (f : ℂ → E) (a b : ℂ) : E :=
  (∫ x : ℝ in a.re..b.re, f (x + a.im * I)) - (∫ x : ℝ in a.re..b.re, f (x + b.im * I)) +
    I • (∫ y : ℝ in a.im..b.im, f (b.re + y * I)) - I • ∫ y : ℝ in a.im..b.im, f (a.re + y * I)

/-- The boundary of the closed rectangle with corners `a` and `b`. -/
def rectBoundary (a b : ℂ) : Set ℂ :=
  (Icc a.re b.re ×ℂ Icc a.im b.im) \ (Ioo a.re b.re ×ℂ Ioo a.im b.im)

section Edges

variable {a b : ℂ}

lemma mapsTo_horizontal_rectBoundary (hre : a.re ≤ b.re) (him : a.im ≤ b.im) {y : ℝ}
    (hy : y = a.im ∨ y = b.im) :
    MapsTo (fun x : ℝ ↦ (x : ℂ) + y * I) [[a.re, b.re]] (rectBoundary a b) := by
  intro x hx
  rw [uIcc_of_le hre] at hx
  refine ⟨⟨by simpa using hx, ?_⟩, fun h ↦ ?_⟩
  · rcases hy with rfl | rfl <;> simp [him]
  · have := h.2
    simp only [mem_preimage, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_add, mem_Ioo] at this
    rcases hy with rfl | rfl <;> simp at this

lemma mapsTo_vertical_rectBoundary (hre : a.re ≤ b.re) (him : a.im ≤ b.im) {x : ℝ}
    (hx : x = a.re ∨ x = b.re) :
    MapsTo (fun y : ℝ ↦ (x : ℂ) + y * I) [[a.im, b.im]] (rectBoundary a b) := by
  intro y hy
  rw [uIcc_of_le him] at hy
  refine ⟨⟨?_, by simpa using hy⟩, fun h ↦ ?_⟩
  · rcases hx with rfl | rfl <;> simp [hre]
  · have := h.1
    simp only [mem_preimage, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, mem_Ioo] at this
    rcases hx with rfl | rfl <;> simp at this

/-- The boundary integral is additive for functions continuous on the boundary. -/
lemma rectBoundaryIntegral_sub (hre : a.re ≤ b.re) (him : a.im ≤ b.im) {f g : ℂ → E}
    (hf : ContinuousOn f (rectBoundary a b)) (hg : ContinuousOn g (rectBoundary a b)) :
    rectBoundaryIntegral (fun ζ ↦ f ζ - g ζ) a b =
      rectBoundaryIntegral f a b - rectBoundaryIntegral g a b := by
  have hH : ∀ {y : ℝ}, (y = a.im ∨ y = b.im) → ∀ {h : ℂ → E},
      ContinuousOn h (rectBoundary a b) →
      IntervalIntegrable (fun x : ℝ ↦ h (x + y * I)) volume a.re b.re := fun hy _ hh ↦
    (hh.comp (by fun_prop) (mapsTo_horizontal_rectBoundary hre him hy)).intervalIntegrable
  have hV : ∀ {x : ℝ}, (x = a.re ∨ x = b.re) → ∀ {h : ℂ → E},
      ContinuousOn h (rectBoundary a b) →
      IntervalIntegrable (fun y : ℝ ↦ h (x + y * I)) volume a.im b.im := fun hx _ hh ↦
    (hh.comp (by fun_prop) (mapsTo_vertical_rectBoundary hre him hx)).intervalIntegrable
  simp only [rectBoundaryIntegral]
  rw [intervalIntegral.integral_sub (hH (Or.inl rfl) hf) (hH (Or.inl rfl) hg),
    intervalIntegral.integral_sub (hH (Or.inr rfl) hf) (hH (Or.inr rfl) hg),
    intervalIntegral.integral_sub (hV (Or.inr rfl) hf) (hV (Or.inr rfl) hg),
    intervalIntegral.integral_sub (hV (Or.inl rfl) hf) (hV (Or.inl rfl) hg)]
  simp only [smul_sub]
  abel

/-- The boundary integral only depends on the values on the boundary. -/
lemma rectBoundaryIntegral_congr (hre : a.re ≤ b.re) (him : a.im ≤ b.im) {f g : ℂ → E}
    (h : EqOn f g (rectBoundary a b)) :
    rectBoundaryIntegral f a b = rectBoundaryIntegral g a b := by
  simp only [rectBoundaryIntegral]
  rw [intervalIntegral.integral_congr fun x hx ↦
      h (mapsTo_horizontal_rectBoundary hre him (Or.inl rfl) hx),
    intervalIntegral.integral_congr fun x hx ↦
      h (mapsTo_horizontal_rectBoundary hre him (Or.inr rfl) hx),
    intervalIntegral.integral_congr fun y hy ↦
      h (mapsTo_vertical_rectBoundary hre him (Or.inr rfl) hy),
    intervalIntegral.integral_congr fun y hy ↦
      h (mapsTo_vertical_rectBoundary hre him (Or.inl rfl) hy)]

/-- Scalar functions times a constant vector. -/
lemma rectBoundaryIntegral_smul_const [CompleteSpace E] (g : ℂ → ℂ) (c : E) :
    rectBoundaryIntegral (fun ζ ↦ g ζ • c) a b = rectBoundaryIntegral g a b • c := by
  simp only [rectBoundaryIntegral, intervalIntegral.integral_smul_const, sub_smul, add_smul,
    smul_assoc]

end Edges

/-- An integral of `u / (u t + v)` along a segment in the slit plane is a difference of
logarithms. -/
lemma integral_div_affine_eq_log (u v : ℂ) {t₀ t₁ : ℝ}
    (h : ∀ t ∈ [[t₀, t₁]], u * t + v ∈ slitPlane) :
    ∫ t in t₀..t₁, u / (u * t + v) = log (u * t₁ + v) - log (u * t₀ + v) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ log (u * t + v))
    (f' := fun t : ℝ ↦ u / (u * t + v)) (fun t ht ↦ ?_) ?_
  · have hd : HasDerivAt (fun t : ℝ ↦ u * (t : ℂ) + v) u t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.const_mul u).add_const v
    exact hd.clog_real (h t ht)
  · exact (continuousOn_const.div (by fun_prop)
      fun t ht ↦ slitPlane_ne_zero (h t ht)).intervalIntegrable

lemma log_neg_of_im_pos {w : ℂ} (hw : 0 < w.im) : log (-w) = log w - (π : ℂ) * I := by
  apply Complex.ext <;> simp [log_re, log_im, arg_neg_eq_arg_sub_pi_of_im_pos hw]

lemma log_neg_of_im_neg {w : ℂ} (hw : w.im < 0) : log (-w) = log w + (π : ℂ) * I := by
  apply Complex.ext <;> simp [log_re, log_im, arg_neg_eq_arg_add_pi_of_im_neg hw]

/-- The winding number of the boundary of a rectangle around an interior point is one. -/
theorem rectBoundaryIntegral_sub_inv {a b z : ℂ}
    (hz : z ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im) :
    rectBoundaryIntegral (fun ζ ↦ (ζ - z)⁻¹) a b = 2 * π * I := by
  obtain ⟨⟨hz1, hz2⟩, hz3, hz4⟩ := hz
  set p₁ : ℂ := a.re + a.im * I - z
  set p₂ : ℂ := b.re + a.im * I - z
  set p₃ : ℂ := b.re + b.im * I - z
  set p₄ : ℂ := a.re + b.im * I - z
  have hbot : (∫ x : ℝ in a.re..b.re, ((x : ℂ) + a.im * I - z)⁻¹) = log p₂ - log p₁ := by
    have h := integral_div_affine_eq_log 1 (a.im * I - z) (t₀ := a.re) (t₁ := b.re)
      fun t _ ↦ mem_slitPlane_iff.mpr (Or.inr (by simp; linarith))
    convert h using 1
    · exact intervalIntegral.integral_congr fun x _ ↦ by simp only [one_mul, one_div]; ring_nf
    · simp only [p₁, p₂, one_mul]; ring_nf
  have htop : (∫ x : ℝ in a.re..b.re, ((x : ℂ) + b.im * I - z)⁻¹) = log p₃ - log p₄ := by
    have h := integral_div_affine_eq_log 1 (b.im * I - z) (t₀ := a.re) (t₁ := b.re)
      fun t _ ↦ mem_slitPlane_iff.mpr (Or.inr (by simp; linarith))
    convert h using 1
    · exact intervalIntegral.integral_congr fun x _ ↦ by simp only [one_mul, one_div]; ring_nf
    · simp only [p₃, p₄, one_mul]; ring_nf
  have hright : I • (∫ y : ℝ in a.im..b.im, ((b.re : ℂ) + y * I - z)⁻¹) =
      log p₃ - log p₂ := by
    have h := integral_div_affine_eq_log I (b.re - z) (t₀ := a.im) (t₁ := b.im)
      fun t _ ↦ mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    convert h using 1
    · exact intervalIntegral.integral_congr fun y _ ↦ by rw [div_eq_mul_inv]; ring_nf
    · simp only [p₂, p₃]; ring_nf
  have hleft : I • (∫ y : ℝ in a.im..b.im, ((a.re : ℂ) + y * I - z)⁻¹) =
      log (-p₄) - log (-p₁) := by
    have h := integral_div_affine_eq_log (-I) (z - a.re) (t₀ := a.im) (t₁ := b.im)
      fun t _ ↦ mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    convert h using 1
    · refine intervalIntegral.integral_congr fun y _ ↦ ?_
      rw [show -I * (y : ℂ) + (z - a.re) = -((a.re : ℂ) + y * I - z) by ring, neg_div_neg_eq,
        div_eq_mul_inv]
    · simp only [p₁, p₄]; ring_nf
  have h₄ : log (-p₄) = log p₄ - (π : ℂ) * I := log_neg_of_im_pos (by simp [p₄]; linarith)
  have h₁ : log (-p₁) = log p₁ + (π : ℂ) * I := log_neg_of_im_neg (by simp [p₁]; linarith)
  simp only [rectBoundaryIntegral]
  rw [hbot, htop, hright, hleft, h₄, h₁]
  ring

/-- **Cauchy integral formula on a rectangle.** If `f` is continuous on a closed rectangle and
holomorphic on its interior, then `∮_{∂R} (ζ - z)⁻¹ • f ζ dζ = 2πi • f z` for every `z` in the
interior. -/
theorem rectBoundaryIntegral_sub_inv_smul [CompleteSpace E] {a b z : ℂ} {f : ℂ → E}
    (hc : ContinuousOn f (Icc a.re b.re ×ℂ Icc a.im b.im))
    (hd : DifferentiableOn ℂ f (Ioo a.re b.re ×ℂ Ioo a.im b.im))
    (hz : z ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im) :
    rectBoundaryIntegral (fun ζ ↦ (ζ - z)⁻¹ • f ζ) a b = (2 * π * I) • f z := by
  have hre : a.re ≤ b.re := (hz.1.1.trans hz.1.2).le
  have him : a.im ≤ b.im := (hz.2.1.trans hz.2.2).le
  have hopen : IsOpen (Ioo a.re b.re ×ℂ Ioo a.im b.im) := isOpen_Ioo.reProdIm isOpen_Ioo
  have hsub : Ioo a.re b.re ×ℂ Ioo a.im b.im ⊆ Icc a.re b.re ×ℂ Icc a.im b.im :=
    fun w hw ↦ ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩
  have hzb : ∀ ζ ∈ rectBoundary a b, ζ ≠ z := fun ζ hζ h ↦ hζ.2 (h ▸ hz)
  set F : ℂ → E := dslope f z
  have hcF : ContinuousOn F (Icc a.re b.re ×ℂ Icc a.im b.im) :=
    (continuousOn_dslope (Filter.mem_of_superset (hopen.mem_nhds hz) hsub)).2
      ⟨hc, hd.differentiableAt (hopen.mem_nhds hz)⟩
  have hdF : ∀ w ∈ Ioo (min a.re b.re) (max a.re b.re) ×ℂ Ioo (min a.im b.im) (max a.im b.im) \
      {z}, DifferentiableAt ℂ F w := by
    intro w hw
    rw [min_eq_left hre, max_eq_right hre, min_eq_left him, max_eq_right him] at hw
    exact (differentiableAt_dslope_of_ne hw.2).2 (hd.differentiableAt (hopen.mem_nhds hw.1))
  have hG : rectBoundaryIntegral F a b = 0 := by
    refine integral_boundary_rect_eq_zero_of_differentiable_on_off_countable F a b {z}
      (countable_singleton z) ?_ hdF
    rwa [uIcc_of_le hre, uIcc_of_le him]
  have hinv : ContinuousOn (fun ζ : ℂ ↦ (ζ - z)⁻¹) (rectBoundary a b) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ ↦ sub_ne_zero.2 (hzb ζ hζ)
  have hbd : rectBoundary a b ⊆ Icc a.re b.re ×ℂ Icc a.im b.im := sdiff_subset
  have hFeq : EqOn F (fun ζ ↦ (ζ - z)⁻¹ • f ζ - (ζ - z)⁻¹ • f z) (rectBoundary a b) := by
    intro ζ hζ
    simp only [F, dslope_of_ne f (hzb ζ hζ), slope_def_module, smul_sub]
  rw [rectBoundaryIntegral_congr hre him hFeq,
    rectBoundaryIntegral_sub hre him (f := fun ζ ↦ (ζ - z)⁻¹ • f ζ)
      (g := fun ζ ↦ (ζ - z)⁻¹ • f z) (hinv.smul (hc.mono hbd)) (hinv.smul continuousOn_const),
    rectBoundaryIntegral_smul_const, rectBoundaryIntegral_sub_inv hz, sub_eq_zero] at hG
  exact hG

end Complex

end
