/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Cousin

/-!
# The Cauchy integral formula on a frame

A *frame* is a closed rectangle `[X₀, X₁] × [Y₀, Y₁]` minus the open square `(-ρ, ρ)²` (strictly
inside). For `F` holomorphic near `frame × P`, and `z` in the interior of the frame,
`F (z, w)` is the Cauchy integral over the outer boundary minus the Cauchy integral over the
boundary of the square, each written as the sum of the four side integrals
(`Complex.RectSide.cauchy`).

The proof tiles the frame by four rectangles (the top and bottom strips and the two remaining
side pieces); the side integrals over the tiles add up to the two boundary integrals, since the
inner edges of the tiles cancel. This proves the formula off the lines `Im z = ±ρ`, and the
remaining points follow by continuity.

## Main results

- `Complex.RectSide.differentiableOn_cauchy_of_boundary`: a side integral is holomorphic off the
  side, as soon as the boundary of the rectangle lies in the domain of `F`.
- `Complex.frame_cauchy`: the Cauchy integral formula on a frame.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval Real Topology

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A side integral is holomorphic off its side, if the boundary of the rectangle lies in `V`. -/
theorem RectSide.differentiableOn_cauchy_of_boundary {a b : ℂ} (hre : a.re ≤ b.re)
    (him : a.im ≤ b.im) {V : Set ℂ} (hbd : rectBoundary a b ⊆ V) {P : Set E} (hP : IsOpen P)
    {F : ℂ × E → ℂ} (hF : DifferentiableOn ℂ F (V ×ˢ P)) (s : RectSide) :
    DifferentiableOn ℂ (RectSide.cauchy F a b s) ((RectSide.set a b s)ᶜ ×ˢ P) := by
  cases s
  · exact (differentiableOn_cauchyEdge hP hF (by fun_prop) fun x hx ↦
      hbd (mapsTo_horizontal_rectBoundary hre him (Or.inl rfl) hx)).const_mul _
  · exact ((differentiableOn_cauchyEdge hP hF (by fun_prop) fun y hy ↦
      hbd (mapsTo_vertical_rectBoundary hre him (Or.inr rfl) hy)).const_mul _).const_mul _
  · exact ((differentiableOn_cauchyEdge hP hF (by fun_prop) fun x hx ↦
      hbd (mapsTo_horizontal_rectBoundary hre him (Or.inr rfl) hx)).const_mul _).neg
  · exact (((differentiableOn_cauchyEdge hP hF (by fun_prop) fun y hy ↦
      hbd (mapsTo_vertical_rectBoundary hre him (Or.inl rfl) hy)).const_mul _).const_mul _).neg

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- The sum of the four side integrals. -/
lemma RectSide.sum_cauchy_eq (F : ℂ × E → ℂ) (a b : ℂ) (p : ℂ × E) :
    ∑ s, RectSide.cauchy F a b s p =
      (2 * π * I)⁻¹ * ((∫ x : ℝ in a.re..b.re, ((x : ℂ) + a.im * I - p.1)⁻¹ *
        F ((x : ℂ) + a.im * I, p.2)) -
      (∫ x : ℝ in a.re..b.re, ((x : ℂ) + b.im * I - p.1)⁻¹ * F ((x : ℂ) + b.im * I, p.2)) +
      I * (∫ y : ℝ in a.im..b.im, ((b.re : ℂ) + y * I - p.1)⁻¹ * F ((b.re : ℂ) + y * I, p.2)) -
      I * (∫ y : ℝ in a.im..b.im, ((a.re : ℂ) + y * I - p.1)⁻¹ *
        F ((a.re : ℂ) + y * I, p.2))) := by
  rw [RectSide.sum_univ_cauchy]
  simp only [cauchyBottom, cauchyRight, cauchyTop, cauchyLeft]
  ring

/-- The closed frame `[X₀, X₁] × [Y₀, Y₁] \ (-ρ, ρ)²`. -/
def closedFrame (X₀ X₁ Y₀ Y₁ ρ : ℝ) : Set ℂ :=
  (Icc X₀ X₁ ×ℂ Icc Y₀ Y₁) \ (Ioo (-ρ) ρ ×ℂ Ioo (-ρ) ρ)

/-- The open frame `(X₀, X₁) × (Y₀, Y₁) \ [-ρ, ρ]²`. -/
def openFrame (X₀ X₁ Y₀ Y₁ ρ : ℝ) : Set ℂ :=
  (Ioo X₀ X₁ ×ℂ Ioo Y₀ Y₁) \ (Icc (-ρ) ρ ×ℂ Icc (-ρ) ρ)

lemma isOpen_openFrame (X₀ X₁ Y₀ Y₁ ρ : ℝ) : IsOpen (openFrame X₀ X₁ Y₀ Y₁ ρ) :=
  (isOpen_Ioo.reProdIm isOpen_Ioo).sdiff (isClosed_Icc.reProdIm isClosed_Icc)

variable {X₀ X₁ Y₀ Y₁ ρ : ℝ} {V : Set ℂ} {P : Set E} {F : ℂ × E → ℂ}

omit [FiniteDimensional ℂ E] in
/-- The frame formula off the lines `Im z = ±ρ`, by tiling. -/
private lemma frame_cauchy_aux (hρ : 0 < ρ) (hX₀ : X₀ < -ρ) (hX₁ : ρ < X₁) (hY₀ : Y₀ < -ρ)
    (hY₁ : ρ < Y₁) (hV : closedFrame X₀ X₁ Y₀ Y₁ ρ ⊆ V) (hF : DifferentiableOn ℂ F (V ×ˢ P))
    {z : ℂ} (hz : z ∈ openFrame X₀ X₁ Y₀ Y₁ ρ) (hzρ : |z.im| ≠ ρ) {w : E} (hw : w ∈ P) :
    ∑ s, RectSide.cauchy F ⟨X₀, Y₀⟩ ⟨X₁, Y₁⟩ s (z, w) -
      ∑ s, RectSide.cauchy F ⟨-ρ, -ρ⟩ ⟨ρ, ρ⟩ s (z, w) = F (z, w) := by
  obtain ⟨⟨⟨hz1, hz2⟩, hz3, hz4⟩, hzsq⟩ := hz
  have hzsq' : ¬ (-ρ ≤ z.re ∧ z.re ≤ ρ ∧ -ρ ≤ z.im ∧ z.im ≤ ρ) := fun h ↦
    hzsq ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  -- continuity of the integrands along the segments used
  have hmemH : ∀ y : ℝ, (y = ρ ∨ y = -ρ) → ∀ x ∈ Icc X₀ X₁, (x : ℂ) + y * I ∈ V := by
    intro y hy x hx
    refine hV ⟨⟨by simpa using hx, ?_⟩, fun h ↦ ?_⟩
    · change ((x : ℂ) + y * I).im ∈ Icc Y₀ Y₁
      rw [show ((x : ℂ) + y * I).im = y by simp]
      rcases hy with rfl | rfl <;> constructor <;> linarith
    · have := h.2; rcases hy with rfl | rfl <;> simp at this
  have hmemV : ∀ x : ℝ, (x = X₀ ∨ x = X₁) → ∀ y ∈ Icc Y₀ Y₁, (x : ℂ) + y * I ∈ V := by
    intro x hx y hy
    refine hV ⟨⟨?_, by simpa using hy⟩, fun h ↦ ?_⟩
    · change ((x : ℂ) + y * I).re ∈ Icc X₀ X₁
      rw [show ((x : ℂ) + y * I).re = x by simp]
      rcases hx with rfl | rfl <;> constructor <;> linarith
    · have := h.1; rcases hx with rfl | rfl <;> simp at this <;> linarith
  have hcont : ∀ γ : ℝ → ℂ, Continuous γ → ∀ S : Set ℝ, (∀ t ∈ S, γ t ∈ V) →
      (∀ t ∈ S, γ t ≠ z) → ContinuousOn (fun t ↦ (γ t - z)⁻¹ * F (γ t, w)) S := by
    intro γ hγ S hS hne
    refine ContinuousOn.mul ((hγ.sub continuous_const).continuousOn.inv₀
      fun t ht ↦ sub_ne_zero.2 (hne t ht)) ?_
    exact hF.continuousOn.comp (by fun_prop) fun t ht ↦ ⟨hS t ht, hw⟩
  have hsplitH : ∀ y : ℝ, (y = ρ ∨ y = -ρ) →
      (∫ x : ℝ in X₀..(-ρ), ((x : ℂ) + y * I - z)⁻¹ * F ((x : ℂ) + y * I, w)) +
      (∫ x : ℝ in (-ρ)..ρ, ((x : ℂ) + y * I - z)⁻¹ * F ((x : ℂ) + y * I, w)) +
      (∫ x : ℝ in ρ..X₁, ((x : ℂ) + y * I - z)⁻¹ * F ((x : ℂ) + y * I, w)) =
      ∫ x : ℝ in X₀..X₁, ((x : ℂ) + y * I - z)⁻¹ * F ((x : ℂ) + y * I, w) := by
    intro y hy
    have hc := hcont (fun x : ℝ ↦ (x : ℂ) + y * I) (by fun_prop) (Icc X₀ X₁)
      (hmemH y hy) fun x _ h ↦ hzρ (by
        have := congrArg Complex.im h; simp at this
        rcases hy with rfl | rfl <;> simp [← this, abs_of_pos hρ])
    have hi : ∀ c d, c ∈ Icc X₀ X₁ → d ∈ Icc X₀ X₁ → IntervalIntegrable
        (fun x : ℝ ↦ ((x : ℂ) + y * I - z)⁻¹ * F ((x : ℂ) + y * I, w)) volume c d :=
      fun c d hc' hd' ↦ (hc.mono (uIcc_subset_Icc hc' hd')).intervalIntegrable
    have m1 : X₀ ∈ Icc X₀ X₁ := ⟨le_rfl, by linarith⟩
    have m2 : -ρ ∈ Icc X₀ X₁ := ⟨by linarith, by linarith⟩
    have m3 : ρ ∈ Icc X₀ X₁ := ⟨by linarith, by linarith⟩
    have m4 : X₁ ∈ Icc X₀ X₁ := ⟨by linarith, le_rfl⟩
    rw [intervalIntegral.integral_add_adjacent_intervals (hi _ _ m1 m2) (hi _ _ m2 m3),
      intervalIntegral.integral_add_adjacent_intervals (hi _ _ m1 m3) (hi _ _ m3 m4)]
  have hsplitV : ∀ x : ℝ, (x = X₀ ∨ x = X₁) →
      (∫ y : ℝ in Y₀..(-ρ), ((x : ℂ) + y * I - z)⁻¹ * F ((x : ℂ) + y * I, w)) +
      (∫ y : ℝ in (-ρ)..ρ, ((x : ℂ) + y * I - z)⁻¹ * F ((x : ℂ) + y * I, w)) +
      (∫ y : ℝ in ρ..Y₁, ((x : ℂ) + y * I - z)⁻¹ * F ((x : ℂ) + y * I, w)) =
      ∫ y : ℝ in Y₀..Y₁, ((x : ℂ) + y * I - z)⁻¹ * F ((x : ℂ) + y * I, w) := by
    intro x hx
    have hc := hcont (fun y : ℝ ↦ (x : ℂ) + y * I) (by fun_prop) (Icc Y₀ Y₁)
      (hmemV x hx) fun y _ h ↦ by
        have := congrArg Complex.re h; simp at this
        rcases hx with rfl | rfl <;> linarith
    have hi : ∀ c d, c ∈ Icc Y₀ Y₁ → d ∈ Icc Y₀ Y₁ → IntervalIntegrable
        (fun y : ℝ ↦ ((x : ℂ) + y * I - z)⁻¹ * F ((x : ℂ) + y * I, w)) volume c d :=
      fun c d hc' hd' ↦ (hc.mono (uIcc_subset_Icc hc' hd')).intervalIntegrable
    have m1 : Y₀ ∈ Icc Y₀ Y₁ := ⟨le_rfl, by linarith⟩
    have m2 : -ρ ∈ Icc Y₀ Y₁ := ⟨by linarith, by linarith⟩
    have m3 : ρ ∈ Icc Y₀ Y₁ := ⟨by linarith, by linarith⟩
    have m4 : Y₁ ∈ Icc Y₀ Y₁ := ⟨by linarith, le_rfl⟩
    rw [intervalIntegral.integral_add_adjacent_intervals (hi _ _ m1 m2) (hi _ _ m2 m3),
      intervalIntegral.integral_add_adjacent_intervals (hi _ _ m1 m3) (hi _ _ m3 m4)]
  -- the tiling identity
  have htiles : ∑ s, RectSide.cauchy F ⟨X₀, Y₀⟩ ⟨X₁, Y₁⟩ s (z, w) -
      ∑ s, RectSide.cauchy F ⟨-ρ, -ρ⟩ ⟨ρ, ρ⟩ s (z, w) =
      ∑ s, RectSide.cauchy F ⟨X₀, ρ⟩ ⟨X₁, Y₁⟩ s (z, w) +
      ∑ s, RectSide.cauchy F ⟨X₀, Y₀⟩ ⟨X₁, -ρ⟩ s (z, w) +
      ∑ s, RectSide.cauchy F ⟨X₀, -ρ⟩ ⟨-ρ, ρ⟩ s (z, w) +
      ∑ s, RectSide.cauchy F ⟨ρ, -ρ⟩ ⟨X₁, ρ⟩ s (z, w) := by
    simp only [RectSide.sum_cauchy_eq]
    have e1 := hsplitH ρ (Or.inl rfl)
    have e2 := hsplitH (-ρ) (Or.inr rfl)
    have e3 := hsplitV X₀ (Or.inl rfl)
    have e4 := hsplitV X₁ (Or.inr rfl)
    push_cast at e1 e2 e3 e4 ⊢
    linear_combination (2 * π * I)⁻¹ * e1 - (2 * π * I)⁻¹ * e2 -
      (2 * π * I)⁻¹ * I * e4 + (2 * π * I)⁻¹ * I * e3
  -- evaluation on the tiles
  have htile : ∀ a b : ℂ, a.re < b.re → a.im < b.im → Icc a.re b.re ×ℂ Icc a.im b.im ⊆ V →
      (z ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im → ∑ s, RectSide.cauchy F a b s (z, w) = F (z, w)) ∧
      (z ∉ Icc a.re b.re ×ℂ Icc a.im b.im → ∑ s, RectSide.cauchy F a b s (z, w) = 0) := by
    intro a b h1 h2 h3
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [RectSide.sum_univ_cauchy]; exact sum_cauchySides_of_mem h3 hF h hw
    · rw [RectSide.sum_univ_cauchy]; exact sum_cauchySides_of_notMem h3 hF h1.le h2.le h hw
  have hsubV : ∀ a b : ℂ, Icc a.re b.re ×ℂ Icc a.im b.im ⊆ closedFrame X₀ X₁ Y₀ Y₁ ρ →
      Icc a.re b.re ×ℂ Icc a.im b.im ⊆ V := fun a b h ↦ h.trans hV
  have hT := htile ⟨X₀, ρ⟩ ⟨X₁, Y₁⟩ (by simp; linarith) (by simp; linarith) (hsubV _ _
    fun u hu ↦ ⟨⟨hu.1, by simp at hu ⊢; constructor <;> linarith [hu.2.1, hu.2.2]⟩,
      fun h ↦ by simp at hu h; linarith [hu.2.1, h.2.2]⟩)
  have hB := htile ⟨X₀, Y₀⟩ ⟨X₁, -ρ⟩ (by simp; linarith) (by simp; linarith) (hsubV _ _
    fun u hu ↦ ⟨⟨hu.1, by simp at hu ⊢; constructor <;> linarith [hu.2.1, hu.2.2]⟩,
      fun h ↦ by simp at hu h; linarith [hu.2.2, h.2.1]⟩)
  have hL := htile ⟨X₀, -ρ⟩ ⟨-ρ, ρ⟩ (by simp; linarith) (by simp; linarith) (hsubV _ _
    fun u hu ↦ ⟨⟨by simp at hu ⊢; constructor <;> linarith [hu.1.1, hu.1.2],
      by simp at hu ⊢; constructor <;> linarith [hu.2.1, hu.2.2]⟩,
      fun h ↦ by simp at hu h; linarith [hu.1.2, h.1.1]⟩)
  have hR := htile ⟨ρ, -ρ⟩ ⟨X₁, ρ⟩ (by simp; linarith) (by simp; linarith) (hsubV _ _
    fun u hu ↦ ⟨⟨by simp at hu ⊢; constructor <;> linarith [hu.1.1, hu.1.2],
      by simp at hu ⊢; constructor <;> linarith [hu.2.1, hu.2.2]⟩,
      fun h ↦ by simp at hu h; linarith [hu.1.1, h.1.2]⟩)
  rw [htiles]
  rcases lt_or_gt_of_ne hzρ with hlt | hgt
  · rw [abs_lt] at hlt
    have hre : z.re < -ρ ∨ ρ < z.re := by
      by_contra h; push Not at h
      exact hzsq' ⟨h.1, h.2, hlt.1.le, hlt.2.le⟩
    rw [hT.2 (fun h ↦ by simp [mem_reProdIm] at h; linarith [h.2.1]),
      hB.2 (fun h ↦ by simp [mem_reProdIm] at h; linarith [h.2.2])]
    rcases hre with hre | hre
    · rw [hL.1 ⟨⟨by simpa using hz1, by simpa using hre⟩, by simpa using hlt.1,
        by simpa using hlt.2⟩, hR.2 (fun h ↦ by simp [mem_reProdIm] at h; linarith [h.1.1])]
      ring
    · rw [hL.2 (fun h ↦ by simp [mem_reProdIm] at h; linarith [h.1.2]),
        hR.1 ⟨⟨by simpa using hre, by simpa using hz2⟩, by simpa using hlt.1,
        by simpa using hlt.2⟩]
      ring
  · rcases lt_abs.1 hgt with h | h
    · rw [hT.1 ⟨⟨by simpa using hz1, by simpa using hz2⟩, by simpa using h,
        by simpa using hz4⟩,
        hB.2 (fun h' ↦ by simp [mem_reProdIm] at h'; linarith [h'.2.2]),
        hL.2 (fun h' ↦ by simp [mem_reProdIm] at h'; linarith [h'.2.2]),
        hR.2 (fun h' ↦ by simp [mem_reProdIm] at h'; linarith [h'.2.2])]
      ring
    · rw [hT.2 (fun h' ↦ by simp [mem_reProdIm] at h'; linarith [h'.2.1]),
        hB.1 ⟨⟨by simpa using hz1, by simpa using hz2⟩, by simpa using hz3,
        by simp; linarith⟩,
        hL.2 (fun h' ↦ by simp [mem_reProdIm] at h'; linarith [h'.2.1]),
        hR.2 (fun h' ↦ by simp [mem_reProdIm] at h'; linarith [h'.2.1])]
      ring

/-- **The Cauchy integral formula on a frame**, with holomorphic parameters: on the open frame,
`F` is the sum of the side integrals over the outer rectangle minus the sum of the side
integrals over the square `[-ρ, ρ]²`. -/
theorem frame_cauchy (hρ : 0 < ρ) (hX₀ : X₀ < -ρ) (hX₁ : ρ < X₁) (hY₀ : Y₀ < -ρ)
    (hY₁ : ρ < Y₁) (hV : closedFrame X₀ X₁ Y₀ Y₁ ρ ⊆ V) (hP : IsOpen P)
    (hF : DifferentiableOn ℂ F (V ×ˢ P)) {z : ℂ} (hz : z ∈ openFrame X₀ X₁ Y₀ Y₁ ρ) {w : E}
    (hw : w ∈ P) :
    ∑ s, RectSide.cauchy F ⟨X₀, Y₀⟩ ⟨X₁, Y₁⟩ s (z, w) -
      ∑ s, RectSide.cauchy F ⟨-ρ, -ρ⟩ ⟨ρ, ρ⟩ s (z, w) = F (z, w) := by
  set O := openFrame X₀ X₁ Y₀ Y₁ ρ
  have hbdO : rectBoundary ⟨X₀, Y₀⟩ ⟨X₁, Y₁⟩ ⊆ V := fun u hu ↦ hV ⟨hu.1, fun h ↦ hu.2
    ⟨⟨by simp; linarith [h.1.1], by simp; linarith [h.1.2]⟩,
      ⟨by simp; linarith [h.2.1], by simp; linarith [h.2.2]⟩⟩⟩
  have hbdI : rectBoundary ⟨-ρ, -ρ⟩ ⟨ρ, ρ⟩ ⊆ V := fun u hu ↦ hV ⟨⟨⟨by linarith [hu.1.1.1],
    by linarith [hu.1.1.2]⟩, ⟨by linarith [hu.1.2.1], by linarith [hu.1.2.2]⟩⟩, hu.2⟩
  have hcontSum : ∀ a b : ℂ, a.re ≤ b.re → a.im ≤ b.im → rectBoundary a b ⊆ V →
      (∀ s, Disjoint O (RectSide.set a b s)) →
      ContinuousOn (fun u ↦ ∑ s, RectSide.cauchy F a b s (u, w)) O := by
    intro a b h1 h2 h3 h4
    refine continuousOn_finsetSum _ fun s _ ↦ ?_
    refine ((RectSide.differentiableOn_cauchy_of_boundary h1 h2 h3 hP hF s).continuousOn.comp
      (by fun_prop) fun u hu ↦ ⟨(h4 s).notMem_of_mem_left hu, hw⟩)
  have hO : ∀ u ∈ O, (X₀ < u.re ∧ u.re < X₁) ∧ (Y₀ < u.im ∧ u.im < Y₁) ∧
      ¬ (-ρ ≤ u.re ∧ u.re ≤ ρ ∧ -ρ ≤ u.im ∧ u.im ≤ ρ) := fun u hu ↦
    ⟨hu.1.1, hu.1.2, fun h ↦ hu.2 ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  have hGc : ContinuousOn (fun u ↦ ∑ s, RectSide.cauchy F ⟨X₀, Y₀⟩ ⟨X₁, Y₁⟩ s (u, w) -
      ∑ s, RectSide.cauchy F ⟨-ρ, -ρ⟩ ⟨ρ, ρ⟩ s (u, w)) O := by
    refine (hcontSum _ _ (by simp; linarith) (by simp; linarith) hbdO fun s ↦ ?_).sub
      (hcontSum _ _ (by simp; linarith) (by simp; linarith) hbdI fun s ↦ ?_) <;>
      refine Set.disjoint_left.2 fun u hu hs ↦ ?_ <;> obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hO u hu
    · cases s
      · have := (RectSide.set_bottom_subset hs).2; simp at this; linarith
      · have := (RectSide.set_right_subset hs).1; simp at this; linarith
      · have := (RectSide.set_top_subset hs).2; simp at this; linarith
      · have := (RectSide.set_left_subset hs).1; simp at this; linarith
    · refine h5 ?_
      cases s
      · obtain ⟨hx, hy⟩ := RectSide.set_bottom_subset hs
        rw [uIcc_of_le (by simp; linarith)] at hx
        replace hx : -ρ ≤ u.re ∧ u.re ≤ ρ := hx
        replace hy : u.im = -ρ := hy
        exact ⟨hx.1, hx.2, by linarith, by linarith⟩
      · obtain ⟨hx, hy⟩ := RectSide.set_right_subset hs
        rw [uIcc_of_le (by simp; linarith)] at hy
        replace hx : u.re = ρ := hx
        replace hy : -ρ ≤ u.im ∧ u.im ≤ ρ := hy
        exact ⟨by linarith, by linarith, hy.1, hy.2⟩
      · obtain ⟨hx, hy⟩ := RectSide.set_top_subset hs
        rw [uIcc_of_le (by simp; linarith)] at hx
        replace hx : -ρ ≤ u.re ∧ u.re ≤ ρ := hx
        replace hy : u.im = ρ := hy
        exact ⟨hx.1, hx.2, by linarith, by linarith⟩
      · obtain ⟨hx, hy⟩ := RectSide.set_left_subset hs
        rw [uIcc_of_le (by simp; linarith)] at hy
        replace hx : u.re = -ρ := hx
        replace hy : -ρ ≤ u.im ∧ u.im ≤ ρ := hy
        exact ⟨by linarith, by linarith, hy.1, hy.2⟩
  have hFc : ContinuousOn (fun u ↦ F (u, w)) O :=
    hF.continuousOn.comp (by fun_prop) fun u hu ↦
      ⟨hV ⟨⟨Ioo_subset_Icc_self hu.1.1, Ioo_subset_Icc_self hu.1.2⟩,
        fun h ↦ hu.2 ⟨Ioo_subset_Icc_self h.1, Ioo_subset_Icc_self h.2⟩⟩, hw⟩
  have hEq : EqOn (fun u ↦ ∑ s, RectSide.cauchy F ⟨X₀, Y₀⟩ ⟨X₁, Y₁⟩ s (u, w) -
      ∑ s, RectSide.cauchy F ⟨-ρ, -ρ⟩ ⟨ρ, ρ⟩ s (u, w)) (fun u ↦ F (u, w))
      (O ∩ {u | |u.im| ≠ ρ}) := fun u hu ↦
    frame_cauchy_aux hρ hX₀ hX₁ hY₀ hY₁ hV hF hu.1 hu.2 hw
  refine hEq.of_subset_closure hGc hFc inter_subset_left (fun u hu ↦ ?_) hz
  by_cases hu' : |u.im| ≠ ρ
  · exact subset_closure ⟨hu, hu'⟩
  push Not at hu'
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 (isOpen_openFrame X₀ X₁ Y₀ Y₁ ρ) u hu
  set m := min (min ε η) ρ / 2 with hm
  have hm0 : 0 < m := by positivity
  have hmε : m < ε := by
    have := (min_le_left (min ε η) ρ).trans (min_le_left ε η); linarith
  have hmη : m < η := by
    have := (min_le_left (min ε η) ρ).trans (min_le_right ε η); linarith
  have hmρ : m < ρ := by have := min_le_right (min ε η) ρ; linarith
  have hdist : dist u (u + m * I) = m := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg hm0.le]
  refine ⟨u + m * I, ⟨hball (by rw [Metric.mem_ball, dist_comm, hdist]; exact hmη), ?_⟩, by
    rw [hdist]; exact hmε⟩
  simp only [mem_setOf_eq, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
    mul_zero, add_zero]
  rcases abs_eq hρ.le |>.1 hu' with h | h <;> rw [h]
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

end Complex

end
