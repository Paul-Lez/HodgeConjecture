/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.FrameCauchy
public import Other.Oka.Analytification.GAGA.Runge

/-!
# Runge approximation on frames, with holomorphic parameters

A function holomorphic near `frame × P`, where the frame is `[X₀, X₁] × [Y₀, Y₁] \ (-ρ, ρ)²`, is a
uniform limit on `K × L` of functions holomorphic on `ℂ^× × P`, for `K` compact in the open frame
with `‖z‖ ≥ 2ρ` on `K`, and `L ⊆ P` compact. By the Cauchy formula on the frame
(`Complex.frame_cauchy`), `f` is the outer boundary integral (holomorphic inside the outer
rectangle, approximated by entire functions by `Complex.exists_approx_entire_of_rect`) minus the
inner boundary integral, whose kernel `(ζ - z)⁻¹` is expanded in powers of `z⁻¹`.

## Main results

- `Complex.exists_approx_cauchyEdge_inner`: approximation of a Cauchy integral along a path by
  integrals of kernels which are polynomials in `(z - c₀)⁻¹`, when `‖γ t - c₀‖ ≤ q ‖z - c₀‖`,
  `q < 1`.
- `Complex.exists_approx_punctured_of_frame`: **Runge approximation on a frame.**
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Interval Real Topology

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The geometric series for the Cauchy kernel in the exterior: for `y = (γ - c) / (z - c)`,
`(γ - z)⁻¹ + ∑_{m < N} (γ - c)^m / (z - c)^(m+1) = y^N / (γ - z)`. -/
lemma inv_add_sum_geom_inner {γ z c : ℂ} (hγz : γ ≠ z) (hzc : z ≠ c) (N : ℕ) :
    (γ - z)⁻¹ - -∑ m ∈ Finset.range N, (γ - c) ^ m / (z - c) ^ (m + 1) =
      ((γ - c) / (z - c)) ^ N / (γ - z) := by
  have h1 : z - c ≠ 0 := sub_ne_zero.2 hzc
  have h2 : γ - z ≠ 0 := sub_ne_zero.2 hγz
  have hy : (γ - c) / (z - c) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq h1]
    intro h
    exact hγz (by linear_combination h)
  have hsum : ∑ m ∈ Finset.range N, (γ - c) ^ m / (z - c) ^ (m + 1) =
      (z - c)⁻¹ * ∑ m ∈ Finset.range N, ((γ - c) / (z - c)) ^ m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [div_pow, pow_succ]
    field_simp
  rw [hsum, geom_sum_eq hy]
  have h3 : (γ - c) / (z - c) - 1 = (γ - z) / (z - c) := by
    field_simp
    ring
  rw [h3]
  field_simp
  ring

/-- **Approximation of a Cauchy integral by kernels in `(z - c₀)⁻¹`.** Let `f` be holomorphic on
`V × P` and `γ` a path in `V` with `‖γ t - c₀‖ ≤ q ‖z - c₀‖` for `z ∈ K`, where `q < 1`. Then
`(z, w) ↦ ∫ (γ t - z)⁻¹ f (γ t, w) dt` is a uniform limit on `K × L` of functions holomorphic on
`(ℂ \ {c₀}) × P`. -/
theorem exists_approx_cauchyEdge_inner {V : Set ℂ} {P : Set E} (hP : IsOpen P)
    {f : ℂ × E → ℂ} (hf : DifferentiableOn ℂ f (V ×ˢ P)) {γ : ℝ → ℂ} (hγ : Continuous γ)
    {t₀ t₁ : ℝ} (hγV : ∀ t ∈ [[t₀, t₁]], γ t ∈ V) {K : Set ℂ} (hK : IsCompact K)
    (hKγ : ∀ z ∈ K, ∀ t ∈ [[t₀, t₁]], γ t ≠ z) {L : Set E} (hL : IsCompact L) (hLP : L ⊆ P)
    {c₀ : ℂ} (hKc : ∀ z ∈ K, z ≠ c₀) {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1)
    (hin : ∀ z ∈ K, ∀ t ∈ [[t₀, t₁]], ‖γ t - c₀‖ ≤ q * ‖z - c₀‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ × E → ℂ, DifferentiableOn ℂ g ({c₀}ᶜ ×ˢ P) ∧ ∀ z ∈ K, ∀ w ∈ L,
      ‖(∫ t in t₀..t₁, (γ t - z)⁻¹ * f (γ t, w)) - g (z, w)‖ ≤ ε := by
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ z ∈ K, ∀ t ∈ [[t₀, t₁]], δ ≤ ‖γ t - z‖ := by
    rcases (K ×ˢ [[t₀, t₁]]).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, fun z hz t ht ↦
        absurd (show (z, t) ∈ K ×ˢ [[t₀, t₁]] from ⟨hz, ht⟩) (by simp [h])⟩
    · obtain ⟨p, hp, hmin⟩ := (hK.prod isCompact_uIcc).exists_isMinOn h
        (f := fun p : ℂ × ℝ ↦ ‖γ p.2 - p.1‖) (by fun_prop)
      exact ⟨_, norm_pos_iff.2 (sub_ne_zero.2 (hKγ p.1 hp.1 p.2 hp.2)),
        fun z hz t ht ↦ by simpa using hmin (show (z, t) ∈ K ×ˢ [[t₀, t₁]] from ⟨hz, ht⟩)⟩
  have hfc : ContinuousOn (fun p : ℝ × E ↦ f (γ p.1, p.2)) ([[t₀, t₁]] ×ˢ L) :=
    hf.continuousOn.comp (by fun_prop) fun p hp ↦ ⟨hγV _ hp.1, hLP hp.2⟩
  obtain ⟨M, hM⟩ := (isCompact_uIcc.prod hL).exists_bound_of_continuousOn hfc
  set C₀ : ℝ := (|M| / δ) * |t₁ - t₀| with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (C₀ + 1) by positivity) hq
  refine ⟨fun p ↦ ∫ t in t₀..t₁,
    (-∑ m ∈ Finset.range N, (γ t - c₀) ^ m / (p.1 - c₀) ^ (m + 1)) * f (γ t, p.2), ?_, ?_⟩
  · have hopen : IsOpen ({c₀}ᶜ ×ˢ P) := isOpen_compl_singleton.prod hP
    refine differentiableOn_intervalIntegral hopen (fun t ht ↦ ?_) ?_
    · refine DifferentiableOn.mul ?_ ?_
      · refine (DifferentiableOn.fun_sum fun m _ ↦ ?_).neg
        simp_rw [div_eq_mul_inv]
        refine (differentiableOn_const _).mul ?_
        refine (((differentiableOn_fst (𝕜 := ℂ)).sub (differentiableOn_const c₀)).pow
          (m + 1)).inv ?_
        exact fun p hp ↦ pow_ne_zero _ (sub_ne_zero.2 hp.1)
      · exact hf.comp ((differentiableOn_const _).prodMk differentiableOn_snd)
          fun p hp ↦ ⟨hγV t ht, hp.2⟩
    · refine ContinuousOn.mul ?_ ?_
      · refine (continuousOn_finsetSum _ fun m _ ↦ ContinuousOn.div (by fun_prop)
          (by fun_prop) fun q hq ↦ pow_ne_zero _ (sub_ne_zero.2 hq.1.1)).neg
      · exact hf.continuousOn.comp (by fun_prop) fun q hq ↦ ⟨hγV q.2 hq.2, hq.1.2⟩
  · intro z hz w hw
    have hint : ∀ h : ℝ → ℂ, ContinuousOn h [[t₀, t₁]] → IntervalIntegrable h volume t₀ t₁ :=
      fun h hh ↦ hh.intervalIntegrable
    have hcf : ContinuousOn (fun t ↦ f (γ t, w)) [[t₀, t₁]] :=
      hf.continuousOn.comp (by fun_prop) fun t ht ↦ ⟨hγV t ht, hLP hw⟩
    have hsub := intervalIntegral.integral_sub
      (f := fun t ↦ (γ t - z)⁻¹ * f (γ t, w))
      (g := fun t ↦ (-∑ m ∈ Finset.range N, (γ t - c₀) ^ m / (z - c₀) ^ (m + 1)) * f (γ t, w))
      (hint _ (ContinuousOn.mul
        ((by fun_prop : Continuous fun t ↦ γ t - z).continuousOn.inv₀
          fun t ht ↦ sub_ne_zero.2 (hKγ z hz t ht)) hcf))
      (hint _ (ContinuousOn.mul (continuousOn_finsetSum _ fun m _ ↦
        ContinuousOn.div (by fun_prop) (by fun_prop)
          fun t _ ↦ pow_ne_zero _ (sub_ne_zero.2 (hKc z hz))).neg hcf))
    change ‖(∫ t in t₀..t₁, (γ t - z)⁻¹ * f (γ t, w)) -
      ∫ t in t₀..t₁, (-∑ m ∈ Finset.range N, (γ t - c₀) ^ m / (z - c₀) ^ (m + 1)) *
        f (γ t, w)‖ ≤ ε
    rw [← hsub]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := q ^ N * (|M| / δ))
      fun t ht ↦ ?_).trans ?_
    · have ht' : t ∈ [[t₀, t₁]] := uIoc_subset_uIcc ht
      rw [← sub_mul, inv_add_sum_geom_inner (hKγ z hz t ht') (hKc z hz), norm_mul, norm_div,
        norm_pow]
      have hx : ‖(γ t - c₀) / (z - c₀)‖ ≤ q := by
        rw [norm_div, div_le_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 (hKc z hz)))]
        exact hin z hz t ht'
      have hfb : ‖f (γ t, w)‖ ≤ |M| := (hM (t, w) ⟨ht', hw⟩).trans (le_abs_self M)
      calc ‖(γ t - c₀) / (z - c₀)‖ ^ N / ‖γ t - z‖ * ‖f (γ t, w)‖
          ≤ q ^ N / δ * |M| := by
            gcongr
            · exact hδle z hz t ht'
        _ = q ^ N * (|M| / δ) := by ring
    · calc q ^ N * (|M| / δ) * |t₁ - t₀| = q ^ N * C₀ := by rw [hC₀]; ring
        _ ≤ ε / (C₀ + 1) * C₀ := by gcongr
        _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith

/-- **Runge approximation on a frame**, with holomorphic parameters. Let `f` be holomorphic on
`V × P`, where `V` contains the closed frame `[X₀, X₁] × [Y₀, Y₁] \ (-ρ, ρ)²`. Then `f` is a
uniform limit on `K × L` of functions holomorphic on `ℂ^× × P`, for every compact `K` in the open
frame with `‖z‖ ≥ 2ρ` on `K`, and every compact `L ⊆ P`. -/
theorem exists_approx_punctured_of_frame {X₀ X₁ Y₀ Y₁ ρ : ℝ} (hρ : 0 < ρ) (hX₀ : X₀ < -ρ)
    (hX₁ : ρ < X₁) (hY₀ : Y₀ < -ρ) (hY₁ : ρ < Y₁) {V : Set ℂ}
    (hV : closedFrame X₀ X₁ Y₀ Y₁ ρ ⊆ V) {P : Set E} (hP : IsOpen P) {f : ℂ × E → ℂ}
    (hf : DifferentiableOn ℂ f (V ×ˢ P)) {K : Set ℂ} (hK : IsCompact K)
    (hKO : K ⊆ openFrame X₀ X₁ Y₀ Y₁ ρ) (hK2 : ∀ z ∈ K, 2 * ρ ≤ ‖z‖) {L : Set E}
    (hL : IsCompact L) (hLP : L ⊆ P) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ × E → ℂ, DifferentiableOn ℂ g ({0}ᶜ ×ˢ P) ∧
      ∀ z ∈ K, ∀ w ∈ L, ‖f (z, w) - g (z, w)‖ ≤ ε := by
  rcases K.eq_empty_or_nonempty with hK0 | ⟨z₀, hz₀⟩
  · exact ⟨0, differentiableOn_const 0, fun z hz ↦ by simp [hK0] at hz⟩
  set a : ℂ := ⟨X₀, Y₀⟩
  set b : ℂ := ⟨X₁, Y₁⟩
  set a' : ℂ := ⟨-ρ, -ρ⟩
  set b' : ℂ := ⟨ρ, ρ⟩
  have hbdO : rectBoundary a b ⊆ V := fun u hu ↦ hV ⟨hu.1, fun h ↦ hu.2
    ⟨⟨by simp [a]; linarith [h.1.1], by simp [b]; linarith [h.1.2]⟩,
      ⟨by simp [a]; linarith [h.2.1], by simp [b]; linarith [h.2.2]⟩⟩⟩
  have hbdI : rectBoundary a' b' ⊆ V := fun u hu ↦ hV ⟨⟨⟨by linarith [hu.1.1.1],
    by linarith [hu.1.1.2]⟩, ⟨by linarith [hu.1.2.1], by linarith [hu.1.2.2]⟩⟩, hu.2⟩
  have hKrect : K ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im := fun z hz ↦ (hKO hz).1
  -- the outer boundary integral, approximated by entire functions
  set Φ : ℂ × E → ℂ := fun p ↦ ∑ s, RectSide.cauchy f a b s p
  have hΦ : DifferentiableOn ℂ Φ ((Ioo a.re b.re ×ℂ Ioo a.im b.im) ×ˢ P) := by
    refine DifferentiableOn.fun_sum fun s _ ↦ ?_
    refine (RectSide.differentiableOn_cauchy_of_boundary (by simp [a, b]; linarith)
      (by simp [a, b]; linarith) hbdO hP hf s).mono (prod_mono (fun z hz hzs ↦ ?_) subset_rfl)
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
    cases s
    · have := (RectSide.set_bottom_subset hzs).2; simp at this; linarith
    · have := (RectSide.set_right_subset hzs).1; simp at this; linarith
    · have := (RectSide.set_top_subset hzs).2; simp at this; linarith
    · have := (RectSide.set_left_subset hzs).1; simp at this; linarith
  obtain ⟨δ₀, hδ₀, hKδ⟩ := exists_margin_of_isCompact hK hKrect
  obtain ⟨m1, m2, m3, m4⟩ := hKδ z₀ hz₀
  obtain ⟨gO, hgO, hO⟩ := exists_approx_entire_of_rect
    (a := ⟨a.re + δ₀ / 2, a.im + δ₀ / 2⟩) (b := ⟨b.re - δ₀ / 2, b.im - δ₀ / 2⟩)
    (by simp; linarith) (by simp; linarith)
    (V := Ioo a.re b.re ×ℂ Ioo a.im b.im) (fun u hu ↦ ⟨⟨by linarith [hu.1.1],
      by linarith [hu.1.2]⟩, ⟨by linarith [hu.2.1], by linarith [hu.2.2]⟩⟩)
    hP hΦ hK (fun z hz ↦ by
      obtain ⟨n1, n2, n3, n4⟩ := hKδ z hz
      exact ⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by simp; linarith, by simp; linarith⟩⟩)
    hL hLP (show 0 < ε / 2 by positivity)
  -- the inner side integrals, approximated by functions holomorphic on `ℂ^×`
  have hKsq : ∀ z ∈ K, ∀ u ∈ Icc a'.re b'.re ×ℂ Icc a'.im b'.im, u ≠ z := by
    intro z hz u hu h
    exact (hKO hz).2 (h ▸ hu)
  have hK0 : ∀ z ∈ K, z ≠ 0 := fun z hz h ↦ by
    have := hK2 z hz; rw [h, norm_zero] at this; linarith
  have hq : √2 / 2 < 1 := by
    rw [div_lt_one two_pos, Real.sqrt_lt' two_pos]; norm_num
  have hin : ∀ u ∈ Icc a'.re b'.re ×ℂ Icc a'.im b'.im, ∀ z ∈ K,
      ‖u - 0‖ ≤ √2 / 2 * ‖z - 0‖ := by
    intro u hu z hz
    rw [sub_zero, sub_zero]
    refine (norm_le_sqrt_two_mul_max u).trans ?_
    have h1 : max |u.re| |u.im| ≤ ρ := max_le (abs_le.2 ⟨hu.1.1, hu.1.2⟩)
      (abs_le.2 ⟨hu.2.1, hu.2.2⟩)
    have := hK2 z hz
    have h2 : 0 ≤ √2 := Real.sqrt_nonneg _
    nlinarith
  have hε8 : 0 < ε / 8 := by positivity
  have hedge : ∀ γ : ℝ → ℂ, Continuous γ → ∀ t₀ t₁ : ℝ,
      (∀ t ∈ [[t₀, t₁]], γ t ∈ rectBoundary a' b') →
      ∃ g : ℂ × E → ℂ, DifferentiableOn ℂ g ({0}ᶜ ×ˢ P) ∧ ∀ z ∈ K, ∀ w ∈ L,
        ‖(∫ t in t₀..t₁, (γ t - z)⁻¹ * f (γ t, w)) - g (z, w)‖ ≤ ε / 8 := by
    intro γ hγ t₀ t₁ hγb
    exact exists_approx_cauchyEdge_inner hP hf hγ (fun t ht ↦ hbdI (hγb t ht)) hK
      (fun z hz t ht ↦ hKsq z hz _ (hγb t ht).1) hL hLP hK0 (by positivity) hq
      (fun z hz t ht ↦ hin _ (hγb t ht).1 z hz) hε8
  have hle : a'.re ≤ b'.re := by simp [a', b']; linarith
  have hle' : a'.im ≤ b'.im := by simp [a', b']; linarith
  obtain ⟨gB, hgB, hB⟩ := hedge (fun x : ℝ ↦ (x : ℂ) + a'.im * I) (by fun_prop) a'.re b'.re
    fun x hx ↦ mapsTo_horizontal_rectBoundary hle hle' (Or.inl rfl) hx
  obtain ⟨gT, hgT, hT⟩ := hedge (fun x : ℝ ↦ (x : ℂ) + b'.im * I) (by fun_prop) a'.re b'.re
    fun x hx ↦ mapsTo_horizontal_rectBoundary hle hle' (Or.inr rfl) hx
  obtain ⟨gR, hgR, hR⟩ := hedge (fun y : ℝ ↦ (b'.re : ℂ) + y * I) (by fun_prop) a'.im b'.im
    fun y hy ↦ mapsTo_vertical_rectBoundary hle hle' (Or.inr rfl) hy
  obtain ⟨gL, hgL, hL'⟩ := hedge (fun y : ℝ ↦ (a'.re : ℂ) + y * I) (by fun_prop) a'.im b'.im
    fun y hy ↦ mapsTo_vertical_rectBoundary hle hle' (Or.inl rfl) hy
  set c : ℂ := (2 * π * I)⁻¹
  refine ⟨fun p ↦ gO p - (c * gB p + c * (I * gR p) - c * gT p - c * (I * gL p)), ?_,
    fun z hz w hw ↦ ?_⟩
  · refine (hgO.mono (prod_mono (subset_univ _) subset_rfl)).sub ?_
    exact (((hgB.const_mul c).add ((hgR.const_mul I).const_mul c)).sub
      (hgT.const_mul c)).sub ((hgL.const_mul I).const_mul c)
  · have hframe := frame_cauchy hρ hX₀ hX₁ hY₀ hY₁ hV hP hf (hKO hz) (hLP hw)
    rw [← hframe]
    rw [RectSide.sum_univ_cauchy (a := a') (b := b')]
    simp only [cauchyBottom, cauchyRight, cauchyTop, cauchyLeft]
    have hcI : ‖c * I‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, mul_one]; exact norm_two_pi_I_inv_le_one
    have hc1 : ‖c‖ ≤ 1 := norm_two_pi_I_inv_le_one
    set IB := ∫ x : ℝ in a'.re..b'.re, ((x : ℂ) + a'.im * I - z)⁻¹ * f ((x : ℂ) + a'.im * I, w)
    set IT := ∫ x : ℝ in a'.re..b'.re, ((x : ℂ) + b'.im * I - z)⁻¹ * f ((x : ℂ) + b'.im * I, w)
    set IR := ∫ y : ℝ in a'.im..b'.im, ((b'.re : ℂ) + y * I - z)⁻¹ * f ((b'.re : ℂ) + y * I, w)
    set IL := ∫ y : ℝ in a'.im..b'.im, ((a'.re : ℂ) + y * I - z)⁻¹ * f ((a'.re : ℂ) + y * I, w)
    have heq : Φ (z, w) - (c * IB + c * (I * IR) + -(c * IT) + -(c * (I * IL))) -
        (gO (z, w) - (c * gB (z, w) + c * (I * gR (z, w)) - c * gT (z, w) -
          c * (I * gL (z, w)))) =
        (Φ (z, w) - gO (z, w)) - (c * (IB - gB (z, w)) + (c * I) * (IR - gR (z, w)) -
          c * (IT - gT (z, w)) - (c * I) * (IL - gL (z, w))) := by ring
    change ‖Φ (z, w) - (c * IB + c * (I * IR) + -(c * IT) + -(c * (I * IL))) -
        (gO (z, w) - (c * gB (z, w) + c * (I * gR (z, w)) - c * gT (z, w) -
          c * (I * gL (z, w))))‖ ≤ ε
    rw [heq]
    have e0 : ‖Φ (z, w) - gO (z, w)‖ ≤ ε / 2 := hO z hz w hw
    have e1 : ‖c * (IB - gB (z, w))‖ ≤ ε / 8 := by
      rw [norm_mul]; nlinarith [hB z hz w hw, norm_nonneg c, norm_nonneg (IB - gB (z, w))]
    have e2 : ‖(c * I) * (IR - gR (z, w))‖ ≤ ε / 8 := by
      rw [norm_mul]; nlinarith [hR z hz w hw, norm_nonneg (c * I), norm_nonneg (IR - gR (z, w))]
    have e3 : ‖c * (IT - gT (z, w))‖ ≤ ε / 8 := by
      rw [norm_mul]; nlinarith [hT z hz w hw, norm_nonneg c, norm_nonneg (IT - gT (z, w))]
    have e4 : ‖(c * I) * (IL - gL (z, w))‖ ≤ ε / 8 := by
      rw [norm_mul]; nlinarith [hL' z hz w hw, norm_nonneg (c * I), norm_nonneg (IL - gL (z, w))]
    calc _ ≤ ‖Φ (z, w) - gO (z, w)‖ + ‖c * (IB - gB (z, w)) + (c * I) * (IR - gR (z, w)) -
          c * (IT - gT (z, w)) - (c * I) * (IL - gL (z, w))‖ := norm_sub_le _ _
      _ ≤ ‖Φ (z, w) - gO (z, w)‖ + (‖c * (IB - gB (z, w))‖ + ‖(c * I) * (IR - gR (z, w))‖ +
          ‖c * (IT - gT (z, w))‖ + ‖(c * I) * (IL - gL (z, w))‖) := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
      _ ≤ ε := by linarith

end Complex

end
