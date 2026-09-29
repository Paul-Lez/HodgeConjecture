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
# Runge approximation on rectangles, with holomorphic parameters

A function holomorphic near `C × P`, where `C` is a closed rectangle, is a uniform limit on
`K × L` (`K` compact in the interior of `C`, `L ⊆ P` compact) of functions holomorphic on
`ℂ × P`, i.e. entire in the first variable. We write `f` as the sum of its Cauchy integrals over
the four sides of `C` and expand the Cauchy kernel `(ζ - z)⁻¹` in a geometric series about a
point `c = ζ - M n` far outside `C` (`n` the outward normal of the side), which gives
polynomials in `z`.

## Main results

- `Complex.exists_approx_cauchyEdge`: approximation of a Cauchy integral along a path `γ` by
  integrals of polynomial kernels, given a family of centres `c t` with
  `‖z - c t‖ ≤ q ‖γ t - c t‖`, `q < 1`, for `z ∈ K`.
- `Complex.exists_approx_entire_of_rect`: **Runge approximation on a rectangle** with holomorphic
  parameters.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Interval Real Topology

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The geometric series for the Cauchy kernel: for `x = (z - c) / (γ - c)`,
`(γ - z)⁻¹ - ∑_{m < N} (z - c)^m / (γ - c)^(m+1) = x^N / (γ - z)`. -/
lemma inv_sub_sum_geom {γ z c : ℂ} (hγz : γ ≠ z) (hγc : γ ≠ c) (N : ℕ) :
    (γ - z)⁻¹ - ∑ m ∈ Finset.range N, (z - c) ^ m / (γ - c) ^ (m + 1) =
      ((z - c) / (γ - c)) ^ N / (γ - z) := by
  have h1 : γ - c ≠ 0 := sub_ne_zero.2 hγc
  have h2 : γ - z ≠ 0 := sub_ne_zero.2 hγz
  have hx : (z - c) / (γ - c) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq h1]
    intro h
    exact hγz (by linear_combination -h)
  have hsum : ∑ m ∈ Finset.range N, (z - c) ^ m / (γ - c) ^ (m + 1) =
      (γ - c)⁻¹ * ∑ m ∈ Finset.range N, ((z - c) / (γ - c)) ^ m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [div_pow, pow_succ]
    field_simp
  rw [hsum, geom_sum_eq hx]
  have h3 : (z - c) / (γ - c) - 1 = -(γ - z) / (γ - c) := by
    field_simp
    ring
  rw [h3]
  field_simp
  ring

/-- **Approximation of a Cauchy integral by polynomial kernels.** Let `f` be holomorphic on
`V × P`, `γ` a path in `V`, and `c t` centres with `‖z - c t‖ ≤ q ‖γ t - c t‖` for `z ∈ K`,
where `q < 1`. Then `(z, w) ↦ ∫ (γ t - z)⁻¹ f (γ t, w) dt` is a uniform limit on `K × L` of
functions holomorphic on `ℂ × P`. -/
theorem exists_approx_cauchyEdge {V : Set ℂ} {P : Set E} (hP : IsOpen P) {f : ℂ × E → ℂ}
    (hf : DifferentiableOn ℂ f (V ×ˢ P)) {γ c : ℝ → ℂ} (hγ : Continuous γ) (hc : Continuous c)
    {t₀ t₁ : ℝ} (hγV : ∀ t ∈ [[t₀, t₁]], γ t ∈ V) (hγc : ∀ t ∈ [[t₀, t₁]], γ t ≠ c t)
    {K : Set ℂ} (hK : IsCompact K) (hKγ : ∀ z ∈ K, ∀ t ∈ [[t₀, t₁]], γ t ≠ z)
    {L : Set E} (hL : IsCompact L) (hLP : L ⊆ P) {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1)
    (hout : ∀ z ∈ K, ∀ t ∈ [[t₀, t₁]], ‖z - c t‖ ≤ q * ‖γ t - c t‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ × E → ℂ, DifferentiableOn ℂ g (univ ×ˢ P) ∧ ∀ z ∈ K, ∀ w ∈ L,
      ‖(∫ t in t₀..t₁, (γ t - z)⁻¹ * f (γ t, w)) - g (z, w)‖ ≤ ε := by
  -- a lower bound for the distance from `K` to the path
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ z ∈ K, ∀ t ∈ [[t₀, t₁]], δ ≤ ‖γ t - z‖ := by
    rcases (K ×ˢ [[t₀, t₁]]).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, fun z hz t ht ↦
        absurd (show (z, t) ∈ K ×ˢ [[t₀, t₁]] from ⟨hz, ht⟩) (by simp [h])⟩
    · obtain ⟨p, hp, hmin⟩ := (hK.prod isCompact_uIcc).exists_isMinOn h
        (f := fun p : ℂ × ℝ ↦ ‖γ p.2 - p.1‖) (by fun_prop)
      exact ⟨_, norm_pos_iff.2 (sub_ne_zero.2 (hKγ p.1 hp.1 p.2 hp.2)),
        fun z hz t ht ↦ by simpa using hmin (show (z, t) ∈ K ×ˢ [[t₀, t₁]] from ⟨hz, ht⟩)⟩
  -- a bound for `f` on the path times `L`
  have hfc : ContinuousOn (fun p : ℝ × E ↦ f (γ p.1, p.2)) ([[t₀, t₁]] ×ˢ L) :=
    hf.continuousOn.comp (by fun_prop) fun p hp ↦ ⟨hγV _ hp.1, hLP hp.2⟩
  obtain ⟨M, hM⟩ := (isCompact_uIcc.prod hL).exists_bound_of_continuousOn hfc
  set C₀ : ℝ := (|M| / δ) * |t₁ - t₀| with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (C₀ + 1) by positivity) hq
  refine ⟨fun p ↦ ∫ t in t₀..t₁,
    (∑ m ∈ Finset.range N, (p.1 - c t) ^ m / (γ t - c t) ^ (m + 1)) * f (γ t, p.2), ?_, ?_⟩
  · refine differentiableOn_intervalIntegral (isOpen_univ.prod hP) (fun t ht ↦ ?_) ?_
    · refine DifferentiableOn.mul ?_ ?_
      · refine DifferentiableOn.fun_sum fun m _ ↦ ?_
        simp_rw [div_eq_mul_inv]
        exact (((differentiableOn_fst (𝕜 := ℂ)).sub (differentiableOn_const (c t))).pow
          m).mul_const _
      · exact hf.comp ((differentiableOn_const _).prodMk differentiableOn_snd)
          fun p hp ↦ ⟨hγV t ht, hp.2⟩
    · refine ContinuousOn.mul ?_ ?_
      · refine continuousOn_finsetSum _ fun m _ ↦ ContinuousOn.div (by fun_prop) (by fun_prop)
          fun q hq ↦ pow_ne_zero _ (sub_ne_zero.2 (hγc q.2 hq.2))
      · exact hf.continuousOn.comp (by fun_prop) fun q hq ↦ ⟨hγV q.2 hq.2, hq.1.2⟩
  · intro z hz w hw
    have hint : ∀ h : ℝ → ℂ, ContinuousOn h [[t₀, t₁]] → IntervalIntegrable h volume t₀ t₁ :=
      fun h hh ↦ hh.intervalIntegrable
    have hcf : ContinuousOn (fun t ↦ f (γ t, w)) [[t₀, t₁]] :=
      hf.continuousOn.comp (by fun_prop) fun t ht ↦ ⟨hγV t ht, hLP hw⟩
    have hsub := intervalIntegral.integral_sub
      (f := fun t ↦ (γ t - z)⁻¹ * f (γ t, w))
      (g := fun t ↦ (∑ m ∈ Finset.range N, (z - c t) ^ m / (γ t - c t) ^ (m + 1)) * f (γ t, w))
      (hint _ (ContinuousOn.mul
        ((by fun_prop : Continuous fun t ↦ γ t - z).continuousOn.inv₀
          fun t ht ↦ sub_ne_zero.2 (hKγ z hz t ht)) hcf))
      (hint _ (ContinuousOn.mul (continuousOn_finsetSum _ fun m _ ↦
        ContinuousOn.div (by fun_prop) (by fun_prop)
          fun t ht ↦ pow_ne_zero _ (sub_ne_zero.2 (hγc t ht))) hcf))
    change ‖(∫ t in t₀..t₁, (γ t - z)⁻¹ * f (γ t, w)) -
      ∫ t in t₀..t₁, (∑ m ∈ Finset.range N, (z - c t) ^ m / (γ t - c t) ^ (m + 1)) *
        f (γ t, w)‖ ≤ ε
    rw [← hsub]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := q ^ N * (|M| / δ))
      fun t ht ↦ ?_).trans ?_
    · have ht' : t ∈ [[t₀, t₁]] := uIoc_subset_uIcc ht
      rw [← sub_mul, inv_sub_sum_geom (hKγ z hz t ht') (hγc t ht'), norm_mul, norm_div,
        norm_pow]
      have hx : ‖(z - c t) / (γ t - c t)‖ ≤ q := by
        rw [norm_div, div_le_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 (hγc t ht')))]
        exact hout z hz t ht'
      have hfb : ‖f (γ t, w)‖ ≤ |M| := (hM (t, w) ⟨ht', hw⟩).trans (le_abs_self M)
      calc ‖(z - c t) / (γ t - c t)‖ ^ N / ‖γ t - z‖ * ‖f (γ t, w)‖
          ≤ q ^ N / δ * |M| := by
            gcongr
            · exact hδle z hz t ht'
        _ = q ^ N * (|M| / δ) := by ring
    · calc q ^ N * (|M| / δ) * |t₁ - t₀| = q ^ N * C₀ := by rw [hC₀]; ring
        _ ≤ ε / (C₀ + 1) * C₀ := by gcongr
        _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith

/-- The constant `(2πi)⁻¹` has norm at most one. -/
lemma norm_two_pi_I_inv_le_one : ‖(2 * π * I)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  refine inv_le_one_of_one_le₀ ?_
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  linarith [Real.one_le_pi_div_two]

/-- A compact subset of an open rectangle keeps a positive distance from its sides. -/
lemma exists_margin_of_isCompact {a b : ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hKab : K ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im) :
    ∃ δ > 0, ∀ z ∈ K, a.re + δ ≤ z.re ∧ z.re ≤ b.re - δ ∧ a.im + δ ≤ z.im ∧
      z.im ≤ b.im - δ := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, fun z hz ↦ by simp [h] at hz⟩
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn h
    (f := fun z : ℂ ↦ min (min (z.re - a.re) (b.re - z.re)) (min (z.im - a.im) (b.im - z.im)))
    (by fun_prop)
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hKab hp
  refine ⟨min (min (p.re - a.re) (b.re - p.re)) (min (p.im - a.im) (b.im - p.im)),
    lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith)),
    fun z hz ↦ ?_⟩
  have h : min (min (p.re - a.re) (b.re - p.re)) (min (p.im - a.im) (b.im - p.im)) ≤
      min (min (z.re - a.re) (b.re - z.re)) (min (z.im - a.im) (b.im - z.im)) := hmin hz
  have e1 := h.trans ((min_le_left _ _).trans (min_le_left _ _))
  have e2 := h.trans ((min_le_left _ _).trans (min_le_right _ _))
  have e3 := h.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e4 := h.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The geometric estimate behind the choice of centres: if `|w.re| ≤ M - δ`, `|w.im| ≤ D` and
`δ² + D² ≤ δ M`, then `‖w‖ ≤ √(1 - δ / M) · M`. -/
lemma norm_le_sqrt_mul {w : ℂ} {M δ D : ℝ} (hδ : 0 < δ) (hMδ : δ ≤ M)
    (hMD : δ ^ 2 + D ^ 2 ≤ δ * M) (hre : |w.re| ≤ M - δ) (him : |w.im| ≤ D) :
    ‖w‖ ≤ √(1 - δ / M) * M := by
  have hM : 0 < M := hδ.trans_le hMδ
  have h0 : 0 ≤ 1 - δ / M := by rw [sub_nonneg, div_le_one hM]; exact hMδ
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
    Real.sq_sqrt h0, Complex.sq_norm, Complex.normSq_apply]
  have h1 : w.re * w.re ≤ (M - δ) ^ 2 := by
    rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre 2
  have h2 : w.im * w.im ≤ D ^ 2 := by
    rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
  have h3 : (1 - δ / M) * M ^ 2 = M ^ 2 - δ * M := by field_simp
  rw [h3]
  nlinarith

/-- **Runge approximation on a rectangle**, with holomorphic parameters. Let `f` be holomorphic on
`V × P`, where `V` contains the closed rectangle with corners `a`, `b`. Then `f` is a uniform
limit on `K × L` of functions holomorphic on `ℂ × P`, for every compact `K` in the open rectangle
and every compact `L ⊆ P`. -/
theorem exists_approx_entire_of_rect {a b : ℂ} (hre : a.re < b.re) (him : a.im < b.im)
    {V : Set ℂ} (hab : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ V) {P : Set E} (hP : IsOpen P)
    {f : ℂ × E → ℂ} (hf : DifferentiableOn ℂ f (V ×ˢ P)) {K : Set ℂ} (hK : IsCompact K)
    (hKab : K ⊆ Ioo a.re b.re ×ℂ Ioo a.im b.im) {L : Set E} (hL : IsCompact L) (hLP : L ⊆ P)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ × E → ℂ, DifferentiableOn ℂ g (univ ×ˢ P) ∧
      ∀ z ∈ K, ∀ w ∈ L, ‖f (z, w) - g (z, w)‖ ≤ ε := by
  obtain ⟨δ, hδ, hKδ⟩ := exists_margin_of_isCompact hK hKab
  set D : ℝ := max (b.re - a.re) (b.im - a.im) with hD
  have hDre : b.re - a.re ≤ D := le_max_left _ _
  have hDim : b.im - a.im ≤ D := le_max_right _ _
  have hD0 : 0 ≤ D := le_trans (by linarith) hDre
  set M : ℝ := D + δ + D ^ 2 / δ with hM
  have hMδ : δ ≤ M := by have : 0 ≤ D ^ 2 / δ := by positivity
                         linarith
  have hMD : δ ^ 2 + D ^ 2 ≤ δ * M := by
    rw [hM, mul_add, mul_add, mul_div_cancel₀ _ hδ.ne']
    nlinarith
  have hMD' : D ≤ M := by have : 0 ≤ D ^ 2 / δ := by positivity
                          linarith
  set q : ℝ := √(1 - δ / M)
  have hM0 : 0 < M := hδ.trans_le hMδ
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow, sub_lt_self_iff]
    positivity
  have hgeom := fun (w : ℂ) (h1 : |w.re| ≤ M - δ) (h2 : |w.im| ≤ D) ↦
    norm_le_sqrt_mul hδ hMδ hMD h1 h2
  have hgeom' : ∀ w : ℂ, |w.im| ≤ M - δ → |w.re| ≤ D → ‖w‖ ≤ q * M := fun w h1 h2 ↦ by
    have := norm_le_sqrt_mul (w := w * I) hδ hMδ hMD (by simpa using h1) (by simpa using h2)
    simpa using this
  have hKo : ∀ z ∈ K, z ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im := fun z hz ↦ hKab hz
  have hε4 : 0 < ε / 4 := by positivity
  -- bottom side, centres `c = γ + M i`
  obtain ⟨gB, hgB, hB⟩ := exists_approx_cauchyEdge (V := V) hP hf
    (γ := fun x : ℝ ↦ (x : ℂ) + a.im * I) (c := fun x : ℝ ↦ (x : ℂ) + a.im * I + M * I)
    (by fun_prop) (by fun_prop) (t₀ := a.re) (t₁ := b.re)
    (fun x hx ↦ hab (mapsTo_horizontal_rectBoundary hre.le him.le (Or.inl rfl) hx).1)
    (fun x _ h ↦ by have := congrArg Complex.im h; simp at this; linarith) hK
    (fun z hz x _ h ↦ by
      have := congrArg Complex.im h; simp at this; linarith [(hKδ z hz).2.2.1])
    hL hLP hq0 hq1 (fun z hz x hx ↦ by
      rw [uIcc_of_le hre.le] at hx
      obtain ⟨h1, h2, h3, h4⟩ := hKδ z hz
      have : ‖(x : ℂ) + a.im * I - ((x : ℂ) + a.im * I + M * I)‖ = M := by
        simp [abs_of_pos hM0]
      rw [this]
      refine hgeom' _ ?_ ?_
      · rw [abs_le]; constructor <;> simp <;> linarith
      · rw [abs_le]; constructor <;> simp <;> linarith [hx.1, hx.2]) hε4
  -- top side, centres `c = γ - M i`
  obtain ⟨gT, hgT, hT⟩ := exists_approx_cauchyEdge (V := V) hP hf
    (γ := fun x : ℝ ↦ (x : ℂ) + b.im * I) (c := fun x : ℝ ↦ (x : ℂ) + b.im * I - M * I)
    (by fun_prop) (by fun_prop) (t₀ := a.re) (t₁ := b.re)
    (fun x hx ↦ hab (mapsTo_horizontal_rectBoundary hre.le him.le (Or.inr rfl) hx).1)
    (fun x _ h ↦ by have := congrArg Complex.im h; simp at this; linarith) hK
    (fun z hz x _ h ↦ by
      have := congrArg Complex.im h; simp at this; linarith [(hKδ z hz).2.2.2])
    hL hLP hq0 hq1 (fun z hz x hx ↦ by
      rw [uIcc_of_le hre.le] at hx
      obtain ⟨h1, h2, h3, h4⟩ := hKδ z hz
      have : ‖(x : ℂ) + b.im * I - ((x : ℂ) + b.im * I - M * I)‖ = M := by
        simp [abs_of_pos hM0]
      rw [this]
      refine hgeom' _ ?_ ?_
      · rw [abs_le]; constructor <;> simp <;> linarith
      · rw [abs_le]; constructor <;> simp <;> linarith [hx.1, hx.2]) hε4
  -- right side, centres `c = γ - M`
  obtain ⟨gR, hgR, hR⟩ := exists_approx_cauchyEdge (V := V) hP hf
    (γ := fun y : ℝ ↦ (b.re : ℂ) + y * I) (c := fun y : ℝ ↦ (b.re : ℂ) + y * I - M)
    (by fun_prop) (by fun_prop) (t₀ := a.im) (t₁ := b.im)
    (fun y hy ↦ hab (mapsTo_vertical_rectBoundary hre.le him.le (Or.inr rfl) hy).1)
    (fun y _ h ↦ by have := congrArg Complex.re h; simp at this; linarith) hK
    (fun z hz y _ h ↦ by
      have := congrArg Complex.re h; simp at this; linarith [(hKδ z hz).2.1])
    hL hLP hq0 hq1 (fun z hz y hy ↦ by
      rw [uIcc_of_le him.le] at hy
      obtain ⟨h1, h2, h3, h4⟩ := hKδ z hz
      have : ‖(b.re : ℂ) + y * I - ((b.re : ℂ) + y * I - M)‖ = M := by
        simp [abs_of_pos hM0]
      rw [this]
      refine hgeom _ ?_ ?_
      · rw [abs_le]; constructor <;> simp <;> linarith
      · rw [abs_le]; constructor <;> simp <;> linarith [hy.1, hy.2]) hε4
  -- left side, centres `c = γ + M`
  obtain ⟨gL, hgL, hL'⟩ := exists_approx_cauchyEdge (V := V) hP hf
    (γ := fun y : ℝ ↦ (a.re : ℂ) + y * I) (c := fun y : ℝ ↦ (a.re : ℂ) + y * I + M)
    (by fun_prop) (by fun_prop) (t₀ := a.im) (t₁ := b.im)
    (fun y hy ↦ hab (mapsTo_vertical_rectBoundary hre.le him.le (Or.inl rfl) hy).1)
    (fun y _ h ↦ by have := congrArg Complex.re h; simp at this; linarith) hK
    (fun z hz y _ h ↦ by
      have := congrArg Complex.re h; simp at this; linarith [(hKδ z hz).1])
    hL hLP hq0 hq1 (fun z hz y hy ↦ by
      rw [uIcc_of_le him.le] at hy
      obtain ⟨h1, h2, h3, h4⟩ := hKδ z hz
      have : ‖(a.re : ℂ) + y * I - ((a.re : ℂ) + y * I + M)‖ = M := by
        simp [abs_of_pos hM0]
      rw [this]
      refine hgeom _ ?_ ?_
      · rw [abs_le]; constructor <;> simp <;> linarith
      · rw [abs_le]; constructor <;> simp <;> linarith [hy.1, hy.2]) hε4
  set c : ℂ := (2 * π * I)⁻¹ with hc
  refine ⟨fun p ↦ c * gB p + c * (I * gR p) - c * gT p - c * (I * gL p), ?_, fun z hz w hw ↦ ?_⟩
  · exact ((((hgB.const_mul c).add ((hgR.const_mul I).const_mul c)).sub
      (hgT.const_mul c)).sub ((hgL.const_mul I).const_mul c))
  · have hsum := sum_cauchySides_of_mem hab hf (hKo z hz) (hLP hw)
    simp only [cauchyBottom, cauchyRight, cauchyTop, cauchyLeft] at hsum
    rw [← hsum]
    have hcI : ‖c * I‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, mul_one]; exact norm_two_pi_I_inv_le_one
    have hc1 : ‖c‖ ≤ 1 := norm_two_pi_I_inv_le_one
    set IB := ∫ x : ℝ in a.re..b.re, ((x : ℂ) + a.im * I - z)⁻¹ * f ((x : ℂ) + a.im * I, w)
    set IT := ∫ x : ℝ in a.re..b.re, ((x : ℂ) + b.im * I - z)⁻¹ * f ((x : ℂ) + b.im * I, w)
    set IR := ∫ y : ℝ in a.im..b.im, ((b.re : ℂ) + y * I - z)⁻¹ * f ((b.re : ℂ) + y * I, w)
    set IL := ∫ y : ℝ in a.im..b.im, ((a.re : ℂ) + y * I - z)⁻¹ * f ((a.re : ℂ) + y * I, w)
    have heq : c * IB + c * (I * IR) + -(c * IT) + -(c * (I * IL)) -
        (c * gB (z, w) + c * (I * gR (z, w)) - c * gT (z, w) - c * (I * gL (z, w))) =
        c * (IB - gB (z, w)) + (c * I) * (IR - gR (z, w)) - c * (IT - gT (z, w)) -
          (c * I) * (IL - gL (z, w)) := by ring
    rw [heq]
    have e1 : ‖c * (IB - gB (z, w))‖ ≤ ε / 4 := by
      rw [norm_mul]; nlinarith [hB z hz w hw, norm_nonneg c, norm_nonneg (IB - gB (z, w))]
    have e2 : ‖(c * I) * (IR - gR (z, w))‖ ≤ ε / 4 := by
      rw [norm_mul]; nlinarith [hR z hz w hw, norm_nonneg (c * I), norm_nonneg (IR - gR (z, w))]
    have e3 : ‖c * (IT - gT (z, w))‖ ≤ ε / 4 := by
      rw [norm_mul]; nlinarith [hT z hz w hw, norm_nonneg c, norm_nonneg (IT - gT (z, w))]
    have e4 : ‖(c * I) * (IL - gL (z, w))‖ ≤ ε / 4 := by
      rw [norm_mul]; nlinarith [hL' z hz w hw, norm_nonneg (c * I), norm_nonneg (IL - gL (z, w))]
    calc _ ≤ ‖c * (IB - gB (z, w)) + (c * I) * (IR - gR (z, w)) - c * (IT - gT (z, w))‖ +
          ‖(c * I) * (IL - gL (z, w))‖ := norm_sub_le _ _
      _ ≤ ‖c * (IB - gB (z, w)) + (c * I) * (IR - gR (z, w))‖ + ‖c * (IT - gT (z, w))‖ +
          ‖(c * I) * (IL - gL (z, w))‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖c * (IB - gB (z, w))‖ + ‖(c * I) * (IR - gR (z, w))‖ + ‖c * (IT - gT (z, w))‖ +
          ‖(c * I) * (IL - gL (z, w))‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ε := by linarith

end Complex

end
