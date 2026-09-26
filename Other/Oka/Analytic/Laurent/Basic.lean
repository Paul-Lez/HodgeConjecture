/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Laurent expansions in one variable

A function holomorphic on an open annulus `A = {z | r < ‖z‖, ‖z‖ < R}` about the origin
(`r : ℝ`, `R : ℝ≥0∞`; a negative `r` gives a disc, `R = ∞` an exterior domain) is the sum of its
Laurent series `∑_{k : ℤ} a_k z ^ k`, where
`a_k = (2πi)⁻¹ ∮_{|z| = ρ} z ^ (-k - 1) f(z) dz` for any `ρ` with `max r 0 < ρ < R`.

## Main definitions

- `Laurent.annulus r R`: the open annulus `{z | r < ‖z‖ ∧ ‖z‖ₑ < R}`.
- `Laurent.IsRadius r R ρ`: `ρ` is the radius of a circle inside `annulus r R`.
- `Laurent.coeff f ρ k`: the `k`-th Laurent coefficient of `f` computed on the circle of
  radius `ρ`.
- `Laurent.plusPart f ρ`, `Laurent.minusPart f ρ`: the sums of the terms of nonnegative,
  resp. negative, degree.

## Main results

- `Laurent.hasSum_circleIntegral_of_dominated`: term-by-term integration over a circle.
- `Laurent.coeff_eq_of_isRadius`: the coefficients do not depend on the radius.
- `Laurent.norm_coeff_le`: the Cauchy estimate `‖a_k‖ ≤ M ρ ^ (-k)`.
- `Laurent.hasSum_coeff`: the Laurent expansion `f w = ∑ k, a_k w ^ k` on the annulus, and
  `Laurent.summable_norm_coeff_mul` its absolute convergence.
- `Laurent.exists_summable_bound`: the Weierstrass bound making the convergence locally uniform,
  and `Laurent.tendstoLocallyUniformlyOn`.
- `Laurent.coeff_eq_of_hasSum`: uniqueness of the coefficients.
- `Laurent.coeff_eq_zero_of_neg`: on a disc (`r < 0`) the coefficients of negative degree vanish.
- `Laurent.differentiableOn_plusPart`, `Laurent.differentiableOn_minusPart`,
  `Laurent.plusPart_add_minusPart`, `Laurent.tendsto_minusPart_cobounded`: the splitting
  `f = f₊ + f₋` with `f₊` holomorphic on `{‖z‖ < R}` and `f₋` holomorphic on `{r < ‖z‖}`,
  tending to `0` at infinity.
-/

@[expose] public section

open Complex Metric Filter Set Bornology
open scoped Real Topology ENNReal

namespace Laurent

/-- The open annulus `{z | r < ‖z‖ ∧ ‖z‖ < R}` about the origin. For `r < 0` it is the open disc
of radius `R`, for `R = ∞` the exterior of the closed disc of radius `r`. -/
def annulus (r : ℝ) (R : ℝ≥0∞) : Set ℂ := {z | r < ‖z‖ ∧ ‖z‖ₑ < R}

/-- `ρ` is the radius of a circle about the origin contained in `annulus r R`. -/
def IsRadius (r : ℝ) (R : ℝ≥0∞) (ρ : ℝ) : Prop := 0 < ρ ∧ r < ρ ∧ ENNReal.ofReal ρ < R

/-- The `k`-th Laurent coefficient `(2πi)⁻¹ ∮_{|z| = ρ} z ^ (-k - 1) f(z) dz` of `f`,
computed on the circle of radius `ρ`. -/
noncomputable def coeff (f : ℂ → ℂ) (ρ : ℝ) (k : ℤ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ z in C(0, ρ), z ^ (-k - 1) * f z

variable {r : ℝ} {R : ℝ≥0∞} {ρ : ℝ}

lemma mem_annulus {z : ℂ} : z ∈ annulus r R ↔ r < ‖z‖ ∧ ‖z‖ₑ < R := Iff.rfl

lemma isOpen_annulus : IsOpen (annulus r R) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_enorm continuous_const)

lemma enorm_lt_iff_ofReal_lt {z : ℂ} : ‖z‖ₑ < R ↔ ENNReal.ofReal ‖z‖ < R := by
  rw [ofReal_norm]

lemma mem_annulus_iff_isRadius {z : ℂ} (hz : z ≠ 0) : z ∈ annulus r R ↔ IsRadius r R ‖z‖ := by
  simp [mem_annulus, IsRadius, enorm_lt_iff_ofReal_lt, norm_pos_iff.2 hz]

lemma IsRadius.pos (h : IsRadius r R ρ) : 0 < ρ := h.1

/-- Every point of the annulus with norm between two admissible radii lies in the annulus. -/
lemma mem_annulus_of_le {ρ₁ ρ₂ : ℝ} (h₁ : IsRadius r R ρ₁) (h₂ : IsRadius r R ρ₂) {z : ℂ}
    (hz₁ : ρ₁ ≤ ‖z‖) (hz₂ : ‖z‖ ≤ ρ₂) : z ∈ annulus r R := by
  refine ⟨h₁.2.1.trans_le hz₁, ?_⟩
  rw [enorm_lt_iff_ofReal_lt]
  exact (ENNReal.ofReal_le_ofReal hz₂).trans_lt h₂.2.2

lemma sphere_subset_annulus (h : IsRadius r R ρ) : sphere (0 : ℂ) ρ ⊆ annulus r R := by
  intro z hz
  rw [mem_sphere_zero_iff_norm] at hz
  exact mem_annulus_of_le h h hz.ge hz.le

/-- An admissible radius below a nonzero point of the annulus. -/
lemma exists_isRadius_lt {z : ℂ} (hz : z ∈ annulus r R) (hz0 : z ≠ 0) :
    ∃ ρ, IsRadius r R ρ ∧ ρ < ‖z‖ := by
  have h0 := norm_pos_iff.2 hz0
  have h1 : max r 0 < ‖z‖ := max_lt hz.1 h0
  refine ⟨(max r 0 + ‖z‖) / 2, ⟨by linarith [le_max_right r 0], by linarith [le_max_left r 0],
    ?_⟩, by linarith⟩
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans_lt (enorm_lt_iff_ofReal_lt.1 hz.2)

lemma exists_isRadius_gt {z : ℂ} (hz : z ∈ annulus r R) :
    ∃ ρ, IsRadius r R ρ ∧ ‖z‖ < ρ := by
  have h := enorm_lt_iff_ofReal_lt.1 hz.2
  obtain ⟨t, -, ht1, ht2⟩ := ENNReal.lt_iff_exists_real_btwn.1 h
  have hzt : ‖z‖ < t := by
    by_contra! hle
    exact (not_le.2 ht1) (ENNReal.ofReal_le_ofReal hle)
  refine ⟨t, ⟨(norm_nonneg z).trans_lt hzt, hz.1.trans hzt, ht2⟩, hzt⟩

/-- Term-by-term integration over a circle of a series dominated by a summable sequence. -/
theorem hasSum_circleIntegral_of_dominated {ι : Type*} [Countable ι] {F : ι → ℂ → ℂ}
    {G : ℂ → ℂ} {c : ℂ} (hρ : 0 ≤ ρ) (hF : ∀ i, ContinuousOn (F i) (sphere c ρ))
    {u : ι → ℝ} (hu : Summable u) (hle : ∀ i, ∀ z ∈ sphere c ρ, ‖F i z‖ ≤ u i)
    (hG : ∀ z ∈ sphere c ρ, HasSum (fun i ↦ F i z) (G z)) :
    HasSum (fun i ↦ ∮ z in C(c, ρ), F i z) (∮ z in C(c, ρ), G z) := by
  simp only [circleIntegral]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun i _ ↦ ρ * u i)
    (fun i ↦ ?_) (fun i ↦ ?_) ?_ intervalIntegrable_const ?_
  · have hd : Continuous fun θ ↦ deriv (circleMap c ρ) θ := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 ρ).mul continuous_const
    exact (hd.smul ((hF i).comp_continuous (continuous_circleMap c ρ)
      (circleMap_mem_sphere c hρ))).aestronglyMeasurable
  · refine .of_forall fun θ _ ↦ ?_
    rw [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, norm_I, mul_one,
      abs_of_nonneg hρ]
    exact mul_le_mul_of_nonneg_left (hle i _ (circleMap_mem_sphere c hρ θ)) hρ
  · exact .of_forall fun θ _ ↦ hu.mul_left ρ
  · exact .of_forall fun θ _ ↦ (hG _ (circleMap_mem_sphere c hρ θ)).const_smul _

/-- An admissible radius above any point of the disc `{‖z‖ < R}`. -/
lemma exists_isRadius_gt_of_enorm_lt (hρ : IsRadius r R ρ) {w : ℂ} (hw : ‖w‖ₑ < R) :
    ∃ b, IsRadius r R b ∧ ‖w‖ < b := by
  set z : ℂ := ((max ρ ‖w‖ : ℝ) : ℂ)
  have hz : ‖z‖ = max ρ ‖w‖ := by
    simp [z, Complex.norm_real, abs_of_nonneg ((norm_nonneg w).trans (le_max_right ρ ‖w‖))]
  have hzA : z ∈ annulus r R := by
    refine ⟨hz ▸ hρ.2.1.trans_le (le_max_left _ _), ?_⟩
    rw [enorm_lt_iff_ofReal_lt, hz, ENNReal.ofReal_max]
    exact max_lt hρ.2.2 (enorm_lt_iff_ofReal_lt.1 hw)
  obtain ⟨b, hb, hzb⟩ := exists_isRadius_gt hzA
  exact ⟨b, hb, (le_max_right ρ ‖w‖).trans_lt (hz ▸ hzb)⟩

lemma ne_zero_of_mem_sphere_zero (hρ : 0 < ρ) {z : ℂ} (hz : z ∈ sphere (0 : ℂ) ρ) : z ≠ 0 := by
  rintro rfl
  rw [mem_sphere_zero_iff_norm, norm_zero] at hz
  exact hρ.ne hz

lemma zpow_neg_natCast_sub_one (z : ℂ) (k : ℕ) : z ^ (-(k : ℤ) - 1) = (z ^ k)⁻¹ * z⁻¹ := by
  rw [show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    pow_succ, mul_inv]

lemma summable_pow_natAbs {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Summable fun k : ℤ ↦ q ^ k.natAbs := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using summable_geometric_of_lt_one h0 h1
  · have : (fun n : ℕ ↦ q ^ (-((n : ℤ) + 1)).natAbs) = fun n ↦ q ^ (n + 1) := by
      funext n
      congr 1
    rw [this]
    exact (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one h0 h1)

section coefficients

variable {f g : ℂ → ℂ}

lemma coeff_congr (hρ : 0 ≤ ρ) (h : EqOn f g (sphere 0 ρ)) (k : ℤ) :
    coeff f ρ k = coeff g ρ k := by
  unfold coeff
  congr 1
  exact circleIntegral.integral_congr hρ fun z hz ↦ by simp [h hz]

/-- The Cauchy estimate for Laurent coefficients. -/
theorem norm_coeff_le (hρ : 0 < ρ) {M : ℝ} (hM : ∀ z ∈ sphere (0 : ℂ) ρ, ‖f z‖ ≤ M) (k : ℤ) :
    ‖coeff f ρ k‖ ≤ M * ρ ^ (-k) := by
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z ↦ z ^ (-k - 1) * f z) (c := 0) hρ.le (C := ρ ^ (-k - 1) * M) fun z hz ↦ by
      rw [mem_sphere_zero_iff_norm] at hz
      rw [norm_mul, norm_zpow, hz]
      exact mul_le_mul_of_nonneg_left (hM z (by simpa using hz)) (zpow_nonneg hρ.le _)
  rw [smul_eq_mul] at h
  refine h.trans (le_of_eq ?_)
  rw [zpow_sub_one₀ hρ.ne']
  field_simp

lemma differentiableAt_zpow_mul (hf : DifferentiableOn ℂ f (annulus r R)) {z : ℂ}
    (hz : z ∈ annulus r R) (hz0 : z ≠ 0) (m : ℤ) :
    DifferentiableAt ℂ (fun z ↦ z ^ m * f z) z :=
  (differentiableAt_zpow.2 (Or.inl hz0)).mul (hf.differentiableAt (isOpen_annulus.mem_nhds hz))

/-- The Laurent coefficients do not depend on the choice of the circle. -/
theorem coeff_eq_of_isRadius (hf : DifferentiableOn ℂ f (annulus r R)) {ρ₁ ρ₂ : ℝ}
    (h₁ : IsRadius r R ρ₁) (h₂ : IsRadius r R ρ₂) (k : ℤ) : coeff f ρ₁ k = coeff f ρ₂ k := by
  wlog hle : ρ₁ ≤ ρ₂ generalizing ρ₁ ρ₂
  · exact (this h₂ h₁ (le_of_not_ge hle)).symm
  have hmem : ∀ z ∈ closedBall (0 : ℂ) ρ₂ \ ball 0 ρ₁, z ∈ annulus r R ∧ z ≠ 0 := by
    intro z ⟨hz₂, hz₁⟩
    rw [mem_closedBall_zero_iff] at hz₂
    rw [mem_ball_zero_iff, not_lt] at hz₁
    exact ⟨mem_annulus_of_le h₁ h₂ hz₁ hz₂, norm_pos_iff.1 (h₁.pos.trans_le hz₁)⟩
  unfold coeff
  congr 1
  refine (circleIntegral_eq_of_differentiable_on_annulus_off_countable h₁.pos hle
    Set.countable_empty (fun z hz ↦ ?_) fun z hz ↦ ?_).symm
  · exact (differentiableAt_zpow_mul hf (hmem z hz).1 (hmem z hz).2 _).continuousAt
      |>.continuousWithinAt
  · have hz' : z ∈ closedBall (0 : ℂ) ρ₂ \ ball 0 ρ₁ :=
      ⟨ball_subset_closedBall hz.1.1, fun h ↦ hz.1.2 (ball_subset_closedBall h)⟩
    exact differentiableAt_zpow_mul hf (hmem z hz').1 (hmem z hz').2 _

/-- On a disc the Laurent coefficients of negative degree vanish. -/
theorem coeff_eq_zero_of_neg (hf : DifferentiableOn ℂ f (annulus r R)) (hr : r < 0)
    (hρ : IsRadius r R ρ) {k : ℤ} (hk : k < 0) : coeff f ρ k = 0 := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -k - 1)
  have hsub : closedBall (0 : ℂ) ρ ⊆ annulus r R := fun z hz ↦ by
    rw [mem_closedBall_zero_iff] at hz
    refine ⟨hr.trans_le (norm_nonneg z), ?_⟩
    rw [enorm_lt_iff_ofReal_lt]
    exact (ENNReal.ofReal_le_ofReal hz).trans_lt hρ.2.2
  have hd : DifferentiableOn ℂ (fun z ↦ z ^ n * f z) (closedBall 0 ρ) :=
    (differentiable_pow n).differentiableOn.mul (hf.mono hsub)
  unfold coeff
  rw [hn]
  simp only [zpow_natCast]
  rw [circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.pos.le Set.countable_empty
    hd.continuousOn fun z hz ↦ hd.differentiableAt (closedBall_mem_nhds_of_mem hz.1), mul_zero]

end coefficients

section expansion

variable {f : ℂ → ℂ}

/-- The Cauchy integral formula on an annulus: `2πi f(w)` is the difference of the Cauchy
integrals over an outer and an inner circle. -/
theorem circleIntegral_sub_circleIntegral (hf : DifferentiableOn ℂ f (annulus r R))
    {ρ₁ ρ₂ : ℝ} (h₁ : IsRadius r R ρ₁) (h₂ : IsRadius r R ρ₂) {w : ℂ} (hw₁ : ρ₁ < ‖w‖)
    (hw₂ : ‖w‖ < ρ₂) :
    (∮ z in C(0, ρ₂), (z - w)⁻¹ * f z) - (∮ z in C(0, ρ₁), (z - w)⁻¹ * f z) =
      2 * π * I * f w := by
  have hle : ρ₁ ≤ ρ₂ := (hw₁.trans hw₂).le
  have hwA : w ∈ annulus r R := mem_annulus_of_le h₁ h₂ hw₁.le hw₂.le
  have hmem : ∀ z ∈ closedBall (0 : ℂ) ρ₂ \ ball 0 ρ₁, z ∈ annulus r R := by
    intro z ⟨hz₂, hz₁⟩
    rw [mem_closedBall_zero_iff] at hz₂
    rw [mem_ball_zero_iff, not_lt] at hz₁
    exact mem_annulus_of_le h₁ h₂ hz₁ hz₂
  have hdiff : ∀ z ∈ annulus r R, DifferentiableAt ℂ f z :=
    fun z hz ↦ hf.differentiableAt (isOpen_annulus.mem_nhds hz)
  -- the difference quotient is holomorphic on the annulus
  have key := circleIntegral_eq_of_differentiable_on_annulus_off_countable (c := 0) h₁.pos hle
    (Set.countable_singleton w) (f := dslope f w) (fun z hz ↦ ?_) fun z hz ↦ ?_
  rotate_left
  · rcases eq_or_ne z w with rfl | hzw
    · exact (continuousAt_dslope_same.2 (hdiff z (hmem z hz))).continuousWithinAt
    · exact ((continuousAt_dslope_of_ne hzw).2
        (hdiff z (hmem z hz)).continuousAt).continuousWithinAt
  · have hz' : z ∈ closedBall (0 : ℂ) ρ₂ \ ball 0 ρ₁ :=
      ⟨ball_subset_closedBall hz.1.1, fun h ↦ hz.1.2 (ball_subset_closedBall h)⟩
    exact (differentiableAt_dslope_of_ne hz.2).2 (hdiff z (hmem z hz'))
  -- on each circle, `dslope f w z = (z - w)⁻¹ * f z - f w * (z - w)⁻¹`
  have hcirc : ∀ {ρ : ℝ}, 0 < ρ → ρ ≠ ‖w‖ → IsRadius r R ρ →
      (∮ z in C(0, ρ), dslope f w z) =
        (∮ z in C(0, ρ), (z - w)⁻¹ * f z) - f w * ∮ z in C(0, ρ), (z - w)⁻¹ := by
    intro ρ hρ hρw hρR
    have hne : ∀ z ∈ sphere (0 : ℂ) ρ, z - w ≠ 0 := fun z hz h ↦ by
      rw [sub_eq_zero] at h
      rw [h, mem_sphere_zero_iff_norm] at hz
      exact hρw hz.symm
    have hc1 : ContinuousOn (fun z ↦ (z - w)⁻¹) (sphere (0 : ℂ) ρ) :=
      (continuousOn_id.sub continuousOn_const).inv₀ hne
    have hc2 : ContinuousOn (fun z ↦ (z - w)⁻¹ * f z) (sphere (0 : ℂ) ρ) :=
      hc1.mul fun z hz ↦ (hdiff z (sphere_subset_annulus hρR hz)).continuousAt.continuousWithinAt
    have hc3 : ContinuousOn (fun z ↦ f w * (z - w)⁻¹) (sphere (0 : ℂ) ρ) :=
      continuousOn_const.mul hc1
    rw [← circleIntegral.integral_const_mul, ← circleIntegral.integral_sub
      (hc2.circleIntegrable hρ.le) (hc3.circleIntegrable hρ.le)]
    refine circleIntegral.integral_congr hρ.le fun z hz ↦ ?_
    simp only [dslope_of_ne _ (sub_ne_zero.1 (hne z hz)), slope_def_field]
    rw [div_eq_inv_mul]
    ring
  rw [hcirc h₂.pos hw₂.ne' h₂, hcirc h₁.pos hw₁.ne h₁,
    circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hw₂)] at key
  have hzero : (∮ z in C(0, ρ₁), (z - w)⁻¹) = 0 := by
    have hne : ∀ z ∈ closedBall (0 : ℂ) ρ₁, z - w ≠ 0 := fun z hz h ↦ by
      rw [sub_eq_zero] at h
      rw [h, mem_closedBall_zero_iff] at hz
      exact (not_le.2 hw₁) hz
    have hc : ContinuousOn (fun z ↦ (z - w)⁻¹) (closedBall (0 : ℂ) ρ₁) :=
      (continuousOn_id.sub continuousOn_const).inv₀ hne
    exact circleIntegral_eq_zero_of_differentiable_on_off_countable h₁.pos.le
      Set.countable_empty hc fun z hz ↦
        ((differentiableAt_id.sub_const w).inv (hne z (ball_subset_closedBall hz.1)))
  rw [hzero, mul_zero, sub_zero] at key
  rw [← key]
  ring

/-- The expansion of the Cauchy integral over the outer circle in nonnegative powers. -/
theorem hasSum_coeff_nat (hρ : 0 < ρ) (hf : ContinuousOn f (sphere 0 ρ)) {w : ℂ}
    (hw : ‖w‖ < ρ) :
    HasSum (fun k : ℕ ↦ coeff f ρ k * w ^ k) ((2 * π * I)⁻¹ * ∮ z in C(0, ρ), (z - w)⁻¹ * f z) := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) ρ).exists_bound_of_continuousOn hf
  have hq0 : 0 ≤ ‖w‖ / ρ := by positivity
  have hq1 : ‖w‖ / ρ < 1 := (div_lt_one hρ).2 hw
  have key := hasSum_circleIntegral_of_dominated (ι := ℕ) hρ.le
    (F := fun k z ↦ w ^ k * (z ^ (-(k : ℤ) - 1) * f z)) (G := fun z ↦ (z - w)⁻¹ * f z)
    (fun k ↦ continuousOn_const.mul
      ((continuousOn_id.zpow₀ _ fun z hz ↦ Or.inl (ne_zero_of_mem_sphere_zero hρ hz)).mul hf))
    ((summable_geometric_of_lt_one hq0 hq1).mul_right (ρ⁻¹ * M)) (fun k z hz ↦ ?_)
    fun z hz ↦ ?_
  · have e : (fun k : ℕ ↦ coeff f ρ k * w ^ k) = fun k : ℕ ↦
        (2 * π * I)⁻¹ * ∮ z in C(0, ρ), w ^ k * (z ^ (-(k : ℤ) - 1) * f z) := by
      funext k
      unfold coeff
      rw [circleIntegral.integral_const_mul]
      ring
    rw [e]
    exact key.mul_left _
  · rw [mem_sphere_zero_iff_norm] at hz
    rw [zpow_neg_natCast_sub_one, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, norm_pow,
      norm_pow, hz, div_pow]
    have := hM z (by simpa using hz)
    calc ‖w‖ ^ k * ((ρ ^ k)⁻¹ * ρ⁻¹ * ‖f z‖) = ‖w‖ ^ k / ρ ^ k * ρ⁻¹ * ‖f z‖ := by ring
      _ ≤ ‖w‖ ^ k / ρ ^ k * ρ⁻¹ * M := by gcongr
      _ = _ := by ring
  · have hz0 := ne_zero_of_mem_sphere_zero hρ hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hlt : ‖w / z‖ < 1 := by rwa [norm_div, hz, div_lt_one hρ]
    have hzw : z - w ≠ 0 := fun h ↦ by
      rw [sub_eq_zero] at h
      rw [h] at hz
      exact hw.ne hz
    have h := (hasSum_geometric_of_norm_lt_one hlt).mul_right (z⁻¹ * f z)
    have e1 : (fun k : ℕ ↦ w ^ k * (z ^ (-(k : ℤ) - 1) * f z)) =
        fun k : ℕ ↦ (w / z) ^ k * (z⁻¹ * f z) := by
      funext k
      rw [zpow_neg_natCast_sub_one, div_pow]
      ring
    have e2 : (z - w)⁻¹ * f z = (1 - w / z)⁻¹ * (z⁻¹ * f z) := by
      field_simp
    rw [e1, e2]
    exact h

lemma circleIntegral_neg (g : ℂ → ℂ) (c : ℂ) (ρ : ℝ) :
    (∮ z in C(c, ρ), -g z) = -∮ z in C(c, ρ), g z := by
  simp only [circleIntegral, smul_neg, intervalIntegral.integral_neg]

/-- The expansion of the Cauchy integral over the inner circle in negative powers. -/
theorem hasSum_coeff_neg (hρ : 0 < ρ) (hf : ContinuousOn f (sphere 0 ρ)) {w : ℂ}
    (hw : ρ < ‖w‖) :
    HasSum (fun k : ℕ ↦ coeff f ρ (-((k : ℤ) + 1)) * w ^ (-((k : ℤ) + 1)))
      (-((2 * π * I)⁻¹ * ∮ z in C(0, ρ), (z - w)⁻¹ * f z)) := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) ρ).exists_bound_of_continuousOn hf
  have hw0 : 0 < ‖w‖ := hρ.trans hw
  have hq0 : 0 ≤ ρ / ‖w‖ := by positivity
  have hq1 : ρ / ‖w‖ < 1 := (div_lt_one hw0).2 hw
  have key := hasSum_circleIntegral_of_dominated (ι := ℕ) hρ.le
    (F := fun k z ↦ (w ^ (k + 1))⁻¹ * (z ^ k * f z)) (G := fun z ↦ (w - z)⁻¹ * f z)
    (fun k ↦ continuousOn_const.mul ((continuousOn_pow k).mul hf))
    ((summable_geometric_of_lt_one hq0 hq1).mul_right (‖w‖⁻¹ * M)) (fun k z hz ↦ ?_)
    fun z hz ↦ ?_
  · have e : (fun k : ℕ ↦ coeff f ρ (-((k : ℤ) + 1)) * w ^ (-((k : ℤ) + 1))) = fun k : ℕ ↦
        (2 * π * I)⁻¹ * ∮ z in C(0, ρ), (w ^ (k + 1))⁻¹ * (z ^ k * f z) := by
      funext k
      unfold coeff
      rw [circleIntegral.integral_const_mul, show -(-((k : ℤ) + 1)) - 1 = (k : ℤ) by ring,
        show -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
      simp only [zpow_natCast]
      ring
    have e' : (∮ z in C(0, ρ), (w - z)⁻¹ * f z) = -∮ z in C(0, ρ), (z - w)⁻¹ * f z := by
      rw [← circleIntegral_neg]
      refine circleIntegral.integral_congr hρ.le fun z _ ↦ ?_
      rw [← neg_sub z w, inv_neg, neg_mul]
    rw [e, ← mul_neg, ← e']
    exact key.mul_left _
  · rw [mem_sphere_zero_iff_norm] at hz
    rw [norm_mul, norm_mul, norm_inv, norm_pow, norm_pow, hz, div_pow]
    have := hM z (by simpa using hz)
    calc (‖w‖ ^ (k + 1))⁻¹ * (ρ ^ k * ‖f z‖) = ρ ^ k / ‖w‖ ^ k * ‖w‖⁻¹ * ‖f z‖ := by
          rw [pow_succ]; field_simp
      _ ≤ ρ ^ k / ‖w‖ ^ k * ‖w‖⁻¹ * M := by gcongr
      _ = _ := by ring
  · rw [mem_sphere_zero_iff_norm] at hz
    have hwne : w ≠ 0 := norm_pos_iff.1 hw0
    have hlt : ‖z / w‖ < 1 := by rwa [norm_div, hz, div_lt_one hw0]
    have hzw : w - z ≠ 0 := fun h ↦ by
      rw [sub_eq_zero] at h
      rw [← h] at hz
      exact hw.ne' hz
    have h := (hasSum_geometric_of_norm_lt_one hlt).mul_right (w⁻¹ * f z)
    have e1 : (fun k : ℕ ↦ (w ^ (k + 1))⁻¹ * (z ^ k * f z)) =
        fun k : ℕ ↦ (z / w) ^ k * (w⁻¹ * f z) := by
      funext k
      rw [div_pow, pow_succ, mul_inv]
      ring
    have e2 : (w - z)⁻¹ * f z = (1 - z / w)⁻¹ * (w⁻¹ * f z) := by
      field_simp
    rw [e1, e2]
    exact h

lemma closedBall_subset_annulus (hr : r < 0) (hρ : IsRadius r R ρ) :
    closedBall (0 : ℂ) ρ ⊆ annulus r R := fun z hz ↦ by
  rw [mem_closedBall_zero_iff] at hz
  refine ⟨hr.trans_le (norm_nonneg z), ?_⟩
  rw [enorm_lt_iff_ofReal_lt]
  exact (ENNReal.ofReal_le_ofReal hz).trans_lt hρ.2.2

/-- **Laurent expansion**: a function holomorphic on an annulus is the sum of its Laurent
series there. -/
theorem hasSum_coeff (hf : DifferentiableOn ℂ f (annulus r R)) (hρ : IsRadius r R ρ) {w : ℂ}
    (hw : w ∈ annulus r R) : HasSum (fun k : ℤ ↦ coeff f ρ k * w ^ k) (f w) := by
  have hcont : ∀ {s : ℝ}, IsRadius r R s → ContinuousOn f (sphere 0 s) :=
    fun hs ↦ hf.continuousOn.mono (sphere_subset_annulus hs)
  rcases eq_or_ne w 0 with rfl | hw0
  · have hr : r < 0 := by simpa using hw.1
    have h0 : coeff f ρ 0 = f 0 := by
      have hd := (hf.mono (closedBall_subset_annulus hr hρ)).circleIntegral_sub_inv_smul
        (mem_ball_self hρ.pos)
      unfold coeff
      simp only [neg_zero, zero_sub, zpow_neg_one, sub_zero, smul_eq_mul] at hd ⊢
      rw [hd, ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]
    have := hasSum_single (f := fun k : ℤ ↦ coeff f ρ k * (0 : ℂ) ^ k) 0 fun k hk ↦ by
      simp [zero_zpow k hk]
    simpa [h0] using this
  · obtain ⟨ρ₁, h₁, hw₁⟩ := exists_isRadius_lt hw hw0
    obtain ⟨ρ₂, h₂, hw₂⟩ := exists_isRadius_gt hw
    have hp := hasSum_coeff_nat h₂.pos (hcont h₂) hw₂
    have hn := hasSum_coeff_neg h₁.pos (hcont h₁) hw₁
    simp only [coeff_eq_of_isRadius hf h₂ hρ, ← zpow_natCast] at hp
    simp only [coeff_eq_of_isRadius hf h₁ hρ] at hn
    have h := HasSum.of_nat_of_neg_add_one (f := fun k : ℤ ↦ coeff f ρ k * w ^ k) hp hn
    have e : f w = (2 * π * I)⁻¹ * (∮ z in C(0, ρ₂), (z - w)⁻¹ * f z) +
        -((2 * π * I)⁻¹ * ∮ z in C(0, ρ₁), (z - w)⁻¹ * f z) := by
      rw [← sub_eq_add_neg, ← mul_sub, circleIntegral_sub_circleIntegral hf h₁ h₂ hw₁ hw₂,
        ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]
    rw [e]
    exact h

lemma norm_coeff_mul_le_of_le (hf : DifferentiableOn ℂ f (annulus r R)) (hρ : IsRadius r R ρ)
    {b M t : ℝ} (hb : IsRadius r R b) (hM : ∀ z ∈ sphere (0 : ℂ) b, ‖f z‖ ≤ M) {z : ℂ}
    (hz : ‖z‖ ≤ t) (n : ℕ) : ‖coeff f ρ n * z ^ (n : ℤ)‖ ≤ M * (t / b) ^ n := by
  rw [coeff_eq_of_isRadius hf hρ hb, norm_mul, zpow_natCast, norm_pow]
  have h1 := norm_coeff_le hb.pos hM n
  have h2 : ‖z‖ ^ n ≤ t ^ n := pow_le_pow_left₀ (norm_nonneg z) hz n
  calc ‖coeff f b n‖ * ‖z‖ ^ n ≤ M * b ^ (-(n : ℤ)) * t ^ n :=
        mul_le_mul h1 h2 (by positivity) ((norm_nonneg _).trans h1)
    _ = M * (t / b) ^ n := by rw [zpow_neg, zpow_natCast, div_pow]; ring

lemma norm_coeff_mul_le_of_ge (hf : DifferentiableOn ℂ f (annulus r R)) (hρ : IsRadius r R ρ)
    {a M t : ℝ} (ha : IsRadius r R a) (hM : ∀ z ∈ sphere (0 : ℂ) a, ‖f z‖ ≤ M) (ht : 0 < t)
    {z : ℂ} (hz : t ≤ ‖z‖) (n : ℕ) :
    ‖coeff f ρ (-(n : ℤ)) * z ^ (-(n : ℤ))‖ ≤ M * (a / t) ^ n := by
  rw [coeff_eq_of_isRadius hf hρ ha, norm_mul, zpow_neg, zpow_natCast, norm_inv, norm_pow]
  have h1 := norm_coeff_le ha.pos hM (-(n : ℤ))
  rw [neg_neg, zpow_natCast] at h1
  have h2 : (‖z‖ ^ n)⁻¹ ≤ (t ^ n)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ ht.le hz n)
  calc ‖coeff f a (-(n : ℤ))‖ * (‖z‖ ^ n)⁻¹ ≤ M * a ^ n * (t ^ n)⁻¹ :=
        mul_le_mul h1 h2 (by positivity) ((norm_nonneg _).trans h1)
    _ = M * (a / t) ^ n := by rw [div_pow]; ring

/-- The Weierstrass bound behind the local uniform convergence of the Laurent series: near every
point of the annulus its terms are dominated by a summable sequence. -/
theorem exists_summable_bound (hf : DifferentiableOn ℂ f (annulus r R)) (hρ : IsRadius r R ρ)
    {w : ℂ} (hw : w ∈ annulus r R) :
    ∃ u : ℤ → ℝ, Summable u ∧ ∃ V ∈ 𝓝 w, ∀ k, ∀ z ∈ V, ‖coeff f ρ k * z ^ k‖ ≤ u k := by
  obtain ⟨b, hb, hwb⟩ := exists_isRadius_gt hw
  obtain ⟨Mb, hMb⟩ := (isCompact_sphere (0 : ℂ) b).exists_bound_of_continuousOn
    (hf.continuousOn.mono (sphere_subset_annulus hb))
  set t₂ := (‖w‖ + b) / 2
  have hq₂ : t₂ / b < 1 := (div_lt_one hb.pos).2 (by simp only [t₂]; linarith)
  have hq₂' : 0 ≤ t₂ / b := div_nonneg (by simp only [t₂]; linarith [norm_nonneg w, hb.pos])
    hb.pos.le
  have hMb0 : 0 ≤ Mb := (norm_nonneg _).trans (hMb _ (by
    simp [Complex.norm_real, abs_of_pos hb.pos] : (b : ℂ) ∈ sphere (0 : ℂ) b))
  have hball : ball (0 : ℂ) t₂ ∈ 𝓝 w := isOpen_ball.mem_nhds (by
    rw [mem_ball_zero_iff]; simp only [t₂]; linarith)
  rcases eq_or_ne w 0 with rfl | hw0
  · have hr : r < 0 := by simpa using hw.1
    refine ⟨fun k ↦ Mb * (t₂ / b) ^ k.natAbs, (summable_pow_natAbs hq₂' hq₂).mul_left Mb,
      ball 0 t₂, hball, fun k z hz ↦ ?_⟩
    rcases lt_or_ge k 0 with hk | hk
    · rw [coeff_eq_zero_of_neg hf hr hρ hk, zero_mul, norm_zero]
      exact mul_nonneg hMb0 (pow_nonneg hq₂' _)
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      rw [mem_ball_zero_iff] at hz
      simpa using norm_coeff_mul_le_of_le hf hρ hb hMb hz.le n
  · obtain ⟨a, ha, haw⟩ := exists_isRadius_lt hw hw0
    obtain ⟨Ma, hMa⟩ := (isCompact_sphere (0 : ℂ) a).exists_bound_of_continuousOn
      (hf.continuousOn.mono (sphere_subset_annulus ha))
    have hMa0 : 0 ≤ Ma := (norm_nonneg _).trans (hMa _ (by
      simp [Complex.norm_real, abs_of_pos ha.pos] : (a : ℂ) ∈ sphere (0 : ℂ) a))
    set t₁ := (a + ‖w‖) / 2
    have ht₁ : 0 < t₁ := by simp only [t₁]; linarith [ha.pos]
    have hq₁ : a / t₁ < 1 := (div_lt_one ht₁).2 (by simp only [t₁]; linarith)
    have hq₁' : 0 ≤ a / t₁ := div_nonneg ha.pos.le ht₁.le
    have hV : {z : ℂ | t₁ < ‖z‖} ∩ ball 0 t₂ ∈ 𝓝 w :=
      inter_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds (by
        simp only [mem_setOf_eq, t₁]; linarith)) hball
    refine ⟨fun k ↦ Mb * (t₂ / b) ^ k.natAbs + Ma * (a / t₁) ^ k.natAbs,
      ((summable_pow_natAbs hq₂' hq₂).mul_left Mb).add
        ((summable_pow_natAbs hq₁' hq₁).mul_left Ma), _, hV, fun k z hz ↦ ?_⟩
    rw [mem_inter_iff, mem_setOf_eq, mem_ball_zero_iff] at hz
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · have := norm_coeff_mul_le_of_le hf hρ hb hMb hz.2.le n
      simp only [Int.natAbs_natCast]
      linarith [mul_nonneg hMa0 (pow_nonneg hq₁' n)]
    · have := norm_coeff_mul_le_of_ge hf hρ ha hMa ht₁ hz.1.le n
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
      linarith [mul_nonneg hMb0 (pow_nonneg hq₂' n)]

/-- The Laurent series converges absolutely on the annulus. -/
theorem summable_norm_coeff_mul (hf : DifferentiableOn ℂ f (annulus r R))
    (hρ : IsRadius r R ρ) {w : ℂ} (hw : w ∈ annulus r R) :
    Summable fun k : ℤ ↦ ‖coeff f ρ k * w ^ k‖ := by
  obtain ⟨u, hu, V, hV, hle⟩ := exists_summable_bound hf hρ hw
  exact hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun k ↦ hle k w (mem_of_mem_nhds hV)

/-- The Laurent series converges locally uniformly on the annulus. -/
theorem tendstoLocallyUniformlyOn (hf : DifferentiableOn ℂ f (annulus r R))
    (hρ : IsRadius r R ρ) :
    TendstoLocallyUniformlyOn (fun (s : Finset ℤ) (z : ℂ) ↦ ∑ k ∈ s, coeff f ρ k * z ^ k) f
      atTop (annulus r R) := by
  intro U hU w hw
  obtain ⟨u, hu, V, hV, hle⟩ := exists_summable_bound hf hρ hw
  refine ⟨annulus r R ∩ V, inter_mem_nhdsWithin _ hV, ?_⟩
  have h := ((tendstoUniformlyOn_tsum hu fun k z hz ↦ hle k z hz).mono
    inter_subset_right).congr_right fun z hz ↦ (hasSum_coeff hf hρ hz.1).tsum_eq
  exact h U hU

/-- **Uniqueness of Laurent coefficients**: if `f` is the sum of an absolutely convergent Laurent
series on the circle of radius `ρ`, then its coefficients are the Laurent coefficients of `f`. -/
theorem coeff_eq_of_hasSum (hρ : 0 < ρ) {b : ℤ → ℂ} (hb : Summable fun k ↦ ‖b k‖ * ρ ^ k)
    (hf : ∀ z ∈ sphere (0 : ℂ) ρ, HasSum (fun k ↦ b k * z ^ k) (f z)) (k : ℤ) :
    coeff f ρ k = b k := by
  have key := hasSum_circleIntegral_of_dominated (ι := ℤ) hρ.le
    (F := fun j z ↦ b j * z ^ (j - k - 1)) (G := fun z ↦ z ^ (-k - 1) * f z)
    (fun j ↦ continuousOn_const.mul
      (continuousOn_id.zpow₀ _ fun z hz ↦ Or.inl (ne_zero_of_mem_sphere_zero hρ hz)))
    (hb.mul_right (ρ ^ (-k - 1))) (fun j z hz ↦ ?_) fun z hz ↦ ?_
  · have hint : ∀ j, (∮ z in C(0, ρ), b j * z ^ (j - k - 1)) =
        if j = k then b k * (2 * π * I) else 0 := by
      intro j
      rw [circleIntegral.integral_const_mul]
      split_ifs with hj
      · subst hj
        have := circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (R := ρ)
          (mem_ball_self hρ)
        simp only [sub_zero] at this
        rw [show j - j - 1 = -1 by ring]
        simp only [zpow_neg_one, this]
      · have := circleIntegral.integral_sub_zpow_of_ne (n := j - k - 1) (by omega) 0 0 ρ
        simp only [sub_zero] at this
        rw [this, mul_zero]
    simp only [hint] at key
    have h := key.unique (hasSum_ite_eq k (b k * (2 * π * I)))
    unfold coeff
    rw [h, mul_comm, mul_assoc, mul_inv_cancel₀ (by simp [Real.pi_ne_zero]), mul_one]
  · rw [mem_sphere_zero_iff_norm] at hz
    rw [norm_mul, norm_zpow, hz, show j - k - 1 = j + (-k - 1) by ring, zpow_add₀ hρ.ne',
      mul_assoc]
  · have hz0 := ne_zero_of_mem_sphere_zero hρ hz
    have e : (fun j ↦ b j * z ^ (j - k - 1)) = fun j ↦ z ^ (-k - 1) * (b j * z ^ j) := by
      funext j
      rw [show j - k - 1 = j + (-k - 1) by ring, zpow_add₀ hz0]
      ring
    rw [e]
    exact (hf z hz).mul_left _

/-- An admissible radius below any nonzero point of `{r < ‖z‖}`. -/
lemma exists_isRadius_lt_of_lt (hρ : IsRadius r R ρ) {w : ℂ} (hw : r < ‖w‖) (hw0 : w ≠ 0) :
    ∃ a, IsRadius r R a ∧ a < ‖w‖ := by
  set z : ℂ := ((min ρ ‖w‖ : ℝ) : ℂ)
  have hz : ‖z‖ = min ρ ‖w‖ := by
    simp [z, Complex.norm_real, abs_of_nonneg (le_min hρ.pos.le (norm_nonneg w))]
  have hz0 : z ≠ 0 := by
    rw [← norm_pos_iff, hz]
    exact lt_min hρ.pos (norm_pos_iff.2 hw0)
  have hzA : z ∈ annulus r R :=
    ⟨hz ▸ lt_min hρ.2.1 hw, by
      rw [enorm_lt_iff_ofReal_lt, hz]
      exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans_lt hρ.2.2⟩
  obtain ⟨a, ha, haz⟩ := exists_isRadius_lt hzA hz0
  exact ⟨a, ha, (hz ▸ haz).trans_le (min_le_right _ _)⟩

/-- The part `∑_{k ≥ 0} a_k z ^ k` of the Laurent series of `f`, of nonnegative degree. -/
noncomputable def plusPart (f : ℂ → ℂ) (ρ : ℝ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, coeff f ρ k * z ^ k

/-- The part `∑_{k < 0} a_k z ^ k` of the Laurent series of `f`, of negative degree. -/
noncomputable def minusPart (f : ℂ → ℂ) (ρ : ℝ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, coeff f ρ (-((k : ℤ) + 1)) * z ^ (-((k : ℤ) + 1))

/-- The **Laurent splitting** `f = f₊ + f₋` on the annulus. -/
theorem plusPart_add_minusPart (hf : DifferentiableOn ℂ f (annulus r R)) (hρ : IsRadius r R ρ)
    {w : ℂ} (hw : w ∈ annulus r R) : plusPart f ρ w + minusPart f ρ w = f w := by
  have hs : Summable fun k : ℤ ↦ coeff f ρ k * w ^ k :=
    (summable_norm_coeff_mul hf hρ hw).of_norm
  have h1 : Summable fun n : ℕ ↦ coeff f ρ n * w ^ (n : ℤ) :=
    hs.comp_injective (i := ((↑) : ℕ → ℤ)) Nat.cast_injective
  have h2 : Summable fun n : ℕ ↦ coeff f ρ (-((n : ℤ) + 1)) * w ^ (-((n : ℤ) + 1)) :=
    hs.comp_injective (i := fun n : ℕ ↦ -((n : ℤ) + 1)) fun a b h ↦ by
      simp only [neg_inj, add_left_inj, Nat.cast_inj] at h
      exact h
  have h := (hasSum_coeff hf hρ hw).tsum_eq
  rw [tsum_of_nat_of_neg_add_one (f := fun k : ℤ ↦ coeff f ρ k * w ^ k) h1 h2] at h
  simp only [zpow_natCast] at h
  exact h

/-- The part of nonnegative degree is holomorphic on the disc `{‖z‖ < R}`. -/
theorem differentiableOn_plusPart (hf : DifferentiableOn ℂ f (annulus r R))
    (hρ : IsRadius r R ρ) : DifferentiableOn ℂ (plusPart f ρ) (eball 0 R) := by
  intro w hw
  rw [Metric.mem_eball, edist_zero_right] at hw
  obtain ⟨b, hb, hwb⟩ := exists_isRadius_gt_of_enorm_lt hρ hw
  obtain ⟨Mb, hMb⟩ := (isCompact_sphere (0 : ℂ) b).exists_bound_of_continuousOn
    (hf.continuousOn.mono (sphere_subset_annulus hb))
  set t := (‖w‖ + b) / 2
  have hq : t / b < 1 := (div_lt_one hb.pos).2 (by simp only [t]; linarith)
  have hq' : 0 ≤ t / b := div_nonneg (by simp only [t]; linarith [norm_nonneg w, hb.pos])
    hb.pos.le
  have hd : DifferentiableOn ℂ (plusPart f ρ) (ball 0 t) :=
    differentiableOn_tsum_of_summable_norm
      ((summable_geometric_of_lt_one hq' hq).mul_left Mb)
      (fun n ↦ ((differentiable_pow n).const_mul _).differentiableOn) isOpen_ball
      fun n z hz ↦ by
        rw [mem_ball_zero_iff] at hz
        simpa using norm_coeff_mul_le_of_le hf hρ hb hMb hz.le n
  exact (hd.differentiableAt (isOpen_ball.mem_nhds (by
    rw [mem_ball_zero_iff]; simp only [t]; linarith))).differentiableWithinAt

lemma norm_coeff_mul_le_neg_succ (hf : DifferentiableOn ℂ f (annulus r R))
    (hρ : IsRadius r R ρ) {a M t : ℝ} (ha : IsRadius r R a)
    (hM : ∀ z ∈ sphere (0 : ℂ) a, ‖f z‖ ≤ M) (ht : 0 < t) {z : ℂ} (hz : t ≤ ‖z‖) (n : ℕ) :
    ‖coeff f ρ (-((n : ℤ) + 1)) * z ^ (-((n : ℤ) + 1))‖ ≤ M * (a / t) ^ (n + 1) := by
  have := norm_coeff_mul_le_of_ge hf hρ ha hM ht hz (n + 1)
  simpa using this

/-- The part of negative degree is holomorphic on `{r < ‖z‖}`. -/
theorem differentiableOn_minusPart (hf : DifferentiableOn ℂ f (annulus r R))
    (hρ : IsRadius r R ρ) : DifferentiableOn ℂ (minusPart f ρ) {z | r < ‖z‖} := by
  rcases lt_or_ge r 0 with hr | hr
  · have h0 : ∀ k : ℕ, coeff f ρ (-((k : ℤ) + 1)) = 0 :=
      fun k ↦ coeff_eq_zero_of_neg hf hr hρ (by omega)
    have : minusPart f ρ = fun _ ↦ 0 :=
      funext fun z ↦ by simp only [minusPart, h0, zero_mul, tsum_zero]
    rw [this]
    exact differentiableOn_const 0
  intro w hw
  have hw0 : w ≠ 0 := norm_pos_iff.1 (hr.trans_lt hw)
  obtain ⟨a, ha, haw⟩ := exists_isRadius_lt_of_lt hρ hw hw0
  obtain ⟨Ma, hMa⟩ := (isCompact_sphere (0 : ℂ) a).exists_bound_of_continuousOn
    (hf.continuousOn.mono (sphere_subset_annulus ha))
  set t := (a + ‖w‖) / 2
  have ht : 0 < t := by simp only [t]; linarith [ha.pos]
  have hq : a / t < 1 := (div_lt_one ht).2 (by simp only [t]; linarith)
  have hq' : 0 ≤ a / t := div_nonneg ha.pos.le ht.le
  have hV : IsOpen {z : ℂ | t < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hd : DifferentiableOn ℂ (minusPart f ρ) {z : ℂ | t < ‖z‖} :=
    differentiableOn_tsum_of_summable_norm
      (((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq' hq)).mul_left Ma)
      (fun n ↦ (differentiableOn_const _).mul (differentiableOn_zpow _ _ (Or.inl fun h ↦ by
        simp only [mem_setOf_eq, norm_zero] at h; linarith))) hV
      fun n z hz ↦ norm_coeff_mul_le_neg_succ hf hρ ha hMa ht (le_of_lt hz) n
  exact (hd.differentiableAt (hV.mem_nhds (by
    simp only [mem_setOf_eq, t]; linarith))).differentiableWithinAt

/-- The part of negative degree tends to `0` at infinity. -/
theorem tendsto_minusPart_cobounded (hf : DifferentiableOn ℂ f (annulus r R))
    (hρ : IsRadius r R ρ) : Tendsto (minusPart f ρ) (cobounded ℂ) (𝓝 0) := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) ρ).exists_bound_of_continuousOn
    (hf.continuousOn.mono (sphere_subset_annulus hρ))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (by
    simp [Complex.norm_real, abs_of_pos hρ.pos] : (ρ : ℂ) ∈ sphere (0 : ℂ) ρ))
  have hbound : ∀ z : ℂ, 2 * ρ ≤ ‖z‖ → ‖minusPart f ρ z‖ ≤ 2 * M * ρ * ‖z‖⁻¹ := by
    intro z hz
    have hz0 : 0 < ‖z‖ := by linarith [hρ.pos]
    have hq : ρ / ‖z‖ ≤ 1 / 2 := by
      rw [div_le_iff₀ hz0]; linarith
    have hq' : 0 ≤ ρ / ‖z‖ := div_nonneg hρ.pos.le hz0.le
    have hle : ∀ n : ℕ, ‖coeff f ρ (-((n : ℤ) + 1)) * z ^ (-((n : ℤ) + 1))‖ ≤
        M * (ρ / ‖z‖) * (1 / 2) ^ n := fun n ↦ by
      refine (norm_coeff_mul_le_neg_succ hf hρ hρ hM hz0 le_rfl n).trans ?_
      rw [pow_succ, mul_comm ((ρ / ‖z‖) ^ n), ← mul_assoc]
      gcongr
    have hs : Summable fun n : ℕ ↦ M * (ρ / ‖z‖) * (1 / 2 : ℝ) ^ n :=
      (summable_geometric_two).mul_left _
    calc ‖minusPart f ρ z‖ ≤ ∑' n : ℕ, ‖coeff f ρ (-((n : ℤ) + 1)) * z ^ (-((n : ℤ) + 1))‖ :=
          norm_tsum_le_tsum_norm (hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle)
      _ ≤ ∑' n : ℕ, M * (ρ / ‖z‖) * (1 / 2 : ℝ) ^ n :=
          (hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle).tsum_le_tsum hle hs
      _ = 2 * M * ρ * ‖z‖⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_two]; ring
  have hlim : Tendsto (fun z : ℂ ↦ 2 * M * ρ * ‖z‖⁻¹) (cobounded ℂ) (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_norm_cobounded_atTop).const_mul
      (2 * M * ρ)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop (2 * ρ))]
    with z hz using hbound z hz

end expansion

end Laurent

end
