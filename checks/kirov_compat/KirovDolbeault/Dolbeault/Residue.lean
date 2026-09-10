/-
  The residue atom (Forster §17.1–17.2 building block).

  `resAt f c` is the residue of `f : ℂ → ℂ` at `c`, defined by the contour integral
  `(2πi)⁻¹ ∮_{|z-c|=r} f` in the limit `r → 0⁺`.  This is the upstream-most genuinely-new object the
  Čech-residue route to Serre duality rests on: every local
  residue `Res_a(ω)` of a meromorphic 1-form is, in a chart, `resAt (coeff of ω) (chart a)`.

  Mathlib has **no** residue / general Laurent-coefficient API (only `meromorphicTrailingCoeffAt`, the
  *leading* coefficient), so we build it on Mathlib's circle-integral + Cauchy–Goursat toolkit.

  This module is pure one-variable complex analysis — no manifold — and so is reusable verbatim in
  every chart.  The `limUnder (𝓝[>] 0)` shape mirrors the repo's `MeromorphicFunction.holoRepr`.

  Lemmas proved here (all complete):
    * `resAt_eq_of_eventuallyEq_circleIntegral` — the workhorse: if the contour integral is eventually
      constant `= K` as `r → 0⁺`, then `resAt f c = (2πi)⁻¹ • K`.
    * `resAt_const_mul_sub_inv` / `resAt_sub_inv` — `Res_c (a/(z-c)) = a` (Forster 17.6's `dz/z` witness).
    * `resAt_eq_zero_of_differentiableOn_ball` — `Res_c(f) = 0` for `f` holomorphic near `c` (the
      holomorphic-difference property that makes `Res` well-defined on Mittag–Leffler cochains).
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Order

open Complex Metric Filter Topology
open scoped Real

namespace Jacobians.Dolbeault

/-- The **residue** of `f : ℂ → ℂ` at `c`: `(2πi)⁻¹ ∮_{|z-c|=r} f` in the limit `r → 0⁺`.
For `f` with an isolated singularity at `c` the contour integral is independent of small `r`
(annulus Cauchy–Goursat), so this picks out that common value = the Laurent coefficient `c₋₁`. -/
noncomputable def resAt (f : ℂ → ℂ) (c : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun r => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), f z)

/-- **Workhorse.** If the contour integral `∮_{|z-c|=r} f` is eventually constant `= K` as `r → 0⁺`,
then `resAt f c = (2πi)⁻¹ • K`.  Every residue computation below funnels through this. -/
theorem resAt_eq_of_eventuallyEq_circleIntegral {f : ℂ → ℂ} {c K : ℂ}
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), (∮ z in C(c, r), f z) = K) :
    resAt f c = (2 * π * I : ℂ)⁻¹ • K := by
  apply Filter.Tendsto.limUnder_eq
  refine (tendsto_const_nhds (x := (2 * π * I : ℂ)⁻¹ • K)).congr' ?_
  filter_upwards [h] with r hr
  rw [hr]

/-- If the contour integral is constant `= K` on a punctured right-neighbourhood `Ioo 0 ρ` of `0`,
the eventual-constancy hypothesis of the workhorse holds. -/
theorem eventuallyEq_circleIntegral_of_forall {f : ℂ → ℂ} {c K : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ r ∈ Set.Ioo (0 : ℝ) ρ, (∮ z in C(c, r), f z) = K) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), (∮ z in C(c, r), f z) = K := by
  have hmem : Set.Ioo (0 : ℝ) ρ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hρ
  filter_upwards [hmem] with r hr using h r hr

/-- **Forster 17.6's witness, general coefficient.**  `Res_c (a·(z-c)⁻¹) = a`. -/
theorem resAt_const_mul_sub_inv (a c : ℂ) :
    resAt (fun z => a * (z - c)⁻¹) c = a := by
  have hcint : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      (∮ z in C(c, r), a * (z - c)⁻¹) = a * (2 * π * I) := by
    intro r hr
    rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball
      (mem_ball_self hr.1)]
  rw [resAt_eq_of_eventuallyEq_circleIntegral
    (eventuallyEq_circleIntegral_of_forall (by norm_num) hcint)]
  rw [smul_eq_mul, ← mul_assoc, mul_comm _ a, mul_assoc, inv_mul_cancel₀, mul_one]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- `Res_c ((z-c)⁻¹) = 1`. -/
theorem resAt_sub_inv (c : ℂ) : resAt (fun z => (z - c)⁻¹) c = 1 := by
  have := resAt_const_mul_sub_inv 1 c
  simpa using this

/-- **Holomorphic-difference property.**  If `f` is complex-differentiable on a ball `ball c ρ`
(`ρ > 0`), its residue at `c` is `0`.  This is what makes `Res` well-defined on Mittag–Leffler
cochains: the differences `ωᵢ - ωⱼ` are holomorphic, hence contribute no residue. -/
theorem resAt_eq_zero_of_differentiableOn_ball {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ∀ z ∈ ball c ρ, DifferentiableAt ℂ f z) :
    resAt f c = 0 := by
  have hcint : ∀ r ∈ Set.Ioo (0 : ℝ) ρ, (∮ z in C(c, r), f z) = 0 := by
    intro r hr
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr.1.le Set.countable_empty
      ?_ (fun z hz => hf z ?_)
    · -- continuity on the closed ball of radius r ⊆ ball c ρ
      intro z hz
      exact (hf z (lt_of_le_of_lt (mem_closedBall.mp hz) hr.2)).continuousAt.continuousWithinAt
    · exact lt_of_lt_of_le (mem_ball.mp hz.1) hr.2.le
  rw [resAt_eq_of_eventuallyEq_circleIntegral
    (eventuallyEq_circleIntegral_of_forall hρ hcint), smul_zero]

/-! ### Radius independence and ℂ-linearity for an isolated singularity -/

/-- `f` is holomorphic on a punctured ball `ball c ρ \ {c}`, i.e. has an isolated singularity (or
none) at `c`.  The setting in which `resAt f c` is contour-independent and ℂ-linear; every
meromorphic-at-`c` function qualifies (`MeromorphicAt.holoPunctured`). -/
def HoloPunctured (f : ℂ → ℂ) (c : ℂ) : Prop :=
  ∃ ρ > 0, ∀ z ∈ ball c ρ \ {c}, DifferentiableAt ℂ f z

theorem MeromorphicAt.holoPunctured {f : ℂ → ℂ} {c : ℂ} (h : MeromorphicAt f c) :
    HoloPunctured f c := by
  have h2 : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z := h.eventually_analyticAt
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h2
  obtain ⟨ε, hε, hball⟩ := h2
  exact ⟨ε, hε, fun z hz => (hball (mem_ball.mp hz.1) hz.2).differentiableAt⟩

/-- **Annulus Cauchy–Goursat.**  For `f` holomorphic on `ball c ρ \ {c}`, the contour integral is
independent of the radius: `∮_{|z-c|=R} f = ∮_{|z-c|=r} f` for `0 < r ≤ R < ρ`. -/
theorem circleIntegral_annulus_eq {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ}
    (hf : ∀ z ∈ ball c ρ \ {c}, DifferentiableAt ℂ f z)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hRρ : R < ρ) :
    (∮ z in C(c, R), f z) = ∮ z in C(c, r), f z := by
  refine circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR Set.countable_empty
    ?_ ?_
  · intro z hz
    have hzc : z ≠ c := fun h => hz.2 (mem_ball.mpr (by rw [h, dist_self]; exact hr))
    exact (hf z (Set.mem_diff_singleton.mpr
      ⟨mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz.1) hRρ), hzc⟩)).continuousAt.continuousWithinAt
  · intro z hz
    have hz' : z ∈ ball c R \ closedBall c r := hz.1
    have hzc : z ≠ c := fun h => hz'.2 (mem_closedBall.mpr (by rw [h, dist_self]; exact hr.le))
    exact hf z (Set.mem_diff_singleton.mpr ⟨mem_ball.mpr (lt_trans (mem_ball.mp hz'.1) hRρ), hzc⟩)

/-- **Compute `resAt` by any small contour.**  For `f` holomorphic on `ball c ρ \ {c}` and `0 < r < ρ`,
`resAt f c = (2πi)⁻¹ • ∮_{|z-c|=r} f`. -/
theorem resAt_eq_smul_circleIntegral {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ}
    (hf : ∀ z ∈ ball c ρ \ {c}, DifferentiableAt ℂ f z) {r : ℝ} (hr : 0 < r) (hrρ : r < ρ) :
    resAt f c = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), f z := by
  refine resAt_eq_of_eventuallyEq_circleIntegral
    (eventuallyEq_circleIntegral_of_forall (lt_trans hr hrρ) (fun r' hr' => ?_))
  rcases le_total r' r with h | h
  · exact (circleIntegral_annulus_eq hf hr'.1 h hrρ).symm
  · exact circleIntegral_annulus_eq hf hr h hr'.2

/-- `CircleIntegrable f c r` for `f` holomorphic on `ball c ρ \ {c}` and `0 < r < ρ` (the circle of
radius `r` avoids the singularity). -/
theorem circleIntegrable_of_holo {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ}
    (hf : ∀ z ∈ ball c ρ \ {c}, DifferentiableAt ℂ f z) {r : ℝ} (hr : 0 < r) (hrρ : r < ρ) :
    CircleIntegrable f c r := by
  refine ContinuousOn.circleIntegrable hr.le (fun z hz => ?_)
  have hd : dist z c = r := Metric.mem_sphere.mp hz
  have hzc : z ≠ c := fun h => by rw [h, dist_self] at hd; exact absurd hd (ne_of_lt hr)
  exact (hf z (Set.mem_diff_singleton.mpr
    ⟨mem_ball.mpr (hd ▸ hrρ), hzc⟩)).continuousAt.continuousWithinAt

/-- **`resAt` is additive** on functions with isolated singularities at `c`. -/
theorem resAt_add {f g : ℂ → ℂ} {c : ℂ} (hf : HoloPunctured f c) (hg : HoloPunctured g c) :
    resAt (f + g) c = resAt f c + resAt g c := by
  obtain ⟨ρf, hρf, hf'⟩ := hf
  obtain ⟨ρg, hρg, hg'⟩ := hg
  set ρ := min ρf ρg with hρdef
  have hρ : 0 < ρ := lt_min hρf hρg
  set r := ρ / 2 with hrdef
  have hr : 0 < r := by positivity
  have hrρ : r < ρ := by rw [hrdef]; exact half_lt_self hρ
  have hfρ : ∀ z ∈ ball c ρ \ {c}, DifferentiableAt ℂ f z := fun z hz =>
    hf' z ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_left _ _)), hz.2⟩
  have hgρ : ∀ z ∈ ball c ρ \ {c}, DifferentiableAt ℂ g z := fun z hz =>
    hg' z ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_right _ _)), hz.2⟩
  have hfgρ : ∀ z ∈ ball c ρ \ {c}, DifferentiableAt ℂ (f + g) z := fun z hz =>
    (hfρ z hz).add (hgρ z hz)
  rw [resAt_eq_smul_circleIntegral hfgρ hr hrρ, resAt_eq_smul_circleIntegral hfρ hr hrρ,
    resAt_eq_smul_circleIntegral hgρ hr hrρ]
  have : (∮ z in C(c, r), (f + g) z) = (∮ z in C(c, r), f z) + ∮ z in C(c, r), g z := by
    simpa using circleIntegral.integral_add (circleIntegrable_of_holo hfρ hr hrρ)
      (circleIntegrable_of_holo hgρ hr hrρ)
  rw [this, smul_add]

/-- **`resAt` is ℂ-homogeneous** on functions with an isolated singularity at `c`. -/
theorem resAt_smul {f : ℂ → ℂ} {c : ℂ} (a : ℂ) (hf : HoloPunctured f c) :
    resAt (a • f) c = a • resAt f c := by
  obtain ⟨ρ, hρ, hf'⟩ := hf
  set r := ρ / 2 with hrdef
  have hr : 0 < r := by positivity
  have hrρ : r < ρ := by rw [hrdef]; exact half_lt_self hρ
  have hafρ : ∀ z ∈ ball c ρ \ {c}, DifferentiableAt ℂ (a • f) z := fun z hz =>
    (hf' z hz).const_smul a
  rw [resAt_eq_smul_circleIntegral hafρ hr hrρ, resAt_eq_smul_circleIntegral hf' hr hrρ]
  have : (∮ z in C(c, r), (a • f) z) = a • ∮ z in C(c, r), f z := by
    simp only [Pi.smul_apply]; exact circleIntegral.integral_smul a f c r
  rw [this, smul_comm]

/-! ### Residue is a local invariant -/

/-- **`resAt` depends only on the germ of `f` at `c`** (a punctured-neighbourhood invariant).  Two
functions agreeing near `c` (off `c`) have the same residue — the small contour integrals coincide. -/
theorem resAt_congr {f g : ℂ → ℂ} {c : ℂ} (h : f =ᶠ[𝓝[≠] c] g) : resAt f c = resAt g c := by
  have h' : ∀ᶠ z in 𝓝[≠] c, f z = g z := h
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h'
  obtain ⟨ρ, hρ, hball⟩ := h'
  have hint : (fun r => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), f z)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun r => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), g z) := by
    filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
    congr 1
    refine circleIntegral.integral_congr hr.1.le (fun z hz => ?_)
    have hd : dist z c = r := Metric.mem_sphere.mp hz
    have hzc : z ≠ c := fun he => by rw [he, dist_self] at hd; exact absurd hd.symm (ne_of_gt hr.1)
    exact hball (show dist z c < ρ by rw [hd]; exact hr.2)
      (by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hzc)
  unfold resAt Filter.limUnder
  rw [Filter.map_congr hint]

/-- **Simple-pole residue.**  If `f` agrees near `c` with `z ↦ a·(z-c)⁻¹`, then `resAt f c = a`.
This is what reads off the residue of `α·g` once it is shown to be a simple pole `a/(z-c)` locally
(Forster §17.6's `dz/z` computation). -/
theorem resAt_eq_of_eventuallyEq_sub_inv {f : ℂ → ℂ} {a c : ℂ}
    (h : f =ᶠ[𝓝[≠] c] fun z => a * (z - c)⁻¹) :
    resAt f c = a := by
  rw [resAt_congr h, resAt_const_mul_sub_inv]

end Jacobians.Dolbeault
