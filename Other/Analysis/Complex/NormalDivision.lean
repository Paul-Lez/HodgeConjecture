/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 license.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Filter Topology Set Asymptotics

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The quotient by the second coordinate, filled in on the zero plane by the normal derivative. -/
noncomputable def normalQuotient (f : E × ℂ → ℂ) : E × ℂ → ℂ :=
  fun p ↦ if p.2 = 0 then fderiv ℂ f p (0, 1) else f p / p.2

private theorem normalQuotient_continuousAt_plane
    {f : E × ℂ → ℂ} {p : E × ℂ} (hp : p.2 = 0)
    (hf : HasStrictFDerivAt f (fderiv ℂ f p) p)
    (hdf : ContinuousAt (fderiv ℂ f) p)
    (hzero : ∀ᶠ v in 𝓝 ((p.1 : E)), f (v, 0) = 0) :
    ContinuousAt (normalQuotient f) p := by
  let L := fderiv ℂ f p
  let k := L (0, 1)
  let φ : (E × ℂ) → ((E × ℂ) × (E × ℂ)) :=
    fun w ↦ (w, (w.1, (0 : ℂ)))
  have hφ : Tendsto φ (𝓝 p) (𝓝 (p, p)) := by
    have hc : ContinuousAt (fun w : E × ℂ ↦ (w, (w.1, (0 : ℂ)))) p :=
      continuousAt_id.prodMk (continuousAt_fst.prodMk continuousAt_const)
    have ht := hc.tendsto
    have hp' : (p.1, (0 : ℂ)) = p := by ext <;> simp [hp]
    rw [hp'] at ht
    simpa [φ] using ht
  have hrem :
      (fun w ↦ f w - f (w.1, (0 : ℂ)) - L (0, w.2)) =o[𝓝 p]
        (fun w ↦ ((0 : E), w.2)) := by
    have h := hf.isLittleO.comp_tendsto hφ
    change (fun w ↦ f w - f (w.1, (0 : ℂ)) - (fderiv ℂ f p)
      (w - (w.1, (0 : ℂ)))) =o[𝓝 p]
      (fun w ↦ w - (w.1, (0 : ℂ))) at h
    have harg (w : E × ℂ) : w - (w.1, (0 : ℂ)) = ((0 : E), w.2) := by
      ext <;> simp
    have h' := h.congr
      (fun w ↦ by rw [harg w]) (fun w ↦ by rw [harg w])
    simpa only [L, Function.comp_def, Prod.fst, Prod.snd, sub_self, sub_zero, zero_add] using h'
  have hEval : ContinuousAt (fun w ↦ fderiv ℂ f w (0, 1)) p :=
    hdf.clm_apply continuousAt_const
  have hzero' : ∀ᶠ w in 𝓝 p, f (w.1, (0 : ℂ)) = 0 := by
    exact continuousAt_fst.tendsto.eventually hzero
  have hkp : normalQuotient f p = k := by
    simp only [normalQuotient, if_pos hp]
    rfl
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hremε := (Asymptotics.isLittleO_iff.mp hrem) (half_pos hε)
  have hEvalε := (Metric.tendsto_nhds.mp hEval) ε hε
  filter_upwards [hremε, hEvalε, hzero'] with w hwR hwE hwzero
  by_cases hzn : w.2 = 0
  · rw [normalQuotient, if_pos hzn]
    rw [hkp]
    simpa [k, dist_eq_norm_sub] using hwE
  · rw [hkp]
    rw [normalQuotient, if_neg hzn]
    rw [dist_eq_norm_sub]
    have hL : L ((0 : E), w.2) = w.2 * k := by
      calc
        L ((0 : E), w.2) = L (w.2 • ((0 : E), 1)) := by
          rw [show ((0 : E), w.2) = w.2 • ((0 : E), 1) by ext <;> simp]
        _ = w.2 • L ((0 : E), 1) := L.map_smul _ _
        _ = w.2 * k := by simp [k]
    have hq : f w / w.2 - k =
        (f w - f (w.1, (0 : ℂ)) - L ((0 : E), w.2)) / w.2 := by
      rw [hL]
      field_simp
      simp [hwzero]
    rw [hq, norm_div]
    calc
      ‖f w - f (w.1, (0 : ℂ)) - L ((0 : E), w.2)‖ / ‖w.2‖ ≤
          ((ε / 2) * ‖((0 : E), w.2)‖) / ‖w.2‖ := by
            gcongr
      _ = ε / 2 := by simp [Prod.norm_def, hzn]
      _ < ε := by linarith

/-- A continuously differentiable function vanishing on the zero-normal plane factors through the
normal coordinate with a continuous quotient on the full neighborhood. -/
theorem continuousOn_normalQuotient
    {f : E × ℂ → ℂ} {V : Set (E × ℂ)} (hV : IsOpen V)
    (hzero : ∀ p ∈ V, p.2 = 0 → f p = 0)
    (hf : ∀ p ∈ V, HasStrictFDerivAt f (fderiv ℂ f p) p)
    (hdf : ContinuousOn (fderiv ℂ f) V) :
    ContinuousOn (normalQuotient f) V := by
  intro p hp
  by_cases hpz : p.2 = 0
  · have hcont : ContinuousAt (normalQuotient f) p :=
      normalQuotient_continuousAt_plane hpz (hf p hp)
        (hdf.continuousAt (hV.mem_nhds hp)) (by
          have hp' : (p.1, (0 : ℂ)) = p := by ext <;> simp [hpz]
          have hVp : V ∈ 𝓝 (p.1, (0 : ℂ)) := by
            have hp' : (p.1, (0 : ℂ)) = p := by ext <;> simp [hpz]
            rw [hp']
            exact hV.mem_nhds hp
          have hev : ∀ᶠ v in 𝓝 ((p.1 : E)), (v, (0 : ℂ)) ∈ V :=
            (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds hVp
          filter_upwards [hev] with v hv
          exact hzero (v, 0) hv (by rfl))
    exact hcont.continuousWithinAt
  · have hq : ContinuousAt (normalQuotient f) p := by
      have hdiv : ContinuousAt (fun q ↦ f q / q.2) p :=
        (hf p hp).continuousAt.div continuousAt_snd (by exact hpz)
      apply hdiv.congr_of_eventuallyEq
      filter_upwards [(isOpen_ne.preimage continuous_snd).mem_nhds hpz] with q hqz
      change q.2 ≠ 0 at hqz
      simp [normalQuotient, hqz]
    exact hq.continuousWithinAt

end Complex

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Analytic functions admit continuous division by a simple normal coordinate on a zero-plane. -/
theorem analyticOnNhd_normalQuotient
    {f : E × ℂ → ℂ} {V : Set (E × ℂ)} (hV : IsOpen V)
    (hzero : ∀ p ∈ V, p.2 = 0 → f p = 0)
    (hf : AnalyticOnNhd ℂ f V) :
    ContinuousOn (normalQuotient f) V := by
  apply continuousOn_normalQuotient hV hzero
  · intro p hp
    exact (hf p hp).hasStrictFDerivAt
  · exact (hf.fderiv).continuousOn

end Complex

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Near a nonzero normal derivative, the continuous normal quotient is a nowhere-zero factor. -/
theorem exists_ball_normalQuotient_factor
    {f : E × ℂ → ℂ} {V : Set (E × ℂ)} (hV : IsOpen V)
    (hzero : ∀ p ∈ V, p.2 = 0 → f p = 0)
    (hcont : ContinuousOn (normalQuotient f) V)
    {p : E × ℂ} (hp : p ∈ V) (hpz : p.2 = 0)
    (hk : fderiv ℂ f p (0, 1) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball p r ⊆ V ∧
      (∀ y ∈ Metric.ball p r, normalQuotient f y ≠ 0) ∧
      (∀ y ∈ Metric.ball p r, f y = y.2 * normalQuotient f y) := by
  have hkp : normalQuotient f p ≠ 0 := by
    simpa [normalQuotient, hpz] using hk
  have hmem : V ∩ (normalQuotient f ⁻¹' ({0}ᶜ)) ∈ 𝓝 p := by
    apply inter_mem (hV.mem_nhds hp)
    change ∀ᶠ z in 𝓝 p, normalQuotient f z ≠ 0
    exact (hcont.continuousAt (hV.mem_nhds hp)).eventually_ne hkp
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨r, hr, fun y hy ↦ (hsub hy).1, ?_, ?_⟩
  · intro y hy
    exact (hsub hy).2
  · intro y hy
    have hyV : y ∈ V := (hsub hy).1
    by_cases hyz : y.2 = 0
    · rw [hzero y hyV hyz]
      simp [hyz]
    · rw [normalQuotient, if_neg hyz]
      field_simp

end Complex

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An analytic simple normal zero has a continuous nowhere-zero factor after shrinking. -/
theorem exists_ball_analytic_normalQuotient_factor
    {f : E × ℂ → ℂ} {V : Set (E × ℂ)} (hV : IsOpen V)
    (hzero : ∀ p ∈ V, p.2 = 0 → f p = 0)
    (hf : AnalyticOnNhd ℂ f V)
    {p : E × ℂ} (hp : p ∈ V) (hpz : p.2 = 0)
    (hk : fderiv ℂ f p (0, 1) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball p r ⊆ V ∧
      (∀ y ∈ Metric.ball p r, normalQuotient f y ≠ 0) ∧
      (∀ y ∈ Metric.ball p r, f y = y.2 * normalQuotient f y) :=
  exists_ball_normalQuotient_factor hV hzero (analyticOnNhd_normalQuotient hV hzero hf)
    hp hpz hk

end Complex
