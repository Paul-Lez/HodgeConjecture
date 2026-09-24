/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 License as described in the file LICENSE.
-/
module

public import Other.Analysis.Complex.NormalDivision

@[expose] public section

open Filter Topology Set

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def normalQuotientFinOne (f : E × (Fin 1 → ℂ) → ℂ) :
    E × (Fin 1 → ℂ) → ℂ :=
  let L := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  fun p ↦ normalQuotient (fun z ↦ f (z.1, L.symm z.2)) (p.1, L p.2)

theorem exists_nhds_normalQuotientFinOne_factor
    {f : E × (Fin 1 → ℂ) → ℂ} {V : Set (E × (Fin 1 → ℂ))} (hV : IsOpen V)
    (hzero : ∀ p ∈ V, p.2 = 0 → f p = 0)
    (hf : AnalyticOnNhd ℂ f V)
    {p : E × (Fin 1 → ℂ)} (hp : p ∈ V) (hpz : p.2 = 0)
    (hk : fderiv ℂ f p (0, fun _ : Fin 1 ↦ (1 : ℂ)) ≠ 0) :
    ∃ U ∈ 𝓝 p, IsOpen U ∧ U ⊆ V ∧
      ∃ u : C((U : Set (E × (Fin 1 → ℂ))), ℂ),
        (∀ y, u y ≠ 0) ∧
        (∀ y : U, f y = (y.1.2 0) * u y) := by
  let L := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  let lift : (E × ℂ) →L[ℂ] (E × (Fin 1 → ℂ)) :=
    ContinuousLinearMap.prod (ContinuousLinearMap.fst ℂ E ℂ)
      (L.symm.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℂ E ℂ))
  let push : (E × (Fin 1 → ℂ)) →L[ℂ] (E × ℂ) :=
    ContinuousLinearMap.prod (ContinuousLinearMap.fst ℂ E (Fin 1 → ℂ))
      (L.toContinuousLinearMap.comp
        (ContinuousLinearMap.snd ℂ E (Fin 1 → ℂ)))
  let V' := lift ⁻¹' V
  have hV' : IsOpen V' := hV.preimage lift.continuous
  have hzero' : ∀ z ∈ V', z.2 = 0 →
      f (lift z) = 0 := by
    intro z hz hzz
    apply hzero (lift z) hz
    change L.symm z.2 = 0
    rw [hzz, map_zero]
  have hf' : AnalyticOnNhd ℂ (f ∘ lift) V' :=
    hf.compContinuousLinearMap
  have hp' : push p ∈ V' := by
    change lift (push p) ∈ V
    change (p.1, L.symm (L p.2)) ∈ V
    rw [L.symm_apply_apply]
    exact hp
  have hpz' : (push p).2 = 0 := by
    change L p.2 = 0
    rw [hpz, map_zero]
  have hLPp : lift (push p) = p := by
    apply Prod.ext
    · rfl
    · exact L.symm_apply_apply p.2
  have hder : HasFDerivAt (f ∘ lift)
      ((fderiv ℂ f p).comp lift) (push p) := by
    have hfp := (hf p hp).hasStrictFDerivAt.hasFDerivAt
    have hfp' : HasFDerivAt f (fderiv ℂ f p) (lift (push p)) := by
      rw [hLPp]
      exact hfp
    have hcomp := hfp'.comp (push p) lift.hasFDerivAt
    simpa only [Function.comp_apply] using hcomp
  have hOne : L.symm (1 : ℂ) = (fun _ : Fin 1 ↦ (1 : ℂ)) := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  have hk' : fderiv ℂ (f ∘ lift) (push p) (0, 1) ≠ 0 := by
    intro h
    apply hk
    rw [hder.fderiv] at h
    simpa [lift, L, ContinuousLinearEquiv.piUnique_apply, hOne] using h
  obtain ⟨r, hr, hball, hne, hfactor⟩ :=
    exists_ball_analytic_normalQuotient_factor hV' hzero' hf' hp' hpz' hk'
  let U := push ⁻¹' Metric.ball (push p) r
  have hUopen : IsOpen U := Metric.isOpen_ball.preimage push.continuous
  have hUn : U ∈ 𝓝 p := by
    apply push.continuous.continuousAt
    exact Metric.mem_nhds_iff.mpr ⟨r, hr, subset_rfl⟩
  have hqcont : ContinuousOn (normalQuotientFinOne f) U := by
    have hqscalar : ContinuousOn (normalQuotient (f ∘ lift))
        (Metric.ball (push p) r) :=
      (continuousOn_normalQuotient_of_analyticOnNhd hV' hzero' hf').mono hball
    have hcomp := hqscalar.comp push.continuous.continuousOn (by
      intro y hy
      change push y ∈ Metric.ball (push p) r at hy
      exact hy)
    apply hcomp.congr
    intro y hy
    simp [normalQuotientFinOne, lift, push, L,
      ContinuousLinearEquiv.piUnique_apply, Function.comp_def]
  let u : C((U : Set (E × (Fin 1 → ℂ))), ℂ) :=
    ⟨fun y ↦ normalQuotientFinOne f y,
      continuousOn_iff_continuous_domRestrict.mp hqcont⟩
  refine ⟨U, hUn, hUopen, ?_, u, ?_, ?_⟩
  · intro y hy
    change push y ∈ Metric.ball (push p) r at hy
    have hyV' := hball hy
    change lift (push y) ∈ V at hyV'
    have hLP : lift (push y) = y := by
      apply Prod.ext
      · rfl
      · exact L.symm_apply_apply y.2
    rw [hLP] at hyV'
    exact hyV'
  · intro y
    have hyball : push (y : E × (Fin 1 → ℂ)) ∈ Metric.ball (push p) r := by
      exact y.property
    exact hne (push (y : E × (Fin 1 → ℂ))) hyball
  · intro y
    have hyball : push (y : E × (Fin 1 → ℂ)) ∈ Metric.ball (push p) r := by
      exact y.property
    have hfac := hfactor (push (y : E × (Fin 1 → ℂ))) hyball
    have hpush : push (y : E × (Fin 1 → ℂ)) = (y.1.1, y.1.2 0) := by
      apply Prod.ext
      · rfl
      · simp [push, L, ContinuousLinearEquiv.piUnique_apply]
    rw [hpush] at hfac
    have hLapply : L y.1.2 = y.1.2 0 := by
      simp [L, ContinuousLinearEquiv.piUnique_apply]
    have hLift : lift (y.1.1, y.1.2 0) = y.1 := by
      apply Prod.ext
      · rfl
      · rw [← hLapply]
        exact L.symm_apply_apply y.1.2
    rw [hLift] at hfac
    simpa [u, normalQuotientFinOne, lift, L,
      ContinuousLinearEquiv.piUnique_apply, Function.comp_def] using hfac

end Complex
