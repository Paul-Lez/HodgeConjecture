/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Analysis.Complex.NormalDivisionFinOne

@[expose] public section

open Filter Topology Set

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! Pulling a function back by a local analytic homeomorphism preserves a nonzero first jet. -/
theorem fderiv_comp_symm_ne_zero_of_openPartialHomeomorph
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (e : OpenPartialHomeomorph E F) {g : E → G} {p : E}
    (hp : p ∈ e.source) (hg : AnalyticAt ℂ g p)
    (he : AnalyticAt ℂ e p)
    (hes : AnalyticAt ℂ e.symm (e p))
    (hgne : fderiv ℂ g p ≠ 0) :
    fderiv ℂ (fun v ↦ g (e.symm v)) (e p) ≠ 0 := by
  have hleft : (fderiv ℂ e.symm (e p)).comp (fderiv ℂ e p) =
      ContinuousLinearMap.id ℂ E := by
    have hcomp := hes.hasStrictFDerivAt.hasFDerivAt.comp p
      he.hasStrictFDerivAt.hasFDerivAt
    have heq : e.symm ∘ e =ᶠ[𝓝 p] id := by
      filter_upwards [e.open_source.mem_nhds hp] with z hz
      exact e.left_inv hz
    have hid := hcomp.congr_of_eventuallyEq heq.symm
    simpa only [Function.comp_apply, fderiv_id] using hid.fderiv.symm
  have hpull : fderiv ℂ (fun v ↦ g (e.symm v)) (e p) =
      (fderiv ℂ g p).comp (fderiv ℂ e.symm (e p)) := by
    have hgp : HasFDerivAt g (fderiv ℂ g p) (e.symm (e p)) := by
      rw [e.left_inv hp]
      exact hg.hasStrictFDerivAt.hasFDerivAt
    have hcomp := hgp.comp (e p)
      hes.hasStrictFDerivAt.hasFDerivAt
    change fderiv ℂ (g ∘ e.symm) (e p) = _
    exact hcomp.fderiv
  intro hzero
  apply hgne
  rw [hpull] at hzero
  have hrewrite : fderiv ℂ g p =
      ((fderiv ℂ g p).comp (fderiv ℂ e.symm (e p))).comp
        (fderiv ℂ e p) := by
    calc
      fderiv ℂ g p = (fderiv ℂ g p).comp (ContinuousLinearMap.id ℂ E) := by
        rw [ContinuousLinearMap.comp_id]
      _ = (fderiv ℂ g p).comp
          ((fderiv ℂ e.symm (e p)).comp (fderiv ℂ e p)) := by rw [hleft]
      _ = ((fderiv ℂ g p).comp (fderiv ℂ e.symm (e p))).comp
          (fderiv ℂ e p) := by rw [ContinuousLinearMap.comp_assoc]
  rw [hrewrite, hzero, ContinuousLinearMap.zero_comp]

/-! A function which vanishes on the normal hyperplane has no tangent first jet. -/
theorem fderiv_eq_zero_on_normal_tangent
    {f : E × (Fin 1 → ℂ) → ℂ} {V : Set (E × (Fin 1 → ℂ))}
    (hV : IsOpen V) (hzero : ∀ p ∈ V, p.2 = 0 → f p = 0)
    (hf : AnalyticOnNhd ℂ f V) {a : E} (ha : (a, 0) ∈ V) (v : E) :
    fderiv ℂ f (a, 0) (v, 0) = 0 := by
  let line : ℂ → E × (Fin 1 → ℂ) := fun t ↦ (a + t • v, 0)
  have hline : HasFDerivAt line
      (((1 : ℂ →L[ℂ] ℂ).smulRight v).prod (0 : ℂ →L[ℂ] (Fin 1 → ℂ))) 0 := by
    have hleft : HasFDerivAt (fun t : ℂ ↦ a + t • v)
        ((1 : ℂ →L[ℂ] ℂ).smulRight v) 0 := by
      simpa only [smul_zero, add_zero, ContinuousLinearMap.smulRight_apply,
        one_apply_eq_self] using
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) v).hasFDerivAt
          : HasFDerivAt _ _ (0 : ℂ)) |>.const_add a
    simpa only [line] using hleft.prodMk (hasFDerivAt_const (0 : Fin 1 → ℂ) 0)
  have hline_zero : ∀ᶠ t : ℂ in 𝓝 0, line t ∈ V :=
    hline.continuousAt (by simpa [line] using hV.mem_nhds ha)
  have hline_eq : (fun _ : ℂ ↦ 0) =ᶠ[𝓝 0] f ∘ line := by
    filter_upwards [hline_zero] with t ht
    symm
    exact hzero (line t) ht rfl
  have hcomp : HasFDerivAt (f ∘ line)
      ((fderiv ℂ f (a, 0)).comp
        (((1 : ℂ →L[ℂ] ℂ).smulRight v).prod
          (0 : ℂ →L[ℂ] (Fin 1 → ℂ)))) 0 := by
    have hf' := (hf (a, 0) ha).hasStrictFDerivAt.hasFDerivAt
    have hf'' : HasFDerivAt f (fderiv ℂ f (a, 0)) (line 0) := by
      simpa [line] using hf'
    have hcomp' := hf''.comp 0 hline
    simpa only [line, Function.comp_apply, smul_zero, add_zero] using hcomp'
  have hcomp_zero := hcomp.congr_of_eventuallyEq hline_eq
  have hder : (fderiv ℂ f (a, 0)).comp
      (((1 : ℂ →L[ℂ] ℂ).smulRight v).prod
        (0 : ℂ →L[ℂ] (Fin 1 → ℂ))) = 0 := by
    simpa using hcomp_zero.fderiv.symm
  have := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1) hder
  simpa using this

theorem normal_deriv_ne_zero_of_fderiv_ne_zero
    {f : E × (Fin 1 → ℂ) → ℂ} {V : Set (E × (Fin 1 → ℂ))}
    (hV : IsOpen V) (hzero : ∀ p ∈ V, p.2 = 0 → f p = 0)
    (hf : AnalyticOnNhd ℂ f V) {a : E} (ha : (a, 0) ∈ V)
    (hfderiv : fderiv ℂ f (a, 0) ≠ 0) :
    fderiv ℂ f (a, 0) (0, fun _ : Fin 1 ↦ (1 : ℂ)) ≠ 0 := by
  intro hn
  apply hfderiv
  apply ContinuousLinearMap.ext
  intro p
  let t : ℂ := p.2 0
  let v : E := p.1
  have hp_tangent := fderiv_eq_zero_on_normal_tangent hV hzero hf ha v
  have hdecomp : p = (v, 0) + t • (0, fun _ : Fin 1 ↦ (1 : ℂ)) := by
    apply Prod.ext
    · simp [v]
    · funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp [t]
  rw [hdecomp, map_add, map_smul, hn, smul_zero, hp_tangent]
  simp

end Complex
