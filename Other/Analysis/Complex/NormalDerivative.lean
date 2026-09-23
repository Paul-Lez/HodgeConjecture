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
