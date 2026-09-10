import KirovDolbeault.GreenPositivity
import KirovDolbeault.SurfacePositivity

/-!
# Box-level Riemann positivity

Combining the two analytic leaves
* `Jacobians.integral_normSq_eq_boundary` (Green bridge: `∬_box ‖h‖² = −(i/2)·∮_{∂box} F̄·h dz`), and
* `Jacobians.integral_normSq_pos` (surface positivity: `∬_box ‖h‖² > 0` for `h ≢ 0`),

this file packages the boundary integral `∮_{∂box} F̄·h dz` as `boundaryForm h F` and proves it
equals a *strictly positive real* area integral (up to the factor `−i/2`).  This is the box-level
avatar of Riemann's second bilinear relation: once the cut chart identifies `∮_{∂box}` with the
period bilinear sum `∑ₖ(Aₖ B̄ₖ − Bₖ Āₖ)`, positivity of the period Hermitian form follows.
-/

open MeasureTheory Set intervalIntegral Complex

namespace Jacobians

/-- The two coordinate maps `ℝ² → ℂ` agree: `wMap p = wCLM p = p.1 + p.2·I`. -/
lemma wMap_eq_wCLM : wMap = wCLM := by
  funext p
  rw [wCLM_apply]
  rfl

/-- The counterclockwise boundary integral `∮_{∂box} F̄ · h dz`, where `∂box` is the boundary of the
unit square traversed `∫P(·,0) + I∫P(1,·) − ∫P(·,1) − I∫P(0,·)` with `P = F̄(w·)·h(w·)`. -/
noncomputable def boundaryForm (h F : ℂ → ℂ) : ℂ :=
  ((∫ x in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (x, 0))) * h (wCLM (x, 0)))
      + Complex.I * ∫ y in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (1, y))) * h (wCLM (1, y)))
    - (∫ x in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (x, 1))) * h (wCLM (x, 1)))
    - Complex.I * ∫ y in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (0, y))) * h (wCLM (0, y))

variable {h F : ℂ → ℂ} {U : Set ℂ}

/-- `h ∘ wCLM` is continuous on the closed box (from holomorphy of `h` on `U ⊇ box`). -/
lemma continuousOn_h_wCLM (hbox : wCLM '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ U)
    (hh : ∀ z ∈ U, HasDerivAt h (deriv h z) z) :
    ContinuousOn (fun p : ℝ × ℝ => h (wCLM p)) (Icc 0 1 ×ˢ Icc 0 1) := by
  intro p hp
  have hwU : wCLM p ∈ U := hbox ⟨p, hp, rfl⟩
  exact (((hh _ hwU).continuousAt).comp wCLM.continuous.continuousAt).continuousWithinAt

/-- **Box-level Riemann positivity (identity form).** For `h` holomorphic on an open `U ⊇ [0,1]²`
with primitive `F`, `−(i/2)·∮_{∂box} F̄·h dz = (∬_box ‖h‖² : ℝ)` (a real number, cast to `ℂ`). -/
theorem boundaryForm_eq_area (hbox : wCLM '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ U)
    (hh : ∀ z ∈ U, HasDerivAt h (deriv h z) z)
    (hF : ∀ z ∈ U, HasDerivAt F (h z) z) :
    -(Complex.I / 2) * boundaryForm h F
      = ((∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖h (wCLM (x, y))‖ ^ 2 : ℝ) : ℂ) := by
  -- `boundaryForm h F` is *definitionally* the explicit boundary expression in the Green bridge,
  -- so we may ascribe the bridge's type directly.
  have hbridge : (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (‖h (wCLM (x, y))‖ ^ 2 : ℂ))
      = -(Complex.I / 2) * boundaryForm h F :=
    integral_normSq_eq_boundary hbox hh hF
  -- the box integrand `(‖h‖² : ℂ)` elaborates as `(↑‖h‖)^2`; rewrite it as `↑(‖h‖²)` and pull the
  -- cast out of both interval integrals.
  have hcast : ∀ x : ℝ, (∫ y in (0:ℝ)..1, (‖h (wCLM (x, y))‖ ^ 2 : ℂ))
      = ((∫ y in (0:ℝ)..1, ‖h (wCLM (x, y))‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    push_cast; ring
  rw [← hbridge]
  simp_rw [hcast]
  exact intervalIntegral.integral_ofReal

/-- **Box-level Riemann positivity.** For `h` holomorphic on `U ⊇ [0,1]²` with primitive `F`, if `h`
is nonzero somewhere in the open box then `−(i/2)·∮_{∂box} F̄·h dz` is a *strictly positive real*. -/
theorem boundaryForm_pos (hbox : wCLM '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ U)
    (hh : ∀ z ∈ U, HasDerivAt h (deriv h z) z)
    (hF : ∀ z ∈ U, HasDerivAt F (h z) z)
    (p₀ : ℝ × ℝ) (hp₀ : p₀ ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) (hp₀ne : h (wCLM p₀) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ -(Complex.I / 2) * boundaryForm h F = (c : ℂ) := by
  refine ⟨∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖h (wCLM (x, y))‖ ^ 2, ?_,
    boundaryForm_eq_area hbox hh hF⟩
  -- positivity from `integral_normSq_pos` (after rewriting `wMap → wCLM`)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => h (wMap p)) (Icc 0 1 ×ˢ Icc 0 1) := by
    rw [wMap_eq_wCLM]; exact continuousOn_h_wCLM hbox hh
  have hp₀ne' : h (wMap p₀) ≠ 0 := by rw [wMap_eq_wCLM]; exact hp₀ne
  have hpos := integral_normSq_pos h hcont p₀ hp₀ hp₀ne'
  rwa [wMap_eq_wCLM] at hpos

end Jacobians
