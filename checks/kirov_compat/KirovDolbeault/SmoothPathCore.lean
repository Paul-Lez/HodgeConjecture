import KirovDolbeault.LineIntegral
import KirovDolbeault.SmoothPath
import KirovDolbeault.Genus
import KirovDolbeault.CotangentCoeff
import Mathlib.Topology.Connected.LocPathConnected

/-!
# SmoothPathCore: smoothPath-independent foundations + chart-ball-hop machinery

This module is **upstream of `Jacobians/PeriodLattice.lean`**. It hoists the
`smoothPath`-INDEPENDENT foundations and the chart-ball-hop machinery out of
`PeriodLattice.lean` and `OfCurveAnalyticitySkeleton.lean`, so that
`exists_smoothPath_family` (in `PeriodLattice.lean`) can be constructed from the
hop lemmas without the layering circularity that arose when those lemmas lived
downstream of `PeriodLattice`.

This is a pure code-relocation module: every declaration here was moved verbatim
(names and namespaces preserved) from `PeriodLattice.lean` (the `Jacobians`
namespace block) or `OfCurveAnalyticitySkeleton.lean` (the
`Jacobians.OfCurveSkeleton` namespace block).

## Contents
* `Jacobians` namespace: `basepoint`, path-connectedness instances,
  `continuousPath`, `periodBasisForm`, `periodVec`, `IsClosedSmoothLoop`,
  `closedLoopPeriods`, `IsSmoothPath` (+ `toClosedSmoothLoop`, `reverse`,
  `isSmoothPath_const`), `IsClosedSmoothLoop.reverse`.
* `Jacobians.OfCurveSkeleton` namespace: `chartFormCoeff`,
  `chartFormCoeff_differentiableOn`, `localLiftChart`, `localLift`,
  `trivAt_symmL_one_eq_fderiv`, `trivAt_symmL_one_eq_fderiv_C`,
  `chartBallPath_mem_source_of_affine`, `chartFrame_cancel`,
  `Q_in_chart_source_eventually`, `affine_in_target_eventually`,
  `localLift_eq_const_add_periodVec_ChartBallPath`,
  `pathSpeed_smoothStep01_comp_eq`, `isSmoothPath_ChartBallPathSmooth`.

## References

Forster §§1–2, 20–21; Miranda Ch. V §§1–3.
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology
open Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Arbitrary basepoint in `X` (via `Nonempty`). The period lattice
is independent of basepoint choice, because any two basepoints can
be connected by a path which conjugates closed loops without changing
the integral (modulo the lattice itself). -/
noncomputable def basepoint (X : Type*) [Nonempty X] : X := Classical.arbitrary X

/-! ### Path-connectedness of a compact Riemann surface (classical)

A connected manifold over a locally-path-connected model is itself
path-connected. Specifically: `ChartedSpace ℂ X` inherits
`LocPathConnectedSpace X` from `ℂ` via chart-local homeomorphisms
(`ChartedSpace.locPathConnectedSpace`), and combined with
`ConnectedSpace X` gives `PathConnectedSpace X`
(`pathConnectedSpace_iff_connectedSpace`).

From this we get `Path P Q` for any `P Q : X` — a continuous path
between any two points on a compact connected Riemann surface. -/

/-- `X` is locally path-connected, inherited from `ℂ` via charts. -/
instance instLocPathConnectedSpaceOfChartedSpaceC
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] :
    LocPathConnectedSpace X :=
  ChartedSpace.locPathConnectedSpace ℂ X

/-- `X` is path-connected (connected + locally path-connected). -/
instance instPathConnectedSpaceOfConnectedChartedSpace
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [ConnectedSpace X] :
    PathConnectedSpace X :=
  pathConnectedSpace_iff_connectedSpace.mpr inferInstance

/-- **Classical fact**: for any two points on a connected compact
Riemann surface, there exists a continuous path between them.

This is just `PathConnectedSpace.somePath`; captured as an explicit
theorem for readability and for consumption by downstream Abel-Jacobi
definitions. Upgrading to a *smooth* path requires additional
content (smooth-approximation theorem — a known Mathlib gap for
general manifolds). -/
noncomputable def continuousPath (P Q : X) : Path P Q :=
  (PathConnectedSpace.somePath P Q)

/-- The i-th basis element of `HolomorphicOneForms X`, defined via
`ambientIso X` applied to the standard unit vector. This choice
aligns the period pairing with the matrix structure of `ambientPhi`
and `ambientPsi`, which are expressed in the `Pi.basisFun` basis. -/
noncomputable def periodBasisForm (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (i : Fin (kirovGenus X)) : HolomorphicOneForms X :=
  ambientIso X (Pi.basisFun ℂ (Fin (kirovGenus X)) i)

/-- Period vector of a path `γ`: line integrals of each basis form. -/
noncomputable def periodVec (γ : ℝ → X) : Fin (kirovGenus X) → ℂ :=
  fun i => lineIntegral (periodBasisForm X i) γ

/-- Regularity predicate for a closed loop in `X`: closed endpoints
+ continuity + chart-pullback differentiability + integrability of
each basis-form integrand. Packages what's needed for the
`lineIntegral` machinery (Phase 1 identities, chain rule, basis
expansion) to apply sensibly. -/
structure IsClosedSmoothLoop (γ : ℝ → X) : Prop where
  closed : γ 0 = γ 1
  cont : Continuous γ
  diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
    DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t
  velCont : ContinuousOn (fun s : ℝ =>
      Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s))
    (Set.Icc 0 1)

/-- **Each basis-form integrand is interval-integrable** (drop-in for the former `integrable`
field): derived from the geometric `velCont` field via
`intervalIntegrable_form_pathSpeed_of_velContinuous`. Same signature as the old field, so all
consumers are unchanged. -/
theorem IsClosedSmoothLoop.integrable {γ : ℝ → X} (h : IsClosedSmoothLoop γ) :
    ∀ i : Fin (kirovGenus X), IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
        MeasureTheory.volume 0 1 :=
  fun i => intervalIntegrable_form_pathSpeed_of_velContinuous (periodBasisForm X i) γ h.velCont

/-- The set of period vectors arising from closed smooth loops (at
any basepoint). Requires `IsClosedSmoothLoop` regularity so that the
Phase 1 line-integral identities + chain rule apply. -/
def closedLoopPeriods (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Set (Fin (kirovGenus X) → ℂ) :=
  {v | ∃ (γ : ℝ → X), IsClosedSmoothLoop γ ∧ v = periodVec γ}

/-- **Smooth path between two points** with `periodVec`-integrability.
Contains exactly the data needed to apply `periodVec` / `lineIntegral`
machinery to the path; the endpoint hypotheses ensure the path goes
from `P` to `Q`. -/
structure IsSmoothPath (P Q : X) (γ : ℝ → X) : Prop where
  /-- Path starts at `P`. -/
  start : γ 0 = P
  /-- Path ends at `Q`. -/
  finish : γ 1 = Q
  /-- Continuity of the path. -/
  cont : Continuous γ
  /-- Chart-pullback differentiability at each point of `[0,1]`. -/
  diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
    DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t
  /-- Continuity of the velocity tangent-section. -/
  velCont : ContinuousOn (fun s : ℝ =>
      Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s))
    (Set.Icc 0 1)

/-- **Each basis-form integrand is interval-integrable** (drop-in for the former `integrable`
field): derived from the geometric `velCont` field via
`intervalIntegrable_form_pathSpeed_of_velContinuous`. Same signature as the old field, so all
consumers are unchanged. -/
theorem IsSmoothPath.integrable {P Q : X} {γ : ℝ → X} (h : IsSmoothPath P Q γ) :
    ∀ i : Fin (kirovGenus X), IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
        MeasureTheory.volume 0 1 :=
  fun i => intervalIntegrable_form_pathSpeed_of_velContinuous (periodBasisForm X i) γ h.velCont

/-- A smooth path from `P` to itself is a closed smooth loop. -/
theorem IsSmoothPath.toClosedSmoothLoop {P : X} {γ : ℝ → X}
    (h : IsSmoothPath P P γ) : IsClosedSmoothLoop γ where
  closed := h.start.trans h.finish.symm
  cont := h.cont
  diff := h.diff
  velCont := h.velCont

/-- **The constant path is a smooth path (and a smooth loop).** Trivial
foundational case: `γ = fun _ => P` satisfies all `IsSmoothPath`
conditions because chart-pullbacks of constants are constant
(differentiable), and the form-integrand vanishes since `pathSpeed` of
a constant curve is zero (`pathSpeed_const`). -/
theorem isSmoothPath_const (P : X) :
    IsSmoothPath P P (fun _ : ℝ => P) where
  start := rfl
  finish := rfl
  cont := continuous_const
  diff := by
    intro t _
    -- (chartAt ℂ P) ∘ (fun _ => P) = fun _ => (chartAt ℂ P) P, a constant.
    show DifferentiableAt ℝ
      (fun _ : ℝ => (chartAt (H := ℂ) P).toFun P) t
    exact differentiableAt_const _
  velCont := by
    -- Velocity section is `⟨P, pathSpeed (const P) s⟩ = ⟨P, 0⟩` (constant) via `pathSpeed_const`.
    have h_eq : (fun s : ℝ => Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) P
        (pathSpeed (fun _ : ℝ => P) s)) =
        (fun _ : ℝ => Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) P
          (0 : TangentSpace 𝓘(ℂ) (M := X) P)) := by
      funext s; rw [pathSpeed_const]; rfl
    rw [h_eq]
    exact continuousOn_const

/-- **Reverse of a closed smooth loop is a closed smooth loop** (REAL).
The reverse loop `t ↦ γ(1 - t)` is still closed and smooth. -/
theorem IsClosedSmoothLoop.reverse {γ : ℝ → X}
    (h : IsClosedSmoothLoop γ) : IsClosedSmoothLoop (Jacobians.reverse γ) where
  closed := by show γ (1 - 0) = γ (1 - 1); simp [h.closed]
  cont := h.cont.comp (continuous_const.sub continuous_id)
  diff := by
    intro t ht
    have h1t : 1 - t ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht ⊢
      rcases ht with ⟨h0, h1⟩
      refine ⟨by linarith, by linarith⟩
    have hdiff_inner := h.diff (1 - t) h1t
    have h_comp : (chartAt (H := ℂ) (Jacobians.reverse γ t)).toFun ∘ Jacobians.reverse γ =
        (chartAt (H := ℂ) (γ (1 - t))).toFun ∘ γ ∘ (fun s => 1 - s) := by
      funext s; rfl
    rw [h_comp]
    have h_sub_diff : DifferentiableAt ℝ (fun s : ℝ => 1 - s) t :=
      (differentiableAt_const _).sub differentiableAt_id
    exact hdiff_inner.comp t h_sub_diff
  velCont := velCont_reverse γ h.diff h.velCont

/-- **Reverse of a smooth path is a smooth path** (REAL). The reverse
path `t ↦ γ(1 - t)` goes from `Q` to `P` when `γ` goes `P` to `Q`,
with smoothness preserved via the chain rule on `(1 - ·)`. -/
theorem IsSmoothPath.reverse {P Q : X} {γ : ℝ → X}
    (h : IsSmoothPath P Q γ) : IsSmoothPath Q P (Jacobians.reverse γ) where
  start := by show γ (1 - 0) = Q; simp [h.finish]
  finish := by show γ (1 - 1) = P; simp [h.start]
  cont := h.cont.comp (continuous_const.sub continuous_id)
  diff := by
    intro t ht
    -- Goal: DifferentiableAt ℝ ((chartAt ℂ (reverse γ t)).toFun ∘ reverse γ) t
    -- = DifferentiableAt ℝ ((chartAt ℂ (γ (1-t))).toFun ∘ (fun s => γ (1-s))) t
    -- By chain rule on `s ↦ 1 - s` + h.diff at (1 - t).
    have h1t : 1 - t ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht ⊢
      rcases ht with ⟨h0, h1⟩
      refine ⟨by linarith, by linarith⟩
    have hdiff_inner := h.diff (1 - t) h1t
    -- Rewrite reverse γ to γ ∘ (1 - ·).
    have h_comp : (chartAt (H := ℂ) (Jacobians.reverse γ t)).toFun ∘ Jacobians.reverse γ =
        (chartAt (H := ℂ) (γ (1 - t))).toFun ∘ γ ∘ (fun s => 1 - s) := by
      funext s
      show (chartAt (H := ℂ) (γ (1 - t))).toFun (γ (1 - s)) = _
      rfl
    rw [h_comp]
    have h_sub_diff : DifferentiableAt ℝ (fun s : ℝ => 1 - s) t :=
      (differentiableAt_const _).sub differentiableAt_id
    exact hdiff_inner.comp t h_sub_diff
  velCont := velCont_reverse γ h.diff h.velCont

open MeasureTheory in
/-- **Concatenation of two smooth paths is a smooth path** — provided the
junction velocities vanish (`pathSpeed γ₁ 1 = 0` and `pathSpeed γ₂ 0 = 0`).

`concat γ₁ γ₂` runs `γ₁(2t)` on `[0,½]` and `γ₂(2t−1)` on `[½,1]`. The C¹
(`diff`) field at the junction `t = ½` requires the left and right chart
velocities to agree; the two hypotheses make both one-sided derivatives `0`,
glued via `HasDerivWithinAt` on `Iic ∪ Ici`. This is the general form of the
proven 2-piece junction lemma
`OfCurveSkeleton.isClosedSmoothLoop_concat_ChartBallPathSmooth_reverse_smoothPathSmooth`,
and the keystone for the n-piece glued path used to discharge
`exists_smoothPath_family`: every hop there is smoothstep-reparametrized, so
its endpoint velocities are `0` and the hypotheses hold. -/
theorem IsSmoothPath.concat {P Q R : X} {γ₁ γ₂ : ℝ → X}
    (h₁ : IsSmoothPath P Q γ₁) (h₂ : IsSmoothPath Q R γ₂)
    (hv₁ : pathSpeed γ₁ 1 = 0) (hv₂ : pathSpeed γ₂ 0 = 0) :
    IsSmoothPath P R (Jacobians.concat γ₁ γ₂) where
  start := by
    rw [Jacobians.concat_apply_left _ _ (by norm_num : (0:ℝ) ≤ 1/2),
        show (2:ℝ) * 0 = 0 from by norm_num]
    exact h₁.start
  finish := by
    rw [Jacobians.concat_apply_right _ _ (by norm_num : ¬ (1:ℝ) ≤ 1/2),
        show (2:ℝ) * 1 - 1 = 1 from by norm_num]
    exact h₂.finish
  cont := by
    unfold Jacobians.concat
    refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
    · exact h₁.cont.comp (continuous_const.mul continuous_id)
    · exact h₂.cont.comp ((continuous_const.mul continuous_id).sub continuous_const)
    · intro t ht
      have ht_eq : t = 1/2 := ht
      rw [ht_eq]
      show γ₁ (2 * (1/2 : ℝ)) = γ₂ (2 * (1/2 : ℝ) - 1)
      rw [show (2:ℝ) * (1/2) = 1 from by norm_num, show (1:ℝ) - 1 = 0 from by norm_num]
      rw [h₁.finish]; exact h₂.start.symm
  diff := by
    intro t ht
    have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht; exact ht
    rcases lt_trichotomy t (1/2) with h_lt | h_eq | h_gt
    · -- t < 1/2
      have h2t_Icc : 2 * t ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact ⟨by linarith [ht_Icc.1], by linarith [ht_Icc.1]⟩
      have h_inner_diff := h₁.diff (2 * t) h2t_Icc
      have h_pt : Jacobians.concat γ₁ γ₂ t = γ₁ (2 * t) :=
        Jacobians.concat_apply_left _ _ (le_of_lt h_lt)
      have h_eventually : (chartAt (H := ℂ) (Jacobians.concat γ₁ γ₂ t)).toFun ∘
          Jacobians.concat γ₁ γ₂ =ᶠ[nhds t]
          ((chartAt (H := ℂ) (γ₁ (2 * t))).toFun ∘ γ₁) ∘ (fun s : ℝ => 2 * s) := by
        have h_open : IsOpen (Set.Iio (1/2 : ℝ)) := isOpen_Iio
        filter_upwards [h_open.mem_nhds (show t ∈ Set.Iio (1/2 : ℝ) from h_lt)] with s hs
        simp only [Function.comp_apply, h_pt]
        rw [Jacobians.concat_apply_left _ _ (le_of_lt hs)]
      rw [Filter.EventuallyEq.differentiableAt_iff h_eventually]
      exact h_inner_diff.comp t ((differentiableAt_const _).mul differentiableAt_id)
    · -- t = 1/2 (junction; both one-sided derivatives are 0)
      subst h_eq
      have hQ_eq : Jacobians.concat γ₁ γ₂ (1/2 : ℝ) = Q := by
        rw [Jacobians.concat_apply_left _ _ (le_refl _),
            show (2:ℝ) * (1/2) = 1 from by norm_num]
        exact h₁.finish
      rw [show (Jacobians.concat γ₁ γ₂ (1/2 : ℝ)) = Q from hQ_eq]
      set f : ℝ → ℂ := (chartAt (H := ℂ) Q).toFun ∘ Jacobians.concat γ₁ γ₂ with hf_def
      have h_one_uIcc : (1 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
      have h_zero_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_refl _, zero_le_one⟩
      have h_2mul_HDA : HasDerivAt (fun s : ℝ => 2 * s) (2 : ℝ) (1/2 : ℝ) := by
        simpa using (hasDerivAt_id (1/2 : ℝ)).const_mul (2 : ℝ)
      -- LEFT: HasDerivWithinAt f 0 on Iic(1/2)
      have h_g_L_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ₁ 1)).toFun ∘ γ₁) 1 :=
        h₁.diff 1 h_one_uIcc
      rw [h₁.finish] at h_g_L_diff
      have h_g_L_HDA : HasDerivAt ((chartAt (H := ℂ) Q).toFun ∘ γ₁) 0 1 := by
        have h_path_eq : pathSpeed γ₁ 1 = deriv ((chartAt (H := ℂ) Q).toFun ∘ γ₁) 1 := by
          show fderiv ℝ ((chartAt (H := ℂ) (γ₁ 1)).toFun ∘ γ₁) 1 1 = _
          rw [h₁.finish]; rfl
        have h_deriv_zero : deriv ((chartAt (H := ℂ) Q).toFun ∘ γ₁) 1 = 0 := by
          rw [← h_path_eq]; exact hv₁
        rw [← h_deriv_zero]; exact h_g_L_diff.hasDerivAt
      have h_f_L_HDA : HasDerivAt
          (((chartAt (H := ℂ) Q).toFun ∘ γ₁) ∘ (fun s : ℝ => 2 * s)) 0 (1/2 : ℝ) := by
        simpa using h_g_L_HDA.scomp_of_eq (1/2 : ℝ) h_2mul_HDA
          (by norm_num : (1 : ℝ) = 2 * (1/2 : ℝ))
      have h_eqOn_Iic : Set.EqOn f
          (((chartAt (H := ℂ) Q).toFun ∘ γ₁) ∘ (fun s : ℝ => 2 * s)) (Set.Iic (1/2 : ℝ)) := by
        intro s hs
        simp only [hf_def, Function.comp_apply]
        rw [Jacobians.concat_apply_left _ _ hs]
      have h_Iic_HDWA : HasDerivWithinAt f 0 (Set.Iic (1/2 : ℝ)) (1/2 : ℝ) :=
        (h_f_L_HDA.hasDerivWithinAt (s := Set.Iic (1/2 : ℝ))).congr
          (fun s hs => h_eqOn_Iic hs) (h_eqOn_Iic Set.self_mem_Iic)
      -- RIGHT: HasDerivWithinAt f 0 on Ici(1/2)
      have h_g_R_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ₂ 0)).toFun ∘ γ₂) 0 :=
        h₂.diff 0 h_zero_uIcc
      rw [h₂.start] at h_g_R_diff
      have h_g_R_HDA : HasDerivAt ((chartAt (H := ℂ) Q).toFun ∘ γ₂) 0 0 := by
        have h_path_eq : pathSpeed γ₂ 0 = deriv ((chartAt (H := ℂ) Q).toFun ∘ γ₂) 0 := by
          show fderiv ℝ ((chartAt (H := ℂ) (γ₂ 0)).toFun ∘ γ₂) 0 1 = _
          rw [h₂.start]; rfl
        have h_deriv_zero : deriv ((chartAt (H := ℂ) Q).toFun ∘ γ₂) 0 = 0 := by
          rw [← h_path_eq]; exact hv₂
        rw [← h_deriv_zero]; exact h_g_R_diff.hasDerivAt
      have h_f_R_HDA : HasDerivAt
          (((chartAt (H := ℂ) Q).toFun ∘ γ₂) ∘ (fun s : ℝ => 2 * s - 1)) 0 (1/2 : ℝ) := by
        simpa using h_g_R_HDA.scomp_of_eq (1/2 : ℝ) (h_2mul_HDA.sub_const 1)
          (by norm_num : (0 : ℝ) = 2 * (1/2 : ℝ) - 1)
      have h_eqOn_Ici : Set.EqOn f
          (((chartAt (H := ℂ) Q).toFun ∘ γ₂) ∘ (fun s : ℝ => 2 * s - 1)) (Set.Ici (1/2 : ℝ)) := by
        intro s hs
        simp only [hf_def, Function.comp_apply]
        rcases eq_or_lt_of_le (show (1/2 : ℝ) ≤ s from hs) with h_eq_half | h_gt_half
        · rw [← h_eq_half, Jacobians.concat_apply_left _ _ (le_refl _),
              show (2:ℝ) * (1/2) - 1 = 0 from by norm_num,
              show (2:ℝ) * (1/2) = 1 from by norm_num, h₁.finish, h₂.start]
        · rw [Jacobians.concat_apply_right _ _ (not_le.mpr h_gt_half)]
      have h_Ici_HDWA : HasDerivWithinAt f 0 (Set.Ici (1/2 : ℝ)) (1/2 : ℝ) :=
        (h_f_R_HDA.hasDerivWithinAt (s := Set.Ici (1/2 : ℝ))).congr
          (fun s hs => h_eqOn_Ici hs) (h_eqOn_Ici Set.self_mem_Ici)
      -- UNION
      have h_union : HasDerivWithinAt f 0
          (Set.Iic (1/2 : ℝ) ∪ Set.Ici (1/2 : ℝ)) (1/2 : ℝ) :=
        h_Iic_HDWA.union h_Ici_HDWA
      have h_union_eq : Set.Iic (1/2 : ℝ) ∪ Set.Ici (1/2 : ℝ) = Set.univ := by
        ext x; simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
        rcases lt_or_ge x (1/2 : ℝ) with h | h
        · exact Or.inl (le_of_lt h)
        · exact Or.inr h
      rw [h_union_eq] at h_union
      exact (h_union.hasDerivAt Filter.univ_mem).differentiableAt
    · -- t > 1/2
      have h2tm1_Icc : 2 * t - 1 ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact ⟨by linarith, by linarith [ht_Icc.2]⟩
      have h_inner_diff := h₂.diff (2 * t - 1) h2tm1_Icc
      have h_pt : Jacobians.concat γ₁ γ₂ t = γ₂ (2 * t - 1) :=
        Jacobians.concat_apply_right _ _ (not_le.mpr h_gt)
      have h_eventually : (chartAt (H := ℂ) (Jacobians.concat γ₁ γ₂ t)).toFun ∘
          Jacobians.concat γ₁ γ₂ =ᶠ[nhds t]
          ((chartAt (H := ℂ) (γ₂ (2 * t - 1))).toFun ∘ γ₂) ∘ (fun s : ℝ => 2 * s - 1) := by
        have h_open : IsOpen (Set.Ioi (1/2 : ℝ)) := isOpen_Ioi
        filter_upwards [h_open.mem_nhds (show t ∈ Set.Ioi (1/2 : ℝ) from h_gt)] with s hs
        simp only [Function.comp_apply, h_pt]
        rw [Jacobians.concat_apply_right _ _ (not_le.mpr hs)]
      rw [Filter.EventuallyEq.differentiableAt_iff h_eventually]
      exact h_inner_diff.comp t
        (((differentiableAt_const _).mul differentiableAt_id).sub (differentiableAt_const _))
  velCont :=
    velCont_concat γ₁ γ₂ h₁.diff h₂.diff hv₁ hv₂ (h₁.finish.trans h₂.start.symm)
      h₁.velCont h₂.velCont

end Jacobians

/-! ## Chart-ball-hop machinery (`Jacobians.OfCurveSkeleton`)

The following declarations were moved verbatim from
`OfCurveAnalyticitySkeleton.lean`. They are all `smoothPath`-INDEPENDENT
and form the transitive closure (within that namespace) of
`isSmoothPath_ChartBallPathSmooth`. -/

open scoped Manifold ContDiff
open Complex Set
open MeasureTheory

namespace Jacobians.OfCurveSkeleton

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Chart-pulled-back periodBasisForm at a chart-coord point.**

Given `Q₀ : X` with chart `e := chartAt ℂ Q₀`, and a chart-coordinate
`z ∈ e.target`, the chart-pulled-back periodBasisForm is the value of
the form's **local representative** (from `Jacobians.Montel.LocalRep`)
at the point `e.symm z`.

The local representative `localRep α x₀ y` evaluates `α.toFun y` at
the canonical tangent vector at `y` induced by the trivialization of
the tangent bundle at `x₀` (applied to the unit `1 : ℂ`). It is the
coefficient of `dz` in the chart-coord expression of `α`. -/
noncomputable def chartFormCoeff (Q₀ : X) (i : Fin (kirovGenus X)) (z : ℂ) : ℂ :=
  Jacobians.Montel.localRep (periodBasisForm X i) Q₀
    ((chartAt (H := ℂ) Q₀).symm z)

/-- **The chart-form coefficient is holomorphic on the chart target.**

PROVEN: direct corollary of `Jacobians.Montel.localRep_analyticOn_chartTarget`
(the existing chart-coord analyticity of `localRep`, proven via
`localRep_contMDiffOn` + `contDiffOn_omega_iff_analyticOn`). -/
theorem chartFormCoeff_differentiableOn (Q₀ : X) (i : Fin (kirovGenus X)) :
    DifferentiableOn ℂ (chartFormCoeff (X := X) Q₀ i)
      ((chartAt (H := ℂ) Q₀).target) :=
  (Jacobians.Montel.localRep_analyticOn_chartTarget
    (periodBasisForm X i) Q₀).differentiableOn

/-- **Local lift `Φ_{Q₀}` in chart coordinates.**

For chart coord `z ∈ e.target` (where `e = chartAt ℂ Q₀`), the local
lift of `ofCurve P` at `Q₀` is

```
Φ̃_{Q₀, i}(z) := constant_i + ∫_0^1 chartFormCoeff Q₀ i (z₀ + t (z - z₀)) * (z - z₀) dt
```

where `z₀ = e Q₀` and `constant_i := periodVec(some-fixed-path P → Q₀) i`.

For now, we only need that `Φ̃_{Q₀, i}` is `AnalyticAt ℂ` at `z₀`. -/
noncomputable def localLiftChart (Q₀ : X) (constants : Fin (kirovGenus X) → ℂ)
    (i : Fin (kirovGenus X)) (z : ℂ) : ℂ :=
  constants i +
    ∫ t in (0 : ℝ)..1,
      (chartFormCoeff (X := X) Q₀ i
        ((chartAt (H := ℂ) Q₀) Q₀ + (t : ℂ) * (z - (chartAt (H := ℂ) Q₀) Q₀))
       * (z - (chartAt (H := ℂ) Q₀) Q₀))

/-- **Vector-valued local lift** at `Q₀`. -/
noncomputable def localLift (Q₀ : X) (constants : Fin (kirovGenus X) → ℂ)
    (Q : X) : Fin (kirovGenus X) → ℂ :=
  fun i => localLiftChart (X := X) Q₀ constants i ((chartAt (H := ℂ) Q₀) Q)

/-- **Chart-Q₀ tangent vector via the trivialization**: at any point
`y` in the chart source of `Q₀`, `(trivAt Q₀).symmL ℂ y 1` equals the
fderiv (over ℂ) of the chart-transition map. This is a specialization
of Mathlib's `TangentBundle.symmL_trivializationAt_eq_core`.

Note: with `I = 𝓘(ℂ)`, `range I = univ`, so `fderivWithin _ _ univ = fderiv`.
We state the lemma in the `fderivWithin` form to match what `tangentBundleCore`
gives directly; downstream we rewrite to `fderiv ℂ`. -/
lemma trivAt_symmL_one_eq_fderiv (Q₀ y : X)
    (hy : y ∈ (chartAt (H := ℂ) Q₀).source) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ y (1 : ℂ) =
      fderivWithin ℂ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) Q₀).symm)
        Set.univ ((chartAt (H := ℂ) Q₀) y) (1 : ℂ) := by
  have h_symmL := TangentBundle.symmL_trivializationAt_eq_core
    (I := 𝓘(ℂ, ℂ)) (M := X) (E := ℂ) (b₀ := Q₀) (b := y) hy
  -- Apply the equality at 1 ∈ ℂ.
  rw [show ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ y (1 : ℂ))
        = ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ y) (1 : ℂ) from rfl]
  rw [h_symmL]
  -- The coord change is `fderivWithin ℂ (extChartAt 𝓘(ℂ) y ∘ (extChartAt 𝓘(ℂ) Q₀).symm)
  --   (range 𝓘(ℂ)) (extChartAt 𝓘(ℂ) Q₀ y)`.
  -- For 𝓘(ℂ), extChartAt = chartAt and range = univ.
  show (tangentBundleCore 𝓘(ℂ, ℂ) X).coordChange (achart ℂ Q₀) (achart ℂ y) y (1 : ℂ) =
    fderivWithin ℂ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) Q₀).symm) Set.univ
      ((chartAt (H := ℂ) Q₀) y) (1 : ℂ)
  rw [tangentBundleCore_coordChange_achart]
  -- Goal: fderivWithin ℂ (extChartAt 𝓘(ℂ) y ∘ (extChartAt 𝓘(ℂ) Q₀).symm) (range 𝓘(ℂ))
  --        (extChartAt 𝓘(ℂ) Q₀ y) 1 = fderivWithin ℂ ((chartAt y) ∘ (chartAt Q₀).symm)
  --        univ ((chartAt Q₀) y) 1
  have hrange : (Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ)) = Set.univ := by
    exact ModelWithCorners.range_eq_univ _
  have hext_chart : ∀ (z : ℂ) (b : X),
      ((extChartAt (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) b) : X → ℂ) = (chartAt (H := ℂ) b) := by
    intro z b; funext w
    simp [extChartAt]
  have hext_chart_pt : ∀ (b : X) (w : X),
      (extChartAt (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) b) w =
        (chartAt (H := ℂ) b) w := by
    intros; simp [extChartAt]
  have hext_symm : ∀ (b : X) (z : ℂ),
      ((extChartAt (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) b).symm) z =
        (chartAt (H := ℂ) b).symm z := by
    intros; simp [extChartAt]
  -- Now rewrite all extChartAt's to chartAt's.
  rw [hrange]
  rw [hext_chart_pt Q₀ y]
  -- After unfolding extChartAt to chartAt, the two functions are definitionally
  -- equal (extChartAt 𝓘(ℂ) b = chartAt b, extChartAt symm = chartAt symm).
  rfl

/-- **ℂ-version of the chart-Q₀-frame tangent identity**. Since
`fderivWithin ℂ _ univ = fderiv ℂ _`, we can express `(trivAt Q₀).symmL ℂ y 1`
as the plain `fderiv ℂ` of the chart transition. -/
lemma trivAt_symmL_one_eq_fderiv_C (Q₀ y : X)
    (hy : y ∈ (chartAt (H := ℂ) Q₀).source) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ y (1 : ℂ) =
      fderiv ℂ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) Q₀).symm)
        ((chartAt (H := ℂ) Q₀) y) (1 : ℂ) := by
  rw [trivAt_symmL_one_eq_fderiv Q₀ y hy, fderivWithin_univ]

/-- **Chart-source membership: ChartBallPath Q₀ Q₀ Q t is in `(chartAt Q₀).source`
when the affine point is in `target`.** Trivial consequence of `ChartBallPath_mem_source`. -/
lemma chartBallPath_mem_source_of_affine (Q₀ Q : X) (t : ℝ)
    (h_target : ((1 - (t : ℂ)) * (chartAt ℂ Q₀) Q₀ + (t : ℂ) * (chartAt ℂ Q₀) Q)
        ∈ (chartAt ℂ Q₀).target) :
    Jacobians.ChartBallPath Q₀ Q₀ Q t ∈ (chartAt (H := ℂ) Q₀).source := by
  exact Jacobians.ChartBallPath_mem_source Q₀ Q₀ Q t h_target

/-- **Key chart-frame cancellation lemma (pointwise).** For `γ := ChartBallPath
Q₀ Q₀ Q` and `α := periodBasisForm X i`, the integrand of `lineIntegral α γ`
equals the chart-coord straight-line integrand. Specifically:

```
α.toFun (γ t) (pathSpeed γ t) = chartFormCoeff Q₀ i (z₀ + t(z-z₀)) · (z - z₀)
```

where `z = (chartAt Q₀) Q`, `z₀ = (chartAt Q₀) Q₀`.

This is the heart of sub-lemma (a) in the docstring above. The proof
uses the chain rule for `pathSpeed`, `trivAt_symmL_one_eq_fderiv_C`,
and ℂ-linearity of `α.toFun`. -/
lemma chartFrame_cancel (Q₀ Q : X) (i : Fin (kirovGenus X)) (t : ℝ)
    (h_target_nbhd : ∀ᶠ s : ℝ in nhds t,
      ((1 - (s : ℂ)) * (chartAt ℂ Q₀) Q₀ + (s : ℂ) * (chartAt ℂ Q₀) Q)
        ∈ (chartAt (H := ℂ) Q₀).target) :
    (periodBasisForm X i).toFun (Jacobians.ChartBallPath Q₀ Q₀ Q t)
        (pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q) t) =
      chartFormCoeff (X := X) Q₀ i
        ((1 - (t : ℂ)) * (chartAt ℂ Q₀) Q₀ + (t : ℂ) * (chartAt ℂ Q₀) Q)
      * ((chartAt ℂ Q₀) Q - (chartAt ℂ Q₀) Q₀) := by
  -- Set up.
  set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀
  set z : ℂ := (chartAt (H := ℂ) Q₀) Q with hz
  set affine : ℝ → ℂ := fun s => (1 - (s : ℂ)) * z₀ + (s : ℂ) * z with haffine
  set γ : ℝ → X := Jacobians.ChartBallPath Q₀ Q₀ Q with hγ
  -- The current-time target membership.
  have h_target_t : affine t ∈ (chartAt (H := ℂ) Q₀).target := h_target_nbhd.self_of_nhds
  -- γ t ∈ chartAt Q₀ source.
  have hγt_source : γ t ∈ (chartAt (H := ℂ) Q₀).source :=
    chartBallPath_mem_source_of_affine Q₀ Q t h_target_t
  -- γ t ∈ chartAt (γ t).source.
  have hγt_self_source : γ t ∈ (chartAt (H := ℂ) (γ t)).source :=
    mem_chart_source ℂ (γ t)
  -- chart Q₀ at γ t = affine t.
  have h_chart_γt : (chartAt (H := ℂ) Q₀) (γ t) = affine t := by
    rw [hγ]
    have h_in_target_at_t : (1 - (t : ℂ)) * (chartAt ℂ Q₀) Q₀ + (t : ℂ) * (chartAt ℂ Q₀) Q
        ∈ (chartAt (H := ℂ) Q₀).target := h_target_t
    -- chart_ChartBallPath_eq: when affine in target, chart of ChartBallPath = affine.
    exact Jacobians.chart_ChartBallPath_eq Q₀ Q₀ Q t h_in_target_at_t
  -- Differentiability of affine at t (always).
  have h_affine_diff : DifferentiableAt ℝ affine t :=
    Jacobians.differentiable_chart_image_formula Q₀ Q₀ Q t
  -- Fderiv of affine at t in direction 1 is `z - z₀`.
  have h_affine_fderiv : fderiv ℝ affine t (1 : ℝ) = z - z₀ := by
    rw [haffine]
    -- affine s = (1 - s) * z₀ + s * z = z₀ + s * (z - z₀)
    have h_eq : (fun s : ℝ => (1 - (s : ℂ)) * z₀ + (s : ℂ) * z) =
        (fun s : ℝ => z₀ + (s : ℂ) * (z - z₀)) := by funext s; ring
    rw [h_eq]
    -- fderiv of (z₀ + s * (z - z₀)) at t in direction 1:
    -- = fderiv (z₀) + fderiv (s * (z-z₀))
    -- = 0 + (z - z₀) * fderiv (s ↦ s)
    -- = (z - z₀) * 1 = (z - z₀).
    have h_id : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h_smul : HasDerivAt (fun s : ℝ => s • (z - z₀)) ((1 : ℝ) • (z - z₀)) t :=
      h_id.smul_const (z - z₀)
    have h_eq2 : (fun s : ℝ => s • (z - z₀)) = (fun s : ℝ => (s : ℂ) * (z - z₀)) := by
      funext s; exact Complex.real_smul
    rw [h_eq2] at h_smul
    have h_one : ((1 : ℝ) • (z - z₀) : ℂ) = z - z₀ := by
      rw [Complex.real_smul]; simp
    rw [h_one] at h_smul
    -- h_smul : HasDerivAt (fun s : ℝ => (s : ℂ) * (z - z₀)) (z - z₀) t
    have h_const : HasDerivAt (fun _ : ℝ => z₀) 0 t := hasDerivAt_const t z₀
    have h_add : HasDerivAt (fun s : ℝ => z₀ + (s : ℂ) * (z - z₀)) (0 + (z - z₀)) t :=
      h_const.add h_smul
    rw [zero_add] at h_add
    -- h_add : HasDerivAt (...) (z - z₀) t.
    -- Convert to HasFDerivAt then take .fderiv.
    have h_fd : HasFDerivAt (fun s : ℝ => z₀ + (s : ℂ) * (z - z₀))
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (z - z₀)) t :=
      h_add.hasFDerivAt
    have h_fderiv_eq := h_fd.fderiv
    rw [h_fderiv_eq]
    -- ContinuousLinearMap.smulRight 1 (z - z₀) applied to 1 = 1 • (z - z₀) = z - z₀
    show ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (z - z₀) (1 : ℝ) = z - z₀
    simp
  -- Chart transition h := (chartAt γt) ∘ (chartAt Q₀).symm.
  set h_trans : ℂ → ℂ := fun w => (chartAt (H := ℂ) (γ t)) ((chartAt (H := ℂ) Q₀).symm w)
    with hh_trans
  -- h_trans is differentiable at (affine t) over ℂ.
  have h_trans_diff_C : DifferentiableAt ℂ h_trans (affine t) := by
    have h_src : (chartAt (H := ℂ) Q₀).symm (affine t) ∈ (chartAt (H := ℂ) (γ t)).source := by
      rw [show (chartAt (H := ℂ) Q₀).symm (affine t) = γ t from ?_]
      · exact hγt_self_source
      · -- γ t = (chartAt Q₀).symm (affine t)
        rw [hγ]
        show Jacobians.ChartBallPath Q₀ Q₀ Q t = _
        rfl
    have h_dC := Jacobians.chart_transition_differentiableAt_C (X := X) Q₀ (γ t) (affine t)
      h_target_t h_src
    -- h_dC : DifferentiableAt ℂ ((chartAt Q₀).symm ≫ₕ (chartAt (γ t))) (affine t)
    -- Express ≫ₕ as plain composition.
    have h_eq_comp : (fun v : ℂ =>
        ((((chartAt (H := ℂ) Q₀).symm ≫ₕ (chartAt (H := ℂ) (γ t))) : ℂ → ℂ)) v) =ᶠ[nhds (affine t)]
        h_trans := by
      have h_open : IsOpen ((chartAt (H := ℂ) Q₀).symm ≫ₕ (chartAt (H := ℂ) (γ t))).source :=
        ((chartAt (H := ℂ) Q₀).symm ≫ₕ (chartAt (H := ℂ) (γ t))).open_source
      have h_mem : affine t ∈ ((chartAt (H := ℂ) Q₀).symm ≫ₕ (chartAt (H := ℂ) (γ t))).source :=
        (Jacobians.chart_trans_source_iff (X := X) Q₀ (γ t) (affine t)).mpr
          ⟨h_target_t, h_src⟩
      filter_upwards [h_open.mem_nhds h_mem] with v _hv
      rfl
    exact h_dC.congr_of_eventuallyEq h_eq_comp
  -- h_trans is differentiable at (affine t) over ℝ (restrict scalars).
  have h_trans_diff_R : DifferentiableAt ℝ h_trans (affine t) :=
    @DifferentiableAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _
      Jacobians.instIsScalarTower_R_C_C
      ℂ _ _ _ Jacobians.instIsScalarTower_R_C_C _ _ h_trans_diff_C
  -- fderiv ℝ h_trans = (fderiv ℂ h_trans).restrictScalars ℝ.
  have h_trans_fderiv_RC : fderiv ℝ h_trans (affine t) =
      (fderiv ℂ h_trans (affine t)).restrictScalars ℝ := by
    have hFD_C : HasFDerivAt h_trans (fderiv ℂ h_trans (affine t)) (affine t) :=
      h_trans_diff_C.hasFDerivAt
    have hFD_R : HasFDerivAt h_trans
        ((fderiv ℂ h_trans (affine t)).restrictScalars ℝ) (affine t) := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hFD_C ⊢
      simp only [ContinuousLinearMap.coe_restrictScalars']
      exact hFD_C
    exact hFD_R.fderiv
  -- Now compute pathSpeed γ t.
  -- pathSpeed γ t = fderiv ℝ (chart γt ∘ γ) t 1.
  -- chart γt ∘ γ is locally (near t) equal to h_trans ∘ affine.
  -- Use h_target_nbhd to get the local equality.
  have h_local_eq : (chartAt (H := ℂ) (γ t)).toFun ∘ γ =ᶠ[nhds t]
      h_trans ∘ affine := by
    filter_upwards [h_target_nbhd] with s hs_target
    -- chart_γt (γ s) = chart_γt ((chartAt Q₀).symm (affine s)) = h_trans (affine s)
    show (chartAt (H := ℂ) (γ t)) (γ s) = h_trans (affine s)
    have h_γs_eq : γ s = (chartAt (H := ℂ) Q₀).symm (affine s) := rfl
    rw [h_γs_eq]
  -- pathSpeed γ t via fderiv.
  have h_pathSpeed : pathSpeed γ t = fderiv ℝ (h_trans ∘ affine) t 1 := by
    show fderiv ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t 1 = _
    rw [Filter.EventuallyEq.fderiv_eq h_local_eq]
  -- Apply chain rule.
  have h_chain : fderiv ℝ (h_trans ∘ affine) t =
      (fderiv ℝ h_trans (affine t)).comp (fderiv ℝ affine t) :=
    fderiv_comp t h_trans_diff_R h_affine_diff
  -- pathSpeed γ t = (fderiv ℝ h_trans (affine t)) (z - z₀).
  have h_pathSpeed_eq : pathSpeed γ t = (fderiv ℝ h_trans (affine t)) (z - z₀) := by
    rw [h_pathSpeed, h_chain, ContinuousLinearMap.comp_apply, h_affine_fderiv]
  -- Replace fderiv ℝ with fderiv ℂ via restrictScalars.
  have h_pathSpeed_C : pathSpeed γ t = (fderiv ℂ h_trans (affine t)) (z - z₀) := by
    rw [h_pathSpeed_eq, h_trans_fderiv_RC, ContinuousLinearMap.coe_restrictScalars']
  -- For a ℂ-linear map ℂ →L[ℂ] ℂ, applying to (z - z₀) = (z - z₀) * applied-to-1.
  have h_fderiv_apply : (fderiv ℂ h_trans (affine t)) (z - z₀) =
      (z - z₀) * (fderiv ℂ h_trans (affine t)) 1 := by
    have := (fderiv ℂ h_trans (affine t)).map_smul (z - z₀) (1 : ℂ)
    -- this : (fderiv ℂ h_trans (affine t)) ((z - z₀) • 1) = (z - z₀) • (fderiv ℂ h_trans (affine t)) 1
    rw [smul_eq_mul, mul_one] at this
    rw [this, smul_eq_mul]
  -- pathSpeed γ t = (z - z₀) * (fderiv ℂ h_trans (affine t) 1).
  have h_pathSpeed_final : pathSpeed γ t = (z - z₀) * (fderiv ℂ h_trans (affine t)) 1 := by
    rw [h_pathSpeed_C, h_fderiv_apply]
  -- chartFormCoeff Q₀ i (affine t) = α.toFun(γt)((trivAt Q₀).symmL ℂ (γt) 1)
  --                                = α.toFun(γt)(fderiv ℂ h_trans (affine t) 1)
  have h_chartFormCoeff : chartFormCoeff (X := X) Q₀ i (affine t) =
      (periodBasisForm X i).toFun (γ t) ((fderiv ℂ h_trans (affine t)) 1) := by
    unfold chartFormCoeff
    show Jacobians.Montel.localRep (periodBasisForm X i) Q₀
        ((chartAt (H := ℂ) Q₀).symm (affine t)) = _
    have h_eq : (chartAt (H := ℂ) Q₀).symm (affine t) = γ t := by
      rw [hγ]
      show _ = Jacobians.ChartBallPath Q₀ Q₀ Q t
      rfl
    rw [h_eq]
    show (periodBasisForm X i).toFun (γ t)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ (γ t) 1) = _
    rw [trivAt_symmL_one_eq_fderiv_C Q₀ (γ t) hγt_source]
    congr 1
    -- Need: fderiv ℂ ((chartAt γt) ∘ (chartAt Q₀).symm) ((chartAt Q₀) (γt)) 1 =
    --       fderiv ℂ h_trans (affine t) 1
    -- (chartAt Q₀)(γt) = affine t (by h_chart_γt).
    -- h_trans = (chartAt γt) ∘ (chartAt Q₀).symm.
    rw [h_chart_γt]
    rfl
  -- Assemble.
  rw [h_chartFormCoeff, h_pathSpeed_final]
  -- Goal: α.toFun(γt) ((z - z₀) * fderiv ℂ h_trans (affine t) 1) =
  --       α.toFun(γt) (fderiv ℂ h_trans (affine t) 1) * (z - z₀)
  -- Use ℂ-linearity of the CLM α.toFun(γt):
  have h_lin : ((periodBasisForm X i).toFun (γ t))
      ((z - z₀) * (fderiv ℂ h_trans (affine t)) 1) =
        (z - z₀) * ((periodBasisForm X i).toFun (γ t))
          ((fderiv ℂ h_trans (affine t)) 1) := by
    have := (periodBasisForm X i).toFun (γ t) |>.map_smul (z - z₀)
      ((fderiv ℂ h_trans (affine t)) 1)
    simp only [smul_eq_mul] at this
    exact this
  rw [h_lin]
  ring

/-- **`Q ∈ (chartAt Q₀).source` eventually in `nhds Q₀`.**

Chart source is open and contains `Q₀`. -/
lemma Q_in_chart_source_eventually (Q₀ : X) :
    ∀ᶠ Q in nhds Q₀, Q ∈ (chartAt (H := ℂ) Q₀).source := by
  exact (chartAt (H := ℂ) Q₀).open_source.mem_nhds (mem_chart_source ℂ Q₀)

/-- **Affine path stays in chart target near Q₀.** Trivially, near Q₀
(where `Q = Q₀`), `affine s = z₀` is in the chart target. We need the
target-membership uniform in `s ∈ Icc 0 1`, for a chart-ball
neighborhood of Q₀. -/
lemma affine_in_target_eventually (Q₀ : X) :
    ∀ᶠ Q in nhds Q₀, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target := by
  -- Pick a chart ball `Metric.ball z₀ r ⊆ (chartAt Q₀).target`.
  set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀
  have h_open := (chartAt (H := ℂ) Q₀).open_target
  have h_src : Q₀ ∈ (chartAt (H := ℂ) Q₀).source := mem_chart_source ℂ Q₀
  have h_mem : z₀ ∈ (chartAt (H := ℂ) Q₀).target :=
    (chartAt (H := ℂ) Q₀).map_source h_src
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp h_open _ h_mem
  -- The set V := {Q | (chartAt Q₀) Q ∈ Metric.ball z₀ r} ∩ (chartAt Q₀).source
  -- is open and contains Q₀.
  -- For Q ∈ V, the convex hull of {z₀, (chartAt Q₀) Q} ⊆ Metric.ball z₀ r ⊆ target.
  have h_chart_cont : ContinuousAt (chartAt (H := ℂ) Q₀) Q₀ :=
    (chartAt (H := ℂ) Q₀).continuousAt h_src
  -- The preimage of `Metric.ball z₀ r` under chartAt Q₀ is open in X at Q₀.
  have h_preimage : ∀ᶠ Q in nhds Q₀, (chartAt (H := ℂ) Q₀) Q ∈ Metric.ball z₀ r :=
    h_chart_cont.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))
  filter_upwards [h_preimage] with Q hQ_in_ball s hs
  -- Convex combination of z₀ (= chart Q₀) and (chart Q) lies in ball z₀ r.
  have hz₀_mem : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr_pos
  have hz_mem : (chartAt (H := ℂ) Q₀) Q ∈ Metric.ball z₀ r := hQ_in_ball
  have hconv : Convex ℝ (Metric.ball z₀ r) := convex_ball _ _
  have h_combine := hconv hz₀_mem hz_mem (a := 1 - s) (b := s)
    (by linarith [hs.1, hs.2]) (by linarith [hs.1, hs.2]) (by linarith)
  -- Convert real-smul to complex-mul.
  have h_eq : ((1 - s : ℝ) • z₀ + s • (chartAt (H := ℂ) Q₀) Q : ℂ) =
      (1 - (s : ℂ)) * z₀ + (s : ℂ) * (chartAt (H := ℂ) Q₀) Q := by
    rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
  rw [h_eq] at h_combine
  exact hr_subset h_combine

/-- **localLift via lineIntegral(ChartBallPath).** Using `chartFrame_cancel`,
we identify `localLift Q₀ c Q` with `c + periodVec(ChartBallPath Q₀ Q₀ Q)`
componentwise, provided the affine path stays in chart target on `[0,1]`.

This is sub-lemma (a) in the docstring above. -/
lemma localLift_eq_const_add_periodVec_ChartBallPath
    (Q₀ Q : X) (c : Fin (kirovGenus X) → ℂ)
    (h_target_Icc : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    localLift (X := X) Q₀ c Q =
      c + Jacobians.periodVec (Jacobians.ChartBallPath Q₀ Q₀ Q) := by
  funext i
  show localLiftChart (X := X) Q₀ c i ((chartAt (H := ℂ) Q₀) Q) = _
  unfold localLiftChart
  set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀
  set z : ℂ := (chartAt (H := ℂ) Q₀) Q with hz
  -- Apply chartFrame_cancel pointwise on [0, 1].
  -- The affine path stays in target on Icc 0 1; extend to nbhd by openness.
  have h_target_nbhd_at : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᶠ (s : ℝ) in nhds t,
        ((1 - (s : ℂ)) * z₀ + (s : ℂ) * z) ∈ (chartAt (H := ℂ) Q₀).target := by
    intro t ht
    -- The set `{s | affine s ∈ target}` is open (preimage of open under continuous).
    have h_cont : Continuous (fun s : ℝ => (1 - (s : ℂ)) * z₀ + (s : ℂ) * z) := by
      refine Continuous.add ?_ ?_
      · exact (continuous_const.sub Complex.continuous_ofReal).mul continuous_const
      · exact Complex.continuous_ofReal.mul continuous_const
    have h_open_set : IsOpen
        {s : ℝ | (1 - (s : ℂ)) * z₀ + (s : ℂ) * z ∈ (chartAt (H := ℂ) Q₀).target} := by
      have := (chartAt (H := ℂ) Q₀).open_target.preimage h_cont
      exact this
    have h_t_mem : t ∈ {s : ℝ | (1 - (s : ℂ)) * z₀ + (s : ℂ) * z ∈
        (chartAt (H := ℂ) Q₀).target} := h_target_Icc t ht
    exact h_open_set.mem_nhds h_t_mem
  -- Pointwise: chart-coord integrand = path integrand on Icc 0 1.
  have h_pointwise : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      chartFormCoeff (X := X) Q₀ i ((1 - (t : ℂ)) * z₀ + (t : ℂ) * z) * (z - z₀) =
        (periodBasisForm X i).toFun (Jacobians.ChartBallPath Q₀ Q₀ Q t)
          (pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q) t) := by
    intro t ht
    exact (chartFrame_cancel (X := X) Q₀ Q i t (h_target_nbhd_at t ht)).symm
  -- Use intervalIntegral.integral_congr to lift pointwise eq to integral eq.
  have h_int_eq : ∫ t in (0 : ℝ)..1,
        chartFormCoeff (X := X) Q₀ i ((1 - (t : ℂ)) * z₀ + (t : ℂ) * z) * (z - z₀) =
      ∫ t in (0 : ℝ)..1,
        (periodBasisForm X i).toFun (Jacobians.ChartBallPath Q₀ Q₀ Q t)
          (pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q) t) := by
    refine intervalIntegral.integral_congr ?_
    -- uIcc 0 1 = Icc 0 1 since 0 ≤ 1.
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact h_pointwise
  -- Conclude.
  show c i + ∫ t in (0 : ℝ)..1,
      chartFormCoeff (X := X) Q₀ i (z₀ + (t : ℂ) * (z - z₀)) * (z - z₀) =
    c i + Jacobians.periodVec (Jacobians.ChartBallPath Q₀ Q₀ Q) i
  -- Step 1: rewrite (z₀ + t(z - z₀)) = (1 - t)·z₀ + t·z
  have h_rewrite : (fun t : ℝ =>
      chartFormCoeff (X := X) Q₀ i (z₀ + (t : ℂ) * (z - z₀)) * (z - z₀)) =
      fun t : ℝ =>
        chartFormCoeff (X := X) Q₀ i ((1 - (t : ℂ)) * z₀ + (t : ℂ) * z) * (z - z₀) := by
    funext t
    have : z₀ + (t : ℂ) * (z - z₀) = (1 - (t : ℂ)) * z₀ + (t : ℂ) * z := by ring
    rw [this]
  rw [h_rewrite, h_int_eq]
  -- Step 2: periodVec γ i = lineIntegral (periodBasisForm X i) γ.
  rfl

/-- **PathSpeed chain rule for smoothStep01 reparameterization.**

For a smooth path `γ : ℝ → X` and `σ := smoothStep01`, the pathSpeed
of `γ ∘ σ` at `t` equals `σ'(t) • pathSpeed γ (σ t)` via the chain
rule applied to `(chartAt (γ(σ t))).toFun ∘ γ ∘ σ`.

Requires:
* `γ` chart-pullback differentiable at `σ t` (i.e., the existing
  `pathSpeed γ (σ t)` is computed from a `HasDerivAt`).
-/
lemma pathSpeed_smoothStep01_comp_eq (γ : ℝ → X) (t : ℝ)
    (hγ_diff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (γ (Jacobians.smoothStep01 t))).toFun ∘ γ)
      (Jacobians.smoothStep01 t)) :
    Jacobians.pathSpeed (γ ∘ Jacobians.smoothStep01) t =
      (Jacobians.smoothStep01_deriv t : ℂ) *
        Jacobians.pathSpeed γ (Jacobians.smoothStep01 t) := by
  unfold Jacobians.pathSpeed
  have h_assoc : (chartAt (H := ℂ) ((γ ∘ Jacobians.smoothStep01) t)).toFun ∘
        (γ ∘ Jacobians.smoothStep01) =
      ((chartAt (H := ℂ) (γ (Jacobians.smoothStep01 t))).toFun ∘ γ) ∘
        Jacobians.smoothStep01 := by
    funext s; rfl
  rw [h_assoc]
  have hσ : HasDerivAt Jacobians.smoothStep01 (Jacobians.smoothStep01_deriv t) t :=
    Jacobians.smoothStep01_hasDerivAt_explicit t
  have hφ : HasDerivAt
      ((chartAt (H := ℂ) (γ (Jacobians.smoothStep01 t))).toFun ∘ γ)
      (Jacobians.pathSpeed γ (Jacobians.smoothStep01 t))
      (Jacobians.smoothStep01 t) := hγ_diff.hasDerivAt
  have h_comp : HasDerivAt
      (((chartAt (H := ℂ) (γ (Jacobians.smoothStep01 t))).toFun ∘ γ) ∘
        Jacobians.smoothStep01)
      (Jacobians.smoothStep01_deriv t • Jacobians.pathSpeed γ (Jacobians.smoothStep01 t))
      t := HasDerivAt.scomp t hφ hσ
  have h_deriv : deriv (((chartAt (H := ℂ) (γ (Jacobians.smoothStep01 t))).toFun ∘ γ) ∘
        Jacobians.smoothStep01) t =
      Jacobians.smoothStep01_deriv t • Jacobians.pathSpeed γ (Jacobians.smoothStep01 t) :=
    h_comp.deriv
  have h_lhs_eq : (fderiv ℝ
      (((chartAt (H := ℂ) (γ (Jacobians.smoothStep01 t))).toFun ∘ γ) ∘
        Jacobians.smoothStep01) t) 1 =
      Jacobians.smoothStep01_deriv t • Jacobians.pathSpeed γ (Jacobians.smoothStep01 t) := by
    rw [← h_deriv]; rfl
  rw [h_lhs_eq]
  exact Complex.real_smul

/-- **IsSmoothPath for ChartBallPathSmooth (smoothstep-reparameterized).**

This variant uses `smoothStep01` reparameterization so that derivatives
at boundary points are zero — which is what's needed for the eventual
concat-smoothness argument. The `start`, `finish`, `cont`, `diff`
fields are PROVEN via the building blocks in `Jacobians/SmoothPath.lean`;
the `integrable` field is closed via `pathSpeed_smoothStep01_comp_eq` +
chartFrame_cancel + ContinuousOn argument. -/
lemma isSmoothPath_ChartBallPathSmooth (Q₀ Q : X)
    (hQ_src : Q ∈ (chartAt (H := ℂ) Q₀).source)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.IsSmoothPath Q₀ Q (Jacobians.ChartBallPathSmooth Q₀ Q) := by
  have hQ₀_src : Q₀ ∈ (chartAt (H := ℂ) Q₀).source := mem_chart_source ℂ Q₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Jacobians.ChartBallPathSmooth.start Q₀ Q hQ₀_src
  · exact Jacobians.ChartBallPathSmooth.finish Q₀ Q hQ_src
  · exact Jacobians.ChartBallPathSmooth.continuous Q₀ Q h_chart_ball
  · intro t _
    exact Jacobians.ChartBallPathSmooth_chart_at_self_differentiableAt Q₀ Q t h_chart_ball
  · -- velCont: ChartBallPathSmooth = (chartAt Q₀).symm ∘ β with β the base ℂ-path; apply
    -- `velCont_compOn` (g = chart symm, C^ω on the open chart target) to the base path's velCont.
    set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀_def
    set z : ℂ := (chartAt (H := ℂ) Q₀) Q with hz_def
    set β : ℝ → ℂ := fun t : ℝ =>
      (1 - (Jacobians.smoothStep01 t : ℂ)) * z₀ + (Jacobians.smoothStep01 t : ℂ) * z with hβ_def
    -- β is continuous and `ContDiff`-enough that `deriv β` is continuous.
    have hβcont : Continuous β := by
      refine Continuous.add ?_ ?_
      · exact (continuous_const.sub
          (Complex.continuous_ofReal.comp Jacobians.smoothStep01_continuous)).mul continuous_const
      · exact (Complex.continuous_ofReal.comp Jacobians.smoothStep01_continuous).mul continuous_const
    have hβderiv_eq : deriv β = fun t : ℝ => (Jacobians.smoothStep01_deriv t : ℂ) * (z - z₀) := by
      funext t
      have hσ : HasDerivAt (fun s : ℝ => (Jacobians.smoothStep01 s : ℂ))
          (Jacobians.smoothStep01_deriv t : ℂ) t :=
        (Jacobians.smoothStep01_hasDerivAt_explicit t).ofReal_comp
      have hβhd : HasDerivAt β ((Jacobians.smoothStep01_deriv t : ℂ) * (z - z₀)) t := by
        have h1 : HasDerivAt (fun s : ℝ => (1 - (Jacobians.smoothStep01 s : ℂ)) * z₀)
            (-(Jacobians.smoothStep01_deriv t : ℂ) * z₀) t := by
          simpa using (hσ.const_sub 1).mul_const z₀
        have h2 : HasDerivAt (fun s : ℝ => (Jacobians.smoothStep01 s : ℂ) * z)
            ((Jacobians.smoothStep01_deriv t : ℂ) * z) t := hσ.mul_const z
        have hsum := h1.add h2
        convert hsum using 1
        ring
      exact hβhd.deriv
    have hβ' : Continuous (deriv β) := by
      rw [hβderiv_eq]
      exact (Complex.continuous_ofReal.comp Jacobians.smoothStep01_deriv_continuous).mul
        continuous_const
    -- base velocity-section continuity (model space ℂ).
    have hβvel := velCont_modelPath β hβcont hβ'
    -- chart-symm is `C^ω` on the open chart target; β maps `Icc 0 1` into it.
    have hVo : IsOpen (chartAt (H := ℂ) Q₀).target := (chartAt (H := ℂ) Q₀).open_target
    have hg : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (fun w : ℂ => (chartAt (H := ℂ) Q₀).symm w)
        (chartAt (H := ℂ) Q₀).target := Jacobians.chartAt_symm_contMDiffOn Q₀
    have hβV : ∀ s ∈ Set.Icc (0 : ℝ) 1, β s ∈ (chartAt (H := ℂ) Q₀).target := by
      intro s hs
      have hs_Icc : Jacobians.smoothStep01 s ∈ Set.Icc (0 : ℝ) 1 :=
        Jacobians.smoothStep01_mem_unit s
      exact h_chart_ball (Jacobians.smoothStep01 s) hs_Icc
    have hβdiff : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        DifferentiableAt ℝ ((chartAt (H := ℂ) (β s)).toFun ∘ β) s := by
      intro s _
      -- For the model space ℂ the chart is the identity, so this is `DifferentiableAt ℝ β s`.
      have hd : DifferentiableAt ℝ β s :=
        ((differentiableAt_const _).sub
          (Complex.ofRealCLM.differentiableAt.comp s (Jacobians.smoothStep01_differentiable s))
            |>.mul (differentiableAt_const _)).add
          ((Complex.ofRealCLM.differentiableAt.comp s (Jacobians.smoothStep01_differentiable s))
            |>.mul (differentiableAt_const _))
      exact hd
    have hcompOn := velCont_compOn (fun w : ℂ => (chartAt (H := ℂ) Q₀).symm w) hg hVo β hβV
      hβcont hβdiff hβvel
    -- `g ∘ β = ChartBallPathSmooth Q₀ Q` definitionally.
    exact hcompOn

end Jacobians.OfCurveSkeleton
