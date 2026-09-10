/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.LineIntegral
import KirovDolbeault.Genus

/-!
# Cotangent-bundle coefficient continuity (the *local* coefficient is the right object)

A `HolomorphicOneForms X` is a `ContMDiffSection` of the cotangent hom-bundle
`x ↦ TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ`. To integrate a form along a path one needs control of
its coefficient. The naive "global coefficient" `x ↦ α.toFun x (1 : TangentSpace 𝓘(ℂ) x)`
is **discontinuous** in general: `1 : TangentSpace 𝓘(ℂ) x` is the `∂/∂z` of the *preferred
chart at `x`*, and since the chart varies with `x` and chart transitions are general
biholomorphisms (derivatives ≠ 1), the constant-`1` tangent section is not continuous (it is
continuous iff the tangent bundle is trivialized by the atlas, i.e. parallelizable — false for
kirovGenus ≥ 2). Pairing it with a form nonzero at a point gives a discontinuous map. The
obstruction is isolated below (`const_one_section_continuous_of_coordChange_fixes_one`,
`target_eq_inCoordinates_of_w`).

The **correct, provable** object is the coefficient read in a *fixed* chart/trivialization
(`continuousAt_inCoordinates`, `continuousAt_localCoeff`). This is the tool a chart-patchwork
needs to integrate `α.toFun (γ s) (pathSpeed γ s)` along a (chart-pointwise-differentiable)
path: on a segment where `γ` stays in one chart, the integrand is the (continuous, bounded)
fixed-chart coefficient times the (integrable) fixed-chart velocity. It is also the
continuity input that `traceForm_comp` needs.

Derived via `contMDiffAt_hom_bundle` (Mathlib): the section's smoothness gives that its
`ContinuousLinearMap.inCoordinates` representation is continuous *into the fixed normed space*
`ℂ →L[ℂ] ℂ`. (Found 2026-05-30; corrects the earlier false "global coefficient" target.)
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology
open Filter Set MeasureTheory

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **The continuous local object.** Near `x₀`, the coordinate of the section `α` in the FIXED
hom-bundle trivialization at `x₀` is continuous (indeed it is `ContMDiffAt`) as a map into the
fixed normed space `ℂ →L[ℂ] ℂ`. This is `inCoordinates (α x)`. -/
theorem continuousAt_inCoordinates (α : HolomorphicOneForms X) (x₀ : X) :
    ContinuousAt (fun x : X => ContinuousLinearMap.inCoordinates ℂ
      (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ) x₀ x x₀ x (α.toFun x)) x₀ := by
  have hα := α.contMDiff_toFun x₀
  rw [contMDiffAt_hom_bundle] at hα
  exact hα.2.continuousAt

/-- **The local coefficient is continuous.** `x ↦ inCoordinates (α x) 1` (the coefficient of
`α` read in the FIXED chart at `x₀`, i.e. `α` paired with the *coordinate vector field of the
chart at `x₀`*) is continuous at `x₀`. NOTE this is `inCoordinates (α x) 1`, **not** the
discontinuous `α x 1`. -/
theorem continuousAt_localCoeff (α : HolomorphicOneForms X) (x₀ : X) :
    ContinuousAt (fun x : X => ContinuousLinearMap.inCoordinates ℂ
      (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ) x₀ x x₀ x (α.toFun x) (1 : ℂ)) x₀ :=
  (continuousAt_inCoordinates α x₀).clm_apply continuousAt_const

/-- **The obstruction, isolated.** Continuity of the constant-`1` tangent section is implied by
(in fact equivalent to, via `FiberBundleCore.continuous_const_section`) the constant `1 : ℂ`
being invariant under EVERY chart-transition derivative, `coordChange i j x 1 = 1`. That
hypothesis is false for a complex 1-manifold with non-trivial tangent bundle (kirovGenus ≥ 2):
chart transitions are general biholomorphisms whose derivatives do not fix `1`. Hence the
constant-`1` section is discontinuous, and `x ↦ α x (1 : TangentSpace x)` is discontinuous. -/
theorem const_one_section_continuous_of_coordChange_fixes_one
    (h : ∀ (i j : atlas ℂ X) (x : X),
        x ∈ (tangentBundleCore 𝓘(ℂ) X).toFiberBundleCore.baseSet i ∩
            (tangentBundleCore 𝓘(ℂ) X).toFiberBundleCore.baseSet j →
        (tangentBundleCore 𝓘(ℂ) X).toFiberBundleCore.coordChange i j x 1 = 1) :
    Continuous (fun x : X => (Bundle.TotalSpace.mk' ℂ
        (E := fun (x : X) => TangentSpace 𝓘(ℂ) x) x ((1 : ℂ) : TangentSpace 𝓘(ℂ) x))) :=
  (tangentBundleCore 𝓘(ℂ) X).toFiberBundleCore.continuous_const_section 1 h

/-- **Why the global target differs from the continuous local coefficient.** Near `x₀`,
`α x (1 : TangentSpace x)` equals `inCoordinates (α x)` applied to the input
`continuousLinearMapAt (triv x₀) x 1`. The operator `inCoordinates (α x)` is continuous
(`continuousAt_inCoordinates`), but the INPUT is the constant-`1` tangent-section coordinate,
which is discontinuous (see the obstruction). So the global target is a continuous operator
times a discontinuous input — discontinuous. -/
theorem target_eq_inCoordinates_of_w (α : HolomorphicOneForms X) (x₀ x : X)
    (hx : x ∈ (chartAt ℂ x₀).source) :
    α.toFun x ((1 : ℂ) : TangentSpace 𝓘(ℂ) x) =
      ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ)
        x₀ x x₀ x (α.toFun x)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).continuousLinearMapAt ℂ x (1 : ℂ)) := by
  have hxbase : x ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hxbase]

/-- **General-vector form of `target_eq_inCoordinates_of_w`.** For any tangent vector `v` at
`x ∈ (chartAt ℂ x₀).source`, applying the form equals applying its fixed-`x₀`-trivialization
`inCoordinates` representation to `v` read in that trivialization. (The `v = 1` case is the
obstruction lemma `target_eq_inCoordinates_of_w`; this general version is what lets a
chart-patchwork rewrite the line-integral integrand `α.toFun (γ s) (pathSpeed γ s)` into a
product of the continuous local coefficient and the trivialized velocity.) -/
theorem apply_eq_inCoordinates (α : HolomorphicOneForms X) (x₀ x : X)
    (hx : x ∈ (chartAt ℂ x₀).source) (v : TangentSpace 𝓘(ℂ) x) :
    α.toFun x v =
      ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ)
        x₀ x x₀ x (α.toFun x)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).continuousLinearMapAt ℂ x v) := by
  have hxbase : x ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hxbase]

/-! ## The justification lemma: continuous velocity ⇒ integrable integrand

This is what makes the genuinely-`C¹` loop predicate sound: if the **velocity tangent
section** `s ↦ ⟨γ s, pathSpeed γ s⟩` is continuous on `[0,1]`, then the line-integral
integrand `α.toFun (γ s) (pathSpeed γ s)` is continuous (hence interval-integrable) — for
*every* form `α`. The proof pairs the (continuous, fixed-chart) `inCoordinates` operator
`continuousAt_inCoordinates` with the trivialized velocity (continuous since the velocity
section is, and the trivialization is continuous), via `apply_eq_inCoordinates`. Crucially the
hypothesis is the *geometric* velocity-section continuity, NOT continuity of the bare number
`pathSpeed γ` (which would still leave the discontinuous coefficient `α.toFun · 1`). -/

/-- Continuous velocity tangent-section ⇒ the form integrand is `ContinuousOn [0,1]`. -/
theorem continuousOn_form_pathSpeed (α : HolomorphicOneForms X) (γ : ℝ → X)
    (hvel : ContinuousOn (fun s : ℝ =>
        (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s)))
      (Set.Icc 0 1)) :
    ContinuousOn (fun s : ℝ => α.toFun (γ s) (pathSpeed γ s)) (Set.Icc 0 1) := by
  have hγ : ContinuousOn γ (Set.Icc (0 : ℝ) 1) :=
    (FiberBundle.continuous_proj ℂ (TangentSpace 𝓘(ℂ) (M := X))).comp_continuousOn hvel
  intro s₀ hs₀
  set x₀ := γ s₀ with hx₀
  set triv := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀ with htriv
  set vel : ℝ → Bundle.TotalSpace ℂ (TangentSpace 𝓘(ℂ) (M := X)) :=
    fun s => Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s)
      (pathSpeed γ s) with hvel_def
  have hx₀src : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have hev_src : ∀ᶠ s in 𝓝[Set.Icc (0 : ℝ) 1] s₀, γ s ∈ (chartAt ℂ x₀).source :=
    (hγ s₀ hs₀).eventually ((chartAt ℂ x₀).open_source.mem_nhds hx₀src)
  have hO : ContinuousWithinAt (fun s : ℝ => ContinuousLinearMap.inCoordinates ℂ
      (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ) x₀ (γ s) x₀ (γ s)
      (α.toFun (γ s))) (Set.Icc 0 1) s₀ :=
    (continuousAt_inCoordinates α x₀).comp_continuousWithinAt (hγ s₀ hs₀)
  have hV : ContinuousWithinAt (fun s : ℝ =>
      triv.continuousLinearMapAt ℂ (γ s) (pathSpeed γ s)) (Set.Icc 0 1) s₀ := by
    have hx₀base : x₀ ∈ triv.baseSet := mem_baseSet_trivializationAt ℂ _ x₀
    have hmem_src : vel s₀ ∈ triv.source := triv.mem_source.mpr hx₀base
    have htrivCA : ContinuousAt triv (vel s₀) :=
      triv.continuousOn.continuousAt (triv.open_source.mem_nhds hmem_src)
    have hcomp : ContinuousWithinAt (fun s : ℝ => (triv (vel s)).2) (Set.Icc 0 1) s₀ :=
      (continuous_snd.continuousAt.comp_continuousWithinAt
        (htrivCA.comp_continuousWithinAt (hvel s₀ hs₀)))
    refine hcomp.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hev_src] with s hs
      have hsbase : γ s ∈ triv.baseSet := by
        rw [htriv, TangentBundle.trivializationAt_baseSet]; exact hs
      exact triv.continuousLinearMapAt_apply_of_mem ℂ hsbase (pathSpeed γ s)
    · exact triv.continuousLinearMapAt_apply_of_mem ℂ hx₀base (pathSpeed γ s₀)
  have hpair : ContinuousWithinAt (fun s : ℝ =>
      (ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ)
        x₀ (γ s) x₀ (γ s) (α.toFun (γ s)))
      (triv.continuousLinearMapAt ℂ (γ s) (pathSpeed γ s))) (Set.Icc 0 1) s₀ :=
    hO.clm_apply hV
  refine hpair.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hev_src] with s hs
    exact apply_eq_inCoordinates α x₀ (γ s) hs (pathSpeed γ s)
  · exact apply_eq_inCoordinates α x₀ (γ s₀) hx₀src (pathSpeed γ s₀)

/-- Continuous velocity tangent-section ⇒ the form integrand is interval-integrable on `[0,1]`.
**The justification for the genuinely-`C¹` loop predicate**: the `integrable` field follows from
the velocity-continuity (`velCont`) field. -/
theorem intervalIntegrable_form_pathSpeed_of_velContinuous (α : HolomorphicOneForms X) (γ : ℝ → X)
    (hvel : ContinuousOn (fun s : ℝ =>
        (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s)))
      (Set.Icc 0 1)) :
    IntervalIntegrable (fun s : ℝ => α.toFun (γ s) (pathSpeed γ s)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact continuousOn_form_pathSpeed α γ hvel

/-! ## Velocity-section continuity is preserved by smooth composition

The constructor-side tools for the C¹ refactor. `velCont_comp` handles `IsClosedSmoothLoop.comp`
(`f∘γ`, global `f`); `velCont_compOn` handles the §3 lift `g∘δr` (local section `g`, `C^ω` on an
open `V`) and the `ChartBall` base case (via `chartAt _).symm`). **Both require, beyond velocity
continuity `hγ`, the pointwise `hγdiff` and `hγcont` fields** — these are NOT implied by `hγ`
(`pathSpeed` uses the junk-value convention, so a nowhere-differentiable continuous curve has a
continuous velocity section), which is exactly why the refactor *keeps* the `cont`/`diff` fields and
only replaces `integrable` with `velCont`. -/

omit [CompactSpace X] in
/-- Local analogue of `pathSpeed_comp_eq_mfderiv`: only `MDifferentiableAt f (γ t)` is needed (the
global `ContMDiff f` in the original is used solely to produce this), so it applies to local sections.
The source `X` need NOT be compact (used with `X = ℂ` in the `ChartBall` base case). -/
theorem pathSpeed_comp_eq_mfderiv_of_mdiff (f : X → Y) (γ : ℝ → X) (t : ℝ)
    (hf_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (γ t))
    (hγ_cont : ContinuousAt γ t)
    (hγ_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) :
    pathSpeed (f ∘ γ) t = mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t) (pathSpeed γ t) := by
  set φ_X := chartAt (H := ℂ) (γ t) with hφ_X_def
  set φ_Y := chartAt (H := ℂ) (f (γ t)) with hφ_Y_def
  set f_loc : ℂ → ℂ := fun z => φ_Y (f (φ_X.symm z)) with hf_loc_def
  set g_X : ℝ → ℂ := φ_X.toFun ∘ γ with hg_X_def
  set g_Y : ℝ → ℂ := φ_Y.toFun ∘ (f ∘ γ) with hg_Y_def
  have hγt_X : γ t ∈ φ_X.source := mem_chart_source ℂ (γ t)
  have hfγt_Y : f (γ t) ∈ φ_Y.source := mem_chart_source ℂ (f (γ t))
  have hγ_source : ∀ᶠ s in 𝓝 t, γ s ∈ φ_X.source :=
    hγ_cont.eventually (φ_X.open_source.mem_nhds hγt_X)
  have h_eq : g_Y =ᶠ[𝓝 t] f_loc ∘ g_X := by
    filter_upwards [hγ_source] with s hs
    simp only [hg_Y_def, hf_loc_def, hg_X_def, Function.comp_apply]
    congr 2
    exact (φ_X.left_inv hs).symm
  have hf_loc_diff_ℂ : DifferentiableAt ℂ f_loc (g_X t) := by
    have h1 := hf_mdiff.differentiableWithinAt_writtenInExtChartAt
    rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
    convert h1 using 2
  have hf_loc_hasFD_ℂ : HasFDerivAt f_loc (fderiv ℂ f_loc (g_X t)) (g_X t) :=
    hf_loc_diff_ℂ.hasFDerivAt
  have hf_loc_hasFD_ℝ : HasFDerivAt f_loc
      ((fderiv ℂ f_loc (g_X t)).restrictScalars ℝ) (g_X t) := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hf_loc_hasFD_ℂ ⊢
    simp only [ContinuousLinearMap.coe_restrictScalars']
    exact hf_loc_hasFD_ℂ
  have hf_loc_diff_ℝ : DifferentiableAt ℝ f_loc (g_X t) :=
    hf_loc_hasFD_ℝ.differentiableAt
  have hf_loc_fderiv_ℝ : fderiv ℝ f_loc (g_X t) =
      (fderiv ℂ f_loc (g_X t)).restrictScalars ℝ :=
    hf_loc_hasFD_ℝ.fderiv
  have h_chain : fderiv ℝ (f_loc ∘ g_X) t =
      (fderiv ℝ f_loc (g_X t)).comp (fderiv ℝ g_X t) :=
    fderiv_comp t hf_loc_diff_ℝ hγ_diff
  have h_mfderiv : mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t) = fderiv ℂ f_loc (g_X t) := by
    rw [hf_mdiff.mfderiv]
    rw [ModelWithCorners.range_eq_univ, fderivWithin_univ]
    congr 1
  show pathSpeed (f ∘ γ) t = mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t) (pathSpeed γ t)
  rw [h_mfderiv]
  show fderiv ℝ ((chartAt (H := ℂ) ((f ∘ γ) t)).toFun ∘ (f ∘ γ)) t 1 =
    fderiv ℂ f_loc (g_X t) (pathSpeed γ t)
  have h_gY : (chartAt (H := ℂ) ((f ∘ γ) t)).toFun ∘ (f ∘ γ) = g_Y := rfl
  rw [h_gY, h_eq.fderiv_eq, h_chain, ContinuousLinearMap.comp_apply,
      hf_loc_fderiv_ℝ, ContinuousLinearMap.coe_restrictScalars']
  rfl

/-- **GLOBAL: velocity-section continuity is preserved by a global `C^ω` map.** For the
`IsClosedSmoothLoop.comp` constructor. Identifies velocity-section(`f∘γ`) with `tangentMap f`
applied to velocity-section(`γ`) (pointwise via `pathSpeed_comp_eq_mfderiv`), then composes with the
continuous `tangentMap f`. -/
theorem velCont_comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (γ : ℝ → X)
    (hγcont : Continuous γ)
    (hγdiff : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ s)).toFun ∘ γ) s)
    (hγ : ContinuousOn (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s))) (Set.Icc 0 1)) :
    ContinuousOn (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := Y)) (f (γ s)) (pathSpeed (f ∘ γ) s))) (Set.Icc 0 1) := by
  have hcont_tm : Continuous (tangentMap 𝓘(ℂ) 𝓘(ℂ) f) :=
    hf.continuous_tangentMap (by decide : (1 : WithTop ℕ∞) ≤ ω)
  have hcomp : ContinuousOn ((tangentMap 𝓘(ℂ) 𝓘(ℂ) f) ∘
      (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
        (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s)))) (Set.Icc 0 1) :=
    hcont_tm.comp_continuousOn hγ
  refine hcomp.congr ?_
  intro s hs
  simp only [Function.comp_apply, tangentMap, Bundle.TotalSpace.mk']
  congr 1
  exact pathSpeed_comp_eq_mfderiv f hf γ s hγcont.continuousAt (hγdiff s hs)

omit [CompactSpace Y] in
/-- **LOCAL: velocity-section continuity is preserved by a map `C^ω` on an open set.** For the §3
lift `g∘γ` (`g` a local section) and the `ChartBall` base case. Open `V` upgrades `ContMDiffOn` to
`ContMDiffAt`/`MDifferentiableAt`, so `pathSpeed_comp_eq_mfderiv_of_mdiff` applies, and
`tangentMapWithin g V = tangentMap g` on `V`. The source `Y` need NOT be compact (the `ChartBall`
base case takes `Y = ℂ`, the non-compact model space). -/
theorem velCont_compOn (g : Y → X) {V : Set Y} (hg : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g V)
    (hVo : IsOpen V) (γ : ℝ → Y) (hγV : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ V)
    (hγcont : Continuous γ)
    (hγdiff : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ s)).toFun ∘ γ) s)
    (hγ : ContinuousOn (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := Y)) (γ s) (pathSpeed γ s))) (Set.Icc 0 1)) :
    ContinuousOn (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := X)) (g (γ s)) (pathSpeed (g ∘ γ) s))) (Set.Icc 0 1) := by
  have htmw : ContinuousOn (tangentMapWithin 𝓘(ℂ) 𝓘(ℂ) g V) (Bundle.TotalSpace.proj ⁻¹' V) :=
    hg.continuousOn_tangentMapWithin (by decide : (1 : WithTop ℕ∞) ≤ ω) hVo.uniqueMDiffOn
  have hmaps : Set.MapsTo (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := Y)) (γ s) (pathSpeed γ s)))
      (Set.Icc 0 1) (Bundle.TotalSpace.proj ⁻¹' V) := fun s hs => hγV s hs
  have hcomp : ContinuousOn ((tangentMapWithin 𝓘(ℂ) 𝓘(ℂ) g V) ∘
      (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
        (E := TangentSpace 𝓘(ℂ) (M := Y)) (γ s) (pathSpeed γ s)))) (Set.Icc 0 1) :=
    htmw.comp hγ hmaps
  refine hcomp.congr ?_
  intro s hs
  have hgmdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (γ s) :=
    (hg.contMDiffAt (hVo.mem_nhds (hγV s hs))).mdifferentiableAt (by decide : ω ≠ 0)
  rw [Function.comp_apply, tangentMapWithin_eq_tangentMap (hVo.uniqueMDiffWithinAt (hγV s hs)) hgmdiff]
  simp only [tangentMap, Bundle.TotalSpace.mk']
  congr 1
  exact pathSpeed_comp_eq_mfderiv_of_mdiff g γ s hgmdiff hγcont.continuousAt (hγdiff s hs)

/-! ## Velocity-section continuity under PRE-composition (reverse) and piecewise gluing (concat)

These are the constructor-side tools for the `IsClosedSmoothLoop.reverse`/`IsSmoothPath.reverse`
and `IsSmoothPath.concat` constructors. Unlike `velCont_comp`/`velCont_compOn` (post-composition
by a manifold map, handled by `tangentMap`), these are reparametrizations / piecewise glues, so
they need a direct trivialization argument via `FiberBundle.continuousWithinAt_totalSpace` (which
reduces total-space continuity to: base proj continuous + the trivialized fibre component
`(trivializationAt _ _ (base x₀) (f x)).2` continuous). -/

/-- **Velocity-section continuity is preserved by time-reversal.** For the
`IsClosedSmoothLoop.reverse`/`IsSmoothPath.reverse` constructors. The reversed velocity section is
`s ↦ ⟨γ(1-s), -pathSpeed γ(1-s)⟩` (via `pathSpeed_reverse`, needs `hγdiff` at `1-s`); base
continuity comes from reparametrizing the original base by `s ↦ 1-s`, and the trivialized fibre is
the negation of the original's (negation is ℂ-linear, passes through `continuousLinearMapAt`). -/
theorem velCont_reverse (γ : ℝ → X)
    (hγdiff : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t)
    (hγ : ContinuousOn (fun s : ℝ =>
        Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s))
      (Set.Icc 0 1)) :
    ContinuousOn (fun s : ℝ =>
        Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
          (Jacobians.reverse γ s) (pathSpeed (Jacobians.reverse γ) s))
      (Set.Icc 0 1) := by
  -- The reparametrization `s ↦ 1 - s` maps `Icc 0 1` into `Icc 0 1` continuously.
  have hsub_cont : Continuous (fun s : ℝ => 1 - s) := continuous_const.sub continuous_id
  have hsub_maps : Set.MapsTo (fun s : ℝ => 1 - s) (Set.Icc (0:ℝ) 1) (Set.Icc 0 1) := by
    intro s hs; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hbase : ContinuousOn (fun s : ℝ => γ (1 - s)) (Set.Icc (0:ℝ) 1) := by
    have hγbase : ContinuousOn γ (Set.Icc (0:ℝ) 1) :=
      (FiberBundle.continuous_proj ℂ (TangentSpace 𝓘(ℂ) (M := X))).comp_continuousOn hγ
    exact hγbase.comp hsub_cont.continuousOn hsub_maps
  intro s₀ hs₀
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨?_, ?_⟩
  · -- base proj continuous: `s ↦ (⟨γ(1-s), …⟩).proj = γ(1-s)`.
    exact hbase s₀ hs₀
  · -- trivialized fibre at base `γ(1-s₀)` is continuous.
    set x₀ := γ (1 - s₀) with hx₀
    set triv := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀ with htriv
    have hx₀base : x₀ ∈ triv.baseSet := mem_baseSet_trivializationAt ℂ _ x₀
    -- 1-s₀ ∈ Icc 0 1.
    have hs₀' : (1 - s₀) ∈ Set.Icc (0:ℝ) 1 := hsub_maps hs₀
    -- The ORIGINAL section's trivialized fibre at base x₀ is continuous at 1-s₀.
    have hγ_at : ContinuousWithinAt
        (fun s : ℝ => Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s)
          (pathSpeed γ s)) (Set.Icc 0 1) (1 - s₀) := hγ (1 - s₀) hs₀'
    rw [FiberBundle.continuousWithinAt_totalSpace] at hγ_at
    -- hγ_at.2 : ContinuousWithinAt (fun u => (triv ⟨γ u, pathSpeed γ u⟩).2) (Icc 0 1) (1-s₀)
    have hfib_orig : ContinuousWithinAt
        (fun u : ℝ => (triv (Bundle.TotalSpace.mk' ℂ
          (E := TangentSpace 𝓘(ℂ) (M := X)) (γ u) (pathSpeed γ u))).2)
        (Set.Icc 0 1) (1 - s₀) := hγ_at.2
    -- Reparametrize by s ↦ 1 - s.
    have hcomp : ContinuousWithinAt
        (fun s : ℝ => (triv (Bundle.TotalSpace.mk' ℂ
          (E := TangentSpace 𝓘(ℂ) (M := X)) (γ (1 - s)) (pathSpeed γ (1 - s)))).2)
        (Set.Icc 0 1) s₀ := by
      have hsub_cwa : ContinuousWithinAt (fun s : ℝ => 1 - s) (Set.Icc (0:ℝ) 1) s₀ :=
        hsub_cont.continuousWithinAt
      exact hfib_orig.comp hsub_cwa hsub_maps
    -- Now: target fibre = - (original reparametrized fibre), via continuousLinearMapAt + pathSpeed_reverse.
    -- The map `· ↦ -·` on ℂ is continuous, so `(- original)` is continuous.
    have hneg : ContinuousWithinAt
        (fun s : ℝ => -(triv (Bundle.TotalSpace.mk' ℂ
          (E := TangentSpace 𝓘(ℂ) (M := X)) (γ (1 - s)) (pathSpeed γ (1 - s)))).2)
        (Set.Icc 0 1) s₀ := hcomp.neg
    refine hneg.congr_of_eventuallyEq ?_ ?_
    · -- eventually equal on Icc near s₀
      have hev : ∀ᶠ s in 𝓝[Set.Icc (0:ℝ) 1] s₀, γ (1 - s) ∈ triv.baseSet := by
        have hbase_at : ContinuousWithinAt (fun s : ℝ => γ (1 - s)) (Set.Icc (0:ℝ) 1) s₀ :=
          hbase s₀ hs₀
        exact hbase_at.eventually (triv.open_baseSet.mem_nhds hx₀base)
      filter_upwards [hev, self_mem_nhdsWithin] with s hs hsIcc
      -- LHS: (triv ⟨γ(1-s), pathSpeed (reverse γ) s⟩).2
      -- RHS: -(triv ⟨γ(1-s), pathSpeed γ(1-s)⟩).2
      have h1s_uIcc : (1 - s) ∈ Set.uIcc (0:ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact ⟨by linarith [hsIcc.2], by linarith [hsIcc.1]⟩
      have hps : pathSpeed (Jacobians.reverse γ) s = -pathSpeed γ (1 - s) :=
        pathSpeed_reverse γ s (hγdiff (1 - s) h1s_uIcc)
      show (triv (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
          (Jacobians.reverse γ s) (pathSpeed (Jacobians.reverse γ) s))).2 = _
      rw [reverse_apply, hps]
      -- Turn both `(triv ⟨·, w⟩).2` into `continuousLinearMapAt`.
      rw [← triv.continuousLinearMapAt_apply_of_mem ℂ hs,
          ← triv.continuousLinearMapAt_apply_of_mem ℂ hs]
      exact (triv.continuousLinearMapAt ℂ (γ (1 - s))).map_neg _
    · -- at s₀ itself
      have h1s₀_uIcc : (1 - s₀) ∈ Set.uIcc (0:ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact ⟨by linarith [hs₀.2], by linarith [hs₀.1]⟩
      have hps : pathSpeed (Jacobians.reverse γ) s₀ = -pathSpeed γ (1 - s₀) :=
        pathSpeed_reverse γ s₀ (hγdiff (1 - s₀) h1s₀_uIcc)
      show (triv (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
          (Jacobians.reverse γ s₀) (pathSpeed (Jacobians.reverse γ) s₀))).2 = _
      rw [reverse_apply, hps]
      rw [← triv.continuousLinearMapAt_apply_of_mem ℂ hx₀base,
          ← triv.continuousLinearMapAt_apply_of_mem ℂ hx₀base]
      exact (triv.continuousLinearMapAt ℂ (γ (1 - s₀))).map_neg _

/-- **The junction velocity of a concatenation vanishes**, given both pieces' chart-pullback
differentiability and vanishing endpoint velocities (`pathSpeed γ₁ 1 = 0`, `pathSpeed γ₂ 0 = 0`)
and matched basepoints `γ₁ 1 = γ₂ 0`. This is the velocity restatement of the junction step of the
`IsSmoothPath.concat` `diff` field (`HasDerivWithinAt … 0` glued on `Iic ∪ Ici`). -/
theorem pathSpeed_concat_junction (γ₁ γ₂ : ℝ → X)
    (h₁diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ₁ 1)).toFun ∘ γ₁) 1)
    (h₂diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ₂ 0)).toFun ∘ γ₂) 0)
    (hv₁ : pathSpeed γ₁ 1 = 0) (hv₂ : pathSpeed γ₂ 0 = 0) (hjoin : γ₁ 1 = γ₂ 0) :
    pathSpeed (Jacobians.concat γ₁ γ₂) (1/2) = 0 := by
  have hmid : Jacobians.concat γ₁ γ₂ (1/2 : ℝ) = γ₁ 1 := by
    rw [Jacobians.concat_apply_left _ _ (le_refl _), show (2:ℝ) * (1/2) = 1 from by norm_num]
  show fderiv ℝ ((chartAt (H := ℂ) (Jacobians.concat γ₁ γ₂ (1/2))).toFun ∘
      Jacobians.concat γ₁ γ₂) (1/2) (1 : ℝ) = 0
  rw [hmid]
  set f : ℝ → ℂ := (chartAt (H := ℂ) (γ₁ 1)).toFun ∘ Jacobians.concat γ₁ γ₂ with hf_def
  have h_2mul_HDA : HasDerivAt (fun s : ℝ => 2 * s) (2 : ℝ) (1/2 : ℝ) := by
    simpa using (hasDerivAt_id (1/2 : ℝ)).const_mul (2 : ℝ)
  -- LEFT: HasDerivWithinAt f 0 on Iic(1/2)
  have h_g_L_HDA : HasDerivAt ((chartAt (H := ℂ) (γ₁ 1)).toFun ∘ γ₁) 0 1 := by
    have h_deriv_zero : deriv ((chartAt (H := ℂ) (γ₁ 1)).toFun ∘ γ₁) 1 = 0 := hv₁
    rw [← h_deriv_zero]; exact h₁diff.hasDerivAt
  have h_f_L_HDA : HasDerivAt
      (((chartAt (H := ℂ) (γ₁ 1)).toFun ∘ γ₁) ∘ (fun s : ℝ => 2 * s)) 0 (1/2 : ℝ) := by
    simpa using h_g_L_HDA.scomp_of_eq (1/2 : ℝ) h_2mul_HDA (by norm_num : (1 : ℝ) = 2 * (1/2 : ℝ))
  have h_eqOn_Iic : Set.EqOn f
      (((chartAt (H := ℂ) (γ₁ 1)).toFun ∘ γ₁) ∘ (fun s : ℝ => 2 * s)) (Set.Iic (1/2 : ℝ)) := by
    intro s hs
    simp only [hf_def, Function.comp_apply]
    rw [Jacobians.concat_apply_left _ _ hs]
  have h_Iic_HDWA : HasDerivWithinAt f 0 (Set.Iic (1/2 : ℝ)) (1/2 : ℝ) :=
    (h_f_L_HDA.hasDerivWithinAt (s := Set.Iic (1/2 : ℝ))).congr
      (fun s hs => h_eqOn_Iic hs) (h_eqOn_Iic Set.self_mem_Iic)
  -- RIGHT: HasDerivWithinAt f 0 on Ici(1/2)
  have h_g_R_HDA : HasDerivAt ((chartAt (H := ℂ) (γ₁ 1)).toFun ∘ γ₂) 0 0 := by
    have h₂diff' : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ₁ 1)).toFun ∘ γ₂) 0 := by
      rw [hjoin]; exact h₂diff
    have h_deriv_zero : deriv ((chartAt (H := ℂ) (γ₁ 1)).toFun ∘ γ₂) 0 = 0 := by
      have : deriv ((chartAt (H := ℂ) (γ₂ 0)).toFun ∘ γ₂) 0 = 0 := hv₂
      rw [hjoin]; exact this
    rw [← h_deriv_zero]; exact h₂diff'.hasDerivAt
  have h_f_R_HDA : HasDerivAt
      (((chartAt (H := ℂ) (γ₁ 1)).toFun ∘ γ₂) ∘ (fun s : ℝ => 2 * s - 1)) 0 (1/2 : ℝ) := by
    simpa using h_g_R_HDA.scomp_of_eq (1/2 : ℝ) (h_2mul_HDA.sub_const 1)
      (by norm_num : (0 : ℝ) = 2 * (1/2 : ℝ) - 1)
  have h_eqOn_Ici : Set.EqOn f
      (((chartAt (H := ℂ) (γ₁ 1)).toFun ∘ γ₂) ∘ (fun s : ℝ => 2 * s - 1)) (Set.Ici (1/2 : ℝ)) := by
    intro s hs
    simp only [hf_def, Function.comp_apply]
    rcases eq_or_lt_of_le (show (1/2 : ℝ) ≤ s from hs) with h_eq_half | h_gt_half
    · rw [← h_eq_half, Jacobians.concat_apply_left _ _ (le_refl _),
          show (2:ℝ) * (1/2) - 1 = 0 from by norm_num,
          show (2:ℝ) * (1/2) = 1 from by norm_num, hjoin]
    · rw [Jacobians.concat_apply_right _ _ (not_le.mpr h_gt_half)]
  have h_Ici_HDWA : HasDerivWithinAt f 0 (Set.Ici (1/2 : ℝ)) (1/2 : ℝ) :=
    (h_f_R_HDA.hasDerivWithinAt (s := Set.Ici (1/2 : ℝ))).congr
      (fun s hs => h_eqOn_Ici hs) (h_eqOn_Ici Set.self_mem_Ici)
  -- UNION ⇒ HasDerivAt f 0 (1/2) ⇒ pathSpeed = 0.
  have h_union : HasDerivWithinAt f 0 (Set.Iic (1/2 : ℝ) ∪ Set.Ici (1/2 : ℝ)) (1/2 : ℝ) :=
    h_Iic_HDWA.union h_Ici_HDWA
  have h_union_eq : Set.Iic (1/2 : ℝ) ∪ Set.Ici (1/2 : ℝ) = Set.univ := by
    ext x; simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
    rcases lt_or_ge x (1/2 : ℝ) with h | h
    · exact Or.inl (le_of_lt h)
    · exact Or.inr h
  rw [h_union_eq] at h_union
  have h_HDA : HasDerivAt f 0 (1/2 : ℝ) := h_union.hasDerivAt Filter.univ_mem
  -- pathSpeed = fderiv … 1 = deriv … = 0.
  show fderiv ℝ f (1/2) (1 : ℝ) = 0
  rw [fderiv_apply_one_eq_deriv]; exact h_HDA.deriv

/-- **Velocity-section continuity under an affine reparametrization `s ↦ a*s + b` with the fibre
rescaled by `a`.** This is the shape of each half of `concat` (left: `a = 2, b = 0`; right:
`a = 2, b = -1`), where `pathSpeed (concat) s = 2 * pathSpeed γᵢ (2s + …)`. Mirrors `velCont_reverse`
(itself the `a = -1, b = 1` case): base continuity from reparametrizing the projection, fibre
continuity from the original trivialized fibre scaled by `a` (scaling is ℂ-linear, passes through
`continuousLinearMapAt`). -/
theorem velCont_affineReparam (γ : ℝ → X) (a b : ℝ) {D : Set ℝ}
    (hmaps : Set.MapsTo (fun s : ℝ => a * s + b) D (Set.Icc 0 1))
    (hγ : ContinuousOn (fun s : ℝ =>
        Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s))
      (Set.Icc 0 1)) :
    ContinuousOn (fun s : ℝ =>
        Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
          (γ (a * s + b)) ((a : ℂ) • pathSpeed γ (a * s + b)))
      D := by
  set r : ℝ → ℝ := fun s : ℝ => a * s + b with hr_def
  have hr_cont : Continuous r :=
    (continuous_const.mul continuous_id).add continuous_const
  have hbase : ContinuousOn (fun s : ℝ => γ (r s)) D := by
    have hγbase : ContinuousOn γ (Set.Icc (0:ℝ) 1) :=
      (FiberBundle.continuous_proj ℂ (TangentSpace 𝓘(ℂ) (M := X))).comp_continuousOn hγ
    exact hγbase.comp hr_cont.continuousOn hmaps
  intro s₀ hs₀
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨hbase s₀ hs₀, ?_⟩
  set x₀ := γ (r s₀) with hx₀
  set triv := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀ with htriv
  have hx₀base : x₀ ∈ triv.baseSet := mem_baseSet_trivializationAt ℂ _ x₀
  have hrs₀ : r s₀ ∈ Set.Icc (0:ℝ) 1 := hmaps hs₀
  have hγ_at : ContinuousWithinAt
      (fun s : ℝ => Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s)
        (pathSpeed γ s)) (Set.Icc 0 1) (r s₀) := hγ (r s₀) hrs₀
  rw [FiberBundle.continuousWithinAt_totalSpace] at hγ_at
  have hfib_orig : ContinuousWithinAt
      (fun u : ℝ => (triv (Bundle.TotalSpace.mk' ℂ
        (E := TangentSpace 𝓘(ℂ) (M := X)) (γ u) (pathSpeed γ u))).2)
      (Set.Icc 0 1) (r s₀) := hγ_at.2
  have hr_cwa : ContinuousWithinAt r D s₀ := hr_cont.continuousWithinAt
  have hcomp : ContinuousWithinAt
      (fun s : ℝ => (triv (Bundle.TotalSpace.mk' ℂ
        (E := TangentSpace 𝓘(ℂ) (M := X)) (γ (r s)) (pathSpeed γ (r s)))).2)
      D s₀ :=
    hfib_orig.comp hr_cwa hmaps
  -- scale the trivialized fibre by `a`.
  have hsmul : ContinuousWithinAt
      (fun s : ℝ => (a : ℂ) • (triv (Bundle.TotalSpace.mk' ℂ
        (E := TangentSpace 𝓘(ℂ) (M := X)) (γ (r s)) (pathSpeed γ (r s)))).2)
      D s₀ := hcomp.const_smul (a : ℂ)
  refine hsmul.congr_of_eventuallyEq ?_ ?_
  · have hev : ∀ᶠ s in 𝓝[D] s₀, γ (r s) ∈ triv.baseSet := by
      have hbase_at : ContinuousWithinAt (fun s : ℝ => γ (r s)) D s₀ :=
        hbase s₀ hs₀
      exact hbase_at.eventually (triv.open_baseSet.mem_nhds hx₀base)
    filter_upwards [hev] with s hs
    show (triv (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
        (γ (r s)) ((a : ℂ) • pathSpeed γ (r s)))).2 = _
    rw [← triv.continuousLinearMapAt_apply_of_mem ℂ hs,
        ← triv.continuousLinearMapAt_apply_of_mem ℂ hs]
    exact (triv.continuousLinearMapAt ℂ (γ (r s))).map_smul (a : ℂ) _
  · show (triv (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
        (γ (r s₀)) ((a : ℂ) • pathSpeed γ (r s₀)))).2 = _
    rw [← triv.continuousLinearMapAt_apply_of_mem ℂ hx₀base,
        ← triv.continuousLinearMapAt_apply_of_mem ℂ hx₀base]
    exact (triv.continuousLinearMapAt ℂ (γ (r s₀))).map_smul (a : ℂ) _

/-- **Velocity-section continuity under a smooth scalar reparametrization `σ`.** For the
`smoothPathSmooth = smoothPath ∘ smoothStep01` case: given the chain-rule fact
`pathSpeed (γ ∘ σ) s = σ'(s) • pathSpeed γ (σ s)` (supplied as `hspeed`, from
`pathSpeed_smoothStep01_comp_eq`), a continuous reparam `σ` mapping `D` into `[0,1]`, and a
continuous scaling `σ'`, the reparametrized velocity section is continuous on `D`. Generalizes
`velCont_affineReparam` (constant scale `a`) to a varying scale `σ'`. -/
theorem velCont_reparam (γ : ℝ → X) (σ σ' : ℝ → ℝ) {D : Set ℝ}
    (hmaps : Set.MapsTo σ D (Set.Icc 0 1)) (hσcont : ContinuousOn σ D)
    (hσ'cont : ContinuousOn (fun s : ℝ => (σ' s : ℂ)) D)
    (hspeed : ∀ s ∈ D, pathSpeed (γ ∘ σ) s = (σ' s : ℂ) • pathSpeed γ (σ s))
    (hγ : ContinuousOn (fun s : ℝ =>
        Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s))
      (Set.Icc 0 1)) :
    ContinuousOn (fun s : ℝ =>
        Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
          ((γ ∘ σ) s) (pathSpeed (γ ∘ σ) s))
      D := by
  have hbase : ContinuousOn (fun s : ℝ => γ (σ s)) D := by
    have hγbase : ContinuousOn γ (Set.Icc (0:ℝ) 1) :=
      (FiberBundle.continuous_proj ℂ (TangentSpace 𝓘(ℂ) (M := X))).comp_continuousOn hγ
    exact hγbase.comp hσcont hmaps
  intro s₀ hs₀
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨hbase s₀ hs₀, ?_⟩
  set x₀ := γ (σ s₀) with hx₀
  set triv := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀ with htriv
  have hx₀base : x₀ ∈ triv.baseSet := mem_baseSet_trivializationAt ℂ _ x₀
  have hrs₀ : σ s₀ ∈ Set.Icc (0:ℝ) 1 := hmaps hs₀
  have hγ_at : ContinuousWithinAt
      (fun s : ℝ => Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s)
        (pathSpeed γ s)) (Set.Icc 0 1) (σ s₀) := hγ (σ s₀) hrs₀
  rw [FiberBundle.continuousWithinAt_totalSpace] at hγ_at
  have hfib_orig : ContinuousWithinAt
      (fun u : ℝ => (triv (Bundle.TotalSpace.mk' ℂ
        (E := TangentSpace 𝓘(ℂ) (M := X)) (γ u) (pathSpeed γ u))).2)
      (Set.Icc 0 1) (σ s₀) := hγ_at.2
  have hcomp : ContinuousWithinAt
      (fun s : ℝ => (triv (Bundle.TotalSpace.mk' ℂ
        (E := TangentSpace 𝓘(ℂ) (M := X)) (γ (σ s)) (pathSpeed γ (σ s)))).2)
      D s₀ :=
    hfib_orig.comp (hσcont s₀ hs₀) hmaps
  -- scale the trivialized fibre by `σ' s` (continuous).
  have hsmul : ContinuousWithinAt
      (fun s : ℝ => (σ' s : ℂ) • (triv (Bundle.TotalSpace.mk' ℂ
        (E := TangentSpace 𝓘(ℂ) (M := X)) (γ (σ s)) (pathSpeed γ (σ s)))).2)
      D s₀ := (hσ'cont s₀ hs₀).smul hcomp
  refine hsmul.congr_of_eventuallyEq ?_ ?_
  · have hev : ∀ᶠ s in 𝓝[D] s₀, γ (σ s) ∈ triv.baseSet :=
      (hbase s₀ hs₀).eventually (triv.open_baseSet.mem_nhds hx₀base)
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hsD
    show (triv (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
        ((γ ∘ σ) s) (pathSpeed (γ ∘ σ) s))).2 = _
    rw [hspeed s hsD]
    show (triv (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
        (γ (σ s)) ((σ' s : ℂ) • pathSpeed γ (σ s)))).2 = _
    rw [← triv.continuousLinearMapAt_apply_of_mem ℂ hs,
        ← triv.continuousLinearMapAt_apply_of_mem ℂ hs]
    exact (triv.continuousLinearMapAt ℂ (γ (σ s))).map_smul (σ' s : ℂ) _
  · show (triv (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
        ((γ ∘ σ) s₀) (pathSpeed (γ ∘ σ) s₀))).2 = _
    rw [hspeed s₀ hs₀]
    show (triv (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
        (γ (σ s₀)) ((σ' s₀ : ℂ) • pathSpeed γ (σ s₀)))).2 = _
    rw [← triv.continuousLinearMapAt_apply_of_mem ℂ hx₀base,
        ← triv.continuousLinearMapAt_apply_of_mem ℂ hx₀base]
    exact (triv.continuousLinearMapAt ℂ (γ (σ s₀))).map_smul (σ' s₀ : ℂ) _

/-- **Velocity-section continuity is preserved by concatenation** at vanishing junction velocities.
For the `IsSmoothPath.concat` constructor. On each open half the concatenation's velocity section
is the corresponding piece's section reparametrized (`2·` left, `2·-1` right) with the fibre scaled
by `2` (`pathSpeed_concat_left`/`right`, via `velCont_affineReparam`); at the junction `s = ½` both
the actual junction velocity (`pathSpeed_concat_junction`, `= 0`) and each scaled-reparam value
(`2 • pathSpeed γ₁ 1 = 0` by `hv₁`, resp. `hv₂`) vanish and the bases match (`hjoin`), so the
concat-section coincides with each clean reparam section up to and INCLUDING `½`, and the two
one-sided `ContinuousWithinAt`s glue (`ContinuousWithinAt.union` on `Iic ½ ∪ Ici ½ = univ`). -/
theorem velCont_concat (γ₁ γ₂ : ℝ → X)
    (h₁diff : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ₁ t)).toFun ∘ γ₁) t)
    (h₂diff : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ₂ t)).toFun ∘ γ₂) t)
    (hv₁ : pathSpeed γ₁ 1 = 0) (hv₂ : pathSpeed γ₂ 0 = 0) (hjoin : γ₁ 1 = γ₂ 0)
    (hγ₁ : ContinuousOn (fun s : ℝ =>
        Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ₁ s) (pathSpeed γ₁ s))
      (Set.Icc 0 1))
    (hγ₂ : ContinuousOn (fun s : ℝ =>
        Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ₂ s) (pathSpeed γ₂ s))
      (Set.Icc 0 1)) :
    ContinuousOn (fun s : ℝ =>
        Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
          (Jacobians.concat γ₁ γ₂ s) (pathSpeed (Jacobians.concat γ₁ γ₂) s))
      (Set.Icc 0 1) := by
  -- uIcc membership helpers.
  have h_one_uIcc : (1 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
  have h_zero_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_refl _, zero_le_one⟩
  -- Junction velocity vanishes.
  have hjunc : pathSpeed (Jacobians.concat γ₁ γ₂) (1/2) = 0 :=
    pathSpeed_concat_junction γ₁ γ₂ (h₁diff 1 h_one_uIcc) (h₂diff 0 h_zero_uIcc) hv₁ hv₂ hjoin
  -- The two clean reparam sections, continuous via `velCont_affineReparam`.
  have hmapsL : Set.MapsTo (fun s : ℝ => 2 * s + 0) (Set.Icc (0:ℝ) (1/2)) (Set.Icc 0 1) := by
    intro s hs; exact ⟨by simpa using by linarith [hs.1], by simpa using by linarith [hs.2]⟩
  have hmapsR : Set.MapsTo (fun s : ℝ => 2 * s + (-1)) (Set.Icc (1/2:ℝ) 1) (Set.Icc 0 1) := by
    intro s hs; exact ⟨by simp; linarith [hs.1], by simp; linarith [hs.2]⟩
  have hS₁ := velCont_affineReparam γ₁ 2 0 hmapsL hγ₁
  have hS₂ := velCont_affineReparam γ₂ 2 (-1) hmapsR hγ₂
  -- Split `Icc 0 1` into the two closed halves.
  have hsplit : Set.Icc (0:ℝ) 1 = Set.Icc (0:ℝ) (1/2) ∪ Set.Icc (1/2) 1 := by
    rw [Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
  rw [hsplit]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
  · -- LEFT half: concat-section = S₁ on Icc 0 (1/2).
    refine hS₁.congr ?_
    intro s hs
    have hs_le : s ≤ 1/2 := hs.2
    have h_base : Jacobians.concat γ₁ γ₂ s = γ₁ (2 * s + 0) := by
      rw [Jacobians.concat_apply_left _ _ hs_le, add_zero]
    have h_fib : pathSpeed (Jacobians.concat γ₁ γ₂) s = ((2:ℝ) : ℂ) • pathSpeed γ₁ (2 * s + 0) := by
      rcases lt_or_eq_of_le hs_le with h_lt | h_eq
      · have h2s_uIcc : 2 * s ∈ Set.uIcc (0:ℝ) 1 := by
          rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
          exact ⟨by linarith [hs.1], by linarith⟩
        rw [Jacobians.pathSpeed_concat_left _ _ s h_lt (h₁diff (2 * s) h2s_uIcc), add_zero,
          smul_eq_mul]; push_cast; ring
      · subst h_eq
        rw [hjunc, show (2:ℝ) * (1/2) + 0 = 1 from by norm_num, hv₁, smul_zero]
    show Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
        (Jacobians.concat γ₁ γ₂ s) (pathSpeed (Jacobians.concat γ₁ γ₂) s) = _
    rw [h_base, h_fib]
  · -- RIGHT half: concat-section = S₂ on Icc (1/2) 1.
    refine hS₂.congr ?_
    intro s hs
    have hs_ge : 1/2 ≤ s := hs.1
    have h_base : Jacobians.concat γ₁ γ₂ s = γ₂ (2 * s + (-1)) := by
      rcases lt_or_eq_of_le hs_ge with h_gt | h_eq
      · rw [Jacobians.concat_apply_right _ _ (not_le.mpr h_gt),
          show (2:ℝ) * s + (-1) = 2*s - 1 from by ring]
      · subst h_eq
        rw [Jacobians.concat_apply_left _ _ (le_refl _),
          show (2:ℝ) * (1/2) = 1 from by norm_num,
          show (1:ℝ) + (-1) = 0 from by norm_num, hjoin]
    have h_fib : pathSpeed (Jacobians.concat γ₁ γ₂) s
        = ((2:ℝ) : ℂ) • pathSpeed γ₂ (2 * s + (-1)) := by
      rcases lt_or_eq_of_le hs_ge with h_gt | h_eq
      · have h2sm1_uIcc : 2 * s - 1 ∈ Set.uIcc (0:ℝ) 1 := by
          rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
          exact ⟨by linarith, by linarith [hs.2]⟩
        rw [Jacobians.pathSpeed_concat_right _ _ s h_gt (h₂diff (2 * s - 1) h2sm1_uIcc),
          show (2:ℝ) * s + (-1) = 2*s - 1 from by ring, smul_eq_mul]; push_cast; ring
      · subst h_eq
        rw [hjunc, show (2:ℝ) * (1/2) + (-1) = 0 from by norm_num, hv₂, smul_zero]
    show Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
        (Jacobians.concat γ₁ γ₂ s) (pathSpeed (Jacobians.concat γ₁ γ₂) s) = _
    rw [h_base, h_fib]

/-- **Velocity-section continuity of a `C¹` path into the model space ℂ.** For ℂ the chart at any
point is the identity, so `pathSpeed β = deriv β` and the tangent bundle is trivial; the velocity
section is therefore continuous as soon as `β` and `deriv β` are. This is the base-path velocity
input for the `ChartBallPathSmooth` case of the C¹ refactor (composed with `(chartAt ℂ Q₀).symm` via
`velCont_compOn`). -/
theorem velCont_modelPath (β : ℝ → ℂ) (hβ : Continuous β) (hβ' : Continuous (deriv β)) :
    ContinuousOn (fun s : ℝ =>
        Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := ℂ)) (β s) (pathSpeed β s))
      (Set.Icc 0 1) := by
  have hps : (fun s : ℝ => pathSpeed β s) = deriv β := by funext s; simp [pathSpeed]
  intro s₀ hs₀
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨hβ.continuousWithinAt, ?_⟩
  have hβ'cwa : ContinuousWithinAt (fun s : ℝ => pathSpeed β s) (Set.Icc 0 1) s₀ := by
    rw [hps]; exact hβ'.continuousWithinAt
  refine hβ'cwa.congr_of_eventuallyEq ?_ ?_ <;> simp

end Jacobians
