/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.AnalyticFiberDiscrete
import KirovDolbeault.Discharge.Manifold.ContMDiffOmegaAnalytic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit true


/-! # Constructing `ChartPullbackData` from `ContMDiffAt … ω`

ZZ22 packaged the per-fibre isolation argument behind the `ChartPullbackData`
structure (in `AnalyticFiberDiscrete.lean`). ZZ24 supplied the bridge
`ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x → AnalyticAt ℂ (chart pullback)`
(in `ContMDiffOmegaAnalytic.lean`).

This file combines them: from `ContMDiffAt … ω f x` plus the local
non-degeneracy hypothesis "the chart-pulled-back representation of `f` near
`x` is not eventually equal to its value at `(chartAt ℂ x) x`", we
construct an inhabitant of `ChartPullbackData f x (f x)`.

No gaps, no `axiom`. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## Constructor at the "free" target value `f x` -/

/-- **Constructor: `ChartPullbackData` from `ContMDiffAt … ω`.**

Given `f : X → Y` between `ChartedSpace ℂ` manifolds, with
`ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x` and the local non-degeneracy hypothesis that
the chart pullback of `f` is **not** eventually equal to its value at
`(chartAt ℂ x) x`, we build a `ChartPullbackData f x (f x)` witness. -/
noncomputable def chartPullbackData_of_contMDiff
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x)
    (hne : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f x)) (f x)) :
    ChartPullbackData f x (f x) := by
  classical
  -- Abbreviations.
  set eX : OpenPartialHomeomorph X ℂ := chartAt ℂ x with heX
  set eY : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with heY
  -- Key chart membership facts.
  have hxS : x ∈ eX.source := mem_chart_source ℂ x
  have hfxS : f x ∈ eY.source := mem_chart_source ℂ (f x)
  -- Continuity of `f` at `x` from `ContMDiffAt`.
  have hf_cont : ContinuousAt f x := hf.continuousAt
  -- `eY.source ∈ 𝓝 (f x)`, so `f ⁻¹' eY.source ∈ 𝓝 x`.
  have hYnhd : eY.source ∈ 𝓝 (f x) := eY.open_source.mem_nhds hfxS
  have hpreimage_nhd : f ⁻¹' eY.source ∈ 𝓝 x := hf_cont hYnhd
  -- Choose an open set `V₀ ⊆ f ⁻¹' eY.source` with `x ∈ V₀`.
  -- Use `Classical.choose` because `obtain`/`cases` cannot eliminate
  -- `Exists` into a non-Prop motive (the goal is `ChartPullbackData …`,
  -- which is in `Type`).
  let V₀ : Set X := Classical.choose (mem_nhds_iff.mp hpreimage_nhd)
  have hV₀_spec := Classical.choose_spec (mem_nhds_iff.mp hpreimage_nhd)
  -- `hV₀_spec : V₀ ⊆ f ⁻¹' eY.source ∧ IsOpen V₀ ∧ x ∈ V₀`.
  have hV₀_sub : V₀ ⊆ f ⁻¹' eY.source := hV₀_spec.1
  have hV₀_open : IsOpen V₀ := hV₀_spec.2.1
  have hxV₀ : x ∈ V₀ := hV₀_spec.2.2
  -- `V := V₀ ∩ eX.source` is open, contains `x`, and is in both
  -- `eX.source` and `f ⁻¹' eY.source`.
  set V : Set X := V₀ ∩ eX.source with hVdef
  have hV_open : IsOpen V := hV₀_open.inter eX.open_source
  have hxV : x ∈ V := ⟨hxV₀, hxS⟩
  have hV_subS : V ⊆ eX.source := fun _ h => h.2
  have hV_subPre : V ⊆ f ⁻¹' eY.source := fun _ h => hV₀_sub h.1
  -- `W := eX '' V` is open in ℂ.
  set W : Set ℂ := eX '' V with hWdef
  have hW_open : IsOpen W := by
    have hWeq : W = eX.target ∩ eX.symm ⁻¹' V := by
      ext z
      constructor
      · rintro ⟨v, hvV, rfl⟩
        refine ⟨eX.map_source (hV_subS hvV), ?_⟩
        show eX.symm (eX v) ∈ V
        rw [eX.left_inv (hV_subS hvV)]
        exact hvV
      · rintro ⟨hz_target, hz_pre⟩
        refine ⟨eX.symm z, hz_pre, ?_⟩
        exact eX.right_inv hz_target
    rw [hWeq]
    exact eX.isOpen_inter_preimage_symm hV_open
  -- `z₀ := eX x`, lies in `W`.
  set z₀ : ℂ := eX x with hz₀def
  have hz₀W : z₀ ∈ W := ⟨x, hxV, rfl⟩
  -- Build `φ : V → W` by restricting `eX`.
  let φ : V → W := fun v => ⟨eX v.1, mem_image_of_mem _ v.2⟩
  -- Continuity of `φ`.
  have hφ_cont : Continuous φ := by
    apply Continuous.subtype_mk
    have h_co : ContinuousOn eX eX.source := eX.continuousOn_toFun
    have h_co_V : ContinuousOn eX V := h_co.mono hV_subS
    have h_restrict : Continuous (V.restrict eX) :=
      continuousOn_iff_continuous_restrict.mp h_co_V
    exact h_restrict
  -- Bijectivity of `φ`.
  have hφ_bij : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · intro v₁ v₂ hv
      have h_eq : eX v₁.1 = eX v₂.1 := by
        have := congrArg Subtype.val hv
        simpa using this
      have hi := eX.injOn (hV_subS v₁.2) (hV_subS v₂.2) h_eq
      exact Subtype.ext hi
    · rintro ⟨w, hw⟩
      obtain ⟨v', hv'V, hv'eq⟩ := hw
      refine ⟨⟨v', hv'V⟩, ?_⟩
      exact Subtype.ext hv'eq
  -- `φ ⟨x, hxV⟩` has underlying value `z₀`.
  have hz₀_eq : (φ ⟨x, hxV⟩ : ℂ) = z₀ := rfl
  -- The chart pullback `F` and target value `c`.
  set F : ℂ → ℂ := (eY) ∘ f ∘ eX.symm with hFdef
  set c : ℂ := eY (f x) with hcdef
  -- Analyticity of `F` at `z₀`: ZZ24's bridge.
  have hFA : AnalyticAt ℂ F z₀ :=
    contMDiffAt_omega_analyticAt_chart_pullback hf
  -- Compatibility.
  have hCompat : ∀ v : V, f v.1 = f x ↔ F (φ v) = c := by
    intro v
    have hv_inS : v.1 ∈ eX.source := hV_subS v.2
    have hfv_inS : f v.1 ∈ eY.source := hV_subPre v.2
    have h_left_inv : eX.symm (eX v.1) = v.1 := eX.left_inv hv_inS
    have hFφ : F (φ v) = eY (f v.1) := by
      show eY (f (eX.symm (eX v.1))) = eY (f v.1)
      rw [h_left_inv]
    constructor
    · intro h
      rw [hFφ, h]
    · intro h
      have hch : eY (f v.1) = eY (f x) := by
        rw [← hFφ]; exact h
      exact eY.injOn hfv_inS hfxS hch
  -- Assemble the structure.
  exact
    { V := V
      hV_open := hV_open
      hxV := hxV
      W := W
      hW_open := hW_open
      φ := φ
      hφ := hφ_cont
      hφ_inv := hφ_bij
      z₀ := z₀
      hz₀ := hz₀_eq
      hz₀W := hz₀W
      F := F
      c := c
      hFA := hFA
      hFne := hne
      hCompat := hCompat }

/-! ## Globalised: target a fixed `y₀` via term-mode rewrite -/

/-- **Globalised constructor.** From global `ContMDiff … ω f` and a
chart-pullback non-degeneracy hypothesis at every fibre point of `y₀`,
build a `ChartPullbackData` witness at every fibre point. -/
noncomputable def chartPullbackData_of_contMDiff_global
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    {y₀ : Y}
    (hne : ∀ x : X, f x = y₀ →
      ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
            = (chartAt ℂ (f x)) (f x)) :
    ∀ x ∈ f ⁻¹' {y₀}, ChartPullbackData f x y₀ := fun x hx =>
  -- Reduce membership in the singleton fibre to the equality `f x = y₀`.
  have hx_eq : f x = y₀ := hx
  -- Build at the "free" target `f x`, then transport along `hx_eq`.
  have D : ChartPullbackData f x (f x) :=
    chartPullbackData_of_contMDiff (hf x) (hne x hx_eq)
  -- Rewrite `(f x)` to `y₀` in the type via `hx_eq`. We avoid `cases hx_eq`
  -- (which can trigger a non-Prop motive issue when the goal is data) and
  -- use term-mode `▸` instead, which uses the `Eq` recursor with a Type
  -- motive — supported because `Eq` allows large elimination.
  hx_eq ▸ D

end Degree
end ContMDiff
end Jacobians.Discharge
