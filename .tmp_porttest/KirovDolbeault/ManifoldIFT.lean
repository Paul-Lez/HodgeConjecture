/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Discharge.Manifold.ContMDiffOmegaAnalytic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! # Manifold inverse function theorem for complex 1-manifolds

For a real-analytic (`C^ω`) map `f : X → Y` between complex-analytic manifolds
modelled on `ℂ`, if the chart-pullback representative
`(chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm` has nonzero derivative at the
chart image of `x`, then `f` admits a local holomorphic (in fact `C^ω`) section
`g` near `f x` with `g (f x) = x` and `f ∘ g = id` on an open neighborhood.

This is the manifold packaging of the complex inverse function theorem, obtained
by:
1. pulling `f` back through charts to a map `F : ℂ → ℂ`, which is `AnalyticAt`
   at `a := (chartAt ℂ x) x` (via
   `Jacobians.Discharge.ContMDiff.Degree.contMDiffAt_omega_analyticAt_chart_pullback`);
2. applying the complex IFT (`HasStrictDerivAt.localInverse`,
   `AnalyticAt.analyticAt_localInverse`) to get a local inverse `G : ℂ → ℂ`;
3. transporting `G` back to the manifold as `g := (chartAt ℂ x).symm ∘ G ∘ (chartAt ℂ (f x))`.

The non-criticality hypothesis `hderiv` is taken as GIVEN input. -/

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace Jacobians

universe u v

/-- **Manifold inverse function theorem (local holomorphic section).**
For `f : X → Y` real-analytic between complex 1-manifolds, with non-vanishing
chart-pullback derivative at `x`, there is a `C^ω` local section `g` of `f`
defined on an open neighborhood `V` of `f x`, with `g (f x) = x` and
`f (g y) = y` for `y ∈ V`. -/
theorem exists_holo_localInverse
    {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x : X)
    (hderiv : deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0) :
    ∃ (g : Y → X) (V : Set Y), IsOpen V ∧ f x ∈ V ∧ g (f x) = x ∧
      (∀ y ∈ V, f (g y) = y) ∧ ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g V := by
  -- Chart abbreviations and the chart-pullback representative `F : ℂ → ℂ`.
  set φX := chartAt ℂ x with hφX
  set φY := chartAt ℂ (f x) with hφY
  set a : ℂ := φX x with ha
  set F : ℂ → ℂ := φY ∘ f ∘ φX.symm with hF
  -- `x` lies in its own chart source; symm recovers it.
  have hxsrc : x ∈ φX.source := mem_chart_source ℂ x
  have hfxsrc : f x ∈ φY.source := mem_chart_source ℂ (f x)
  have hsymm_a : φX.symm a = x := by
    rw [ha]; exact φX.left_inv hxsrc
  -- `F a = φY (f x)`.
  have hFa_eq : F a = φY (f x) := by
    simp only [hF, Function.comp_apply, hsymm_a]
  -- Step 1: `F` is `AnalyticAt ℂ` at `a` via the project's chart-pullback bridge.
  have hFanalytic : AnalyticAt ℂ F a :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiffAt_omega_analyticAt_chart_pullback (hf x)
  -- Step 2: analytic ⇒ strict deriv; with `hderiv` we get a local inverse `G`.
  have hsd : HasStrictDerivAt F (deriv F a) a := hFanalytic.hasStrictDerivAt
  set G : ℂ → ℂ := hsd.localInverse F (deriv F a) a hderiv with hG
  -- `G` is analytic at `F a`.
  have hGanalytic : AnalyticAt ℂ G (F a) := hFanalytic.analyticAt_localInverse hderiv
  -- The local inverse fixes `a` at the centre: `G (F a) = a`.
  have hG_Fa : G (F a) = a := (hsd.eventually_left_inverse hderiv).self_of_nhds
  -- `a = φX x ∈ φX.target`.
  have ha_target : a ∈ φX.target := by rw [ha]; exact φX.map_source hxsrc
  -- Step 3a: assemble the three facts we need near `F a` into one `Eventually`:
  --   (i) `F ∘ G = id` (right inverse),
  --   (ii) `G z ∈ φX.target` (so `φX.symm` is on its source),
  --   (iii) `G` is `AnalyticAt` at `z` (so `G` is `ContMDiff`/continuous there).
  have h_rinv : ∀ᶠ z in 𝓝 (F a), F (G z) = z := hsd.eventually_right_inverse hderiv
  have h_Gtarget : ∀ᶠ z in 𝓝 (F a), G z ∈ φX.target := by
    have hGcont : ContinuousAt G (F a) := hGanalytic.continuousAt
    have : G ⁻¹' φX.target ∈ 𝓝 (F a) :=
      hGcont.preimage_mem_nhds (by rw [hG_Fa]; exact φX.open_target.mem_nhds ha_target)
    exact this
  have h_Ganalytic : ∀ᶠ z in 𝓝 (F a), AnalyticAt ℂ G z := hGanalytic.eventually_analyticAt
  have h_all : ∀ᶠ z in 𝓝 (F a), F (G z) = z ∧ G z ∈ φX.target ∧ AnalyticAt ℂ G z :=
    (h_rinv.and (h_Gtarget.and h_Ganalytic))
  -- Extract an open `U ∋ F a` on which all three hold.
  obtain ⟨U, hU_sub, hU_open, hU_mem⟩ := eventually_nhds_iff.mp h_all
  -- The candidate section and its preliminary domain `V₀`.
  set g : Y → X := fun y => φX.symm (G (φY y)) with hg
  set V₀ : Set Y := φY.source ∩ φY ⁻¹' U with hV₀
  have hV₀_open : IsOpen V₀ := φY.isOpen_inter_preimage hU_open
  have hfx_V₀ : f x ∈ V₀ := by
    refine ⟨hfxsrc, ?_⟩
    show φY (f x) ∈ U
    rw [← hFa_eq]; exact hU_mem
  -- `g (f x) = x`.
  have hg_fx : g (f x) = x := by
    have : φY (f x) = F a := hFa_eq.symm
    simp only [hg, this, hG_Fa, hsymm_a]
  -- Smoothness of the three building blocks.
  -- (i) `φY` is `C^ω` on `V₀ ⊆ φY.source`.
  have hφY_smooth : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω φY V₀ :=
    (contMDiffOn_chart (x := f x)).mono inter_subset_left
  -- (ii) `G` is `C^ω` on `U` (from analyticity at each point).
  have hG_smooth : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω G U := fun z hz =>
    (((hU_sub z hz).2.2.contDiffAt).contMDiffAt).contMDiffWithinAt
  -- (iii) `φX.symm` is `C^ω` on `φX.target`.
  have hφXsymm_smooth : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω φX.symm φX.target :=
    contMDiffOn_chart_symm
  -- Compose: `g = φX.symm ∘ G ∘ φY` is `C^ω` on `V₀`.
  have hG_comp_φY : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (G ∘ φY) V₀ :=
    hG_smooth.comp hφY_smooth inter_subset_right
  have hMapsTo : V₀ ⊆ (G ∘ φY) ⁻¹' φX.target := by
    intro y hy
    show G (φY y) ∈ φX.target
    exact (hU_sub (φY y) hy.2).2.1
  have hg_smooth : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g V₀ :=
    hφXsymm_smooth.comp hG_comp_φY hMapsTo
  -- Refine the domain so that `f (g y)` lands in `φY.source` (needed to invert
  -- the chart on the left): `V := V₀ ∩ (f ∘ g) ⁻¹' φY.source`.
  have hfg_cont : ContinuousOn (f ∘ g) V₀ :=
    hf.continuous.comp_continuousOn hg_smooth.continuousOn
  set V : Set Y := V₀ ∩ (f ∘ g) ⁻¹' φY.source with hV
  have hV_open : IsOpen V :=
    hfg_cont.isOpen_inter_preimage hV₀_open φY.open_source
  have hfx_V : f x ∈ V := by
    refine ⟨hfx_V₀, ?_⟩
    show f (g (f x)) ∈ φY.source
    rw [hg_fx]; exact hfxsrc
  -- The section identity `f (g y) = y` on `V`.
  have hsection : ∀ y ∈ V, f (g y) = y := by
    intro y hy
    obtain ⟨⟨hy_src, hy_pre⟩, hy_fgsrc⟩ := hy
    have hφYy_U : φY y ∈ U := hy_pre
    -- `F (G (φY y)) = φY y` (right inverse on `U`).
    obtain ⟨hrinv, -, -⟩ := hU_sub (φY y) hφYy_U
    -- Unfold `F` at `G (φY y)`: `F (G (φY y)) = φY (f (φX.symm (G (φY y)))) = φY (f (g y))`.
    have hFG : F (G (φY y)) = φY (f (g y)) := by
      simp only [hF, hg, Function.comp_apply]
    -- Hence `φY (f (g y)) = φY y`.
    have hchart_eq : φY (f (g y)) = φY y := by rw [← hFG, hrinv]
    -- `f (g y) ∈ φY.source` (the refinement), so apply `φY.symm` on the left.
    have : f (g y) = φY.symm (φY y) := by
      rw [← hchart_eq]; exact (φY.left_inv hy_fgsrc).symm
    rw [this, φY.left_inv hy_src]
  -- Restrict smoothness to `V ⊆ V₀`.
  have hg_smooth_V : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g V :=
    hg_smooth.mono inter_subset_left
  exact ⟨g, V, hV_open, hfx_V, hg_fx, hsection, hg_smooth_V⟩
