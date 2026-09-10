/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.HurwitzPatchingDataConstruction
import KirovDolbeault.Discharge.Manifold.ContMDiffOmegaAnalytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

set_option autoImplicit true

/-! # `LocalSheetData` from `ContMDiffAt … ω` + chart-pullback non-degenerate derivative (ZZ169)

This file produces `LocalSheetData f y₀ x₀` (defined in
`HurwitzPatchingDataConstruction.lean`) from
`ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x₀` plus the chart-pullback non-degeneracy
hypothesis
`deriv ((chartAt ℂ y₀) ∘ f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0`.

## Strategy

ZZ24's bridge gives `AnalyticAt ℂ F z₀` where `F = eY ∘ f ∘ eX.symm` and
`z₀ = eX x₀`. Combined with the non-degenerate-derivative hypothesis we apply
the inverse function theorem inline (rather than via ZZ152's externally-stated
wrapper) so that we keep the underlying `OpenPartialHomeomorph`. This is what
supplies the *global* continuity of `φ.symm` on its target, needed for the
`ContinuousOn g V` field of `LocalSheetData`.

Concretely:

* `hsd : HasStrictDerivAt F (deriv F z₀) z₀` via `AnalyticAt.hasStrictDerivAt`,
* `hsfd : HasStrictFDerivAt F E z₀` via `HasStrictDerivAt.hasStrictFDerivAt_equiv`
  with the unit equivalence built from `deriv F z₀ ≠ 0`,
* `φ : OpenPartialHomeomorph ℂ ℂ := hsfd.toOpenPartialHomeomorph F` carries
  `(φ : ℂ → ℂ) = F` on `φ.source` and `ContinuousOn φ.symm φ.target` for free.

Then we shrink:

* `V₀` open in `X`, `V₀ ⊆ eX.source ∩ f ⁻¹' eY.source`, `x₀ ∈ V₀`,
* `S := eX '' V₀` open in `ℂ`, `z₀ ∈ S`, `S ⊆ eX.target`,
* `Vc'` open in `ℂ`, `Vc' ⊆ φ.target ∩ eY.target ∩ φ.symm ⁻¹' (S ∩ φ.source)`,
* `Uc'` open in `ℂ`, `Uc' ⊆ φ.source ∩ S ∩ φ ⁻¹' Vc'`.

Transport: `U := eX.symm '' Uc'`, `V := eY.symm '' Vc'`,
`g := eX.symm ∘ φ.symm ∘ eY`.

## Anti-cheat

* No `axiom`, no gaps.
* No signature change to any pre-existing definition or theorem.
* Adds one new file imported into the manifest.
-/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge

universe u v

namespace LocalSheetData

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **`LocalSheetData` from `ContMDiffAt … ω` + non-degenerate chart-pullback
derivative.** -/
noncomputable def ofContMDiffMfderivNeZero
    {f : X → Y} {x₀ : X} {y₀ : Y}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x₀)
    (hxy : f x₀ = y₀)
    (h_deriv :
      deriv ((chartAt ℂ y₀) ∘ f ∘ (chartAt ℂ x₀).symm)
          ((chartAt ℂ x₀) x₀) ≠ 0) :
    LocalSheetData f y₀ x₀ := by
  classical
  -- Substitute `y₀ := f x₀` everywhere via the hypothesis `hxy : f x₀ = y₀`.
  -- `cases hxy` would fail (Type-valued goal); we use `subst` on the variable
  -- `y₀`. Since `hxy : f x₀ = y₀`, `subst y₀` replaces `y₀` with `f x₀`
  -- throughout the goal and remaining hypotheses.
  subst y₀
  -- Now `chartAt ℂ y₀` has become `chartAt ℂ (f x₀)`, matching the bridge output.
  -- Abbreviations.
  set eX : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with heX
  set eY : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x₀) with heY
  have hx₀S : x₀ ∈ eX.source := mem_chart_source ℂ x₀
  have hy₀S : f x₀ ∈ eY.source := mem_chart_source ℂ (f x₀)
  have hfx₀S : f x₀ ∈ eY.source := hy₀S
  have hf_cont : ContinuousAt f x₀ := hf.continuousAt
  set F : ℂ → ℂ := (eY) ∘ f ∘ eX.symm with hFdef
  set z₀ : ℂ := eX x₀ with hz₀def
  set w₀ : ℂ := eY (f x₀) with hw₀def
  have hz₀_target : z₀ ∈ eX.target := eX.map_source hx₀S
  have hw₀_target : w₀ ∈ eY.target := eY.map_source hy₀S
  have hFz₀ : F z₀ = w₀ := by
    show eY (f (eX.symm (eX x₀))) = eY (f x₀)
    rw [eX.left_inv hx₀S]
  -- Analyticity of `F` at `z₀` via ZZ24's bridge.
  have hFA : AnalyticAt ℂ F z₀ :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiffAt_omega_analyticAt_chart_pullback hf
  -- Non-degenerate derivative of `F` at `z₀` (definitionally identical to `h_deriv`).
  have h_deriv_F : deriv F z₀ ≠ 0 := h_deriv
  -- Build the biholomorphism `φ : OpenPartialHomeomorph ℂ ℂ` inline.
  have hsd : HasStrictDerivAt F (deriv F z₀) z₀ := hFA.hasStrictDerivAt
  have hsfd : HasStrictFDerivAt F
      (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv F z₀) h_deriv_F) :
        ℂ →L[ℂ] ℂ) z₀ :=
    hsd.hasStrictFDerivAt_equiv h_deriv_F
  set φ : OpenPartialHomeomorph ℂ ℂ := hsfd.toOpenPartialHomeomorph F with hφdef
  have hz₀_φsrc : z₀ ∈ φ.source := hsfd.mem_toOpenPartialHomeomorph_source
  have h_φ_coe : (φ : ℂ → ℂ) = F := hsfd.toOpenPartialHomeomorph_coe
  have hFz₀_φtgt : F z₀ ∈ φ.target := hsfd.image_mem_toOpenPartialHomeomorph_target
  have hw₀_φtgt : w₀ ∈ φ.target := hFz₀ ▸ hFz₀_φtgt
  have hφ_symm_cont : ContinuousOn (φ.symm : ℂ → ℂ) φ.target := φ.continuousOn_invFun
  -- Choose explicit open V₀.
  have hYnhd : eY.source ∈ 𝓝 (f x₀) := eY.open_source.mem_nhds hfx₀S
  have hpreimage_nhd : f ⁻¹' eY.source ∈ 𝓝 x₀ := hf_cont hYnhd
  have hexS_nhd : eX.source ∈ 𝓝 x₀ := eX.open_source.mem_nhds hx₀S
  have hcombined_nhd : eX.source ∩ f ⁻¹' eY.source ∈ 𝓝 x₀ :=
    Filter.inter_mem hexS_nhd hpreimage_nhd
  -- Use `Classical.choose` since the goal `LocalSheetData …` is Type-valued and
  -- `obtain ⟨…⟩ := mem_nhds_iff.mp …` cannot eliminate `Exists` into a non-Prop motive.
  let V₀ : Set X := Classical.choose (mem_nhds_iff.mp hcombined_nhd)
  have hV₀_spec := Classical.choose_spec (mem_nhds_iff.mp hcombined_nhd)
  have hV₀_sub : V₀ ⊆ eX.source ∩ f ⁻¹' eY.source := hV₀_spec.1
  have hV₀_open : IsOpen V₀ := hV₀_spec.2.1
  have hxV₀ : x₀ ∈ V₀ := hV₀_spec.2.2
  have hV₀_subS : V₀ ⊆ eX.source := fun z hz => (hV₀_sub hz).1
  have hV₀_subPre : V₀ ⊆ f ⁻¹' eY.source := fun z hz => (hV₀_sub hz).2
  -- `S := eX '' V₀`.
  set S : Set ℂ := eX '' V₀ with hSdef
  have hS_open : IsOpen S := by
    have hSeq : S = eX.target ∩ eX.symm ⁻¹' V₀ := by
      ext z
      constructor
      · rintro ⟨v, hvV₀, rfl⟩
        refine ⟨eX.map_source (hV₀_subS hvV₀), ?_⟩
        show eX.symm (eX v) ∈ V₀
        rw [eX.left_inv (hV₀_subS hvV₀)]; exact hvV₀
      · rintro ⟨hz_target, hz_pre⟩
        exact ⟨eX.symm z, hz_pre, eX.right_inv hz_target⟩
    rw [hSeq]; exact eX.isOpen_inter_preimage_symm hV₀_open
  have hz₀_S : z₀ ∈ S := ⟨x₀, hxV₀, rfl⟩
  have hS_target : S ⊆ eX.target := by
    rintro z ⟨v, hvV₀, rfl⟩; exact eX.map_source (hV₀_subS hvV₀)
  have hS_symm_in_pre : ∀ z ∈ S, eX.symm z ∈ f ⁻¹' eY.source := by
    rintro z ⟨v, hvV₀, rfl⟩
    rw [eX.left_inv (hV₀_subS hvV₀)]; exact hV₀_subPre hvV₀
  have hS_symm_in_eXsrc : ∀ z ∈ S, eX.symm z ∈ eX.source := fun z hz =>
    eX.map_target (hS_target hz)
  -- For z ∈ S ∩ φ.source we have F z = (φ : ℂ → ℂ) z.
  -- φ.symm w₀ = z₀.
  have hφsymm_w₀ : φ.symm w₀ = z₀ := by
    have h1 : φ.symm ((φ : ℂ → ℂ) z₀) = z₀ := φ.left_inv hz₀_φsrc
    have h2 : (φ : ℂ → ℂ) z₀ = F z₀ := by rw [h_φ_coe]
    rw [h2, hFz₀] at h1; exact h1
  have hφsymm_cont_w₀ : ContinuousAt (φ.symm : ℂ → ℂ) w₀ :=
    hφ_symm_cont.continuousAt (φ.open_target.mem_nhds hw₀_φtgt)
  -- Build Vc'.
  have hSφsrc_nhds : S ∩ φ.source ∈ 𝓝 z₀ :=
    Filter.inter_mem (hS_open.mem_nhds hz₀_S) (φ.open_source.mem_nhds hz₀_φsrc)
  have hVc_φS_pre : (φ.symm : ℂ → ℂ) ⁻¹' (S ∩ φ.source) ∈ 𝓝 w₀ :=
    ContinuousAt.preimage_mem_nhds hφsymm_cont_w₀
      (by rw [hφsymm_w₀]; exact hSφsrc_nhds)
  have hφ_target_nhds : φ.target ∈ 𝓝 w₀ := φ.open_target.mem_nhds hw₀_φtgt
  have heY_target_nhds : eY.target ∈ 𝓝 w₀ := eY.open_target.mem_nhds hw₀_target
  have hVc'_nhds_full :
      φ.target ∩ eY.target ∩ (φ.symm : ℂ → ℂ) ⁻¹' (S ∩ φ.source) ∈ 𝓝 w₀ :=
    Filter.inter_mem (Filter.inter_mem hφ_target_nhds heY_target_nhds) hVc_φS_pre
  let Vc' : Set ℂ := Classical.choose (mem_nhds_iff.mp hVc'_nhds_full)
  have hVc'_spec := Classical.choose_spec (mem_nhds_iff.mp hVc'_nhds_full)
  have hVc'_sub : Vc' ⊆ φ.target ∩ eY.target ∩ (φ.symm : ℂ → ℂ) ⁻¹' (S ∩ φ.source) :=
    hVc'_spec.1
  have hVc'_open : IsOpen Vc' := hVc'_spec.2.1
  have hw₀_Vc' : w₀ ∈ Vc' := hVc'_spec.2.2
  have hVc'_subφT : Vc' ⊆ φ.target := fun w hw => (hVc'_sub hw).1.1
  have hVc'_subeYT : Vc' ⊆ eY.target := fun w hw => (hVc'_sub hw).1.2
  have hVc'_symm_S : ∀ w ∈ Vc', φ.symm w ∈ S := fun w hw => ((hVc'_sub hw).2).1
  have hVc'_symm_φsrc : ∀ w ∈ Vc', φ.symm w ∈ φ.source := fun w hw => ((hVc'_sub hw).2).2
  -- Build Uc' := φ.source ∩ S ∩ φ ⁻¹' Vc'.
  have hφVc'_open : IsOpen (φ.source ∩ φ ⁻¹' Vc') :=
    φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source hVc'_open
  set Uc' : Set ℂ := (φ.source ∩ φ ⁻¹' Vc') ∩ S with hUc'def
  have hUc'_open : IsOpen Uc' := hφVc'_open.inter hS_open
  have hz₀_Uc' : z₀ ∈ Uc' := by
    refine ⟨⟨hz₀_φsrc, ?_⟩, hz₀_S⟩
    show (φ : ℂ → ℂ) z₀ ∈ Vc'
    rw [h_φ_coe, hFz₀]; exact hw₀_Vc'
  have hUc'_subφsrc : Uc' ⊆ φ.source := fun z hz => hz.1.1
  have hUc'_subφVc' : Uc' ⊆ φ ⁻¹' Vc' := fun z hz => hz.1.2
  have hUc'_subS : Uc' ⊆ S := fun z hz => hz.2
  have hUc'_subTarget : Uc' ⊆ eX.target := fun z hz => hS_target hz.2
  -- F = (φ : ℂ → ℂ) on φ.source.
  have hF_eq_φ : ∀ z ∈ φ.source, F z = (φ : ℂ → ℂ) z := fun z _ => by
    rw [h_φ_coe]
  -- Define U, V, g.
  set U : Set X := eX.symm '' Uc' with hUdef
  set V : Set Y := eY.symm '' Vc' with hVdef
  set g : Y → X := fun y => eX.symm (φ.symm (eY y)) with hgdef
  -- U open: U = eX.source ∩ eX ⁻¹' Uc'.
  have hU_eq : U = eX.source ∩ eX ⁻¹' Uc' := by
    ext x
    constructor
    · rintro ⟨z, hzUc', rfl⟩
      have hz_target : z ∈ eX.target := hUc'_subTarget hzUc'
      refine ⟨eX.map_target hz_target, ?_⟩
      show eX (eX.symm z) ∈ Uc'
      rw [eX.right_inv hz_target]; exact hzUc'
    · rintro ⟨hxS_, hx_pre⟩
      exact ⟨eX x, hx_pre, eX.left_inv hxS_⟩
  have hU_open : IsOpen U := by
    rw [hU_eq]
    exact eX.continuousOn_toFun.isOpen_inter_preimage eX.open_source hUc'_open
  have hx₀_U : x₀ ∈ U := ⟨z₀, hz₀_Uc', eX.left_inv hx₀S⟩
  -- V open.
  have hV_eq : V = eY.source ∩ eY ⁻¹' Vc' := by
    ext y
    constructor
    · rintro ⟨w, hwVc', rfl⟩
      have hw_target : w ∈ eY.target := hVc'_subeYT hwVc'
      refine ⟨eY.map_target hw_target, ?_⟩
      show eY (eY.symm w) ∈ Vc'
      rw [eY.right_inv hw_target]; exact hwVc'
    · rintro ⟨hyS_, hy_pre⟩
      exact ⟨eY y, hy_pre, eY.left_inv hyS_⟩
  have hV_open : IsOpen V := by
    rw [hV_eq]
    exact eY.continuousOn_toFun.isOpen_inter_preimage eY.open_source hVc'_open
  have hy₀_V : f x₀ ∈ V := ⟨w₀, hw₀_Vc', eY.left_inv hy₀S⟩
  -- MapsTo f U V.
  have hf_mapsTo : MapsTo f U V := by
    rintro x ⟨z, hzUc', hzx⟩
    -- F z = (φ : ℂ → ℂ) z ∈ Vc' (from hUc'_subφVc').
    have hzφsrc : z ∈ φ.source := hUc'_subφsrc hzUc'
    have hφz_in : (φ : ℂ → ℂ) z ∈ Vc' := hUc'_subφVc' hzUc'
    have hFz_in : F z ∈ Vc' := by rw [hF_eq_φ z hzφsrc]; exact hφz_in
    have hSz : z ∈ S := hUc'_subS hzUc'
    have hf_in_eY : f (eX.symm z) ∈ eY.source := hS_symm_in_pre z hSz
    refine ⟨F z, hFz_in, ?_⟩
    show eY.symm (eY (f (eX.symm z))) = f x
    rw [eY.left_inv hf_in_eY, ← hzx]
  -- ContinuousOn g V.
  have hV_subYsrc : V ⊆ eY.source := by rw [hV_eq]; exact fun y hy => hy.1
  have h_eY_cont_V : ContinuousOn (eY : Y → ℂ) V :=
    eY.continuousOn_toFun.mono hV_subYsrc
  have h_eY_mapsTo_Vc' : MapsTo (eY : Y → ℂ) V Vc' := by
    rintro y ⟨w, hwVc', rfl⟩
    show eY (eY.symm w) ∈ Vc'
    rw [eY.right_inv (hVc'_subeYT hwVc')]; exact hwVc'
  have h_φsymm_cont_Vc' : ContinuousOn (φ.symm : ℂ → ℂ) Vc' :=
    hφ_symm_cont.mono hVc'_subφT
  have h_φsymm_mapsTo : MapsTo (φ.symm : ℂ → ℂ) Vc' (S ∩ φ.source) := by
    intro w hw
    exact ⟨hVc'_symm_S w hw, hVc'_symm_φsrc w hw⟩
  have hSφs_subTarget : S ∩ φ.source ⊆ eX.target := fun z hz => hS_target hz.1
  have h_eXsymm_cont : ContinuousOn (eX.symm : ℂ → X) (S ∩ φ.source) :=
    eX.continuousOn_invFun.mono hSφs_subTarget
  have hg_continuousOn : ContinuousOn g V := by
    have h12 : ContinuousOn ((φ.symm : ℂ → ℂ) ∘ (eY : Y → ℂ)) V :=
      h_φsymm_cont_Vc'.comp h_eY_cont_V h_eY_mapsTo_Vc'
    have h12_mapsTo : MapsTo ((φ.symm : ℂ → ℂ) ∘ (eY : Y → ℂ)) V (S ∩ φ.source) :=
      h_φsymm_mapsTo.comp h_eY_mapsTo_Vc'
    exact h_eXsymm_cont.comp h12 h12_mapsTo
  -- MapsTo g V U.
  -- For y ∈ V = eY.symm '' Vc', y = eY.symm w with w ∈ Vc'.
  -- g y = eX.symm (φ.symm (eY (eY.symm w))) = eX.symm (φ.symm w).
  -- We need g y ∈ U = eX.symm '' Uc'. Take preimage z := φ.symm w. Need
  -- z ∈ Uc' = (φ.source ∩ φ⁻¹' Vc') ∩ S. We have z ∈ φ.source and z ∈ S.
  -- And φ z = φ (φ.symm w) = w (since w ∈ φ.target), so z ∈ φ⁻¹' Vc'.
  have hg_mapsTo : MapsTo g V U := by
    rintro y ⟨w, hwVc', rfl⟩
    have hw_target : w ∈ eY.target := hVc'_subeYT hwVc'
    have hw_φtgt : w ∈ φ.target := hVc'_subφT hwVc'
    set z := φ.symm w with hzdef
    have hz_φsrc : z ∈ φ.source := hVc'_symm_φsrc w hwVc'
    have hz_S : z ∈ S := hVc'_symm_S w hwVc'
    have hφz : (φ : ℂ → ℂ) z = w := φ.right_inv hw_φtgt
    have hz_Uc' : z ∈ Uc' := ⟨⟨hz_φsrc, by show (φ : ℂ → ℂ) z ∈ Vc'; rw [hφz]; exact hwVc'⟩, hz_S⟩
    refine ⟨z, hz_Uc', ?_⟩
    show eX.symm z = eX.symm (φ.symm (eY (eY.symm w)))
    rw [eY.right_inv hw_target]
  -- LeftInvOn g f U.
  -- For x ∈ U, x = eX.symm z with z ∈ Uc'. Then f x = f (eX.symm z), and
  -- g (f x) = eX.symm (φ.symm (eY (f (eX.symm z)))) = eX.symm (φ.symm (F z))
  --        = eX.symm (φ.symm (φ z)) = eX.symm z = x.
  have hg_leftInvOn : LeftInvOn g f U := by
    rintro x ⟨z, hzUc', rfl⟩
    have hzφsrc : z ∈ φ.source := hUc'_subφsrc hzUc'
    have hSz : z ∈ S := hUc'_subS hzUc'
    have hf_in_eY : f (eX.symm z) ∈ eY.source := hS_symm_in_pre z hSz
    show eX.symm (φ.symm (eY (f (eX.symm z)))) = eX.symm z
    have hF_eq : F z = (φ : ℂ → ℂ) z := hF_eq_φ z hzφsrc
    -- eY (f (eX.symm z)) = F z (definition)
    -- φ.symm (F z) = φ.symm (φ z) = z
    have hcomp : φ.symm (eY (f (eX.symm z))) = z := by
      show φ.symm ((eY : Y → ℂ) (f ((eX.symm : ℂ → X) z))) = z
      have : (eY : Y → ℂ) (f ((eX.symm : ℂ → X) z)) = F z := rfl
      rw [this, hF_eq]
      exact φ.left_inv hzφsrc
    rw [hcomp]
  -- RightInvOn g f V.
  -- For y ∈ V = eY.symm '' Vc', y = eY.symm w with w ∈ Vc'. Then
  -- g y = eX.symm (φ.symm w). Let z := φ.symm w. Then z ∈ S ∩ φ.source.
  -- f (g y) = f (eX.symm z), and eY (f (eX.symm z)) = F z = φ z = w.
  -- Since f (eX.symm z) ∈ eY.source, we have f (eX.symm z) = eY.symm w = y.
  have hg_rightInvOn : RightInvOn g f V := by
    rintro y ⟨w, hwVc', rfl⟩
    have hw_target : w ∈ eY.target := hVc'_subeYT hwVc'
    have hw_φtgt : w ∈ φ.target := hVc'_subφT hwVc'
    set z := φ.symm w with hzdef
    have hz_φsrc : z ∈ φ.source := hVc'_symm_φsrc w hwVc'
    have hz_S : z ∈ S := hVc'_symm_S w hwVc'
    have hf_in_eY : f (eX.symm z) ∈ eY.source := hS_symm_in_pre z hz_S
    have hφz : (φ : ℂ → ℂ) z = w := φ.right_inv hw_φtgt
    have hF_eq : F z = (φ : ℂ → ℂ) z := hF_eq_φ z hz_φsrc
    -- f (g (eY.symm w)) = f (eX.symm (φ.symm (eY (eY.symm w))))
    --                  = f (eX.symm (φ.symm w))         (eY.right_inv)
    --                  = f (eX.symm z)
    show f (g (eY.symm w)) = eY.symm w
    show f (eX.symm (φ.symm (eY (eY.symm w)))) = eY.symm w
    rw [eY.right_inv hw_target]
    -- Now goal: f (eX.symm (φ.symm w)) = eY.symm w, i.e., f (eX.symm z) = eY.symm w.
    -- Apply eY to both: eY (f (eX.symm z)) = F z = φ z = w; then eY.symm of both.
    have hkey : eY (f (eX.symm z)) = w := by
      show F z = w; rw [hF_eq, hφz]
    -- f (eX.symm z) = eY.symm (eY (f (eX.symm z))) = eY.symm w.
    have hLHS : f (eX.symm z) = eY.symm (eY (f (eX.symm z))) :=
      (eY.left_inv hf_in_eY).symm
    rw [hLHS, hkey]
  -- Assemble.
  exact
    { U := U
      U_open := hU_open
      mem_U := hx₀_U
      V := V
      V_open := hV_open
      mem_V := hy₀_V
      mapsTo := hf_mapsTo
      g := g
      g_continuousOn := hg_continuousOn
      g_mapsTo := hg_mapsTo
      leftInvOn := hg_leftInvOn
      rightInvOn := hg_rightInvOn }

end LocalSheetData

end Jacobians.Discharge

end
