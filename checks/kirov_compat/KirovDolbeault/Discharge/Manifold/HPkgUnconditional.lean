/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.CriticalValueSetFinite
import KirovDolbeault.Discharge.Manifold.LocalSheetDataAtRegularValue
import KirovDolbeault.Discharge.Manifold.HLcUnconditional
import KirovDolbeault.Discharge.Manifold.FibresFiniteUnconditional
import KirovDolbeault.Discharge.Manifold.RegularValueExistsRegUnconditional
import KirovDolbeault.Discharge.Manifold.CriticalValuesFiniteGeneral

/-! # Unconditional `h_pkg` (item 9 close — composition chip)

Composes the landed unconditional ingredients into the analytic packaging
`h_pkg` consumed by `fibre_card_well_defined_at_regular_holds_of_h_pkg`
(`Manifold/HurwitzWellDefinedUnconditionalTopo.lean`).

We choose `C := criticalValuesGeneral f` directly so its identification is
preserved syntactically, and inline the disjointness proof (the same shape
as chip B's `critical_value_set_finite`, but stated for the concrete set so
the `IsLocallyConstant` clause downstream can refer to `Cᶜ` as
`(criticalValuesGeneral f)ᶜ`). -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace Jacobians.Discharge

namespace ContMDiff

namespace Degree

universe u v

/-- **Unconditional `h_pkg`.** -/
theorem h_pkg_holds_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
      ∃ (C : Set Y), C.Finite ∧
        (∀ w : RegularValueWitnessReg f, w.toWitness.value ∈ (Cᶜ : Set Y)) ∧
        IsLocallyConstant
          (fun y : (Cᶜ : Set Y) => (f ⁻¹' {y.val}).ncard) := by
  intro f hf hnc
  classical
  refine ⟨Jacobians.Discharge.Manifold.criticalValuesGeneral f,
    Jacobians.Discharge.Manifold.criticalValues_finite_general f hf hnc, ?_, ?_⟩
  · -- Witness-in-complement: replicate chip B's contradiction shape against
    -- the concrete set.  This is the same argument as
    -- `critical_value_set_finite` but applied to our explicit `C` so the
    -- syntactic identification holds.
    intro w hv_in
    obtain ⟨x, hx_crit, hfx_eq⟩ := hv_in
    have hx_pre : x ∈ f ⁻¹' {w.toWitness.value} := hfx_eq
    have h_deriv_ne :
        deriv ((chartAt ℂ w.toWitness.value) ∘ f ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x) ≠ 0 :=
      w.is_regular x hx_pre
    have h_deriv_ne' :
        deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x) ≠ 0 := by
      have hvfx : w.toWitness.value = f x := hfx_eq.symm
      rw [hvfx] at h_deriv_ne
      exact h_deriv_ne
    -- Analyticity at the chart image.
    have hFA_at_x :
        AnalyticAt ℂ ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x) :=
      Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback
        hf x
    -- Planar local injectivity from deriv ≠ 0.
    have h_inj_F :
        ∃ U' ∈ 𝓝 ((chartAt ℂ x) x),
          Set.InjOn
            ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) U' :=
      Jacobians.Discharge.Manifold.injOn_nhds_of_deriv_ne_zero hFA_at_x h_deriv_ne'
    -- Lift to a manifold neighbourhood of x.  Inline the chart left-inverse
    -- argument (≈30 LOC; mirrors chip B's private
    -- `injOn_f_nhds_of_injOn_chart_pullback`).
    have h_inj_f : ∃ U ∈ 𝓝 x, Set.InjOn f U := by
      set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
      set d : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with hd_def
      set F : ℂ → ℂ := d ∘ f ∘ c.symm with hF_def
      have hxc : x ∈ c.source := mem_chart_source ℂ x
      have hfx_d : f x ∈ d.source := mem_chart_source ℂ (f x)
      obtain ⟨U', hU'_nhds, hU'_inj⟩ := h_inj_F
      have hc_cont : ContinuousOn c c.source := c.continuousOn_toFun
      obtain ⟨U'_open, hU'_open_open, hU'_open_sub, hcx_U'_open⟩ :
          ∃ U_o, IsOpen U_o ∧ U_o ⊆ U' ∧ c x ∈ U_o := by
        obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU'_nhds
        exact ⟨W, hW_open, hW_sub, hxW⟩
      set U : Set X := (c.source ∩ f ⁻¹' d.source) ∩ c ⁻¹' U'_open with hU_def
      have hU_open' : IsOpen U := by
        have hopen1 : IsOpen (c.source ∩ f ⁻¹' d.source) :=
          c.open_source.inter (d.open_source.preimage hf.continuous)
        have hopen2 : IsOpen (c.source ∩ c ⁻¹' U'_open) :=
          hc_cont.isOpen_inter_preimage c.open_source hU'_open_open
        have h_eq : U =
            (c.source ∩ f ⁻¹' d.source) ∩ (c.source ∩ c ⁻¹' U'_open) := by
          ext y
          constructor
          · rintro ⟨⟨hy_c, hy_fd⟩, hy_pre⟩
            exact ⟨⟨hy_c, hy_fd⟩, ⟨hy_c, hy_pre⟩⟩
          · rintro ⟨⟨hy_c, hy_fd⟩, ⟨_, hy_pre⟩⟩
            exact ⟨⟨hy_c, hy_fd⟩, hy_pre⟩
        rw [h_eq]; exact hopen1.inter hopen2
      have hx_U : x ∈ U :=
        ⟨⟨hxc, hfx_d⟩, by show c x ∈ U'_open; exact hcx_U'_open⟩
      refine ⟨U, hU_open'.mem_nhds hx_U, ?_⟩
      intro y₁ hy₁ y₂ hy₂ hf_eq
      obtain ⟨⟨hy₁_subc, hy₁_fd⟩, hy₁_pre⟩ := hy₁
      obtain ⟨⟨hy₂_subc, hy₂_fd⟩, hy₂_pre⟩ := hy₂
      have hcy₁_U' : c y₁ ∈ U' := hU'_open_sub hy₁_pre
      have hcy₂_U' : c y₂ ∈ U' := hU'_open_sub hy₂_pre
      have h_inv_y₁ : c.symm (c y₁) = y₁ := c.left_inv hy₁_subc
      have h_inv_y₂ : c.symm (c y₂) = y₂ := c.left_inv hy₂_subc
      have hF_at_y₁ : F (c y₁) = d (f y₁) := by
        show (d ∘ f ∘ c.symm) (c y₁) = d (f y₁)
        simp [Function.comp, h_inv_y₁]
      have hF_at_y₂ : F (c y₂) = d (f y₂) := by
        show (d ∘ f ∘ c.symm) (c y₂) = d (f y₂)
        simp [Function.comp, h_inv_y₂]
      have hF_eq : F (c y₁) = F (c y₂) := by
        rw [hF_at_y₁, hF_at_y₂, hf_eq]
      have hcy_eq : c y₁ = c y₂ := hU'_inj hcy₁_U' hcy₂_U' hF_eq
      have h_inj_c : Set.InjOn c c.source := c.injOn
      exact h_inj_c hy₁_subc hy₂_subc hcy_eq
    exact hx_crit h_inj_f
  · -- Local constancy on Cᶜ via LocalSheetData supplier + HLcUnconditional.
    have h_fib_all : ∀ y : Y, (f ⁻¹' {y}).Finite :=
      fibres_finite_statement_unconditional f hf hnc
    have h_fib :
        ∀ y ∈ ((Jacobians.Discharge.Manifold.criticalValuesGeneral f)ᶜ : Set Y),
          (f ⁻¹' {y}).Finite := fun y _ => h_fib_all y
    have h_sheets :
        ∀ y ∈ ((Jacobians.Discharge.Manifold.criticalValuesGeneral f)ᶜ : Set Y),
          ∀ x ∈ f ⁻¹' {y}, LocalSheetData f y x := by
      intro y hy_compl x hx
      have hy_not : y ∉ Jacobians.Discharge.Manifold.criticalValuesGeneral f := hy_compl
      have hx_eq : f x = y := hx
      have hx_not_crit : x ∉ Jacobians.Discharge.Manifold.criticalSetGeneral f := by
        intro hx_crit
        exact hy_not ⟨x, hx_crit, hx_eq⟩
      have h_inj_x : ∃ U ∈ 𝓝 x, Set.InjOn f U := by
        by_contra h_no
        exact hx_not_crit h_no
      have h_deriv_fx :
          deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
            ((chartAt ℂ x) x) ≠ 0 :=
        Jacobians.Discharge.ContMDiff.Degree.deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood
          hf hnc x h_inj_x
      have h_deriv_y :
          deriv ((chartAt ℂ y) ∘ f ∘ (chartAt ℂ x).symm)
            ((chartAt ℂ x) x) ≠ 0 := by
        rw [← hx_eq]; exact h_deriv_fx
      exact LocalSheetData.ofContMDiffMfderivNeZero
        (hf := hf.contMDiffAt) (hxy := hx) (h_deriv := h_deriv_y)
    exact h_lc_holds_for_subset_of_localSheets_supplier
      hf.continuous (Jacobians.Discharge.Manifold.criticalValuesGeneral f)
      h_fib h_sheets

end Degree

end ContMDiff

end Jacobians.Discharge

end

end
