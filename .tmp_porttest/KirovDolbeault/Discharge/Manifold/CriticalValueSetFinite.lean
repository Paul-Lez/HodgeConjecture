/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.CriticalValuesFiniteGeneral
import KirovDolbeault.Discharge.Manifold.CriticalSetDerivBridge
import KirovDolbeault.Discharge.Manifold.Degree

set_option autoImplicit true

/-! # `h_critical`: finite critical-value set containing every regular witness

This file (the **zzCritFin** chip) discharges the **`h_critical`** leg of the
`h_pkg` packaging consumed by
`fibre_card_well_defined_at_regular_holds_of_h_pkg` in
`Manifold/HurwitzWellDefinedUnconditionalTopo.lean`:

```
∃ C : Set Y, C.Finite ∧
  (∀ w : RegularValueWitnessReg f, w.toWitness.value ∈ (Cᶜ : Set Y))
```

The construction takes
`C := criticalValuesGeneral f`, finite by `criticalValues_finite_general`
(`Manifold/CriticalValuesFiniteGeneral.lean`).  Membership in the complement
for every `RegularValueWitnessReg f` is by contradiction: if
`w.toWitness.value = f x` with `x ∈ criticalSetGeneral f`, then `x` lies in
the preimage of `w.toWitness.value`, hence by `w.is_regular` the literal
chart pullback has nonzero derivative at `(chartAt ℂ x) x`.  The planar
forward bridge `injOn_nhds_of_deriv_ne_zero` (ZZ99,
`Manifold/CriticalSetDerivBridge.lean`) then produces a planar neighbourhood
on which the chart pullback is injective; lifting through the chart
homeomorphism gives `∃ U ∈ 𝓝 x, Set.InjOn f U`, contradicting
`x ∈ criticalSetGeneral f`.

No gaps, no `axiom`, no signature changes to consumer files. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace Jacobians.Discharge

namespace Manifold

universe u v

/-- **Planar-to-manifold lift of local injectivity.**  If the literal chart
pullback `F = (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm` is injective on a
planar neighbourhood of `(chartAt ℂ x) x`, then `f` is injective on a
manifold neighbourhood of `x`.

This is the contrapositive of the `(∃ U ∈ 𝓝 x, InjOn f U) →
(∃ U' ∈ 𝓝 (c x), InjOn F U')` lift used in
`RegularValueExistsRegUnconditional.deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood`. -/
private lemma injOn_f_nhds_of_injOn_chart_pullback
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (hf_cont : Continuous f) (x : X)
    (h_inj_F :
      ∃ U' ∈ 𝓝 ((chartAt ℂ x) x),
        Set.InjOn
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) U') :
    ∃ U ∈ 𝓝 x, Set.InjOn f U := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
  set d : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with hd_def
  set F : ℂ → ℂ := d ∘ f ∘ c.symm with hF_def
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hfx_d : f x ∈ d.source := mem_chart_source ℂ (f x)
  obtain ⟨U', hU'_nhds, hU'_inj⟩ := h_inj_F
  -- Pull back U' through c (continuous on c.source), and intersect with
  -- c.source ∩ f ⁻¹' d.source so that the chart inverse identities hold.
  have hc_cont : ContinuousOn c c.source := c.continuousOn_toFun
  obtain ⟨U'_open, hU'_open_open, hU'_open_sub, hcx_U'_open⟩ :
      ∃ U_o, IsOpen U_o ∧ U_o ⊆ U' ∧ c x ∈ U_o := by
    obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU'_nhds
    exact ⟨W, hW_open, hW_sub, hxW⟩
  set U : Set X := (c.source ∩ f ⁻¹' d.source) ∩ c ⁻¹' U'_open with hU_def
  have hU_open' : IsOpen U := by
    have hopen1 : IsOpen (c.source ∩ f ⁻¹' d.source) :=
      c.open_source.inter (d.open_source.preimage hf_cont)
    have hopen2 : IsOpen (c.source ∩ c ⁻¹' U'_open) :=
      hc_cont.isOpen_inter_preimage c.open_source hU'_open_open
    have h_eq : U = (c.source ∩ f ⁻¹' d.source) ∩ (c.source ∩ c ⁻¹' U'_open) := by
      ext y
      constructor
      · rintro ⟨⟨hy_c, hy_fd⟩, hy_pre⟩
        exact ⟨⟨hy_c, hy_fd⟩, ⟨hy_c, hy_pre⟩⟩
      · rintro ⟨⟨hy_c, hy_fd⟩, ⟨_, hy_pre⟩⟩
        exact ⟨⟨hy_c, hy_fd⟩, hy_pre⟩
    rw [h_eq]
    exact hopen1.inter hopen2
  -- Membership of x.
  have hx_U : x ∈ U := by
    refine ⟨⟨hxc, hfx_d⟩, ?_⟩
    show c x ∈ U'_open
    exact hcx_U'_open
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

/-- **zzCritFin headline.**  For non-constant analytic `f : X → Y` between
compact connected complex 1-manifolds, the set of critical values is finite
and contains no value of any `RegularValueWitnessReg f`.

This is the `h_critical` ingredient of the `h_pkg` packaging in
`HurwitzWellDefinedUnconditionalTopo.fibre_card_well_defined_at_regular_holds_of_h_pkg`.
-/
theorem critical_value_set_finite
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap f) :
    ∃ C : Set Y, C.Finite ∧
      (∀ w : Jacobians.Discharge.ContMDiff.RegularValueWitnessReg f,
        w.toWitness.value ∈ (Cᶜ : Set Y)) := by
  classical
  refine ⟨criticalValuesGeneral f, criticalValues_finite_general f hf hnc, ?_⟩
  intro w hv_in
  -- Suppose value ∈ criticalValuesGeneral f.  Then value = f x for some
  -- x ∈ criticalSetGeneral f.  By w.is_regular, the chart-pullback deriv
  -- at (chartAt ℂ x) x is nonzero; by the planar→manifold lift this means
  -- f is locally injective at x, contradicting x ∈ criticalSetGeneral f.
  obtain ⟨x, hx_crit, hfx_eq⟩ := hv_in
  -- x ∈ f ⁻¹' {w.toWitness.value}.
  have hx_pre : x ∈ f ⁻¹' {w.toWitness.value} := hfx_eq
  -- Regularity certificate at x.
  have h_deriv_ne :
      deriv ((chartAt ℂ w.toWitness.value) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 :=
    w.is_regular x hx_pre
  -- Substitute w.toWitness.value = f x.
  have h_deriv_ne' :
      deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 := by
    have : w.toWitness.value = f x := hfx_eq.symm
    rw [this] at h_deriv_ne
    exact h_deriv_ne
  -- Analyticity of F at (chartAt ℂ x) x (ZZ24).
  have hFA_at_x :
      AnalyticAt ℂ ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback
      hf x
  -- Planar: deriv ≠ 0 ⇒ locally injective.
  have h_inj_F :
      ∃ U' ∈ 𝓝 ((chartAt ℂ x) x),
        Set.InjOn
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) U' :=
    injOn_nhds_of_deriv_ne_zero hFA_at_x h_deriv_ne'
  -- Lift to manifold.
  have h_inj_f : ∃ U ∈ 𝓝 x, Set.InjOn f U :=
    injOn_f_nhds_of_injOn_chart_pullback hf.continuous x h_inj_F
  -- Contradiction with hx_crit : x ∈ criticalSetGeneral f.
  exact hx_crit h_inj_f

end Manifold

end Jacobians.Discharge

end

end
