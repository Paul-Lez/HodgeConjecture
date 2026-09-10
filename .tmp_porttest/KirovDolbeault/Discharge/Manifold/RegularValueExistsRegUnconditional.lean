/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.Degree
import KirovDolbeault.Discharge.Manifold.RegularValueExistsUnconditional
import KirovDolbeault.Discharge.Manifold.CriticalValuesFiniteGeneral
import KirovDolbeault.Discharge.Manifold.FibresFiniteUnconditional
import KirovDolbeault.Discharge.Manifold.ContMDiffOmegaAnalytic
import KirovDolbeault.Discharge.Manifold.CriticalSetDerivBridge
import Mathlib.Topology.Separation.Basic

set_option autoImplicit true


/-! # Unconditional discharge of `Nonempty (RegularValueWitnessReg f)`

This file (the **RegFix** chip) ships the unconditional existence of a
`RegularValueWitnessReg f` for every non-constant analytic
`f : X → Y` between compact connected complex 1-manifolds.

This closes the architectural defect in `degreeFiber`:
`Classical.choice` over `Nonempty (RegularValueWitness f)` could pick
a branch-point witness whose fibre cardinality is strictly smaller
than the topological degree. By switching `degreeFiber`'s body to
choose from `Nonempty (RegularValueWitnessReg f)` (whose chosen value
carries the chart-pullback-derivative-nonzero certificate), the
fallback `else 0` branch never fires for non-constant `f` — provided
this file's existence theorem is in scope.

## Composition

* `criticalValues_finite_general` (CV-Gen): the critical-value set
  `criticalValuesGeneral f` is finite for non-constant analytic `f`.
* `fibres_finite_statement_unconditional` (ZZ48): every fibre of
  a non-constant analytic `f` is finite.
* `Y` is infinite, derived from `ChartedSpace ℂ Y` + `T2Space Y` +
  non-emptiness.

Pick a value `y₀ ∈ Y \ criticalValuesGeneral f` (non-empty because
critical values are finite and `Y` is infinite). At every preimage
`x ∈ f ⁻¹' {y₀}`, `x ∉ criticalSetGeneral f`, so the chart-pullback of
`f` at `x` is locally injective. By the planar bridge ZZ99
(`notInjOn_iff_deriv_zero_of_analytic_of_order`), local injectivity at
an analytic point forces the derivative to be nonzero. Combined with
fibre finiteness, this delivers a `RegularValueWitnessReg f`.

No gaps, no `axiom`. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## Auxiliary: connected complex 1-manifolds are infinite

`Y` carries `ChartedSpace ℂ Y` + `T2Space Y` + `ConnectedSpace Y`. A chart
at any point has open target in `ℂ`. Open sets in `ℂ` containing a point
are infinite (by `infinite_of_mem_nhds` on `ℂ`). Hence `Y` is infinite. -/

/-- **`ℂ` has nonbot punctured neighborhoods.** For any `z : ℂ`, the
filter `𝓝[≠] z` is non-trivial. This follows from `ℂ` being a
non-trivially normed field viewed as a module over itself. -/
private lemma neBot_nhdsNE_complex (z : ℂ) : Filter.NeBot (𝓝[≠] z) :=
  Module.punctured_nhds_neBot ℂ ℂ z

/-- **Open subsets of `ℂ` containing a point are infinite.** -/
private lemma isOpen_complex_set_infinite_of_mem
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) : U.Infinite := by
  haveI : Filter.NeBot (𝓝[≠] z) := neBot_nhdsNE_complex z
  exact infinite_of_mem_nhds z (hU.mem_nhds hz)

/-- **A connected complex 1-manifold is infinite.** From `ChartedSpace ℂ Y`
plus `T2Space Y` plus `Nonempty Y` (via `ConnectedSpace Y`), there is a
chart at any point whose source is open in `Y` and homeomorphic to an open
set of `ℂ`. Open sets of `ℂ` are infinite, so `Y` is infinite. -/
theorem y_infinite_of_chartedSpace_complex
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] : Infinite Y := by
  -- Pick any y₀ : Y.
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y)
  -- Get the chart at y₀; its target is open in ℂ and contains chartAt ℂ y₀ y₀.
  set c : OpenPartialHomeomorph Y ℂ := chartAt ℂ y₀ with hc_def
  have hy₀_src : y₀ ∈ c.source := mem_chart_source ℂ y₀
  have hcy₀_tgt : c y₀ ∈ c.target := c.map_source hy₀_src
  -- c.target is open in ℂ.
  have h_tgt_open : IsOpen c.target := c.open_target
  -- c.target is infinite (open in ℂ, contains a point).
  have h_tgt_inf : c.target.Infinite :=
    isOpen_complex_set_infinite_of_mem h_tgt_open hcy₀_tgt
  -- Push back through c.symm: c.symm '' c.target is infinite (c.symm injective on target).
  have h_inj_symm : Set.InjOn c.symm c.target := c.symm.injOn
  have h_symm_image_inf : (c.symm '' c.target).Infinite :=
    h_tgt_inf.image h_inj_symm
  -- Hence Y (whose universe contains this image) is infinite.
  refine Set.infinite_univ_iff.mp ?_
  exact h_symm_image_inf.mono (Set.subset_univ _)

/-! ## Main existence theorem

For non-constant analytic `f : X → Y`, the set `criticalValuesGeneral f` is
finite (CV-Gen); since `Y` is infinite, its complement is non-empty. Any
value `y₀` in the complement is a regular value: every preimage `x` of `y₀`
is locally injective (by definition of `criticalSetGeneral` complement),
which combined with the planar order-of-vanishing analysis forces the
chart-pullback derivative at `x` to be nonzero. -/

/-- **Auxiliary:** for `y` not in `criticalValuesGeneral f`, every preimage
of `y` lies in the regular set complement, i.e. `f` is locally injective at
every preimage. -/
private lemma preimages_locally_injective_of_notMem_criticalValues
    {X : Type u} [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y]
    {f : X → Y} {y : Y}
    (hy : y ∉ Jacobians.Discharge.Manifold.criticalValuesGeneral f) :
    ∀ x ∈ f ⁻¹' {y}, ∃ U ∈ 𝓝 x, Set.InjOn f U := by
  intro x hx
  -- hx : f x = y
  have hfx_eq : f x = y := hx
  -- If x ∈ criticalSetGeneral, then y = f x ∈ criticalValuesGeneral, contradicting hy.
  have hx_not_crit : x ∉ Jacobians.Discharge.Manifold.criticalSetGeneral f := by
    intro hx_crit
    apply hy
    exact ⟨x, hx_crit, hfx_eq⟩
  -- Unfold criticalSetGeneral: x ∉ {x | ¬ ∃ U ∈ 𝓝 x, Set.InjOn f U} means
  -- ∃ U ∈ 𝓝 x, Set.InjOn f U.
  have h_inj : ∃ U ∈ 𝓝 x, Set.InjOn f U := by
    by_contra h
    apply hx_not_crit
    show ¬ ∃ U ∈ 𝓝 x, Set.InjOn f U
    exact h
  exact h_inj

/-- **Auxiliary:** local injectivity of `f` at `x` plus analyticity of the
chart pullback at `c x` (where `c = chartAt ℂ x`) implies the chart
pullback's derivative at `c x` is nonzero, provided we additionally know
the pullback is not eventually constant at `c x` (delivered by the
clopenness-of-locally-const machinery for non-constant `f`).

This packages the planar bridge ZZ99 specialised to the situation we are
in: at a non-critical preimage of a non-critical-value `y`, both
analyticity and non-eventual-constancy hold. -/
lemma deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap f) (x : X)
    (h_inj : ∃ U ∈ 𝓝 x, Set.InjOn f U) :
    deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) ≠ 0 := by
  classical
  -- Abbreviations
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
  set d : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with hd_def
  set F : ℂ → ℂ := d ∘ f ∘ c.symm with hF_def
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hfx_d : f x ∈ d.source := mem_chart_source ℂ (f x)
  -- Analyticity of F at c x (ZZ24).
  have hFA_at_x : AnalyticAt ℂ F (c x) :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback
      hf x
  -- Non-eventual-constancy of F at c x (clopenness discharge, general).
  have hClop :
      Jacobians.Discharge.ContMDiff.Degree.ClopennessOfLocallyConstHypothesis
        X Y :=
    Jacobians.Discharge.ContMDiff.Degree.clopennessOfLocallyConst_holds
  have hChartNEC :
      Jacobians.Discharge.ContMDiff.Degree.ChartPullbackNotEventuallyConstHypothesis
        X Y :=
    Jacobians.Discharge.ContMDiff.Degree.chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst
      hClop
  have hFne_raw :
      ¬ ∀ᶠ z in 𝓝 (c x),
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f x)) (f x) :=
    hChartNEC f hf hnc (f x) x rfl
  -- F (c x) = d (f x) via chart left-inverse.
  have hFcx : F (c x) = d (f x) := by
    have h_inv : c.symm (c x) = x := c.left_inv hxc
    show (d ∘ f ∘ c.symm) (c x) = d (f x)
    simp [Function.comp, h_inv]
  -- F not eventually equal to F (c x).
  have hFne : ¬ ∀ᶠ z in 𝓝 (c x), F z = F (c x) := by
    intro hev
    apply hFne_raw
    exact hev.mono (fun z hz => by
      show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f x)) (f x)
      have : F z = F (c x) := hz
      rw [show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z = F z from rfl,
          this, hFcx])
  -- Local injectivity of f at x lifts to local injectivity of F at c x.
  -- We follow the same chain as in CriticalValuesFiniteGeneral:
  -- (∃ U ∈ 𝓝 x, InjOn f U) → (∃ U' ∈ 𝓝 (c x), InjOn F U').
  have h_inj_F : ∃ U' ∈ 𝓝 (c x), Set.InjOn F U' := by
    obtain ⟨U, hU_nhds, hU_inj⟩ := h_inj
    set U₁ : Set X := U ∩ c.source ∩ f ⁻¹' d.source with hU₁_def
    have hf_cont : Continuous f := hf.continuous
    have hU₁_nhds : U₁ ∈ 𝓝 x :=
      Filter.inter_mem (Filter.inter_mem hU_nhds (c.open_source.mem_nhds hxc))
        (hf_cont.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds hfx_d))
    have hU₁_subc : U₁ ⊆ c.source := fun _ hy => hy.1.2
    obtain ⟨U₁_open, hU₁_open_open, hU₁_open_sub, hx_U₁_open⟩ :
        ∃ U_o, IsOpen U_o ∧ U_o ⊆ U₁ ∧ x ∈ U_o := by
      obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU₁_nhds
      exact ⟨W, hW_open, hW_sub, hxW⟩
    have hU₁_open_subc : U₁_open ⊆ c.source := hU₁_open_sub.trans hU₁_subc
    set U' : Set ℂ := c '' U₁_open with hU'_def
    have hU'_open : IsOpen U' :=
      c.isOpen_image_of_subset_source hU₁_open_open hU₁_open_subc
    have hcx_in_U' : c x ∈ U' := ⟨x, hx_U₁_open, rfl⟩
    have hU'_nhds : U' ∈ 𝓝 (c x) := hU'_open.mem_nhds hcx_in_U'
    refine ⟨U', hU'_nhds, ?_⟩
    rintro z₁ ⟨y₁, hy₁_U, hy₁_eq⟩ z₂ ⟨y₂, hy₂_U, hy₂_eq⟩ hF_eq
    have hy₁_subc : y₁ ∈ c.source := hU₁_open_subc hy₁_U
    have hy₂_subc : y₂ ∈ c.source := hU₁_open_subc hy₂_U
    have hy₁_U₁ : y₁ ∈ U₁ := hU₁_open_sub hy₁_U
    have hy₂_U₁ : y₂ ∈ U₁ := hU₁_open_sub hy₂_U
    have hy₁_U_outer : y₁ ∈ U := hy₁_U₁.1.1
    have hy₂_U_outer : y₂ ∈ U := hy₂_U₁.1.1
    have hy₁_fd : f y₁ ∈ d.source := hy₁_U₁.2
    have hy₂_fd : f y₂ ∈ d.source := hy₂_U₁.2
    have h_inv_y₁ : c.symm (c y₁) = y₁ := c.left_inv hy₁_subc
    have h_inv_y₂ : c.symm (c y₂) = y₂ := c.left_inv hy₂_subc
    have hF_at_y₁ : F (c y₁) = d (f y₁) := by
      show (d ∘ f ∘ c.symm) (c y₁) = d (f y₁)
      simp [Function.comp, h_inv_y₁]
    have hF_at_y₂ : F (c y₂) = d (f y₂) := by
      show (d ∘ f ∘ c.symm) (c y₂) = d (f y₂)
      simp [Function.comp, h_inv_y₂]
    rw [← hy₁_eq, ← hy₂_eq] at hF_eq
    rw [hF_at_y₁, hF_at_y₂] at hF_eq
    have h_inj_d : Set.InjOn d d.source := d.injOn
    have hf_eq : f y₁ = f y₂ :=
      h_inj_d hy₁_fd hy₂_fd hF_eq
    have hy_eq : y₁ = y₂ := hU_inj hy₁_U_outer hy₂_U_outer hf_eq
    rw [← hy₁_eq, ← hy₂_eq, hy_eq]
  -- Order analysis on F at c x.
  have hFA_sub : AnalyticAt ℂ (fun z => F z - F (c x)) (c x) :=
    hFA_at_x.sub analyticAt_const
  have h_ord_ne_top :
      analyticOrderAt (fun z => F z - F (c x)) (c x) ≠ ⊤ := by
    intro h_top
    apply hFne
    have h := analyticOrderAt_eq_top.mp h_top
    exact h.mono (fun z hz => sub_eq_zero.mp hz)
  have hF_self : (fun z => F z - F (c x)) (c x) = 0 := by simp
  have h_ord_ne_zero :
      analyticOrderAt (fun z => F z - F (c x)) (c x) ≠ 0 := by
    intro h_zero
    have hne := (hFA_sub.analyticOrderAt_eq_zero).mp h_zero
    exact hne hF_self
  set ord : ℕ∞ := analyticOrderAt (fun z => F z - F (c x)) (c x) with hord_def
  obtain ⟨k, hk_eq⟩ : ∃ k : ℕ, ord = (k : ℕ∞) := by
    cases hord_eq : ord with
    | top => exact absurd hord_eq h_ord_ne_top
    | coe n => exact ⟨n, by simp⟩
  have hk_ge_one : 1 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k
    apply h_ord_ne_zero
    exact hk_eq
  -- Apply the planar bridge ZZ99.
  have h_planar :
      (¬ ∃ U ∈ 𝓝 (c x), Set.InjOn F U) ↔ deriv F (c x) = 0 :=
    Jacobians.Discharge.Manifold.notInjOn_iff_deriv_zero_of_analytic_of_order
      hFA_at_x hk_ge_one hk_eq
  -- We have local injectivity of F at c x; conclude deriv F (c x) ≠ 0.
  have h_neg_iff : ¬ (¬ ∃ U ∈ 𝓝 (c x), Set.InjOn F U) := by
    intro h_neg
    exact h_neg h_inj_F
  by_contra h_d_zero
  exact h_neg_iff (h_planar.mpr h_d_zero)

/-- **Witness at a prescribed regular value.** A value `y₀` off the
critical-value set yields a regularity-certified witness *with that exact
value* — so its fibre cardinality can be identified with `y₀`'s. (This is
steps 4–7 of `regular_value_exists_reg_unconditional` at a caller-chosen
`y₀` instead of a `Classical.choice`-picked one.) -/
lemma exists_regularValueWitnessReg_value_eq
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    (f : X → Y) (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap f)
    {y₀ : Y} (hy₀ : y₀ ∉ Jacobians.Discharge.Manifold.criticalValuesGeneral f) :
    ∃ w : RegularValueWitnessReg f, w.toWitness.value = y₀ := by
  classical
  -- Fibre over y₀ is finite (ZZ48).
  have h_fib_fin : (f ⁻¹' {y₀}).Finite :=
    fibres_finite_statement_unconditional f hf hnc y₀
  -- Plain witness at y₀.
  let w : RegularValueWitness f := { value := y₀, fiber_finite := h_fib_fin }
  -- Regularity certificate at every preimage (same argument as the headline).
  have h_reg : ∀ x ∈ f ⁻¹' {w.value},
      deriv ((chartAt ℂ w.value) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 := by
    intro x hx
    have hfx_eq : f x = y₀ := hx
    have h_inj : ∃ U ∈ 𝓝 x, Set.InjOn f U :=
      preimages_locally_injective_of_notMem_criticalValues
        (f := f) (y := y₀) hy₀ x hx
    have h_deriv_at_fx :
        deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x) ≠ 0 :=
      deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood hf hnc x h_inj
    show deriv ((chartAt ℂ y₀) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0
    rw [← hfx_eq]; exact h_deriv_at_fx
  exact ⟨w.toRegular h_reg, rfl⟩

/-- **Headline existence.** For every non-constant analytic
`f : X → Y` between compact connected complex 1-manifolds,
`Nonempty (RegularValueWitnessReg f)`. -/
theorem regular_value_exists_reg_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    (f : X → Y) (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap f) :
    Nonempty (RegularValueWitnessReg f) := by
  classical
  -- 1. critical values finite (CV-Gen).
  have h_cv_fin : (Jacobians.Discharge.Manifold.criticalValuesGeneral f).Finite :=
    Jacobians.Discharge.Manifold.criticalValues_finite_general f hf hnc
  -- 2. Y is infinite.
  haveI : Infinite Y := y_infinite_of_chartedSpace_complex
  -- 3. Y \ criticalValuesGeneral f is non-empty.
  have h_compl_nonempty :
      (Jacobians.Discharge.Manifold.criticalValuesGeneral f)ᶜ.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    have h_univ_fin : (Set.univ : Set Y).Finite := h ▸ h_cv_fin
    exact (Set.infinite_univ).not_finite h_univ_fin
  obtain ⟨y₀, hy₀⟩ := h_compl_nonempty
  -- 4. Fibre over y₀ is finite (ZZ48).
  have h_fib_fin : (f ⁻¹' {y₀}).Finite :=
    fibres_finite_statement_unconditional f hf hnc y₀
  -- 5. Build the underlying RegularValueWitness.
  let w : RegularValueWitness f :=
    { value := y₀, fiber_finite := h_fib_fin }
  -- 6. Verify the regularity certificate at every preimage.
  have h_reg : ∀ x ∈ f ⁻¹' {w.value},
      deriv ((chartAt ℂ w.value) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 := by
    intro x hx
    -- hx : x ∈ f ⁻¹' {y₀}, i.e. f x = y₀.
    have hfx_eq : f x = y₀ := hx
    -- Translate w.value to y₀ in the goal.
    have h_val_eq : w.value = y₀ := rfl
    -- y₀ is not a critical value, so f is locally injective at x.
    have h_inj : ∃ U ∈ 𝓝 x, Set.InjOn f U :=
      preimages_locally_injective_of_notMem_criticalValues
        (f := f) (y := y₀) hy₀ x hx
    -- Apply the deriv-nonzero lemma; it states the conclusion at f x = y₀.
    have h_deriv_at_fx :
        deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x) ≠ 0 :=
      deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood hf hnc x h_inj
    -- Rewrite f x = y₀ = w.value.
    rw [h_val_eq, ← hfx_eq]
    exact h_deriv_at_fx
  -- 7. Package as a RegularValueWitnessReg.
  exact ⟨w.toRegular h_reg⟩

end Degree
end ContMDiff
end Jacobians.Discharge

end

end
