/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.AnalyticDerivOrder
import KirovDolbeault.Discharge.Manifold.ContMDiffOmegaAnalytic
import KirovDolbeault.Discharge.Manifold.ChartOverlapPropagationDischarge
import KirovDolbeault.Discharge.Manifold.ClopennessOfLocallyConstDischarge
import KirovDolbeault.Discharge.Manifold.ChartBallOffCentreWitnessDischarge
import KirovDolbeault.Discharge.Manifold.CriticalSetDiscrete
import KirovDolbeault.Discharge.Manifold.CriticalSetDerivBridge
import KirovDolbeault.Discharge.Manifold.MeromorphicAt
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option autoImplicit true


/-! # Unconditional finiteness of critical values for general `f : X → Y`

This file (the **CV-Gen** chip) ships the unconditional finiteness theorem
for the critical set / critical values of a general analytic map
`f : X → Y` between two compact connected charted spaces over `ℂ`,
generalising the Wire-CV chip's `MeromorphicNonzero`-bound result.

The proof is a near-verbatim port of `CriticalValuesFiniteUnconditional.lean`
with `f.toRiemannSphere` replaced by `f` and `MeromorphicNonzero X`
replaced by `(f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)`. All four
ingredient chips (R-Compat, R-MN, R-Closed, RH6) are themselves
generalisable because the load-bearing lemmas in their proofs already
accept general `Y`:

* `contMDiff_omega_analyticAt_chart_pullback` (ZZ24) is general,
* `clopennessOfLocallyConst_holds` and
  `chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst` (ZZ43) are
  general,
* `analyticAt_chart_transition_of_isManifold` and
  `deriv_chart_transition_of_isManifold_ne_zero` are general,
* `notInjOn_iff_deriv_zero_of_analytic_of_order` (ZZ99) is purely planar.

We do not factor through `MeromorphicNonzero`'s `criticalSet`/
`criticalValues` definitions: instead, this file introduces parallel
general definitions

* `criticalSetGeneral f := { x | ¬ ∃ U ∈ 𝓝 x, InjOn f U }`,
* `criticalValuesGeneral f := f '' criticalSetGeneral f`,

and discharges finiteness for them via the general
`criticalSet_finite_of_chart_pullback` already supplied by ZZ44 in
`CriticalSetDiscrete.lean`.

## What this file ships

* `criticalSetGeneral`, `criticalValuesGeneral` — definitions.
* `isClosed_criticalSetGeneral` — closedness (parallel to R-Closed).
* `criticalChartPullbackData_general` — per-point bridge data for any
  `x ∈ criticalSetGeneral f hf`, given non-constancy of `f`.
* `criticalSet_finite_general` — finiteness of the critical set.
* `criticalValues_finite_general` — finiteness of the critical values.

No gaps, no `axiom`, no signature changes outside this file. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace Jacobians.Discharge

namespace Manifold

universe u v

/-! ## General critical set / values (no `MeromorphicNonzero` binding) -/

/-- **General critical set** of `f : X → Y`. Topological proxy for "fails
to be a local biholomorphism": the points where `f` is not locally
injective. For a non-constant analytic map between complex 1-manifolds,
this coincides with the classical chart-pullback-derivative-vanishing
notion via the local branched-cover normal form. -/
def criticalSetGeneral
    {X : Type u} {Y : Type v} (f : X → Y)
    [TopologicalSpace X] : Set X :=
  { x : X | ¬ ∃ U ∈ 𝓝 x, Set.InjOn f U }

/-- **General critical values** of `f : X → Y`. -/
def criticalValuesGeneral
    {X : Type u} {Y : Type v} (f : X → Y)
    [TopologicalSpace X] : Set Y :=
  f '' (criticalSetGeneral f)

/-! ## Closedness (general analogue of R-Closed) -/

/-- **General regular set.** Points where `f` is locally injective.
By construction the complement of `criticalSetGeneral f`. -/
def regularSetGeneral
    {X : Type u} {Y : Type v} (f : X → Y)
    [TopologicalSpace X] : Set X :=
  { x : X | ∃ U ∈ 𝓝 x, Set.InjOn f U }

/-- The general regular set is the set-theoretic complement of the
general critical set. -/
lemma regularSetGeneral_eq_compl_criticalSetGeneral
    {X : Type u} {Y : Type v} (f : X → Y)
    [TopologicalSpace X] :
    regularSetGeneral f = (criticalSetGeneral f)ᶜ := by
  ext x
  unfold regularSetGeneral criticalSetGeneral
  simp [Set.mem_compl_iff, Set.mem_setOf_eq, Classical.not_not]

/-- The general critical set is the set-theoretic complement of the
general regular set. -/
lemma criticalSetGeneral_eq_compl_regularSetGeneral
    {X : Type u} {Y : Type v} (f : X → Y)
    [TopologicalSpace X] :
    criticalSetGeneral f = (regularSetGeneral f)ᶜ := by
  rw [regularSetGeneral_eq_compl_criticalSetGeneral, compl_compl]

/-- **R-Closed (general).** The general regular set is open: any
neighbourhood `U` witnessing local injectivity at `x` can be shrunk to an
open `V ⊆ U` with `x ∈ V`, on which `InjOn f V` (restriction of
`InjOn f U`), and `V` is a neighbourhood of every one of its points. -/
theorem isOpen_regularSetGeneral
    {X : Type u} {Y : Type v} (f : X → Y)
    [TopologicalSpace X] :
    IsOpen (regularSetGeneral f) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU_mem, hU_inj⟩ := hx
  obtain ⟨V, hV_subU, hV_open, hxV⟩ := mem_nhds_iff.mp hU_mem
  have hV_sub_reg : V ⊆ regularSetGeneral f := by
    intro y hyV
    refine ⟨V, hV_open.mem_nhds hyV, ?_⟩
    exact hU_inj.mono hV_subU
  exact Filter.mem_of_superset (hV_open.mem_nhds hxV) hV_sub_reg

/-- **R-Closed (general headline).** The general critical set is closed. -/
theorem isClosed_criticalSetGeneral
    {X : Type u} {Y : Type v} (f : X → Y)
    [TopologicalSpace X] :
    IsClosed (criticalSetGeneral f) := by
  rw [criticalSetGeneral_eq_compl_regularSetGeneral]
  exact (isOpen_regularSetGeneral f).isClosed_compl

/-! ## Per-point chart-pullback data

For each `x ∈ criticalSetGeneral f hf`, build a
`CriticalChartPullbackData f (criticalSetGeneral f hf) x` whose `F'`
is the derivative of the literal chart pullback of `f`.

The construction uses the standard chart-transition compatibility argument,
applied to the general `f`. The proof body works with `f` directly
(rather than `f.toRiemannSphere`) throughout. -/

/-- **Per-point chart-pullback data (general).**

For `(f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ) ω f)` non-constant, at
every `x : X`, build a `CriticalChartPullbackData f (criticalSetGeneral f) x`
whose `F'` is the derivative of the literal chart pullback of `f` through
`chartAt ℂ x` and `chartAt ℂ (f x)`. -/
noncomputable def criticalChartPullbackData_general
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    (f : X → Y) (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap f)
    (x : X) :
    Jacobians.Discharge.ContMDiff.Degree.CriticalChartPullbackData
      f (criticalSetGeneral f) x := by
  classical
  -- Abbreviations.
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
  set d : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with hd_def
  set F : ℂ → ℂ := d ∘ f ∘ c.symm with hF_def
  -- Chart-source membership.
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hfx_d : f x ∈ d.source := mem_chart_source ℂ (f x)
  -- Open neighbourhood `V` of `x`.
  set V : Set X := c.source ∩ f ⁻¹' d.source with hV_def
  have hV_open : IsOpen V := by
    refine c.open_source.inter ?_
    exact d.open_source.preimage hf.continuous
  have hxV : x ∈ V := ⟨hxc, hfx_d⟩
  have hV_subS : V ⊆ c.source := fun _ hy => hy.1
  -- Analyticity of `F` at `c x` (ZZ24).
  have hFA_at_x : AnalyticAt ℂ F (c x) :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback
      hf x
  -- Non-eventual-constancy of `F` at `c x` (clopenness discharge, general).
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
  -- `F (c x) = d (f x)` via chart left-inverse.
  have hFcx : F (c x) = d (f x) := by
    have h_inv : c.symm (c x) = x := c.left_inv hxc
    show (d ∘ f ∘ c.symm) (c x) = d (f x)
    simp [Function.comp, h_inv]
  -- Translate `hFne_raw` to "F not eventually equal to F (c x)".
  have hFne : ¬ ∀ᶠ z in 𝓝 (c x), F z = F (c x) := by
    intro hev
    apply hFne_raw
    exact hev.mono (fun z hz => by
      show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f x)) (f x)
      have : F z = F (c x) := hz
      rw [show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z = F z from rfl,
          this, hFcx])
  -- Per-point compatibility on V.
  -- For x' ∈ V: x' ∈ criticalSetGeneral f ↔ deriv F (c x') = 0.
  have hCompat :
      ∀ x' ∈ V, (x' ∈ criticalSetGeneral f) ↔ deriv F (c x') = 0 := by
    intro x' hx'V
    obtain ⟨hx'c, hx'fd⟩ := hx'V
    -- Canonical charts at x' and at f x'.
    set c' : OpenPartialHomeomorph X ℂ := chartAt ℂ x' with hc'_def
    set d' : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x') with hd'_def
    set F' : ℂ → ℂ := d' ∘ f ∘ c'.symm with hF'_def
    have hx'c' : x' ∈ c'.source := mem_chart_source ℂ x'
    have hfx'd' : f x' ∈ d'.source := mem_chart_source ℂ (f x')
    -- F' analytic at c' x' (ZZ24).
    have hF'A_at_x' : AnalyticAt ℂ F' (c' x') :=
      Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback
        hf x'
    -- F' (c' x') = d' (f x').
    have hF'cx' : F' (c' x') = d' (f x') := by
      have h_inv : c'.symm (c' x') = x' := c'.left_inv hx'c'
      show (d' ∘ f ∘ c'.symm) (c' x') = d' (f x')
      simp [Function.comp, h_inv]
    -- F' not eventually equal to F' (c' x') (chart NEC at x').
    have hF'ne_raw :
        ¬ ∀ᶠ z in 𝓝 (c' x'),
          ((chartAt ℂ (f x')) ∘ f ∘ (chartAt ℂ x').symm) z
            = (chartAt ℂ (f x')) (f x') :=
      hChartNEC f hf hnc (f x') x' rfl
    have hF'ne : ¬ ∀ᶠ z in 𝓝 (c' x'), F' z = F' (c' x') := by
      intro hev
      apply hF'ne_raw
      exact hev.mono (fun z hz => by
        show ((chartAt ℂ (f x')) ∘ f ∘ (chartAt ℂ x').symm) z
            = (chartAt ℂ (f x')) (f x')
        have : F' z = F' (c' x') := hz
        rw [show ((chartAt ℂ (f x')) ∘ f ∘ (chartAt ℂ x').symm) z = F' z from rfl,
            this, hF'cx'])
    -- Order of (F' - F' (c' x')) at (c' x') is finite, ≥ 1.
    have hF'A_sub : AnalyticAt ℂ (fun z => F' z - F' (c' x')) (c' x') :=
      hF'A_at_x'.sub analyticAt_const
    have h_ord_ne_top :
        analyticOrderAt (fun z => F' z - F' (c' x')) (c' x') ≠ ⊤ := by
      intro h_top
      apply hF'ne
      have h := analyticOrderAt_eq_top.mp h_top
      exact h.mono (fun z hz => sub_eq_zero.mp hz)
    have hF'_self : (fun z => F' z - F' (c' x')) (c' x') = 0 := by simp
    have h_ord_ne_zero :
        analyticOrderAt (fun z => F' z - F' (c' x')) (c' x') ≠ 0 := by
      intro h_zero
      have hne := (hF'A_sub.analyticOrderAt_eq_zero).mp h_zero
      exact hne hF'_self
    set ord : ℕ∞ := analyticOrderAt (fun z => F' z - F' (c' x')) (c' x') with hord_def
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
    -- ZZ99 planar bridge.
    have h_planar :
        (¬ ∃ U ∈ 𝓝 (c' x'), Set.InjOn F' U) ↔ deriv F' (c' x') = 0 := by
      apply notInjOn_iff_deriv_zero_of_analytic_of_order hF'A_at_x' hk_ge_one
      exact hk_eq
    -- Manifold ↔ chart-pullback injectivity at x'.
    have h_inj_iff_x' :
        (∃ U ∈ 𝓝 x', Set.InjOn f U) ↔
          (∃ U' ∈ 𝓝 (c' x'), Set.InjOn F' U') := by
      constructor
      · rintro ⟨U, hU_nhds, hU_inj⟩
        set U₁ : Set X := U ∩ c'.source ∩ f ⁻¹' d'.source with hU₁_def
        have hf_cont : Continuous f := hf.continuous
        have hU₁_nhds : U₁ ∈ 𝓝 x' :=
          Filter.inter_mem (Filter.inter_mem hU_nhds (c'.open_source.mem_nhds hx'c'))
            (hf_cont.continuousAt.preimage_mem_nhds (d'.open_source.mem_nhds hfx'd'))
        have hU₁_subc' : U₁ ⊆ c'.source := fun _ hy => hy.1.2
        obtain ⟨U₁_open, hU₁_open_open, hU₁_open_sub, hx'_U₁_open⟩ :
            ∃ U_o, IsOpen U_o ∧ U_o ⊆ U₁ ∧ x' ∈ U_o := by
          obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU₁_nhds
          exact ⟨W, hW_open, hW_sub, hxW⟩
        have hU₁_open_subc' : U₁_open ⊆ c'.source := hU₁_open_sub.trans hU₁_subc'
        set U' : Set ℂ := c' '' U₁_open with hU'_def
        have hU'_open : IsOpen U' :=
          c'.isOpen_image_of_subset_source hU₁_open_open hU₁_open_subc'
        have hcx'_in_U' : c' x' ∈ U' := ⟨x', hx'_U₁_open, rfl⟩
        have hU'_nhds : U' ∈ 𝓝 (c' x') := hU'_open.mem_nhds hcx'_in_U'
        refine ⟨U', hU'_nhds, ?_⟩
        rintro z₁ ⟨y₁, hy₁_U, hy₁_eq⟩ z₂ ⟨y₂, hy₂_U, hy₂_eq⟩ hF'_eq
        have hy₁_subc' : y₁ ∈ c'.source := hU₁_open_subc' hy₁_U
        have hy₂_subc' : y₂ ∈ c'.source := hU₁_open_subc' hy₂_U
        have hy₁_U₁ : y₁ ∈ U₁ := hU₁_open_sub hy₁_U
        have hy₂_U₁ : y₂ ∈ U₁ := hU₁_open_sub hy₂_U
        have hy₁_U_outer : y₁ ∈ U := hy₁_U₁.1.1
        have hy₂_U_outer : y₂ ∈ U := hy₂_U₁.1.1
        have hy₁_fd' : f y₁ ∈ d'.source := hy₁_U₁.2
        have hy₂_fd' : f y₂ ∈ d'.source := hy₂_U₁.2
        have h_inv_y₁ : c'.symm (c' y₁) = y₁ := c'.left_inv hy₁_subc'
        have h_inv_y₂ : c'.symm (c' y₂) = y₂ := c'.left_inv hy₂_subc'
        have hF'_at_y₁ : F' (c' y₁) = d' (f y₁) := by
          show (d' ∘ f ∘ c'.symm) (c' y₁) = d' (f y₁)
          simp [Function.comp, h_inv_y₁]
        have hF'_at_y₂ : F' (c' y₂) = d' (f y₂) := by
          show (d' ∘ f ∘ c'.symm) (c' y₂) = d' (f y₂)
          simp [Function.comp, h_inv_y₂]
        rw [← hy₁_eq, ← hy₂_eq] at hF'_eq
        rw [hF'_at_y₁, hF'_at_y₂] at hF'_eq
        have h_inj_d : Set.InjOn d' d'.source := d'.injOn
        have hf_eq : f y₁ = f y₂ :=
          h_inj_d hy₁_fd' hy₂_fd' hF'_eq
        have hy_eq : y₁ = y₂ := hU_inj hy₁_U_outer hy₂_U_outer hf_eq
        rw [← hy₁_eq, ← hy₂_eq, hy_eq]
      · rintro ⟨U', hU'_nhds, hU'_inj⟩
        have hc'_cont : ContinuousOn c' c'.source := c'.continuousOn_toFun
        obtain ⟨U'_open, hU'_open_open, hU'_open_sub, hcx'_U'_open⟩ :
            ∃ U'_o, IsOpen U'_o ∧ U'_o ⊆ U' ∧ c' x' ∈ U'_o := by
          obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU'_nhds
          exact ⟨W, hW_open, hW_sub, hxW⟩
        set U : Set X := c'.source ∩ c' ⁻¹' U'_open with hU_def
        have hU_open : IsOpen U :=
          hc'_cont.isOpen_inter_preimage c'.open_source hU'_open_open
        have hx'_U : x' ∈ U := ⟨hx'c', hcx'_U'_open⟩
        have hU_nhds : U ∈ 𝓝 x' := hU_open.mem_nhds hx'_U
        refine ⟨U, hU_nhds, ?_⟩
        intro y₁ hy₁ y₂ hy₂ hf_eq
        obtain ⟨hy₁_subc', hy₁_pre⟩ := hy₁
        obtain ⟨hy₂_subc', hy₂_pre⟩ := hy₂
        have hcy₁_U' : c' y₁ ∈ U' := hU'_open_sub hy₁_pre
        have hcy₂_U' : c' y₂ ∈ U' := hU'_open_sub hy₂_pre
        have h_inv_y₁ : c'.symm (c' y₁) = y₁ := c'.left_inv hy₁_subc'
        have h_inv_y₂ : c'.symm (c' y₂) = y₂ := c'.left_inv hy₂_subc'
        have hF'_at_y₁ : F' (c' y₁) = d' (f y₁) := by
          show (d' ∘ f ∘ c'.symm) (c' y₁) = d' (f y₁)
          simp [Function.comp, h_inv_y₁]
        have hF'_at_y₂ : F' (c' y₂) = d' (f y₂) := by
          show (d' ∘ f ∘ c'.symm) (c' y₂) = d' (f y₂)
          simp [Function.comp, h_inv_y₂]
        have hF'_eq : F' (c' y₁) = F' (c' y₂) := by
          rw [hF'_at_y₁, hF'_at_y₂, hf_eq]
        have hcy_eq : c' y₁ = c' y₂ := hU'_inj hcy₁_U' hcy₂_U' hF'_eq
        have h_inj_c : Set.InjOn c' c'.source := c'.injOn
        exact h_inj_c hy₁_subc' hy₂_subc' hcy_eq
    -- Critical-set general membership at x' ↔ deriv F' (c' x') = 0.
    have h_crit_iff_F' :
        (x' ∈ criticalSetGeneral f) ↔ deriv F' (c' x') = 0 := by
      have h_iff_neg : (¬ ∃ U ∈ 𝓝 x', Set.InjOn f U) ↔
          ¬ ∃ U' ∈ 𝓝 (c' x'), Set.InjOn F' U' := by
        constructor
        · intro h hex; exact h (h_inj_iff_x'.mpr hex)
        · intro h hex; exact h (h_inj_iff_x'.mp hex)
      have h_crit : (x' ∈ criticalSetGeneral f) ↔
          ¬ ∃ U ∈ 𝓝 x', Set.InjOn f U := Iff.rfl
      rw [h_crit, h_iff_neg, h_planar]
    -- Translate `deriv F' (c' x') = 0` ↔ `deriv F (c x') = 0`.
    have h_atlas_d : d ∈ atlas ℂ Y := chart_mem_atlas ℂ (f x)
    have h_atlas_d' : d' ∈ atlas ℂ Y := chart_mem_atlas ℂ (f x')
    have hfx'_d : f x' ∈ d.source := hx'fd
    have hfx'_d' : f x' ∈ d'.source := hfx'd'
    have h_deriv_d_d' :
        deriv (d ∘ d'.symm) (d' (f x')) ≠ 0 :=
      Jacobians.Discharge.deriv_chart_transition_of_isManifold_ne_zero
        h_atlas_d' h_atlas_d hfx'_d' hfx'_d
    have h_atlas_x : chartAt ℂ x ∈ atlas ℂ X := chart_mem_atlas ℂ x
    have h_atlas_x' : chartAt ℂ x' ∈ atlas ℂ X := chart_mem_atlas ℂ x'
    have h_deriv_c'_c : deriv (c' ∘ c.symm) (c x') ≠ 0 := by
      have h_atlas_c : c ∈ atlas ℂ X := h_atlas_x
      have h_atlas_c' : c' ∈ atlas ℂ X := h_atlas_x'
      exact Jacobians.Discharge.deriv_chart_transition_of_isManifold_ne_zero
        h_atlas_c h_atlas_c' hx'c hx'c'
    set W : Set ℂ :=
      c.target ∩ c.symm ⁻¹' (c'.source ∩ f ⁻¹' d'.source) with hW_def
    have hW_open : IsOpen W := by
      refine c.isOpen_inter_preimage_symm ?_
      refine c'.open_source.inter ?_
      exact d'.open_source.preimage hf.continuous
    have hc_x'_target : c x' ∈ c.target := c.map_source hx'c
    have hcx'_W : c x' ∈ W := by
      refine ⟨hc_x'_target, ?_⟩
      show c.symm (c x') ∈ c'.source ∩ f ⁻¹' d'.source
      rw [c.left_inv hx'c]
      exact ⟨hx'c', hfx'd'⟩
    have hW_nhds : W ∈ 𝓝 (c x') := hW_open.mem_nhds hcx'_W
    have h_F_eq_comp : ∀ z ∈ W,
        F z = ((d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)) z := by
      intro z hz
      obtain ⟨_, hz_pre⟩ := hz
      have hz_pre' : c.symm z ∈ c'.source ∩ f ⁻¹' d'.source := hz_pre
      obtain ⟨hcsymm_c'src, hcsymm_d'pre⟩ := hz_pre'
      have hfcsymm_d' : f (c.symm z) ∈ d'.source := hcsymm_d'pre
      have h_inv_d' : d'.symm (d' (f (c.symm z))) =
          f (c.symm z) := d'.left_inv hfcsymm_d'
      have h_inv_c' : c'.symm (c' (c.symm z)) = c.symm z := c'.left_inv hcsymm_c'src
      show (d ∘ f ∘ c.symm) z =
          ((d ∘ d'.symm) ∘ (d' ∘ f ∘ c'.symm) ∘ (c' ∘ c.symm)) z
      simp [Function.comp, h_inv_c', h_inv_d']
    have h_F_evEq : F =ᶠ[𝓝 (c x')] ((d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨W, hW_nhds, h_F_eq_comp⟩
    have h_an_c'_c : AnalyticAt ℂ (c' ∘ c.symm) (c x') :=
      Jacobians.Discharge.analyticAt_chart_transition_of_isManifold
        h_atlas_x h_atlas_x' hx'c hx'c'
    have h_an_d_d' : AnalyticAt ℂ (d ∘ d'.symm) (d' (f x')) :=
      Jacobians.Discharge.analyticAt_chart_transition_of_isManifold
        h_atlas_d' h_atlas_d hfx'_d' hfx'_d
    have h_diff_c'_c : DifferentiableAt ℂ (c' ∘ c.symm) (c x') :=
      h_an_c'_c.differentiableAt
    have h_pt_inner : (c' ∘ c.symm) (c x') = c' x' := by
      show c' (c.symm (c x')) = c' x'
      rw [c.left_inv hx'c]
    have h_diff_F' : DifferentiableAt ℂ F' ((c' ∘ c.symm) (c x')) := by
      rw [h_pt_inner]; exact hF'A_at_x'.differentiableAt
    have h_pt_F' : F' ((c' ∘ c.symm) (c x')) = d' (f x') := by
      rw [h_pt_inner]; exact hF'cx'
    have h_diff_d_d' : DifferentiableAt ℂ (d ∘ d'.symm) (F' ((c' ∘ c.symm) (c x'))) := by
      rw [h_pt_F']; exact h_an_d_d'.differentiableAt
    have h_chain_inner :
        deriv (F' ∘ (c' ∘ c.symm)) (c x') =
          deriv F' ((c' ∘ c.symm) (c x')) * deriv (c' ∘ c.symm) (c x') :=
      deriv_comp (c x') h_diff_F' h_diff_c'_c
    have h_diff_inner : DifferentiableAt ℂ (F' ∘ (c' ∘ c.symm)) (c x') :=
      h_diff_F'.comp (c x') h_diff_c'_c
    have h_chain_outer :
        deriv ((d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)) (c x') =
          deriv (d ∘ d'.symm) ((F' ∘ (c' ∘ c.symm)) (c x'))
            * deriv (F' ∘ (c' ∘ c.symm)) (c x') :=
      deriv_comp (c x') h_diff_d_d' h_diff_inner
    have h_F_deriv :
        deriv F (c x') = deriv ((d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)) (c x') :=
      h_F_evEq.deriv_eq
    have h_pt_inner_comp : (F' ∘ (c' ∘ c.symm)) (c x') = F' (c' x') := by
      show F' ((c' ∘ c.symm) (c x')) = F' (c' x')
      rw [h_pt_inner]
    have h_F_deriv_factored :
        deriv F (c x') =
          deriv (d ∘ d'.symm) (d' (f x'))
            * (deriv F' (c' x') * deriv (c' ∘ c.symm) (c x')) := by
      rw [h_F_deriv, h_chain_outer, h_chain_inner, h_pt_inner_comp, h_pt_inner]
      rw [hF'cx']
    have h_deriv_iff : deriv F (c x') = 0 ↔ deriv F' (c' x') = 0 := by
      rw [h_F_deriv_factored]
      constructor
      · intro h
        rcases mul_eq_zero.mp h with h1 | h2
        · exact absurd h1 h_deriv_d_d'
        rcases mul_eq_zero.mp h2 with h3 | h4
        · exact h3
        · exact absurd h4 h_deriv_c'_c
      · intro h
        rw [h, zero_mul, mul_zero]
    rw [h_crit_iff_F']
    exact h_deriv_iff.symm
  -- Now turn `(F, hCompat)` into a `CriticalChartPullbackData` whose `F'`
  -- field is `deriv F`. Build the chart restriction `φ : V → W := c '' V`.
  -- The boilerplate mirrors `criticalChartPullbackData_of_bridge` from
  -- `CriticalSetWitnessSupplier.lean` but is inlined here for the
  -- general-`Y` setting.
  set Wim : Set ℂ := c '' V with hWim_def
  have hxS : x ∈ c.source := hxc
  have hWim_open : IsOpen Wim := by
    have hWeq : Wim = c.target ∩ c.symm ⁻¹' V := by
      ext z
      constructor
      · rintro ⟨v, hvV, rfl⟩
        refine ⟨c.map_source (hV_subS hvV), ?_⟩
        show c.symm (c v) ∈ V
        rw [c.left_inv (hV_subS hvV)]
        exact hvV
      · rintro ⟨hz_target, hz_pre⟩
        refine ⟨c.symm z, hz_pre, ?_⟩
        exact c.right_inv hz_target
    rw [hWeq]
    exact c.isOpen_inter_preimage_symm hV_open
  set z₀ : ℂ := c x with hz₀_def
  have hz₀W : z₀ ∈ Wim := ⟨x, hxV, rfl⟩
  -- The restricted map φ : V → Wim.
  let φ : V → Wim := fun v => ⟨c v.1, mem_image_of_mem _ v.2⟩
  have hφ_cont : Continuous φ := by
    apply Continuous.subtype_mk
    have h_co : ContinuousOn c c.source := c.continuousOn_toFun
    have h_co_V : ContinuousOn c V := h_co.mono hV_subS
    exact continuousOn_iff_continuous_restrict.mp h_co_V
  have hφ_bij : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · intro v₁ v₂ hv
      have h_eq : c v₁.1 = c v₂.1 := by
        have := congrArg Subtype.val hv
        simpa using this
      have hi := c.injOn (hV_subS v₁.2) (hV_subS v₂.2) h_eq
      exact Subtype.ext hi
    · rintro ⟨w, hw⟩
      obtain ⟨v', hv'V, hv'eq⟩ := hw
      refine ⟨⟨v', hv'V⟩, ?_⟩
      exact Subtype.ext hv'eq
  have hz₀_eq : (φ ⟨x, hxV⟩ : ℂ) = z₀ := rfl
  -- F' is `deriv F`; analyticity at z₀ comes from `hFA_at_x.deriv`.
  have hF'A_z0 : AnalyticAt ℂ (deriv F) z₀ := hFA_at_x.deriv
  -- F' (= deriv F) not eventually zero at z₀: from non-eventual-constancy of F.
  have hF'ne_z0 : ¬ ∀ᶠ z in 𝓝 z₀, deriv F z = 0 :=
    Jacobians.Discharge.Manifold.deriv_not_eventually_zero_of_analyticAt_not_eventually_const
      hFA_at_x hFne
  -- Compatibility on the subtype side: `x'.1 ∈ criticalSetGeneral f ↔ deriv F (φ x') = 0`.
  have hCompat_sub :
      ∀ x' : V, x'.1 ∈ criticalSetGeneral f ↔ deriv F (φ x') = 0 := by
    intro x'
    have h := hCompat x'.1 x'.2
    have h_eq : (φ x' : ℂ) = c x'.1 := rfl
    rw [h_eq]; exact h
  -- Assemble.
  exact
    { V := V
      hV_open := hV_open
      hxV := hxV
      W := Wim
      hW_open := hWim_open
      φ := φ
      hφ := hφ_cont
      hφ_inv := hφ_bij
      z₀ := z₀
      hz₀ := hz₀_eq
      hz₀W := hz₀W
      F' := deriv F
      hF'A := hF'A_z0
      hF'ne := hF'ne_z0
      hCompat := hCompat_sub }

/-! ## Headline finiteness theorems -/

/-- **CV-Gen headline.** Critical set is finite for any non-constant
analytic `f : X → Y` between two compact connected charted spaces over `ℂ`. -/
theorem criticalSet_finite_general
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    (f : X → Y) (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap f) :
    (criticalSetGeneral f).Finite :=
  Jacobians.Discharge.ContMDiff.Degree.criticalSet_finite_of_chart_pullback
    f (criticalSetGeneral f) (isClosed_criticalSetGeneral f)
    (fun x _hx => criticalChartPullbackData_general f hf hnc x)

/-- **CV-Gen corollary.** Critical values are finite under the same
hypotheses. -/
theorem criticalValues_finite_general
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    (f : X → Y) (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap f) :
    (criticalValuesGeneral f).Finite :=
  (criticalSet_finite_general f hf hnc).image f

end Manifold

end Jacobians.Discharge

end

end
