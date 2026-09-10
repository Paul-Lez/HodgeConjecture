/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.ChartOverlapPropagationDischarge

set_option autoImplicit true


/-! # Discharging `ClopennessOfLocallyConstHypothesis`

ZZ46 (`ChartOverlapPropagationDischarge.lean`) reduced the chart-overlap
propagation hypothesis to a single residual analytic-continuation
statement: the locally-constant locus
`S = {x | ∀ᶠ x' in 𝓝 x, f x' = y₀}`
of any `C^ω` map onto a fixed value `y₀` is closed.

This file (ZZ47) discharges that statement via the local identity theorem
applied chart-by-chart, with no path-walking.

## The argument

Take `x ∈ closure S`.

1. `S ⊆ f ⁻¹' {y₀}` (by `locallyConstLocus_apply`), and `f` is continuous,
   `Y` is `T2`, so `f ⁻¹' {y₀}` is closed and contains the closure of `S`.
   Hence `f x = y₀`.

2. With `f x = y₀`, the target chart `chartAt ℂ (f x) = chartAt ℂ y₀`. By
   ZZ24's bridge, the chart pullback
   `F := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm`
   is `AnalyticAt ℂ` at `(chartAt ℂ x) x`. ZZ34's helper supplies a
   preconnected open ball `B = Metric.ball ((chartAt ℂ x) x) r` on which
   `F` is `AnalyticOnNhd ℂ`.

3. Pulling back `B` through the chart and intersecting with the open
   neighbourhoods on which `chartAt ℂ x` is defined and `f` lands in
   `(chartAt ℂ y₀).source`, we obtain an open neighbourhood of `x` in `X`.
   Since `x ∈ closure S`, that neighbourhood meets `S`. Pick a witness
   `x' ∈ S` inside it.

4. `x' ∈ S` gives an open `W ∋ x'` with `f ≡ y₀` on `W`. On
   `W ∩ (chartAt ℂ x).source`, we have
   `F z = (chartAt ℂ y₀) y₀` for every `z ∈ (chartAt ℂ x) '' (W ∩ source)`,
   and a small ball around `(chartAt ℂ x) x'` lies in that image, giving
   `F =ᶠ[𝓝 ((chartAt ℂ x) x')] (fun _ => (chartAt ℂ y₀) y₀)`.

5. Apply `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` against the
   constant on `B`: `F` equals `(chartAt ℂ y₀) y₀` on all of `B`. In
   particular `F` is constant on the open ball `B ∋ (chartAt ℂ x) x`, so
   pulling back to `X` we get an open neighbourhood of `x` on which
   `f ≡ y₀` (using injectivity of `chartAt ℂ y₀` on its source). Hence
   `x ∈ S`.

No gaps, no `axiom`. -/

@[expose] public section

open Set Filter Topology Metric
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-- **Discharge of `ClopennessOfLocallyConstHypothesis`.** The
locally-constant locus `S = {x | ∀ᶠ x' in 𝓝 x, f x' = y₀}` of a `C^ω`
map `f : X → Y` is closed.

The proof is the chart-local identity theorem: at any closure point `x`
of `S`, continuity + `T2` already forces `f x = y₀`; analyticity of the
chart pullback on a preconnected open ball, combined with eventual
equality at a witness point of `S` inside the ball, propagates constancy
across the ball and hence to a neighbourhood of `x`. -/
theorem clopennessOfLocallyConst_holds
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    ClopennessOfLocallyConstHypothesis X Y := by
  intro f hf y₀
  -- Reduce closedness to: every closure point lies in `S`.
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm ?_ subset_closure
  intro x hx_closure
  -- `f` is continuous (from `ContMDiff … ω`).
  have hf_cont : Continuous f := hf.continuous
  -- Step 1. `f x = y₀`.
  have hS_sub : locallyConstLocus f y₀ ⊆ f ⁻¹' {y₀} := by
    intro y hy
    exact locallyConstLocus_apply hy
  have h_preimage_closed : IsClosed (f ⁻¹' ({y₀} : Set Y)) :=
    (isClosed_singleton).preimage hf_cont
  have hx_preimage : x ∈ f ⁻¹' ({y₀} : Set Y) :=
    h_preimage_closed.closure_subset
      (closure_mono hS_sub hx_closure)
  have hfx : f x = y₀ := hx_preimage
  -- Step 2. Analyticity of the chart pullback on a preconnected open ball.
  set c := chartAt ℂ x with hc_def
  set d := chartAt ℂ (f x) with hd_def
  set F : ℂ → ℂ := d ∘ f ∘ c.symm with hF_def
  set z₀ : ℂ := c x with hz₀_def
  have hFA_at : AnalyticAt ℂ F z₀ :=
    contMDiff_omega_analyticAt_chart_pullback hf x
  obtain ⟨r, hr_pos, hB_pc, hz₀_mem_B, hFA_on⟩ :=
    exists_preconnected_open_ball_of_analyticAt hFA_at
  -- Set up open neighbourhoods of `x` in `X`.
  have hx_csrc : x ∈ c.source := mem_chart_source ℂ x
  have hfx_dsrc : f x ∈ d.source := mem_chart_source ℂ (f x)
  -- The set `c.source ∩ c ⁻¹' (Metric.ball z₀ r) ∩ f ⁻¹' d.source`.
  have hc_cont : ContinuousOn c c.source := c.continuousOn_toFun
  have h_ball_open : IsOpen (Metric.ball z₀ r) := Metric.isOpen_ball
  have h_pre_open :
      IsOpen (c.source ∩ c ⁻¹' (Metric.ball z₀ r)) :=
    hc_cont.isOpen_inter_preimage c.open_source h_ball_open
  have h_fpre_open : IsOpen (f ⁻¹' d.source) :=
    d.open_source.preimage hf_cont
  set U : Set X :=
    (c.source ∩ c ⁻¹' (Metric.ball z₀ r)) ∩ f ⁻¹' d.source with hU_def
  have hU_open : IsOpen U := h_pre_open.inter h_fpre_open
  have hxU : x ∈ U := by
    refine ⟨⟨hx_csrc, ?_⟩, hfx_dsrc⟩
    show c x ∈ Metric.ball z₀ r
    exact hz₀_mem_B
  -- Step 3. Witness point `x' ∈ S ∩ U`, since `x ∈ closure S`.
  have hU_nhds : U ∈ 𝓝 x := hU_open.mem_nhds hxU
  have hx_freq : ∃ x' ∈ U, x' ∈ locallyConstLocus f y₀ := by
    have h := mem_closure_iff.mp hx_closure U hU_open hxU
    rcases h with ⟨x', hx'_U, hx'_S⟩
    exact ⟨x', hx'_U, hx'_S⟩
  obtain ⟨x', hx'_U, hx'_S⟩ := hx_freq
  obtain ⟨⟨hx'_csrc, hx'_inB⟩, hx'_fdsrc⟩ := hx'_U
  -- Step 4. Eventual equality of `F` to `(chartAt ℂ y₀) y₀ = d y₀ = d (f x)`
  -- near `c x'`.
  set cst : ℂ := d (f x) with hcst_def
  -- A neighbourhood `W ⊆ c.source` of `x'` on which `f ≡ y₀`.
  obtain ⟨W₀, hW₀_sub, hW₀_open, hx'_W₀⟩ := mem_nhds_iff.mp hx'_S
  set W : Set X := W₀ ∩ c.source with hW_def
  have hW_open : IsOpen W := hW₀_open.inter c.open_source
  have hx'_W : x' ∈ W := ⟨hx'_W₀, hx'_csrc⟩
  have hW_const : ∀ y ∈ W, f y = y₀ := fun y hy => hW₀_sub hy.1
  have hW_in_csrc : W ⊆ c.source := fun _ hy => hy.2
  -- The image `c '' W` is open in ℂ since `c` is a partial homeomorph and
  -- `W ⊆ c.source` is open in `X`.
  have hcW_open : IsOpen (c '' W) := by
    have : IsOpen (W ∩ c.source) := hW_open.inter c.open_source
    have : W ∩ c.source = W := by
      ext y; constructor
      · intro hy; exact hy.1
      · intro hy; exact ⟨hy, hW_in_csrc hy⟩
    -- Apply `c.isOpen_image_of_subset_source`.
    have := c.isOpen_image_of_subset_source hW_open hW_in_csrc
    exact this
  have hcx'_in_cW : c x' ∈ c '' W := ⟨x', hx'_W, rfl⟩
  -- Eventual equality of `F` to `cst` near `c x'`.
  have hF_ev_cx' : ∀ᶠ z in 𝓝 (c x'), F z = cst := by
    have hcW_nhds : c '' W ∈ 𝓝 (c x') := hcW_open.mem_nhds hcx'_in_cW
    refine Filter.eventually_of_mem hcW_nhds ?_
    rintro z ⟨y, hy_W, hyz⟩
    -- `c.symm z = y` because `y ∈ c.source` and `c y = z`.
    have hy_csrc : y ∈ c.source := hW_in_csrc hy_W
    have h_inv : c.symm z = y := by
      rw [← hyz]; exact c.left_inv hy_csrc
    -- `F z = d (f (c.symm z)) = d (f y) = d y₀ = d (f x) = cst`.
    have h_fy : f y = y₀ := hW_const y hy_W
    show (d ∘ f ∘ c.symm) z = cst
    simp [Function.comp, h_inv, h_fy, hcst_def, hfx]
  -- Step 5. Identity theorem on the preconnected ball `B`.
  have hcst_analytic_on : AnalyticOnNhd ℂ (fun _ : ℂ => cst) (Metric.ball z₀ r) :=
    analyticOnNhd_const
  have hcx'_in_B : c x' ∈ Metric.ball z₀ r := hx'_inB
  have hF_eqOn : EqOn F (fun _ => cst) (Metric.ball z₀ r) :=
    hFA_on.eqOn_of_preconnected_of_eventuallyEq
      hcst_analytic_on hB_pc hcx'_in_B hF_ev_cx'
  -- Step 6. Translate back: `f ≡ y₀` on a neighbourhood of `x` in `X`.
  -- Build `V := c.source ∩ c ⁻¹' B ∩ f ⁻¹' d.source` (open, contains `x`).
  have hV_open : IsOpen ((c.source ∩ c ⁻¹' (Metric.ball z₀ r)) ∩ f ⁻¹' d.source) :=
    hU_open
  have hxV : x ∈ (c.source ∩ c ⁻¹' (Metric.ball z₀ r)) ∩ f ⁻¹' d.source := hxU
  -- For any `y ∈ V`: `c y ∈ B`, so `F (c y) = cst`. Unfolding `F`,
  -- `d (f y) = cst = d (f x)`. Both `f y` and `f x` lie in `d.source`,
  -- and `d` is injective on `d.source`. Hence `f y = f x = y₀`.
  have h_const_on_V :
      ∀ y ∈ (c.source ∩ c ⁻¹' (Metric.ball z₀ r)) ∩ f ⁻¹' d.source,
        f y = y₀ := by
    intro y hy
    obtain ⟨⟨hy_csrc, hy_inB⟩, hy_fdsrc⟩ := hy
    have hcy_inB : c y ∈ Metric.ball z₀ r := hy_inB
    have hF_y : F (c y) = cst := hF_eqOn hcy_inB
    have h_inv : c.symm (c y) = y := c.left_inv hy_csrc
    have h_d_fy : d (f y) = cst := by
      have : (d ∘ f ∘ c.symm) (c y) = cst := hF_y
      simpa [Function.comp, h_inv] using this
    have h_d_eq : d (f y) = d (f x) := by rw [h_d_fy, hcst_def]
    have h_inj : Set.InjOn d d.source := d.injOn
    have h_fy_eq : f y = f x := h_inj hy_fdsrc hfx_dsrc h_d_eq
    rw [h_fy_eq, hfx]
  -- Hence `x ∈ S = locallyConstLocus f y₀`.
  exact mem_locallyConstLocus_of_isOpen hV_open hxV h_const_on_V

end Degree
end ContMDiff
end Jacobians.Discharge
