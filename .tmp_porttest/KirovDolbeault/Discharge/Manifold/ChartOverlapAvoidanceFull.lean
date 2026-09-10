/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez

Chip ZZ165e: chart-overlap finite-avoidance, **full** case.

Whereas `ChartOverlapAvoidance.lean` (ZZ165d) handled only `y ∉ C` (taking
`z := y`), this file handles the general case `y ∈ U` (and the chart-overlap
version `y ∈ U ∩ V`) where `y` may itself lie in the finite obstruction `C`,
provided the ambient space is a `ChartedSpace ℂ Y`. The construction
perturbs `y` inside a small ball-chart around `y` to a point `z` whose chart
image is close to `(chartAt ℂ y) y` but not in the chart-image of the finite
set `C`. The path is the pull-back of a straight segment in the chart ball,
which lives entirely in the chart source ⊆ `U`.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import KirovDolbeault.Discharge.Manifold.ChartRestrictionToBall

noncomputable section

namespace Jacobians.Discharge.Manifold

open Set Metric Topology
open scoped Topology

/--
**Full chart-overlap avoidance for a `ChartedSpace ℂ Y`.**

If `Y` is a charted space modelled on `ℂ`, `U` is open with `y ∈ U`, and
`C : Set Y` is finite (no assumption that `y ∉ C`), there exists `z ∈ U`
with `z ∉ C` and a path from `y` to `z` lying entirely in `U`.

Construction: take a ball-chart `φ'` at `y` (`ChartRestrictionToBall`), shrink
its source to land inside `U`, then perturb `(chartAt ℂ y) y` along a straight
segment in the chart ball whose pulled-back endpoint avoids `C`. Such a
segment exists because the finite chart-image of `C` blocks at most finitely
many directions through the centre.
-/
theorem exists_avoidance_in_open_chartedSpace_complex
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {U : Set Y} (hU : IsOpen U) {y : Y} (hy : y ∈ U)
    {C : Set Y} (hC : C.Finite) :
    ∃ z : Y, z ∈ U ∧ z ∉ C ∧ JoinedIn U y z := by
  -- (1) Get a ball-chart `φ'` at `y` from ZZ164c.
  obtain ⟨r₀, hr₀_pos, φ', hy_src, htarget, hcoe, hsrc_sub_chart⟩ :=
    Jacobians.Discharge.chart_restrict_to_ball (Y := Y) y
  -- Centre `c := φ' y = (chartAt ℂ y) y`.
  set c : ℂ := (chartAt ℂ y) y with hc_def
  -- The function-coercion of `φ'` equals `chartAt ℂ y`.
  have hφ'_y : φ' y = c := by
    have : (φ' : Y → ℂ) y = (chartAt ℂ y : Y → ℂ) y := by rw [hcoe]
    simpa [c] using this
  -- (2) Use continuity of `φ'.symm` at `c` to find `r ≤ r₀` with
  --     `φ'.symm '' (ball c r) ⊆ U`.
  -- `φ'.symm` is continuous on `φ'.target = ball c r₀`. Pull back `U` to find
  -- an open neighborhood of `c` (in `ball c r₀`) mapping into `U`.
  have hcont_symm : ContinuousOn φ'.symm φ'.target := φ'.continuousOn_symm
  have hc_target : c ∈ φ'.target := by
    rw [htarget]; exact Metric.mem_ball_self hr₀_pos
  -- `φ'.symm c = y ∈ U`.
  have hsymm_c : φ'.symm c = y := by
    have h1 : φ' y = c := hφ'_y
    have h2 : φ'.symm (φ' y) = y := φ'.left_inv hy_src
    rw [← h1]; exact h2
  -- The preimage `φ'.symm ⁻¹' U` intersected with `φ'.target` is open in
  -- `φ'.target` (subspace topology). Get a small ball around `c` in this set.
  have hpre_open_in_target : ∃ V : Set ℂ, IsOpen V ∧ c ∈ V ∧
      V ∩ φ'.target ⊆ φ'.symm ⁻¹' U := by
    have hctsAt : ContinuousWithinAt φ'.symm φ'.target c := hcont_symm c hc_target
    have hUmem : U ∈ 𝓝 (φ'.symm c) := hU.mem_nhds (hsymm_c ▸ hy)
    have hpre : φ'.symm ⁻¹' U ∈ 𝓝[φ'.target] c := hctsAt hUmem
    rw [mem_nhdsWithin] at hpre
    obtain ⟨V, hVopen, hcV, hVsub⟩ := hpre
    exact ⟨V, hVopen, hcV, hVsub⟩
  obtain ⟨V, hVopen, hcV, hVsub⟩ := hpre_open_in_target
  -- Shrink to a metric ball `ball c r ⊆ V ∩ ball c r₀`.
  have hVcap_open : IsOpen (V ∩ Metric.ball c r₀) :=
    hVopen.inter Metric.isOpen_ball
  have hcVcap : c ∈ V ∩ Metric.ball c r₀ :=
    ⟨hcV, Metric.mem_ball_self hr₀_pos⟩
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    Metric.isOpen_iff.mp hVcap_open c hcVcap
  -- `ball c r ⊆ ball c r₀ = φ'.target`, and `ball c r ⊆ V`.
  have hr_sub_target : Metric.ball c r ⊆ φ'.target := by
    intro w hw
    have := hr_sub hw
    rw [htarget]; exact this.2
  have hr_sub_V : Metric.ball c r ⊆ V := fun w hw => (hr_sub hw).1
  -- Then `φ'.symm '' (ball c r) ⊆ U`.
  have hsymm_sub_U : ∀ w ∈ Metric.ball c r, φ'.symm w ∈ U := by
    intro w hw
    have hw_target : w ∈ φ'.target := hr_sub_target hw
    have hw_V : w ∈ V := hr_sub_V hw
    exact hVsub ⟨hw_V, hw_target⟩
  -- (3) Find `c' ∈ ball c r` with `c' ≠ c` and `φ'.symm c' ∉ C`.
  -- The image of `C ∩ φ'.source` under `φ'` is finite, so the set
  -- of "bad" points in `ball c r` is finite, hence the punctured ball minus
  -- this finite set is nonempty (any nontrivial ball is uncountable).
  have hbad_fin : (φ' '' (φ'.source ∩ C)).Finite :=
    (hC.inter_of_right φ'.source).image φ'
  -- We want a nonzero `δ : ℝ` with `|δ| < r` and `c + δ ∉ φ' '' (φ'.source ∩ C)`.
  -- The set of "bad real shifts" is finite (one shift per bad chart-image point).
  -- `ball c r` contains uncountably many `c + δ` for `δ ∈ (-r, r) \ {0}`.
  -- It is enough to use that a finite set in ℝ has cofinite complement.
  set Bad : Set ℝ := {δ : ℝ | c + (δ : ℂ) ∈ φ' '' (φ'.source ∩ C)} with hBad_def
  have hBad_fin : Bad.Finite := by
    -- The map `δ ↦ c + δ` is injective from ℝ to ℂ; preimage of finite is finite.
    have hinj : Function.Injective (fun δ : ℝ => c + (δ : ℂ)) := by
      intro a b hab
      have : (a : ℂ) = (b : ℂ) := by
        have := hab
        simpa [add_left_cancel_iff] using this
      exact_mod_cast this
    have : Bad = (fun δ : ℝ => c + (δ : ℂ)) ⁻¹' (φ' '' (φ'.source ∩ C)) := rfl
    rw [this]
    exact hbad_fin.preimage hinj.injOn
  -- The interval `Ioo 0 r` is uncountable (in particular infinite), but `Bad` is finite,
  -- so their difference is nonempty.
  have hIoo_infinite : (Set.Ioo (0 : ℝ) r).Infinite := Set.Ioo_infinite hr_pos
  have hexists : ∃ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) r ∧ δ ∉ Bad := by
    by_contra hne
    push Not at hne
    have : Set.Ioo (0 : ℝ) r ⊆ Bad := fun δ hδ => hne δ hδ
    exact hIoo_infinite (hBad_fin.subset this)
  obtain ⟨δ, hδ_mem, hδ_notBad⟩ := hexists
  obtain ⟨hδ_pos, hδ_lt_r⟩ := hδ_mem
  -- Define `c' := c + δ`. Then `c' ∈ ball c r`.
  set c' : ℂ := c + (δ : ℂ) with hc'_def
  have hc'_in_ball : c' ∈ Metric.ball c r := by
    rw [Metric.mem_ball, hc'_def]
    have hdist : dist (c + (δ : ℂ)) c = |δ| := by
      rw [dist_eq_norm]
      have h1 : c + (δ : ℂ) - c = (δ : ℂ) := by ring
      rw [h1]
      simp [Complex.norm_real]
    rw [hdist, abs_of_pos hδ_pos]; exact hδ_lt_r
  -- `c'` is in `φ'.target`.
  have hc'_target : c' ∈ φ'.target := hr_sub_target hc'_in_ball
  -- (4) Define `z := φ'.symm c'`. It lies in `φ'.source ⊆ original chart source`,
  --     and is in `U` by `hsymm_sub_U`.
  set z : Y := φ'.symm c' with hz_def
  have hz_src : z ∈ φ'.source := φ'.map_target hc'_target
  have hz_U : z ∈ U := hsymm_sub_U c' hc'_in_ball
  -- (5) `z ∉ C`. Suppose `z ∈ C`. Then `z ∈ φ'.source ∩ C`, so
  --     `φ' z ∈ φ' '' (φ'.source ∩ C)`. But `φ' z = c'` (since `φ'.symm c' = z`
  --     and `c' ∈ φ'.target`, `right_inv` gives `φ' (φ'.symm c') = c'`). So
  --     `c' ∈ φ' '' (φ'.source ∩ C)`, i.e. `δ ∈ Bad`, contradicting `hδ_notBad`.
  have hz_notC : z ∉ C := by
    intro hzC
    have hφ'z : φ' z = c' := by
      have h := φ'.right_inv hc'_target
      simpa [hz_def] using h
    have : c' ∈ φ' '' (φ'.source ∩ C) := ⟨z, ⟨hz_src, hzC⟩, hφ'z⟩
    have : δ ∈ Bad := this
    exact hδ_notBad this
  -- (6) Path: `t ↦ φ'.symm (c + (t * δ : ℂ))` for `t ∈ [0,1]`. At `t=0`, value is
  --     `φ'.symm c = y`. At `t=1`, value is `φ'.symm c' = z`. The intermediate
  --     points `c + t*δ` lie in `ball c r` (which is convex), so the pulled-back
  --     points lie in `φ'.symm '' (ball c r) ⊆ U`.
  refine ⟨z, hz_U, hz_notC, ?_⟩
  -- Build the path explicitly.
  -- Continuous map `γ_chart : I → ℂ`, `γ_chart t = c + (t * δ : ℂ)`.
  let γ_chart : C(unitInterval, ℂ) :=
    { toFun := fun t => c + ((t.1 * δ : ℝ) : ℂ)
      continuous_toFun := by
        refine continuous_const.add ?_
        refine Complex.continuous_ofReal.comp ?_
        exact (continuous_subtype_val).mul continuous_const }
  -- Show `γ_chart t ∈ ball c r` for all `t ∈ I`.
  have hγ_chart_mem_ball : ∀ t : unitInterval, γ_chart t ∈ Metric.ball c r := by
    intro t
    have ht0 : 0 ≤ t.1 := t.2.1
    have ht1 : t.1 ≤ 1 := t.2.2
    show c + ((t.1 * δ : ℝ) : ℂ) ∈ Metric.ball c r
    rw [Metric.mem_ball]
    have hdist : dist (c + ((t.1 * δ : ℝ) : ℂ)) c = |t.1 * δ| := by
      rw [dist_eq_norm]
      have h1 : c + ((t.1 * δ : ℝ) : ℂ) - c = ((t.1 * δ : ℝ) : ℂ) := by ring
      rw [h1]
      simp [Complex.norm_real]
    rw [hdist]
    have htδ_nn : 0 ≤ t.1 * δ := mul_nonneg ht0 (le_of_lt hδ_pos)
    rw [abs_of_nonneg htδ_nn]
    calc t.1 * δ ≤ 1 * δ := by
            exact mul_le_mul_of_nonneg_right ht1 (le_of_lt hδ_pos)
      _ = δ := one_mul δ
      _ < r := hδ_lt_r
  -- Continuity of `φ'.symm ∘ γ_chart`.
  have hsymm_cont_on : ContinuousOn φ'.symm φ'.target := φ'.continuousOn_symm
  have hsymm_cont_on_ball : ContinuousOn φ'.symm (Metric.ball c r) :=
    hsymm_cont_on.mono hr_sub_target
  -- Build the path on `Y`.
  let γ : C(unitInterval, Y) :=
    { toFun := fun t => φ'.symm (γ_chart t)
      continuous_toFun := by
        have h1 : Continuous γ_chart := γ_chart.continuous
        have h2 : ∀ t : unitInterval, γ_chart t ∈ Metric.ball c r := hγ_chart_mem_ball
        exact (hsymm_cont_on_ball.comp_continuous h1 h2)
      }
  -- Endpoints.
  have hγ_zero : γ ⟨0, by simp [unitInterval]⟩ = y := by
    show φ'.symm (γ_chart ⟨0, _⟩) = y
    have hch : γ_chart ⟨(0 : ℝ), by simp [unitInterval]⟩ = c := by
      change c + (((0 : ℝ) * δ : ℝ) : ℂ) = c
      simp
    rw [hch]; exact hsymm_c
  have hγ_one : γ ⟨1, by simp [unitInterval]⟩ = z := by
    show φ'.symm (γ_chart ⟨1, _⟩) = z
    have hch : γ_chart ⟨(1 : ℝ), by simp [unitInterval]⟩ = c' := by
      change c + (((1 : ℝ) * δ : ℝ) : ℂ) = c'
      rw [hc'_def]; push_cast; ring
    rw [hch]
  -- Wrap in `Path`.
  refine ⟨{ toContinuousMap := γ, source' := hγ_zero, target' := hγ_one }, ?_⟩
  intro t
  show γ t ∈ U
  show φ'.symm (γ_chart t) ∈ U
  exact hsymm_sub_U (γ_chart t) (hγ_chart_mem_ball t)

/--
**Chart-overlap version.** If `y ∈ U ∩ V` with both `U, V` open, the same
construction (carried out with `U ∩ V` in place of `U`) gives `z ∈ U ∩ V`,
`z ∉ C`, and a path from `y` to `z` lying in `U ∩ V`.
-/
theorem exists_chart_overlap_avoidance_full
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    {y : Y} (hy : y ∈ U ∩ V) {C : Set Y} (hC : C.Finite) :
    ∃ z : Y, z ∈ U ∩ V ∧ z ∉ C ∧ JoinedIn (U ∩ V) y z := by
  exact exists_avoidance_in_open_chartedSpace_complex (hU.inter hV) hy hC

end Jacobians.Discharge.Manifold
