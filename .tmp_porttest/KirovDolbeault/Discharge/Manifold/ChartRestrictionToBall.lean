/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Chart restriction whose target is a metric ball

Given a charted space `Y` modelled on `ℂ` and a point `x : Y`, the canonical
chart `chartAt ℂ x : OpenPartialHomeomorph Y ℂ` has an open target in `ℂ`
containing the chart image `(chartAt ℂ x) x`. Picking any `r > 0` with
`Metric.ball ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target` (which exists by
`Metric.isOpen_iff` applied to the open target), we restrict the chart to the
preimage of this ball, producing a sub-open-partial-homeomorphism whose target
is exactly `Metric.ball ((chartAt ℂ x) x) r` and whose underlying function
agrees with the chart on its (smaller) source.

## Main result

* `chart_restrict_to_ball` — produces such a radius `r > 0` and a restricted
  `OpenPartialHomeomorph Y ℂ` whose target is the open ball, whose underlying
  function is the original chart, and whose source sits inside the original
  chart source.

No `axiom`, no gaps. -/

noncomputable section

open Set
open scoped Topology

namespace Jacobians.Discharge

/-- **Chart restriction to a metric ball target.**
For a charted space `Y` modelled on `ℂ` and a point `x : Y`, there exists a
radius `r > 0` and an `OpenPartialHomeomorph Y ℂ` whose target is the open
ball `Metric.ball ((chartAt ℂ x) x) r`, whose function coercion equals
`chartAt ℂ x`, and whose source is contained in the original chart source. -/
theorem chart_restrict_to_ball
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (x : Y) :
    ∃ (r : ℝ) (_ : 0 < r) (φ' : OpenPartialHomeomorph Y ℂ),
      x ∈ φ'.source ∧
      φ'.target = Metric.ball ((chartAt ℂ x) x) r ∧
      (φ' : Y → ℂ) = (chartAt ℂ x : Y → ℂ) ∧
      φ'.source ⊆ (chartAt ℂ x).source := by
  -- Notation for the original chart and its image of `x`.
  set φ : OpenPartialHomeomorph Y ℂ := chartAt ℂ x with hφ
  set c : ℂ := φ x with hc
  -- (1) `c = φ x ∈ φ.target` because `x ∈ φ.source` by `mem_chart_source`.
  have hx_src : x ∈ φ.source := mem_chart_source ℂ x
  have hc_target : c ∈ φ.target := φ.map_source hx_src
  -- (2) `φ.target` is open in `ℂ`, so we extract a radius around `c`.
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    Metric.isOpen_iff.mp φ.open_target c hc_target
  refine ⟨r, hr_pos, ?_, ?_, ?_, ?_, ?_⟩
  -- The target ball, as a subset of `φ.target`.
  · -- Build the restricted `OpenPartialHomeomorph` directly. The underlying
    -- `PartialEquiv` is the `IsImage`-restriction of `φ.toPartialEquiv`
    -- along `s := φ ⁻¹' Metric.ball c r` ↔ `t := Metric.ball c r`.
    refine
      { toPartialEquiv :=
          (PartialEquiv.IsImage.of_preimage_eq
              (e := φ.toPartialEquiv)
              (s := (φ.toPartialEquiv : Y → ℂ) ⁻¹' Metric.ball c r)
              (t := Metric.ball c r) rfl).restr
        open_source := ?_
        open_target := ?_
        continuousOn_toFun := ?_
        continuousOn_invFun := ?_ }
    -- Source = `φ.source ∩ (φ : Y → ℂ) ⁻¹' Metric.ball c r`, open via
    -- `OpenPartialHomeomorph.isOpen_inter_preimage`.
    · have h1 : IsOpen (Metric.ball c r) := Metric.isOpen_ball
      show IsOpen ((PartialEquiv.IsImage.of_preimage_eq
          (e := φ.toPartialEquiv)
          (s := (φ.toPartialEquiv : Y → ℂ) ⁻¹' Metric.ball c r)
          (t := Metric.ball c r) rfl).restr.source)
      rw [PartialEquiv.IsImage.restr_source]
      -- `φ.toPartialEquiv.source = φ.source` (field projection).
      change IsOpen (φ.source ∩ (φ : Y → ℂ) ⁻¹' Metric.ball c r)
      exact φ.isOpen_inter_preimage h1
    -- Target = `φ.target ∩ Metric.ball c r = Metric.ball c r` (ball ⊆ target).
    · have hball_open : IsOpen (Metric.ball c r) := Metric.isOpen_ball
      have htar : φ.target ∩ Metric.ball c r = Metric.ball c r :=
        inter_eq_right.mpr hr_sub
      -- The restricted target is `φ.target ∩ Metric.ball c r = Metric.ball c r`.
      show IsOpen ((PartialEquiv.IsImage.of_preimage_eq
          (e := φ.toPartialEquiv)
          (s := (φ.toPartialEquiv : Y → ℂ) ⁻¹' Metric.ball c r)
          (t := Metric.ball c r) rfl).restr.target)
      rw [PartialEquiv.IsImage.restr_target, htar]
      exact hball_open
    -- Continuity of `φ` on the smaller source: restrict from `φ.continuousOn`.
    · -- The restricted source is `φ.source ∩ (φ.toPartialEquiv) ⁻¹' ball`,
      -- a subset of `φ.source`. The PartialEquiv toFun = OpenPartialHomeomorph
      -- toFun' (defEq), so we can apply `φ.continuousOn.mono`.
      have hsub : (PartialEquiv.IsImage.of_preimage_eq
          (e := φ.toPartialEquiv)
          (s := (φ.toPartialEquiv : Y → ℂ) ⁻¹' Metric.ball c r)
          (t := Metric.ball c r) rfl).restr.source ⊆ φ.source := by
        intro y hy
        rw [PartialEquiv.IsImage.restr_source] at hy
        exact hy.1
      exact φ.continuousOn.mono hsub
    -- Continuity of `φ.symm` on the smaller target = ball: it's a subset of
    -- `φ.target`, where `φ.symm` is continuous.
    · have hsub : (PartialEquiv.IsImage.of_preimage_eq
          (e := φ.toPartialEquiv)
          (s := (φ.toPartialEquiv : Y → ℂ) ⁻¹' Metric.ball c r)
          (t := Metric.ball c r) rfl).restr.target ⊆ φ.target := by
        intro z hz
        rw [PartialEquiv.IsImage.restr_target] at hz
        exact hz.1
      exact φ.continuousOn_symm.mono hsub
  -- `x ∈ source`: `x ∈ φ.source` and `φ x = c ∈ Metric.ball c r`.
  · -- The OpenPartialHomeomorph source projects to the underlying
    -- PartialEquiv source = `φ.source ∩ (φ.toPartialEquiv) ⁻¹' Metric.ball c r`.
    show x ∈ (PartialEquiv.IsImage.of_preimage_eq
        (e := φ.toPartialEquiv)
        (s := (φ.toPartialEquiv : Y → ℂ) ⁻¹' Metric.ball c r)
        (t := Metric.ball c r) rfl).restr.source
    rw [PartialEquiv.IsImage.restr_source]
    refine ⟨hx_src, ?_⟩
    show (φ.toPartialEquiv : Y → ℂ) x ∈ Metric.ball c r
    have hxc : (φ.toPartialEquiv : Y → ℂ) x = c := by
      change φ x = c; exact hc.symm
    rw [hxc]
    exact Metric.mem_ball_self hr_pos
  -- `target = Metric.ball c r`.
  · have htar : φ.target ∩ Metric.ball c r = Metric.ball c r :=
      inter_eq_right.mpr hr_sub
    show (PartialEquiv.IsImage.of_preimage_eq
        (e := φ.toPartialEquiv)
        (s := (φ.toPartialEquiv : Y → ℂ) ⁻¹' Metric.ball c r)
        (t := Metric.ball c r) rfl).restr.target = Metric.ball c r
    rw [PartialEquiv.IsImage.restr_target]
    exact htar
  -- Function coercion is unchanged.
  · rfl
  -- Source ⊆ original chart source.
  · intro y hy
    -- `hy : y ∈ φ'.source = φ.source ∩ (φ.toPartialEquiv) ⁻¹' Metric.ball c r`.
    have hy' : y ∈ φ.source ∩ (φ.toPartialEquiv : Y → ℂ) ⁻¹' Metric.ball c r := hy
    exact hy'.1

end Jacobians.Discharge
