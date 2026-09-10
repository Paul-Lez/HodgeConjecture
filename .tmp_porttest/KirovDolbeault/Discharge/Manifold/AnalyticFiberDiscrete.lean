/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.Degree
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset

set_option autoImplicit true


/-! # From per-fibre analytic non-degeneracy to discreteness

Companion to `Jacobians.Discharge.Manifold.Degree`. ZZ20 reduced
`Degree.fibres_finite_statement` to the topological hypothesis

```
∀ f y, IsDiscrete (f ⁻¹' {y}).
```

This file gives the next reduction step: it reduces `IsDiscrete` of a fibre
of `f : X → Y` to a hypothesis about chart pullbacks of `f`. Concretely the
deliverable is a chart-pullback driver: given that the chart-pullback
representative of `f` at a point `x ∈ f ⁻¹' {y}` is analytic at the chart
image and is **not** identically equal to the chart image of `y` near it, the
point `x` is isolated in the fibre.

What this file *does* discharge:

* `analyticAt_isolated_zero_of_not_eventually` — pure-ℂ identity-theorem core:
  if `F : ℂ → ℂ` is analytic at `z₀`, takes value `c` at `z₀` and is not
  eventually `c`, then `z₀` is the only zero of `F - c` in some open
  neighbourhood. This is the per-point isolated-zero principle.

* `fiber_pointIsolated_via_chart_pullback` — manifold-side per-point
  consequence: if for every `x ∈ f ⁻¹' {y₀}` there is a chart-trivialised
  neighbourhood of `x` on which the chart-pulled-back `f` is analytic and
  not identically the chart of `y₀`, then `x` is isolated in `f ⁻¹' {y₀}`.
  The "chart trivialisation" is packaged as a homeomorphism between an open
  neighbourhood of `x` and an open subset of `ℂ`, plus a chart for `Y` near
  `y₀`. This avoids `extChartAt`-typeclass elaboration costs and keeps the
  statement self-contained.

* `isDiscrete_fiber_of_chart_pullback` — globalisation in `x`: if the
  chart-pullback non-degeneracy hypothesis holds at every `x ∈ f ⁻¹' {y₀}`,
  then `f ⁻¹' {y₀}` is `IsDiscrete`.

* `fibres_finite_of_chart_pullback` — composition with ZZ20: this discharges
  `Degree.fibres_finite_statement` from the chart-pullback non-degeneracy
  hypothesis.

What this file does **not** do (still open):

* The bridge `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → for each x, the chart pullback of f
  at x is `AnalyticAt`. This is the mathlib bridge from real-analytic
  manifold smoothness to ℂ-analytic chart pullbacks under the model with
  corners `𝓘(ℂ)`. It is left as a hypothesis-parameter on the final
  reduction lemma (no `axiom`, no gaps).

* The bridge `¬ IsConstantMap f → for each y, there is some x ∈ f⁻¹' {y}
  with chart pullback not identically equal to chart-of-y near x`. This
  is the standard analytic-continuation step on a connected manifold and is
  also passed as a hypothesis-parameter.

The point of this file: reduce *two* missing classical inputs (chart
analyticity of `ContMDiff … ω`, and analytic-continuation
non-degeneracy on connected manifolds) to a *single* clean condition on
chart pullbacks, and execute the identity-theorem core of the argument
unconditionally on the ℂ-analytic side.
-/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-! ## ℂ-analytic core: per-point isolated zero -/

/-- **Per-point identity theorem (zero version).** If `F : ℂ → ℂ` is analytic
at `z₀`, `F z₀ = 0`, and `F` is not identically zero on any neighbourhood of
`z₀`, then there is an open set `U ∋ z₀` on which `z₀` is the unique zero of
`F`. -/
lemma analyticAt_isolated_zero_of_not_eventually_zero
    {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F z₀) (hz : F z₀ = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 z₀, F z = 0) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ U ∩ {z | F z = 0} = {z₀} := by
  -- Identity-theorem dichotomy: either `F` is eventually 0 near `z₀` (excluded)
  -- or `F ≠ 0` on a punctured neighbourhood of `z₀`.
  rcases hF.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact (hne h).elim
  · -- `h : ∀ᶠ z in 𝓝[≠] z₀, F z ≠ 0`. Extract an open punctured neighbourhood.
    rw [eventually_nhdsWithin_iff] at h
    rcases (mem_nhds_iff.mp h) with ⟨U, hU_sub, hU_open, hU_mem⟩
    refine ⟨U, hU_open, hU_mem, ?_⟩
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨hU_mem, ?_⟩, ?_⟩
    · simpa using hz
    · intro z hz_mem
      rcases hz_mem with ⟨hzU, hzF⟩
      by_contra hne_z
      -- `z ∈ U`, `z ≠ z₀`, `F z = 0`, but the punctured-nbhd condition forbids it.
      have : F z ≠ 0 := hU_sub hzU hne_z
      exact this hzF

/-- **Per-point identity theorem (value version).** Same as
`analyticAt_isolated_zero_of_not_eventually_zero` but framed as
"`F z = c` is isolated at `z₀`" for an arbitrary target value `c`. -/
lemma analyticAt_isolated_value_of_not_eventually_const
    {F : ℂ → ℂ} {z₀ c : ℂ}
    (hF : AnalyticAt ℂ F z₀) (hz : F z₀ = c)
    (hne : ¬ ∀ᶠ z in 𝓝 z₀, F z = c) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ U ∩ {z | F z = c} = {z₀} := by
  -- Apply the zero version to `G := F - (fun _ => c)`.
  set G : ℂ → ℂ := fun z => F z - c with hG_def
  have hG : AnalyticAt ℂ G z₀ := hF.sub analyticAt_const
  have hG0 : G z₀ = 0 := by simp [hG_def, hz]
  have hGne : ¬ ∀ᶠ z in 𝓝 z₀, G z = 0 := by
    intro hG_zero
    apply hne
    filter_upwards [hG_zero] with z hz
    exact sub_eq_zero.mp hz
  rcases analyticAt_isolated_zero_of_not_eventually_zero hG hG0 hGne with
    ⟨U, hU_open, hU_mem, hU_eq⟩
  refine ⟨U, hU_open, hU_mem, ?_⟩
  -- Rewrite `{z | G z = 0}` as `{z | F z = c}`.
  have hset : {z : ℂ | G z = 0} = {z : ℂ | F z = c} := by
    ext z; simp [hG_def, sub_eq_zero]
  rw [hset] at hU_eq
  exact hU_eq

/-! ## Manifold side: per-fiber chart-pullback driver

We package the chart-pullback hypothesis as an explicit data triple at each
fibre point: an open neighbourhood `V ⊆ X`, an open `W ⊆ ℂ`, and a homeo
between them sending `x` to `z₀`, together with the chart pullback being
analytic and the non-degeneracy hypothesis on it. This avoids touching the
`ChartedSpace` typeclass plumbing while staying mathematically faithful. -/

/-- **Chart-pullback isolation data.** For a map `f : X → Y` between
topological spaces, point `x : X` and value `y₀ : Y`, this records a
chart-pullback witness that `x` is isolated in `f ⁻¹' {y₀}`.

* `V` — open neighbourhood of `x` in `X`,
* `chartX : V → ℂ` — homeomorphic image of `V` into ℂ,
* `chartY : Y → ℂ` — a continuous "chart-like" function with `chartY y₀ = c`
  for some constant `c`, and the property that `chartY` separates `y₀`
  from other values *on `f '' V`*: `f x' = y₀ ↔ chartY (f x') = c` for
  `x' ∈ V`.
* `F : ℂ → ℂ` — the chart-pulled-back representation `chartY ∘ f ∘ chartX⁻¹`,
* `hFA` — `F` is analytic at `chartX x`,
* `hFne` — `F` is not eventually equal to `c` near `chartX x`.

We do **not** assume `F z = chartY (f (chartX⁻¹ z))` globally, only that the
zero-set comparison goes through, which is the only thing the proof uses.
-/
structure ChartPullbackData {X : Type u} [TopologicalSpace X]
    {Y : Type v} (f : X → Y) (x : X) (y₀ : Y) where
  /-- Open neighbourhood of `x`. -/
  V : Set X
  hV_open : IsOpen V
  hxV : x ∈ V
  /-- Chart image: an open subset of ℂ. -/
  W : Set ℂ
  hW_open : IsOpen W
  /-- Homeomorphism from `V` onto `W`. -/
  φ : V → W
  hφ : Continuous φ
  hφ_inv : Function.Bijective φ
  /-- Image of `x` under the chart. -/
  z₀ : ℂ
  hz₀ : (φ ⟨x, hxV⟩ : ℂ) = z₀
  hz₀W : z₀ ∈ W
  /-- Chart-pulled-back representation. -/
  F : ℂ → ℂ
  /-- Target chart value of `y₀`. -/
  c : ℂ
  hFA : AnalyticAt ℂ F z₀
  hFne : ¬ ∀ᶠ z in 𝓝 z₀, F z = c
  /-- Compatibility: on `V`, the fibre condition `f x' = y₀` is detected by
  `F` evaluated at the chart image. The user supplies this; the proof of
  `f x' = y₀ ↔ F (φ x') = c` is exactly what the (chart_Y ∘ f ∘ chart_X⁻¹)
  story would give. -/
  hCompat :
    ∀ x' : V, f x'.1 = y₀ ↔ F (φ x') = c

/-- **Per-point isolation from chart-pullback data.** Given chart-pullback
data witnessing that the chart-pulled-back `f` is analytic and not eventually
constant at `chartX x`, the point `x` is isolated in `f ⁻¹' {y₀}`. -/
lemma fiber_pointIsolated_via_chart_pullback
    {X : Type u} [TopologicalSpace X]
    {Y : Type v}
    (f : X → Y) (y₀ : Y) (x : X) (hx : f x = y₀)
    (D : ChartPullbackData f x y₀) :
    ∃ U : Set X, IsOpen U ∧ U ∩ f ⁻¹' {y₀} = {x} := by
  -- Use the ℂ-side identity theorem to get `U_ℂ ⊆ ℂ` open isolating `z₀`.
  rcases analyticAt_isolated_value_of_not_eventually_const D.hFA
      (c := D.c) (z₀ := D.z₀)
      (by
        -- We need `F D.z₀ = D.c`. From `hCompat` at `x`, `f x = y₀ ↔ F (φ x) = c`.
        have hcomp := (D.hCompat ⟨x, D.hxV⟩).mp (by simpa using hx)
        -- `hcomp : F (↑(D.φ ⟨x, D.hxV⟩)) = D.c`; rewrite via `D.hz₀`.
        rw [← D.hz₀]; exact hcomp)
      D.hFne with
    ⟨U_C, hU_C_open, hz₀_mem, hU_C_eq⟩
  -- Pull back `U_C` along the chart to get an open subset of `X`.
  -- `U := V ∩ φ⁻¹' (U_C ∩ W)` lives in `X` (regarded via the embedding).
  -- We construct `U := { x' : X | x' ∈ V ∧ ∃ h : x' ∈ V, (φ ⟨x', h⟩ : ℂ) ∈ U_C }`.
  classical
  let U : Set X := {x' : X | ∃ h : x' ∈ D.V, (D.φ ⟨x', h⟩ : ℂ) ∈ U_C}
  have hxU : x ∈ U := ⟨D.hxV, by rw [D.hz₀]; exact hz₀_mem⟩
  -- `U` is open in `X`: it is the preimage under the inclusion `V ↪ X` of
  -- the open set `(↑) ⁻¹' U_C` in the subspace `V`, intersected with `V`.
  -- Since `V` is open in `X`, "open in `V`" lifts to "open in `X`".
  have hU_open : IsOpen U := by
    -- Compose `D.φ` with the subtype-val map on `D.W` to get `g : D.V → ℂ`,
    -- continuous, with `g ⟨x', h⟩ = (D.φ ⟨x', h⟩ : ℂ)`.
    set g : D.V → ℂ := fun v => ((D.φ v : D.W) : ℂ) with hg_def
    have hg_cont : Continuous g :=
      (continuous_subtype_val).comp D.hφ
    have h_pre_open_in_V : IsOpen (g ⁻¹' U_C) :=
      hg_cont.isOpen_preimage U_C hU_C_open
    -- The inclusion `V ↪ X` is an open embedding (since `V` is open).
    have h_emb : IsOpenEmbedding ((↑) : D.V → X) :=
      D.hV_open.isOpenEmbedding_subtypeVal
    -- `U = (↑) '' (g ⁻¹' U_C)`.
    have hU_eq_image :
        U = ((↑) : D.V → X) '' (g ⁻¹' U_C) := by
      ext x'
      constructor
      · rintro ⟨hx'V, hφxU⟩
        refine ⟨⟨x', hx'V⟩, ?_, rfl⟩
        simpa [hg_def, Set.mem_preimage] using hφxU
      · rintro ⟨⟨x'', hx''V⟩, hmem, rfl⟩
        refine ⟨hx''V, ?_⟩
        simpa [hg_def, Set.mem_preimage] using hmem
    rw [hU_eq_image]
    exact h_emb.isOpenMap _ h_pre_open_in_V
  refine ⟨U, hU_open, ?_⟩
  -- Show `U ∩ f⁻¹' {y₀} = {x}`.
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨hxU, by simpa using hx⟩, ?_⟩
  rintro x' ⟨⟨hx'V, hφx'⟩, hf_x'⟩
  -- `hf_x' : f x' = y₀`; by `hCompat`, `F (φ ⟨x', hx'V⟩) = D.c`.
  have hFc : D.F (D.φ ⟨x', hx'V⟩ : ℂ) = D.c := (D.hCompat ⟨x', hx'V⟩).mp (by
    simpa using hf_x')
  -- From `hU_C_eq : U_C ∩ {z | F z = c} = {z₀}`, `(φ ⟨x', hx'V⟩ : ℂ) = z₀`.
  have hz_eq : (D.φ ⟨x', hx'V⟩ : ℂ) = D.z₀ := by
    have hmem : (D.φ ⟨x', hx'V⟩ : ℂ) ∈ U_C ∩ {z | D.F z = D.c} :=
      ⟨hφx', hFc⟩
    rw [hU_C_eq] at hmem
    simpa using hmem
  -- Combine `hz_eq` with `D.hz₀` and injectivity of `D.φ` (via `hφ_inv`).
  have h_eq_x : (⟨x', hx'V⟩ : D.V) = ⟨x, D.hxV⟩ := by
    apply D.hφ_inv.1
    apply Subtype.ext
    -- `(D.φ ⟨x', hx'V⟩ : ℂ) = D.z₀ = (D.φ ⟨x, D.hxV⟩ : ℂ)`.
    rw [hz_eq, ← D.hz₀]
  -- Read off `x' = x`.
  exact congrArg Subtype.val h_eq_x

/-! ## Manifold side: globalisation of point-isolation to `IsDiscrete` -/

/-- **Globalised: `IsDiscrete` of a fibre from per-point chart data.** If for
every `x ∈ f ⁻¹' {y₀}` we have a `ChartPullbackData` witness, then the fibre
`f ⁻¹' {y₀}` carries the discrete subspace topology. -/
lemma isDiscrete_fiber_of_chart_pullback
    {X : Type u} [TopologicalSpace X]
    {Y : Type v}
    (f : X → Y) (y₀ : Y)
    (h : ∀ x ∈ f ⁻¹' {y₀}, ChartPullbackData f x y₀) :
    IsDiscrete (f ⁻¹' {y₀}) := by
  rw [isDiscrete_iff_forall_exists_isOpen]
  intro x hx
  have hx' : f x = y₀ := by simpa using hx
  rcases fiber_pointIsolated_via_chart_pullback (f := f) (y₀ := y₀)
      (x := x) hx' (h x hx) with ⟨U, hU_open, hU_eq⟩
  exact ⟨U, hU_open, hU_eq⟩

/-! ## Composition with ZZ20: discharge of `fibres_finite_statement` -/

/-- **Discharge of `fibres_finite_statement` from chart-pullback hypothesis.**
Composing `fibres_finite_of_all_fibers_isDiscrete` (ZZ20) with
`isDiscrete_fiber_of_chart_pullback` reduces the full classical
`fibres_finite_statement` to a single clean chart-pullback hypothesis: for
every analytic non-constant `f` and every `y`, every fibre point admits a
`ChartPullbackData` witness.

This is the maximal reduction available without bridging
`ContMDiff … ω → AnalyticAt` on chart pullbacks, which is itself an
unstated mathlib fact at this pin. -/
lemma fibres_finite_of_chart_pullback
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_chart : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
      ∀ y : Y, ∀ x ∈ f ⁻¹' {y}, ChartPullbackData f x y) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
      ∀ y : Y, (f ⁻¹' {y}).Finite := by
  intro f hf hnc y
  refine fiber_finite_of_isDiscrete hf.continuous y ?_
  exact isDiscrete_fiber_of_chart_pullback f y (h_chart f hf hnc y)

end Degree
end ContMDiff
end Jacobians.Discharge
