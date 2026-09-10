/-
Copyright (c) 2026 Jacobian Lean Challenge contributors. All rights reserved.

Foundation chip ZZ165c: refinement of `ZZ165b.Path.exists_chart_subdivision`
that uses *ball-restricted* charts (from `ZZ164c.chart_restrict_to_ball`).

For a continuous path `γ : Path p q` in a `ChartedSpace ℂ Y`, we produce a
finite monotone partition of `[0,1]` together with, for each piece, an
`OpenPartialHomeomorph Y ℂ` whose **target is an open ball** in `ℂ`, and
whose source covers the image of the piece. This is the form needed by
downstream chips that integrate against ball-shaped chart targets.

The combinatorics is the same as ZZ165b: the open cover
`{ γ ⁻¹' (φ_y).source }_{y : I}` of `I`, refined via
`exists_monotone_Icc_subset_open_cover_unitInterval`. The only new ingredient
is that for each `y` we use the ball-restricted chart `φ_y` from
`chart_restrict_to_ball` instead of the raw `chartAt ℂ (γ y)`.

No `axiom`, no gaps.
-/
import KirovDolbeault.Discharge.Manifold.ChartRestrictionToBall
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Path

namespace Jacobians.Discharge.Manifold

open Set unitInterval Jacobians.Discharge

/--
Path subdivision by **ball-targeted** charts: any continuous path
`γ : Path p q` in a charted space `Y` over `ℂ` admits a finite monotone
partition `t : ℕ → I` with `t 0 = 0`, eventually `t m = 1`, together with,
for each piece `i`, an `OpenPartialHomeomorph Y ℂ` whose target is an open
ball in `ℂ` (with positive radius and a chosen centre) and whose source
contains the image of `γ` on `Icc (t i) (t (i+1))`.

Strategy:
1. For each `y : I`, `chart_restrict_to_ball (γ y)` produces a ball-restricted
   chart `φ y` with `γ y ∈ (φ y).source`.
2. The family `c y := γ ⁻¹' (φ y).source` is an open cover of `I` (each is
   open as a preimage of an open set under a continuous map; `y ∈ c y`
   because `γ y ∈ (φ y).source`).
3. Apply `exists_monotone_Icc_subset_open_cover_unitInterval` to refine to a
   monotone partition with one Lebesgue index `y i : I` per piece.
4. Take the ball-restricted chart at `γ (y i)` for piece `i`.
-/
theorem Path.exists_ball_chart_subdivision
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {p q : Y} (γ : Path p q) :
    ∃ (t : ℕ → I) (φ : ℕ → OpenPartialHomeomorph Y ℂ)
      (r : ℕ → ℝ) (centers : ℕ → ℂ),
      t 0 = 0 ∧ Monotone t ∧ (∃ N, ∀ m ≥ N, t m = 1) ∧
      (∀ i, 0 < r i) ∧
      (∀ i, (φ i).target = Metric.ball (centers i) (r i)) ∧
      (∀ i, ∀ s ∈ Icc (t i) (t (i + 1)), γ s ∈ (φ i).source) := by
  -- For each `y : I`, choose a ball-restricted chart at `γ y`.
  choose r hr_pos φ hy_src hφ_target _hφ_eq _hφ_sub_src using
    fun y : I => chart_restrict_to_ball (γ y)
  -- Open cover of `I` by preimages of ball-chart sources.
  let c : I → Set I := fun y => γ ⁻¹' (φ y).source
  have hc_open : ∀ y, IsOpen (c y) := fun y =>
    (φ y).open_source.preimage γ.continuous
  have hc_cover : (univ : Set I) ⊆ ⋃ y, c y := by
    intro x _
    refine mem_iUnion.mpr ⟨x, ?_⟩
    exact hy_src x
  -- Refine to a finite monotone partition with one ball-chart-index per piece.
  obtain ⟨t, ht0, ht_mono, ⟨N, htN⟩, hpiece⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc_open hc_cover
  -- For each piece `i`, choose the Lebesgue index `y i : I`.
  choose yidx hyidx using hpiece
  refine ⟨t, fun i => φ (yidx i), fun i => r (yidx i),
         fun i => (chartAt ℂ (γ (yidx i))) (γ (yidx i)),
         ht0, ht_mono, ⟨N, htN⟩, ?_, ?_, ?_⟩
  · intro i; exact hr_pos (yidx i)
  · intro i; exact hφ_target (yidx i)
  · intro i s hs; exact hyidx i hs

end Jacobians.Discharge.Manifold
