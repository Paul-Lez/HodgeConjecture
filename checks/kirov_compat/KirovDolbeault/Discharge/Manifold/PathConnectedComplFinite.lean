/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez

Chip ZZ165 (retry-2): the global path-connected gluing chip.

For a connected, T2 charted space `Y` modelled on `ℂ`, the complement of any
finite set `C ⊆ Y` is path-connected (provided it is nonempty).

Strategy:
1. `Y` is path-connected (ZZ162 + ZZ163).
2. Pick a basepoint `p ∈ Cᶜ`. For any `q ∈ Cᶜ`, take a path `γ` from `p`
   to `q` (`PathConnectedSpace.somePath` / `PathConnectedSpace.joined`).
3. Subdivide `γ` into finitely many pieces, each contained in the source of
   a ball-restricted chart `φ_i` (`Path.exists_ball_chart_subdivision`,
   ZZ165c).
4. For each interior endpoint `z_i := γ(t_i)`, perturb it to a point
   `z'_i` lying in the chart-overlap `φ_{i-1}.source ∩ φ_i.source`,
   outside `C`, with a chart-local path `z_i ⇝ z'_i` inside that overlap
   (`exists_avoidance_in_open_chartedSpace_complex`, ZZ165e). The boundary
   endpoints stay fixed: `z'_0 := p`, `z'_N := q`.
5. For each piece `i`, both `z'_i` and `z'_{i+1}` lie in `φ_i.source` and
   outside `C`. Use `chart_local_detour_of_pathConnected_complement` (ZZ164)
   together with `Set.Countable.isPathConnected_ball_diff_complex` (ZZ164b)
   to get a path from `z'_i` to `z'_{i+1}` in `Cᶜ ∩ φ_i.source ⊆ Cᶜ`.
6. Concatenate all these `JoinedIn Cᶜ` segments to obtain a path from `p`
   to `q` in `Cᶜ`.

No `axiom`, no gaps.
-/
import KirovDolbeault.Discharge.Manifold.ChartedSpaceLocPathConnected
import KirovDolbeault.Discharge.Manifold.ConnectedManifoldPathConnected
import KirovDolbeault.Discharge.Manifold.ChartLocalDetour
import KirovDolbeault.Discharge.Manifold.IsPathConnectedBallMinusCountable
import KirovDolbeault.Discharge.Manifold.ChartRestrictionToBall
import KirovDolbeault.Discharge.Manifold.PathSubdivisionByBallCharts
import KirovDolbeault.Discharge.Manifold.ChartOverlapAvoidanceFull
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected

open scoped Manifold Topology ContDiff

noncomputable section

namespace Jacobians.Discharge.Manifold

open Set unitInterval Topology Jacobians.Discharge

/-- **Auxiliary: path-connected piece inside a ball-chart source minus `C`.**

If `φ : OpenPartialHomeomorph Y ℂ` has `φ.target = Metric.ball center r` for
some `0 < r`, and `C ⊆ Y` is finite, then for any two points
`u, v ∈ φ.source` with `u ∉ C` and `v ∉ C`, we have
`JoinedIn (Cᶜ ∩ φ.source) u v`. -/
private lemma joinedIn_compl_in_ball_chart_source
    {Y : Type*} [TopologicalSpace Y]
    {φ : OpenPartialHomeomorph Y ℂ} {center : ℂ} {r : ℝ}
    (hr_pos : 0 < r) (htarget : φ.target = Metric.ball center r)
    {C : Set Y} (hC_fin : C.Finite)
    {u v : Y} (hu_src : u ∈ φ.source) (hv_src : v ∈ φ.source)
    (hu_nc : u ∉ C) (hv_nc : v ∉ C) :
    JoinedIn ((Cᶜ : Set Y) ∩ φ.source) u v := by
  -- Image of `φ.source ∩ C` under `φ` is finite, hence countable.
  have h_img_fin : (φ '' (φ.source ∩ C)).Finite :=
    (hC_fin.inter_of_right φ.source).image φ
  have h_img_countable : (φ '' (φ.source ∩ C)).Countable := h_img_fin.countable
  -- Path-connectedness of `Metric.ball center r \ φ '' (φ.source ∩ C)`.
  have h_pc_ball :
      IsPathConnected (Metric.ball center r \ φ '' (φ.source ∩ C)) :=
    h_img_countable.isPathConnected_ball_diff_complex hr_pos
  -- Rewrite as `φ.target \ φ '' (φ.source ∩ C)`.
  have hPC : IsPathConnected (φ.target \ φ '' (φ.source ∩ C)) := by
    rw [htarget]; exact h_pc_ball
  -- Apply the chart-local detour lemma from ZZ164.
  exact OpenPartialHomeomorph.chart_local_detour_of_pathConnected_complement
    (φ := φ) hC_fin hPC hu_src hv_src hu_nc hv_nc

/-- The image of a continuous path between two points lies in the
ambient space; the parameter `1 : I` lands at `q`. -/
private lemma path_target_eq {Y : Type*} [TopologicalSpace Y]
    {p q : Y} (γ : Path p q) : γ (1 : I) = q := γ.target

private lemma path_source_eq {Y : Type*} [TopologicalSpace Y]
    {p q : Y} (γ : Path p q) : γ (0 : I) = p := γ.source

/-- **Inductive gluing along the chart subdivision.**

Given a path `γ : Path p q` in a `ChartedSpace ℂ Y` (with `Y` T2 — we don't
actually need T2 for this lemma but it costs nothing), a finite set `C`,
a monotone partition `t : ℕ → I` with `t 0 = 0` and `t N = 1`, and a
ball-chart `φ i` covering each piece, the lemma asserts: for every
`k ≤ N`, if `γ (t 0) = p ∈ Cᶜ` and `γ (t k) ∈ Cᶜ`, then there is a
`JoinedIn Cᶜ` from `p` to `γ (t k)`.

We proceed by induction on `k` and weave together the chart-overlap
perturbations. -/
private lemma joinedIn_compl_along_subdivision
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {C : Set Y} (hC_fin : C.Finite)
    {p q : Y} (γ : Path p q) (hp_nc : p ∉ C) (hq_nc : q ∉ C)
    (t : ℕ → I) (φ : ℕ → OpenPartialHomeomorph Y ℂ)
    (rfun : ℕ → ℝ) (cfun : ℕ → ℂ)
    (ht0 : t 0 = 0) (ht_mono : Monotone t)
    (N : ℕ) (htN : t N = 1)
    (hr_pos : ∀ i, 0 < rfun i)
    (hφ_target : ∀ i, (φ i).target = Metric.ball (cfun i) (rfun i))
    (hpiece : ∀ i, ∀ s ∈ Set.Icc (t i) (t (i + 1)), γ s ∈ (φ i).source) :
    JoinedIn (Cᶜ : Set Y) p q := by
  -- We first establish, for every `0 ≤ k ≤ N`, a chart-source-anchored
  -- statement: there exists `w ∈ φ_?.source` outside `C` joined to `p` in
  -- `Cᶜ`, and from `w` we can continue. Concretely: by induction on `k`
  -- we build `w_k ∈ φ k .source ∩ Cᶜ` joined to `p` in `Cᶜ`, with
  -- `w_0 := p` (using `p ∈ φ 0 .source` from `t 0 = 0` and the piece `0`).
  --
  -- At step `k`, we have `w_k ∈ (φ k).source ∩ Cᶜ`. The next piece-endpoint
  -- `γ (t (k+1))` lies in `(φ k).source` (by `hpiece k` at `s = t (k+1)`).
  -- It also lies in `(φ (k+1)).source` if `k+1 < N` (`hpiece (k+1)` at
  -- `s = t (k+1)`). Apply `exists_avoidance_in_open_chartedSpace_complex`
  -- to the open overlap to perturb to `w_{k+1} ∈ overlap ∩ Cᶜ`, with a
  -- `JoinedIn overlap` path. Then connect `w_k` to `w_{k+1}` inside
  -- `(φ k).source ∩ Cᶜ` via `joinedIn_compl_in_ball_chart_source`.
  --
  -- Final step `k = N`: `γ (t N) = γ 1 = q`. Use the last piece (index
  -- `N - 1`) to connect `w_{N-1}` directly to `q` (since `q ∈ Cᶜ` and
  -- `q ∈ (φ (N-1)).source` by `hpiece (N-1)` at `s = t N = 1`).
  --
  -- Implementation: we package everything as a single `Nat.rec`-style
  -- statement.
  -- We prove: `∀ k, k ≤ N → ∃ w : Y, w ∈ Cᶜ ∧ JoinedIn (Cᶜ : Set Y) p w ∧
  --   (k < N → w ∈ (φ k).source) ∧ (k = N → w = q)`.
  suffices H : ∀ k, k ≤ N →
      ∃ w : Y, w ∉ C ∧ JoinedIn (Cᶜ : Set Y) p w ∧
        (k < N → w ∈ (φ k).source) ∧ (k = N → w = q) by
    obtain ⟨w, _, hjoin, _, hw_eq⟩ := H N le_rfl
    rw [hw_eq rfl] at hjoin
    exact hjoin
  intro k hk
  induction k with
  | zero =>
    -- Base: `w := p`. Need `p ∉ C` (given), constant path `JoinedIn Cᶜ p p`,
    -- `p ∈ (φ 0).source` if `0 < N`, and the `0 = N` case is vacuous unless
    -- `N = 0`, in which case `p = q` (since `γ` connects `p` to `q` and
    -- if there's only one partition step there's still a path; but the
    -- statement `0 = N → p = q` requires care).
    refine ⟨p, hp_nc, JoinedIn.refl ?_, ?_, ?_⟩
    · simp [hp_nc]
    · intro _hlt
      -- `p = γ 0 = γ (t 0)`, lies in `(φ 0).source` via `hpiece 0`.
      have hp_eq : p = γ (t 0) := by
        rw [ht0]; exact (path_source_eq γ).symm
      rw [hp_eq]
      have ht_mem : t 0 ∈ Set.Icc (t 0) (t 1) :=
        ⟨le_rfl, ht_mono (Nat.le_succ 0)⟩
      exact hpiece 0 (t 0) ht_mem
    · intro h_eq
      -- `0 = N`, so `t N = t 0 = 0`, but `t N = 1`. Contradiction.
      exfalso
      have h1 : t N = (1 : I) := htN
      have h2 : t N = t 0 := by rw [← h_eq]
      have h3 : t 0 = (1 : I) := h2 ▸ h1
      rw [ht0] at h3
      have h4 : ((0 : I) : ℝ) = ((1 : I) : ℝ) := congrArg Subtype.val h3
      norm_num at h4
  | succ k ih =>
    have hk' : k ≤ N := Nat.le_of_succ_le hk
    obtain ⟨w_k, hw_k_nc, hjoin_k, hw_k_src, _⟩ := ih hk'
    -- We need `k < N` to use `hw_k_src`. Since `k+1 ≤ N`, we have `k < N`.
    have hk_lt_N : k < N := hk
    have hw_k_in : w_k ∈ (φ k).source := hw_k_src hk_lt_N
    -- The next-endpoint parameter point.
    -- `γ (t (k+1)) ∈ (φ k).source` from `hpiece k`.
    have hs_next_in_k : t (k + 1) ∈ Set.Icc (t k) (t (k + 1)) :=
      ⟨ht_mono (Nat.le_succ k), le_rfl⟩
    have hγ_in_k : γ (t (k + 1)) ∈ (φ k).source :=
      hpiece k (t (k + 1)) hs_next_in_k
    -- Case-split on whether `k + 1 = N` or `k + 1 < N`.
    by_cases hN_eq : k + 1 = N
    · -- Final step: `t (k+1) = t N = 1`, so `γ (t (k+1)) = q`.
      have hs_next_one : t (k + 1) = (1 : I) := by rw [hN_eq]; exact htN
      have hγ_eq_q : γ (t (k + 1)) = q := by
        rw [hs_next_one]
        exact path_target_eq γ
      -- Connect `w_k` to `q` inside `(φ k).source ∩ Cᶜ`.
      have hq_in_φk : q ∈ (φ k).source := hγ_eq_q ▸ hγ_in_k
      have hjoin_kq : JoinedIn ((Cᶜ : Set Y) ∩ (φ k).source) w_k q :=
        joinedIn_compl_in_ball_chart_source (hr_pos k) (hφ_target k) hC_fin
          hw_k_in hq_in_φk hw_k_nc hq_nc
      have hjoin_kq' : JoinedIn (Cᶜ : Set Y) w_k q :=
        hjoin_kq.mono (fun _ hx => hx.1)
      refine ⟨q, hq_nc, hjoin_k.trans hjoin_kq', ?_, ?_⟩
      · intro hlt
        -- `k + 1 < N` contradicts `k + 1 = N`.
        exfalso; omega
      · intro _; rfl
    · -- Non-final: `k + 1 < N`, so `γ (t (k+1)) ∈ (φ (k+1)).source`.
      have hk1_lt_N : k + 1 < N := lt_of_le_of_ne hk hN_eq
      have hs_next_in_k1 : t (k + 1) ∈ Set.Icc (t (k + 1)) (t (k + 1 + 1)) :=
        ⟨le_rfl, ht_mono (Nat.le_succ (k + 1))⟩
      have hγ_in_k1 : γ (t (k + 1)) ∈ (φ (k + 1)).source :=
        hpiece (k + 1) (t (k + 1)) hs_next_in_k1
      -- Open chart-overlap.
      set U : Set Y := (φ k).source ∩ (φ (k + 1)).source with hU_def
      have hU_open : IsOpen U := (φ k).open_source.inter (φ (k + 1)).open_source
      have hγ_in_U : γ (t (k + 1)) ∈ U := ⟨hγ_in_k, hγ_in_k1⟩
      -- Apply ZZ165e to perturb `γ s_next` to a `C`-avoiding point in `U`.
      obtain ⟨z', hz'_U, hz'_nC, hjoin_z⟩ :=
        exists_avoidance_in_open_chartedSpace_complex
          (Y := Y) (U := U) hU_open hγ_in_U hC_fin
      -- `z' ∈ (φ k).source` and `z' ∈ (φ (k+1)).source`.
      have hz'_in_k : z' ∈ (φ k).source := hz'_U.1
      have hz'_in_k1 : z' ∈ (φ (k + 1)).source := hz'_U.2
      -- Path from `γ s_next` to `z'` in `U`, hence in `Cᶜ`? Not directly —
      -- `JoinedIn U` doesn't give `JoinedIn Cᶜ`. Instead we connect `w_k` to
      -- `z'` directly inside `(φ k).source ∩ Cᶜ` using
      -- `joinedIn_compl_in_ball_chart_source` (no need for the perturbation
      -- path). We just used the perturbation construction to *find* `z'`.
      have hjoin_kz : JoinedIn ((Cᶜ : Set Y) ∩ (φ k).source) w_k z' :=
        joinedIn_compl_in_ball_chart_source (hr_pos k) (hφ_target k) hC_fin
          hw_k_in hz'_in_k hw_k_nc hz'_nC
      have hjoin_kz' : JoinedIn (Cᶜ : Set Y) w_k z' :=
        hjoin_kz.mono (fun _ hx => hx.1)
      refine ⟨z', hz'_nC, hjoin_k.trans hjoin_kz', ?_, ?_⟩
      · intro _; exact hz'_in_k1
      · intro h_eq
        -- `k + 1 = N` contradicts `k + 1 < N`.
        exfalso; omega

/-- **Main result.** In a connected, T2 charted space modelled on `ℂ` (with
the analytic-smoothness manifold structure available so that the statement
type-checks at the natural level for downstream use), the complement of any
finite set is path-connected, provided it is nonempty. -/
theorem isPathConnected_compl_finite_of_connected_chartedSpace_complex
    {Y : Type*} [TopologicalSpace Y] [ConnectedSpace Y] [T2Space Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {C : Set Y} (hC_fin : C.Finite) (hC_compl : (Cᶜ : Set Y).Nonempty) :
    IsPathConnected (Cᶜ : Set Y) := by
  -- Path-connectedness of `Y`.
  have : LocPathConnectedSpace Y := locPathConnectedSpace_of_chartedSpace_complex
  have : PathConnectedSpace Y := pathConnectedSpace_of_connectedSpace_locPathConnected
  -- Pick a basepoint in `Cᶜ`.
  obtain ⟨p, hp_nc⟩ := hC_compl
  refine ⟨p, hp_nc, ?_⟩
  intro q hq_nc
  -- Get a path from `p` to `q`.
  obtain ⟨γ⟩ := PathConnectedSpace.joined p q
  -- Subdivide via ZZ165c.
  obtain ⟨t, φ, rfun, cfun, ht0, ht_mono, ⟨N, htN⟩, hr_pos, hφ_target, hpiece⟩ :=
    Path.exists_ball_chart_subdivision (Y := Y) γ
  -- `htN : ∀ m ≥ N, t m = 1`. We use `t N = 1`.
  have htN' : t N = 1 := htN N le_rfl
  -- Apply the inductive gluing.
  exact joinedIn_compl_along_subdivision hC_fin γ hp_nc hq_nc t φ rfun cfun
    ht0 ht_mono N htN' hr_pos hφ_target hpiece

end Jacobians.Discharge.Manifold
