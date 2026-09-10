/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Path-connectedness of `ball z r \ s` for a countable obstruction `s`

Mathlib's `Set.Countable.isPathConnected_compl_of_one_lt_rank` proves that the
complement of any countable set in a real vector space of rank `> 1` is
path-connected. We adapt that argument to a *bounded* version: the relative
complement of a countable set in any open ball of `ℂ` is still path-connected.

The proof copies the original Linearly-independent-segment construction, but
chooses the auxiliary parameter `t` from a small interval around `0` so that
the intermediate point `c + t • y` stays inside the ambient ball. Since the
ball is convex, the two segments joining the two given endpoints to that
intermediate point then automatically remain inside the ball, and the original
disjointness argument still rules out countably many `t`s for which they meet
the obstruction `s`. The uncountable interval `(-δ, δ)` minus the countable
exceptional set is therefore nonempty.
-/

open Set Metric
open scoped Convex

namespace Jacobians.Discharge

/-- Helper: with `c ∈ Metric.ball z r` and `y : ℂ`, there exists `δ > 0` such
that for every `|t| < δ`, the point `c + t • y` lies in the ball. -/
private lemma exists_delta_smul_mem_ball
    {z c : ℂ} {r : ℝ} (hc : c ∈ Metric.ball z r) (y : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → c + t • y ∈ Metric.ball z r := by
  -- The function `t ↦ c + t • y` is continuous and sends `0` to `c ∈ ball z r`.
  have hcont : Continuous (fun t : ℝ => c + t • y) := by
    continuity
  have h0 : (fun t : ℝ => c + t • y) 0 = c := by simp
  have hpre : IsOpen ((fun t : ℝ => c + t • y) ⁻¹' Metric.ball z r) :=
    Metric.isOpen_ball.preimage hcont
  have hmem : (0 : ℝ) ∈ (fun t : ℝ => c + t • y) ⁻¹' Metric.ball z r := by
    simp [hc]
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hpre 0 hmem
  refine ⟨δ, hδpos, fun t ht => ?_⟩
  have : t ∈ Metric.ball (0 : ℝ) δ := by
    simp [ht]
  exact hδsub this

/-- Ball-restricted analogue of
`Set.Countable.isPathConnected_compl_of_one_lt_rank` for the complex plane:
the relative complement of a countable set inside an open ball of `ℂ` is
path-connected. -/
theorem Set.Countable.isPathConnected_ball_diff_complex
    {z : ℂ} {r : ℝ} (hr : 0 < r) {s : Set ℂ} (hs : s.Countable) :
    IsPathConnected (Metric.ball z r \ s) := by
  -- Pick a basepoint in the ball not in `s`.
  have hball_open : IsOpen (Metric.ball z r) := Metric.isOpen_ball
  have hball_nonempty : (Metric.ball z r).Nonempty :=
    ⟨z, by simp [Metric.mem_ball, hr]⟩
  -- The intersection `ball ∩ sᶜ` is nonempty: the ball has cardinality continuum.
  have hcompl_dense : Dense (sᶜ : Set ℂ) := hs.dense_compl ℝ
  have ha_ex : (Metric.ball z r ∩ sᶜ).Nonempty :=
    hcompl_dense.inter_open_nonempty (Metric.ball z r) hball_open hball_nonempty
  obtain ⟨a, haball, ha_ns⟩ := ha_ex
  refine ⟨a, ⟨haball, ha_ns⟩, ?_⟩
  intro b hb
  obtain ⟨hbball, hb_ns⟩ := hb
  -- If `a = b`, we are done with the trivial path.
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ⟨haball, ha_ns⟩
  -- Setup mirroring the mathlib proof.
  let c : ℂ := (2 : ℝ)⁻¹ • (a + b)
  let x : ℂ := (2 : ℝ)⁻¹ • (b - a)
  have Ia : c - x = a := by
    simp only [c, x]; module
  have Ib : c + x = b := by
    simp only [c, x]; module
  have x_ne_zero : x ≠ 0 := by
    simpa [x] using sub_ne_zero.2 hab.symm
  -- Convexity of the ball gives `c ∈ ball`: `c` is a convex combination.
  have hc_ball : c ∈ Metric.ball z r := by
    have hmem : c ∈ segment ℝ a b := by
      refine ⟨(2 : ℝ)⁻¹, (2 : ℝ)⁻¹, by norm_num, by norm_num, by norm_num, ?_⟩
      simp only [c]
      module
    exact (convex_ball z r).segment_subset haball hbball hmem
  -- A linearly independent partner `y`.
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank hrank x_ne_zero
  -- Countable obstructions for `t`.
  have A : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_setOf_nonempty_of_disjoint _ (fun _ => inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ib] using hb_ns
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc,
      ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have B : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_setOf_nonempty_of_disjoint _ (fun _ => inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ia] using ha_ns
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc,
      ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  -- Bounded-`t` constraint: choose `t` small enough that `c + t•y ∈ ball`.
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_smul_mem_ball hc_ball y
  -- The complement of the countable bad-set is dense in ℝ.
  have hdense : Dense (({t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty} ∪
      {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty})ᶜ : Set ℝ) :=
    (A.union B).dense_compl ℝ
  -- Intersect with the open interval `Ioo (-δ) δ` to extract a witness `t`.
  have hIoo_open : IsOpen (Set.Ioo (-δ) δ : Set ℝ) := isOpen_Ioo
  have hIoo_ne : (Set.Ioo (-δ) δ : Set ℝ).Nonempty := ⟨0, by simp [hδpos]⟩
  obtain ⟨t, ht_mem, ht⟩ := hdense.inter_open_nonempty _ hIoo_open hIoo_ne
  have ht_abs : |t| < δ := abs_lt.mpr ht_mem
  let w : ℂ := c + t • y
  have hw_ball : w ∈ Metric.ball z r := hδ t ht_abs
  -- Decode the negated union membership.
  have ht' : t ∉ {u : ℝ | ([c + x -[ℝ] c + u • y] ∩ s).Nonempty} ∧
              t ∉ {u : ℝ | ([c - x -[ℝ] c + u • y] ∩ s).Nonempty} := by
    have := ht
    rw [Set.mem_compl_iff, Set.mem_union] at this
    tauto
  have ht1 : ([c + x -[ℝ] c + t • y] ∩ s) = ∅ := by
    have : ¬ ([c + x -[ℝ] c + t • y] ∩ s).Nonempty := ht'.1
    rwa [Set.not_nonempty_iff_eq_empty] at this
  have ht2 : ([c - x -[ℝ] c + t • y] ∩ s) = ∅ := by
    have : ¬ ([c - x -[ℝ] c + t • y] ∩ s).Nonempty := ht'.2
    rwa [Set.not_nonempty_iff_eq_empty] at this
  -- Build the two ball-respecting JoinedIn segments.
  have hseg_aw : [a -[ℝ] w] ⊆ Metric.ball z r := by
    have : [a -[ℝ] w] ⊆ Metric.ball z r :=
      (convex_ball z r).segment_subset haball hw_ball
    exact this
  have hseg_bw : [b -[ℝ] w] ⊆ Metric.ball z r := by
    have : [b -[ℝ] w] ⊆ Metric.ball z r :=
      (convex_ball z r).segment_subset hbball hw_ball
    exact this
  -- The obstruction `s` is disjoint from each segment.
  have hwt : w = c + t • y := rfl
  have hseg_aw_ns : [a -[ℝ] w] ⊆ sᶜ := by
    rw [hwt, ← Ia, subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    exact ht2
  have hseg_bw_ns : [b -[ℝ] w] ⊆ sᶜ := by
    rw [hwt, ← Ib, subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    exact ht1
  have hseg_aw_diff : [a -[ℝ] w] ⊆ Metric.ball z r \ s := by
    intro p hp
    exact ⟨hseg_aw hp, hseg_aw_ns hp⟩
  have hseg_bw_diff : [b -[ℝ] w] ⊆ Metric.ball z r \ s := by
    intro p hp
    exact ⟨hseg_bw hp, hseg_bw_ns hp⟩
  -- Assemble the path.
  have JA : JoinedIn (Metric.ball z r \ s) a w :=
    JoinedIn.of_segment_subset hseg_aw_diff
  have JB : JoinedIn (Metric.ball z r \ s) b w :=
    JoinedIn.of_segment_subset hseg_bw_diff
  exact JA.trans JB.symm

end Jacobians.Discharge
