/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.AnalyticKthRoot
import KirovDolbeault.Discharge.Manifold.LocalKFoldMultiplicity
import KirovDolbeault.Discharge.Manifold.LocalMultiplicityInvariance
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable

set_option autoImplicit true


/-! # Unconditional k-fold local multiplicity (composition of ZZ74 + ZZ75 + ZZ87)

Composes ZZ87 (analytic k-th root) + ZZ75 (substitution bundle) + ZZ74
(re-implemented inline with a radius bound) to give: under a local
analytic factorization `g(z) - w₀ = (z - x₀)^k · u(z)` with `u(x₀) ≠ 0`,
the equation `g z = w` has exactly `k` solutions in a small ball around
`x₀` for `w` near (but not equal to) `w₀`.

Bijection: `z ↦ v z` between
`{z ∈ ball x₀ ε | g z = w}` and `{ξ : ℂ | ξ^k = w - w₀}`. -/

noncomputable section

open scoped Topology
open Set Filter Metric

namespace Jacobians.Discharge
namespace Manifold

/-- **Bundle construction from a local factorization.** -/
theorem kthRootSubstitution_of_localFactorization
    {g u : ℂ → ℂ} {x₀ w₀ : ℂ} {R : ℝ} {k : ℕ}
    (hR : 0 < R) (hk : 1 ≤ k)
    (hu_an : AnalyticOnNhd ℂ u (Metric.closedBall x₀ R))
    (hu_x₀ : u x₀ ≠ 0)
    (hfact : ∀ z ∈ Metric.closedBall x₀ R,
        g z - w₀ = (z - x₀) ^ k * u z) :
    KthRootSubstitution g x₀ w₀ k := by
  obtain ⟨r, ρ', hρ'_pos, hρ'_le, hr_an, hr_pow⟩ :=
    analytic_kth_root_of_nonvanishing hR hu_an hu_x₀ hk
  refine ⟨⟨fun z => (z - x₀) * r z, ρ', hρ'_pos, ?_, ?_, ?_, ?_⟩⟩
  · intro z hz
    have h1 : AnalyticAt ℂ (fun ζ : ℂ => ζ - x₀) z :=
      analyticAt_id.sub analyticAt_const
    have h2 : AnalyticAt ℂ r z := hr_an z hz
    exact h1.mul h2
  · change (x₀ - x₀) * r x₀ = 0
    simp
  · have hx₀_in : x₀ ∈ Metric.closedBall x₀ ρ' := Metric.mem_closedBall_self hρ'_pos.le
    have hr_x₀_pow : r x₀ ^ k = u x₀ := hr_pow x₀ hx₀_in
    have hr_x₀_ne : r x₀ ≠ 0 := by
      intro h
      have hpow : (0 : ℂ) ^ k = u x₀ := by rw [← h]; exact hr_x₀_pow
      have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
      rw [zero_pow hk0] at hpow
      exact hu_x₀ hpow.symm
    have hr_diff : DifferentiableAt ℂ r x₀ := (hr_an x₀ hx₀_in).differentiableAt
    have hsub_diff : DifferentiableAt ℂ (fun ζ : ℂ => ζ - x₀) x₀ :=
      (differentiableAt_id).sub (differentiableAt_const x₀)
    have hderiv :
        deriv (fun z => (z - x₀) * r z) x₀ =
          deriv (fun ζ : ℂ => ζ - x₀) x₀ * r x₀ +
          (x₀ - x₀) * deriv r x₀ := by
      simpa using deriv_mul hsub_diff hr_diff
    have hderiv_sub : deriv (fun ζ : ℂ => ζ - x₀) x₀ = 1 := by
      have hh : deriv (fun ζ : ℂ => ζ - x₀) x₀
            = deriv (id : ℂ → ℂ) x₀ - deriv (fun _ : ℂ => x₀) x₀ :=
        deriv_sub differentiableAt_id (differentiableAt_const x₀)
      rw [hh]; simp
    rw [hderiv, hderiv_sub, sub_self, zero_mul, add_zero, one_mul]
    exact hr_x₀_ne
  · intro z hz
    have hz_in_R : z ∈ Metric.closedBall x₀ R :=
      (Metric.closedBall_subset_closedBall hρ'_le) hz
    have h1 : g z - w₀ = (z - x₀) ^ k * u z := hfact z hz_in_R
    have h2 : r z ^ k = u z := hr_pow z hz
    rw [h1, ← h2, mul_pow]

/-- ZZ74 with an extra radius bound `ε ≤ R`. -/
theorem localMultiplicityOne_preimage_card_with_radius
    {g : ℂ → ℂ} {x₀ : ℂ}
    (h_an : AnalyticAt ℂ g x₀) (hd : deriv g x₀ ≠ 0)
    {R : ℝ} (hR : 0 < R) :
    ∃ ε > (0 : ℝ), ε ≤ R ∧ ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = 1 := by
  have hsd : HasStrictDerivAt g (deriv g x₀) x₀ := h_an.hasStrictDerivAt
  have hsfd :
      HasStrictFDerivAt g
        (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv g x₀) hd) :
          ℂ →L[ℂ] ℂ) x₀ :=
    hsd.hasStrictFDerivAt_equiv hd
  set φ : OpenPartialHomeomorph ℂ ℂ := hsfd.toOpenPartialHomeomorph g with hφ
  have h_x0_src : x₀ ∈ φ.source := hsfd.mem_toOpenPartialHomeomorph_source
  have h_w0_tgt : g x₀ ∈ φ.target := hsfd.image_mem_toOpenPartialHomeomorph_target
  have h_coe : (φ : ℂ → ℂ) = g := hsfd.toOpenPartialHomeomorph_coe
  have h_src_nhds : φ.source ∈ 𝓝 x₀ := φ.open_source.mem_nhds h_x0_src
  obtain ⟨ε₀, hε₀_pos, hε₀_sub⟩ := Metric.mem_nhds_iff.mp h_src_nhds
  set ε : ℝ := min ε₀ R with hε_def
  have hε_pos : 0 < ε := lt_min hε₀_pos hR
  have hε_le_R : ε ≤ R := min_le_right _ _
  have hε_le_ε₀ : ε ≤ ε₀ := min_le_left _ _
  have hε_sub : Metric.ball x₀ ε ⊆ φ.source := fun z hz =>
    hε₀_sub (Metric.ball_subset_ball hε_le_ε₀ hz)
  have h_symm_cont : ContinuousAt φ.symm (g x₀) :=
    (φ.continuousOn_symm).continuousAt (φ.open_target.mem_nhds h_w0_tgt)
  have h_symm_w0 : φ.symm (g x₀) = x₀ := by
    have hpre := φ.left_inv h_x0_src
    have hφx₀ : (φ : ℂ → ℂ) x₀ = g x₀ := by rw [h_coe]
    rw [hφx₀] at hpre
    exact hpre
  have h_ball_x0_nhds : Metric.ball x₀ ε ∈ 𝓝 x₀ :=
    Metric.ball_mem_nhds x₀ hε_pos
  have h_preimage_nhds : φ.symm ⁻¹' (Metric.ball x₀ ε) ∈ 𝓝 (g x₀) := by
    have ht := h_symm_cont.tendsto
    rw [h_symm_w0] at ht
    exact ht h_ball_x0_nhds
  have h_combo_nhds :
      φ.target ∩ φ.symm ⁻¹' (Metric.ball x₀ ε) ∈ 𝓝 (g x₀) :=
    Filter.inter_mem (φ.open_target.mem_nhds h_w0_tgt) h_preimage_nhds
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhds_iff.mp h_combo_nhds
  refine ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, ?_⟩
  intro w hw_ball hw_ne
  have hw_target : w ∈ φ.target := (hδ_sub hw_ball).1
  have hw_pre_in_ball : φ.symm w ∈ Metric.ball x₀ ε := (hδ_sub hw_ball).2
  have h_symm_w_src : φ.symm w ∈ φ.source := φ.map_target hw_target
  have h_g_symm : g (φ.symm w) = w := by
    have hr : (φ : ℂ → ℂ) (φ.symm w) = w := φ.right_inv hw_target
    rw [h_coe] at hr
    exact hr
  have h_preimage_eq :
      {z ∈ Metric.ball x₀ ε | g z = w} = {φ.symm w} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨hw_pre_in_ball, h_g_symm⟩, ?_⟩
    intro z hz
    obtain ⟨hz_ball, hz_g⟩ := hz
    have hz_src : z ∈ φ.source := hε_sub hz_ball
    have hφz : (φ : ℂ → ℂ) z = w := by rw [h_coe]; exact hz_g
    have hφ_symm_w : (φ : ℂ → ℂ) (φ.symm w) = w := by
      rw [h_coe]; exact h_g_symm
    exact φ.injOn hz_src h_symm_w_src (hφz.trans hφ_symm_w.symm)
  rw [h_preimage_eq]
  exact Set.ncard_singleton _

/-! ## Cardinality of k-th roots of a nonzero complex number -/

/-- The k-th roots of a nonzero complex number, viewed as a `Finset`. -/
noncomputable def kthRootsFinset (k : ℕ) (a : ℂ) : Finset ℂ :=
  (Polynomial.X ^ k - Polynomial.C a : Polynomial ℂ).roots.toFinset

/-- The set of k-th roots of `a` equals `(kthRootsFinset k a : Set ℂ)`,
when `a ≠ 0` and `k ≥ 1`. -/
lemma kth_roots_eq_finset {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (_ha : a ≠ 0) :
    {ξ : ℂ | ξ ^ k = a} = (kthRootsFinset k a : Set ℂ) := by
  set p : Polynomial ℂ := Polynomial.X ^ k - Polynomial.C a with hp_def
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  have hp_deg : p.natDegree = k := by
    rw [hp_def]; exact Polynomial.natDegree_X_pow_sub_C
  have hp_ne : p ≠ 0 := fun h => by
    rw [h] at hp_deg
    simp at hp_deg
    exact hk0 hp_deg.symm
  ext ξ
  simp only [Set.mem_setOf_eq, kthRootsFinset, Finset.mem_coe,
             Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hp_ne]
  show ξ ^ k = a ↔ p.IsRoot ξ
  unfold Polynomial.IsRoot
  rw [hp_def]
  simp [sub_eq_zero, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, eq_comm]

/-- The Finset of k-th roots has cardinality `k`. -/
lemma kth_roots_finset_card {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (ha : a ≠ 0) :
    (kthRootsFinset k a).card = k := by
  classical
  set p : Polynomial ℂ := Polynomial.X ^ k - Polynomial.C a with hp_def
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  have hp_deg : p.natDegree = k := by
    rw [hp_def]; exact Polynomial.natDegree_X_pow_sub_C
  have h_separable : p.Separable := by
    rw [hp_def]
    exact Polynomial.separable_X_pow_sub_C a (by exact_mod_cast hk0) ha
  have h_splits : p.Splits := IsAlgClosed.splits p
  have h_card_roots : p.roots.card = p.natDegree :=
    Polynomial.splits_iff_card_roots.mp h_splits
  have h_nodup : p.roots.Nodup := Polynomial.nodup_roots h_separable
  unfold kthRootsFinset
  rw [show (Polynomial.X ^ k - Polynomial.C a : Polynomial ℂ) = p from rfl]
  rw [Multiset.toFinset_card_of_nodup h_nodup, h_card_roots, hp_deg]

/-! ## Main count from the bundle -/

/-- **Cardinality count from the substitution bundle.** -/
theorem localKFoldMultiplicity_preimage_card_of_substitution
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ}
    (hk : 1 ≤ k)
    (hsub : KthRootSubstitution g x₀ w₀ k)
    (h_w₀ : g x₀ = w₀) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = k := by
  obtain ⟨v, ρ, hρ_pos, hv_an, hv_x₀_eq, hv_d, hv_pow⟩ := hsub.exists_substitution
  have hv_at_x₀ : AnalyticAt ℂ v x₀ :=
    hv_an x₀ (Metric.mem_closedBall_self hρ_pos.le)
  obtain ⟨ε, hε_pos, hε_le_ρ, δ₁, hδ₁_pos, hZZ74_v⟩ :=
    localMultiplicityOne_preimage_card_with_radius hv_at_x₀ hv_d hρ_pos
  rw [hv_x₀_eq] at hZZ74_v
  set δ : ℝ := (δ₁ / 2) ^ k with hδ_def
  have hδ_pos : 0 < δ := pow_pos (by linarith) k
  refine ⟨ε, hε_pos, δ, hδ_pos, ?_⟩
  intro w hw_ball hw_ne
  have hw₀_eq_gx₀ : w₀ = g x₀ := h_w₀.symm
  set w₁ : ℂ := w - w₀ with hw₁_def
  have hw₁_ne : w₁ ≠ 0 := by
    rw [hw₁_def, sub_ne_zero, hw₀_eq_gx₀]; exact hw_ne
  have hw_dist : ‖w - w₀‖ < δ := by
    have hh : ‖w - g x₀‖ < δ := by
      rw [Metric.mem_ball, dist_eq_norm] at hw_ball; exact hw_ball
    rw [hw₀_eq_gx₀]; exact hh
  have h_roots_small : ∀ ξ : ℂ, ξ ^ k = w₁ → ‖ξ‖ < δ₁ := by
    intro ξ hξ
    have hξn : ‖ξ‖ ^ k = ‖w₁‖ := by rw [← norm_pow, hξ]
    have h1 : ‖ξ‖ ^ k < (δ₁ / 2) ^ k := by
      rw [hξn, ← hδ_def]; exact hw_dist
    have hδ₁_half_nn : 0 ≤ δ₁ / 2 := by linarith
    have h2 : ‖ξ‖ < δ₁ / 2 := by
      by_contra h
      push Not at h
      have hh : (δ₁ / 2) ^ k ≤ ‖ξ‖ ^ k := pow_le_pow_left₀ hδ₁_half_nn h k
      linarith
    linarith
  have h_roots_ne : ∀ ξ : ℂ, ξ ^ k = w₁ → ξ ≠ 0 := by
    intro ξ hξ hξ0
    rw [hξ0] at hξ
    have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    rw [zero_pow hk0] at hξ
    exact hw₁_ne hξ.symm
  classical
  set Pre : Set ℂ := {z ∈ Metric.ball x₀ ε | g z = w} with hPre_def
  -- Use the Finset-of-roots encoding directly.
  set F : Finset ℂ := kthRootsFinset k w₁ with hF_def
  have hF_card : F.card = k := kth_roots_finset_card hk hw₁_ne
  have hF_eq : (F : Set ℂ) = {ξ : ℂ | ξ ^ k = w₁} := (kth_roots_eq_finset hk hw₁_ne).symm
  -- z ↦ v z maps Pre to F.
  have h_ball_sub_closed : Metric.ball x₀ ε ⊆ Metric.closedBall x₀ ρ := by
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall]
    exact (le_of_lt hz).trans hε_le_ρ
  have h_v_to_roots : ∀ z ∈ Pre, v z ∈ F := by
    intro z hz
    obtain ⟨hz_ball, hz_g⟩ := hz
    have hz_closed : z ∈ Metric.closedBall x₀ ρ := h_ball_sub_closed hz_ball
    have hpow : g z - w₀ = v z ^ k := hv_pow z hz_closed
    rw [hz_g] at hpow
    have hvk : v z ^ k = w₁ := by rw [hw₁_def]; exact hpow.symm
    -- Move v z into F via hF_eq.
    have hin_set : v z ∈ ({ξ : ℂ | ξ ^ k = w₁} : Set ℂ) := hvk
    rw [← hF_eq] at hin_set
    exact_mod_cast hin_set
  have h_v_count : ∀ ξ ∈ F, ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).ncard = 1 := by
    intro ξ hξ
    have hξ_in_set : ξ ∈ ({ξ : ℂ | ξ ^ k = w₁} : Set ℂ) := by
      rw [← hF_eq]; exact_mod_cast hξ
    have hξk : ξ ^ k = w₁ := hξ_in_set
    have hξ_ne : ξ ≠ 0 := h_roots_ne ξ hξk
    have hξ_norm : ‖ξ‖ < δ₁ := h_roots_small ξ hξk
    have hξ_ball : ξ ∈ Metric.ball (0 : ℂ) δ₁ := by
      rw [Metric.mem_ball, dist_zero_right]; exact hξ_norm
    exact hZZ74_v ξ hξ_ball hξ_ne
  -- Existence: each ξ ∈ F has a (unique) preimage in Pre.
  have h_exists : ∀ ξ ∈ F, ∃ z ∈ Pre, v z = ξ := by
    intro ξ hξ
    have h_card1 : ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).ncard = 1 := h_v_count ξ hξ
    have h_finite : ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).Finite :=
      Set.finite_of_ncard_ne_zero (by rw [h_card1]; exact one_ne_zero)
    have h_ne : ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).Nonempty := by
      rw [← Set.ncard_pos h_finite, h_card1]; exact Nat.one_pos
    obtain ⟨z, hz_ball_mem, hzv⟩ := h_ne
    refine ⟨z, ⟨hz_ball_mem, ?_⟩, hzv⟩
    have hz_closed : z ∈ Metric.closedBall x₀ ρ := h_ball_sub_closed hz_ball_mem
    have hpow : g z - w₀ = v z ^ k := hv_pow z hz_closed
    rw [hzv] at hpow
    have hξ_in_set : ξ ∈ ({ξ : ℂ | ξ ^ k = w₁} : Set ℂ) := by
      rw [← hF_eq]; exact_mod_cast hξ
    have hξk : ξ ^ k = w₁ := hξ_in_set
    rw [hξk] at hpow
    -- hpow : g z - w₀ = w₁; want g z = w. w₁ = w - w₀.
    have : g z = w₁ + w₀ := by
      have hh : g z = (g z - w₀) + w₀ := by ring
      rw [hh, hpow]
    rw [this, hw₁_def]; ring
  -- Injectivity of z ↦ v z on Pre via ZZ74 uniqueness.
  have h_v_injOn : Set.InjOn (fun z => v z) Pre := by
    intro z₁ hz₁ z₂ hz₂ hvz
    have hξ : v z₁ ∈ F := h_v_to_roots z₁ hz₁
    have h_card1 : ({z ∈ Metric.ball x₀ ε | v z = v z₁} : Set ℂ).ncard = 1 :=
      h_v_count (v z₁) hξ
    have hz₁_mem : z₁ ∈ ({z ∈ Metric.ball x₀ ε | v z = v z₁} : Set ℂ) :=
      ⟨hz₁.1, rfl⟩
    have hz₂_mem : z₂ ∈ ({z ∈ Metric.ball x₀ ε | v z = v z₁} : Set ℂ) :=
      ⟨hz₂.1, hvz.symm⟩
    have h_eq_singleton : ({z ∈ Metric.ball x₀ ε | v z = v z₁} : Set ℂ).ncard = 1 := h_card1
    -- Use Set.ncard_eq_one to extract singleton.
    rw [Set.ncard_eq_one] at h_eq_singleton
    obtain ⟨a, ha⟩ := h_eq_singleton
    rw [ha] at hz₁_mem hz₂_mem
    rw [Set.mem_singleton_iff] at hz₁_mem hz₂_mem
    exact hz₁_mem.trans hz₂_mem.symm
  -- Image of Pre under z ↦ v z equals (F : Set ℂ).
  have h_image_eq : (fun z => v z) '' Pre = (F : Set ℂ) := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨z, hz_pre, hzy⟩ := hy
      rw [← hzy]
      exact_mod_cast h_v_to_roots z hz_pre
    · intro ξ hξ
      have hξF : ξ ∈ F := by exact_mod_cast hξ
      obtain ⟨z, hz_pre, hzv⟩ := h_exists ξ hξF
      exact ⟨z, hz_pre, hzv⟩
  -- Pre.ncard = image.ncard (injOn) = F.card = k.
  have hPre_ncard : Pre.ncard = F.card := by
    have h1 : Pre.ncard = ((fun z => v z) '' Pre).ncard :=
      (Set.InjOn.ncard_image h_v_injOn).symm
    rw [h1, h_image_eq, Set.ncard_coe_finset]
  rw [hPre_ncard, hF_card]

/-- **Unconditional `k`-fold local multiplicity** under a local analytic
factorization hypothesis. -/
theorem localKFoldMultiplicity_preimage_card_unconditional
    {g u : ℂ → ℂ} {x₀ w₀ : ℂ} {R : ℝ} {k : ℕ}
    (hR : 0 < R) (hk : 1 ≤ k)
    (hu_an : AnalyticOnNhd ℂ u (Metric.closedBall x₀ R))
    (hu_x₀ : u x₀ ≠ 0)
    (h_w₀ : g x₀ = w₀)
    (hfact : ∀ z ∈ Metric.closedBall x₀ R,
        g z - w₀ = (z - x₀) ^ k * u z) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = k := by
  have hsub : KthRootSubstitution g x₀ w₀ k :=
    kthRootSubstitution_of_localFactorization hR hk hu_an hu_x₀ hfact
  exact localKFoldMultiplicity_preimage_card_of_substitution hk hsub h_w₀

end Manifold
end Jacobians.Discharge

end
