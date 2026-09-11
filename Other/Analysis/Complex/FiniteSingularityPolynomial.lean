/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Other.Analysis.Complex.PolynomialGrowth
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Polynomial growth away from finitely many singularities

A complex function bounded by a continuous function away from finitely many points
extends to an entire function with the same bound. In particular, a polynomial growth
bound makes this extension a polynomial of the corresponding degree.
-/

public section

open Filter Set Function
open scoped Topology

namespace Complex

/-- Removing finitely many singularities preserves a continuous pointwise bound. -/
theorem exists_entire_extension_of_finite_compl {E : Set ℂ} (hE : E.Finite)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Eᶜ) {B : ℂ → ℝ}
    (hB : Continuous B) (hbound : ∀ z ∉ E, ‖f z‖ ≤ B z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z ∉ E, g z = f z) ∧
      ∀ z, ‖g z‖ ≤ B z := by
  induction E, hE using Set.Finite.induction_on generalizing f with
  | empty =>
    exact ⟨f, by rw [compl_empty] at hf; exact differentiableOn_univ.mp hf, fun _ _ => rfl, fun z => hbound z (by simp)⟩
  | @insert c E hc hE ih =>
    have hEc : Eᶜ ∈ 𝓝 c := hE.isClosed.isOpen_compl.mem_nhds hc
    have hloc : ∀ᶠ z in 𝓝[≠] c, z ∉ insert c E := by
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hEc, self_mem_nhdsWithin] with z hz hzc
      exact fun h => (Set.mem_insert_iff.mp h).elim (fun h => hzc h) hz
    have hbounded : IsBoundedUnder (· ≤ ·) (𝓝[≠] c)
        (norm ∘ fun z => f z - f c) := by
      refine ⟨B c + 1 + ‖f c‖, ?_⟩
      change ∀ᶠ z in 𝓝[≠] c, ‖f z - f c‖ ≤ B c + 1 + ‖f c‖
      have hBnear : ∀ᶠ z in 𝓝[≠] c, B z < B c + 1 :=
        (hB.continuousAt.eventually (gt_mem_nhds (by linarith))).filter_mono
          nhdsWithin_le_nhds
      filter_upwards [hloc, hBnear] with z hz hBz
      exact norm_sub_le_of_le ((hbound z hz).trans hBz.le) le_rfl
    let g := update f c (limUnder (𝓝[≠] c) f)
    have hg : DifferentiableOn ℂ g Eᶜ :=
      differentiableOn_update_limUnder_of_isLittleO hEc
        (hf.mono (by intro z hz; simp only [mem_compl_iff, mem_insert_iff, Set.mem_sdiff, mem_singleton_iff] at hz ⊢; exact fun h => h.elim hz.2 hz.1)) hbounded.isLittleO_sub_self_inv
    have hgbound : ∀ z ∉ E, ‖g z‖ ≤ B z := by
      intro z hz
      by_cases hzc : z = c
      · rw [hzc]
        have : NeBot (𝓝[≠] c) := NormedField.nhdsNE_neBot c
        have hcont := (hg.differentiableAt hEc).continuousAt
        apply le_of_tendsto_of_tendsto (b := 𝓝[≠] c)
          (hcont.norm.tendsto.mono_left nhdsWithin_le_nhds)
          (hB.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        filter_upwards [hloc] with w hw
        have hwc : w ≠ c := (ne_of_mem_of_not_mem (Set.mem_insert c E) hw).symm
        simpa [g, update_of_ne hwc] using hbound w hw
      · simpa [g, update_of_ne hzc] using hbound z (by simp [hzc, hz])
    obtain ⟨F, hF, hFeq, hFbound⟩ := ih hg hgbound
    refine ⟨F, hF, ?_, hFbound⟩
    intro z hz
    have hzc : z ≠ c := (ne_of_mem_of_not_mem (Set.mem_insert c E) hz).symm
    rw [hFeq z (fun h => hz (Set.mem_insert_of_mem c h))]
    exact update_of_ne hzc _ _

/-- Polynomial growth away from finitely many points determines a polynomial. -/
theorem exists_polynomial_of_polynomial_growth_off_finite {E : Set ℂ} (hE : E.Finite)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Eᶜ) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hbound : ∀ z ∉ E, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z ∉ E, p.eval z = f z := by
  obtain ⟨g, hg, heq, hgbound⟩ := exists_entire_extension_of_finite_compl hE hf
    (by fun_prop) hbound
  obtain ⟨p, hp, hpg⟩ := exists_polynomial_of_polynomial_growth hg hC N hgbound
  exact ⟨p, hp, fun z hz => (hpg z).trans (heq z hz)⟩

end Complex
