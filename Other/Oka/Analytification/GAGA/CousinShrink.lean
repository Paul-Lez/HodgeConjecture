/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.CousinCoordinate
public import Other.Oka.Analytification.GAGA.HoledRect

/-!
# Cousin splitting after shrinking, for cuts of holed rectangles

This file provides the analytic input (for `q = 1`) of the Mayer–Vietoris merging step in the
proof of Theorem B for the structure sheaf on products of holed rectangles
(`Complex.HoledRect.prod`), see the plan in `Oka.Analytification.GAGA.Cousin`.

A product `prod s` of holed rectangles is cut in the real (or imaginary) direction of the
`i`-th coordinate into two overlapping products `A = prod (update s i σA)` and
`B = prod (update s i σB)` (`Complex.HoledRect.withX₁`, `Complex.HoledRect.withX₀`), where the
closed strip `[t - δ, t + δ]` of the cut does not contain the edges `±r` of the hole. For every
compact `K ⊆ A ∪ B` we find shrinkings `A'' ⋐ A' ⋐ A`, `B'' ⋐ B' ⋐ B` covering `K`, with `A' ∩ B'`
again a product of holed rectangles, such that every holomorphic function on `A' ∩ B'` is a sum
of holomorphic functions on `A''` and on `B''` on their overlap (`Complex.CousinShrinkable`).

## Main results

- `Complex.exists_split_of_rects`: Cousin splitting for finitely many rectangles at once, by
  grouping the sides of each rectangle.
- `Complex.exists_split_cutRe`, `Complex.exists_split_cutIm`: the planar splittings.
- `Complex.cousinShrinkable_cutRe`, `Complex.cousinShrinkable_cutIm`: the cuts are
  `CousinShrinkable`.
-/

@[expose] public section

open Set

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Cousin splitting for finitely many rectangles.** Let `F` be holomorphic on `V × P` and let
`D` be a finite family of closed rectangles in `V`. If `U_A` avoids the sides in `S` of every
rectangle, `U_B` the other sides, and every point of `U_A ∩ U_B` lies in the interior of exactly
one rectangle and outside the others, then `F = f_A + f_B` on `(U_A ∩ U_B) × P` with `f_A`
holomorphic on `U_A × P` and `f_B` on `U_B × P`. -/
theorem exists_split_of_rects {V : Set ℂ} {P : Set E} (hP : IsOpen P) {F : ℂ × E → ℂ}
    (hF : DifferentiableOn ℂ F (V ×ˢ P)) (D : Finset (ℂ × ℂ))
    (hD : ∀ p ∈ D, p.1.re < p.2.re ∧ p.1.im < p.2.im ∧
      Icc p.1.re p.2.re ×ℂ Icc p.1.im p.2.im ⊆ V)
    (S : Finset RectSide) {UA UB : Set ℂ}
    (hUA : ∀ p ∈ D, ∀ s ∈ S, Disjoint UA (RectSide.set p.1 p.2 s))
    (hUB : ∀ p ∈ D, ∀ s ∈ Sᶜ, Disjoint UB (RectSide.set p.1 p.2 s))
    (hUAB : ∀ z ∈ UA ∩ UB, ∃ p ∈ D, z ∈ Ioo p.1.re p.2.re ×ℂ Ioo p.1.im p.2.im ∧
      ∀ p' ∈ D, p' ≠ p → z ∉ Icc p'.1.re p'.2.re ×ℂ Icc p'.1.im p'.2.im) :
    ∃ fA fB : ℂ × E → ℂ, DifferentiableOn ℂ fA (UA ×ˢ P) ∧ DifferentiableOn ℂ fB (UB ×ˢ P) ∧
      ∀ z ∈ UA ∩ UB, ∀ w ∈ P, F (z, w) = fA (z, w) + fB (z, w) := by
  refine ⟨fun q ↦ ∑ p ∈ D, ∑ s ∈ S, RectSide.cauchy F p.1 p.2 s q,
    fun q ↦ ∑ p ∈ D, ∑ s ∈ Sᶜ, RectSide.cauchy F p.1 p.2 s q, ?_, ?_, ?_⟩
  · refine DifferentiableOn.fun_sum fun p hp ↦ ?_
    obtain ⟨h1, h2, h3⟩ := hD p hp
    refine (RectSide.differentiableOn_sum_cauchy h3 hP hF h1.le h2.le S).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl)
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    exact fun s hs hzs ↦ (hUA p hp s hs).notMem_of_mem_left hz hzs
  · refine DifferentiableOn.fun_sum fun p hp ↦ ?_
    obtain ⟨h1, h2, h3⟩ := hD p hp
    refine (RectSide.differentiableOn_sum_cauchy h3 hP hF h1.le h2.le Sᶜ).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl)
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    exact fun s hs hzs ↦ (hUB p hp s hs).notMem_of_mem_left hz hzs
  · intro z hz w hw
    obtain ⟨p, hp, hzp, hother⟩ := hUAB z hz
    rw [← Finset.sum_add_distrib, Finset.sum_eq_single p]
    · obtain ⟨_, _, h3⟩ := hD p hp
      exact (RectSide.sum_add_sum_compl_of_mem h3 hF S hzp hw).symm
    · intro p' hp' hne
      obtain ⟨h1, h2, h3⟩ := hD p' hp'
      exact RectSide.sum_add_sum_compl_of_notMem h3 hF h1.le h2.le S (hother p' hp' hne) hw
    · exact fun h ↦ (h hp).elim

namespace HoledRect

/-- `σ` with the right end of the rectangle moved to `u`. -/
def withX₁ (σ : HoledRect) (u : ℝ) : HoledRect := ⟨σ.x₀, u, σ.y₀, σ.y₁, σ.r⟩

/-- `σ` with the left end of the rectangle moved to `u`. -/
def withX₀ (σ : HoledRect) (u : ℝ) : HoledRect := ⟨u, σ.x₁, σ.y₀, σ.y₁, σ.r⟩

/-- `σ` with the upper end of the rectangle moved to `u`. -/
def withY₁ (σ : HoledRect) (u : ℝ) : HoledRect := ⟨σ.x₀, σ.x₁, σ.y₀, u, σ.r⟩

/-- `σ` with the lower end of the rectangle moved to `u`. -/
def withY₀ (σ : HoledRect) (u : ℝ) : HoledRect := ⟨σ.x₀, σ.x₁, u, σ.y₁, σ.r⟩

lemma mem_set_iff' {σ : HoledRect} {z : ℂ} :
    z ∈ σ.set ↔ (σ.x₀ < z.re ∧ z.re < σ.x₁) ∧ (σ.y₀ < z.im ∧ z.im < σ.y₁) ∧
      σ.r < max |z.re| |z.im| := by
  simp only [set, mem_sdiff, mem_reProdIm, mem_Ioo, mem_hole_iff, not_le]
  tauto

lemma set_mono_of_le {σ : HoledRect} {ε ε' : ℝ} (h : ε ≤ ε') :
    (σ.shrink ε').set ⊆ (σ.shrink ε).set := fun _ hz ↦
  mem_shrink_set_iff.2 (h.trans_lt (mem_shrink_set_iff.1 hz))

end HoledRect

open HoledRect

/-- Cousin splitting after shrinking, for two opens `A`, `B` of `ℂ^ι`: every compact subset of
`A ∪ B` is covered by opens `A'' ⋐ A' ⋐ A`, `B'' ⋐ B' ⋐ B` (relatively compact), with `A' ∩ B'` a
product of holed rectangles, such that every function holomorphic on `A' ∩ B'` is a sum of
functions holomorphic on `A''` and on `B''`, on `A'' ∩ B''`. -/
def CousinShrinkable {ι : Type*} (A B : Set (ι → ℂ)) : Prop :=
  ∀ K : Set (ι → ℂ), IsCompact K → K ⊆ A ∪ B → ∃ A' B' A'' B'' : Set (ι → ℂ),
    IsOpen A' ∧ IsOpen B' ∧ IsOpen A'' ∧ IsOpen B'' ∧
    IsCompact (closure A') ∧ closure A' ⊆ A ∧ IsCompact (closure B') ∧ closure B' ⊆ B ∧
    closure A'' ⊆ A' ∧ closure B'' ⊆ B' ∧ K ⊆ A'' ∪ B'' ∧
    (∃ s : ι → HoledRect, A' ∩ B' = HoledRect.prod s) ∧
    ∀ d : (ι → ℂ) → ℂ, DifferentiableOn ℂ d (A' ∩ B') →
      ∃ fA fB : (ι → ℂ) → ℂ, DifferentiableOn ℂ fA A'' ∧ DifferentiableOn ℂ fB B'' ∧
        ∀ x ∈ A'' ∩ B'', d x = fA x + fB x

end Complex

namespace Complex

open HoledRect

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Explicit membership in a shrunk holed rectangle. -/
lemma mem_shrink_iff {σ : HoledRect} {e : ℝ} {z : ℂ} :
    z ∈ (σ.shrink e).set ↔ (σ.x₀ + e < z.re ∧ z.re < σ.x₁ - e) ∧
      (σ.y₀ + e < z.im ∧ z.im < σ.y₁ - e) ∧ σ.r + e < max |z.re| |z.im| := by
  rw [mem_set_iff']
  rfl

/-- The planar splitting for a cut in the real direction. -/
theorem exists_split_cutRe {σ : HoledRect} {t δ ε : ℝ} (hε : 0 < ε) (hδ : 4 * ε < δ)
    (h0 : σ.x₀ ≤ t - δ) (h1 : t + δ ≤ σ.x₁)
    (hhole : (∀ x ∈ Icc (t - δ) (t + δ), σ.r + ε < |x|) ∨ Icc (t - δ) (t + δ) ⊆ Ioo (-σ.r) σ.r)
    {P : Set E} (hP : IsOpen P) {F : ℂ × E → ℂ}
    (hF : DifferentiableOn ℂ F
      ((((σ.withX₁ (t + δ)).shrink ε).set ∩ ((σ.withX₀ (t - δ)).shrink ε).set) ×ˢ P)) :
    ∃ fA fB : ℂ × E → ℂ,
      DifferentiableOn ℂ fA (((σ.withX₁ (t + δ)).shrink (2 * ε)).set ×ˢ P) ∧
      DifferentiableOn ℂ fB (((σ.withX₀ (t - δ)).shrink (2 * ε)).set ×ˢ P) ∧
      ∀ z ∈ ((σ.withX₁ (t + δ)).shrink (2 * ε)).set ∩ ((σ.withX₀ (t - δ)).shrink (2 * ε)).set,
        ∀ w ∈ P, F (z, w) = fA (z, w) + fB (z, w) := by
  set UA := ((σ.withX₁ (t + δ)).shrink (2 * ε)).set
  set UB := ((σ.withX₀ (t - δ)).shrink (2 * ε)).set
  have hUA : ∀ z ∈ UA, (σ.x₀ + 2 * ε < z.re ∧ z.re < t + δ - 2 * ε) ∧
      (σ.y₀ + 2 * ε < z.im ∧ z.im < σ.y₁ - 2 * ε) ∧ σ.r + 2 * ε < max |z.re| |z.im| :=
    fun z hz ↦ mem_shrink_iff.1 hz
  have hUB : ∀ z ∈ UB, (t - δ + 2 * ε < z.re ∧ z.re < σ.x₁ - 2 * ε) ∧
      (σ.y₀ + 2 * ε < z.im ∧ z.im < σ.y₁ - 2 * ε) ∧ σ.r + 2 * ε < max |z.re| |z.im| :=
    fun z hz ↦ mem_shrink_iff.1 hz
  have hV : ∀ z : ℂ, (t - δ + 3 / 2 * ε ≤ z.re ∧ z.re ≤ t + δ - 3 / 2 * ε) →
      (σ.y₀ + 3 / 2 * ε ≤ z.im ∧ z.im ≤ σ.y₁ - 3 / 2 * ε) → σ.r + ε < max |z.re| |z.im| →
      z ∈ ((σ.withX₁ (t + δ)).shrink ε).set ∩ ((σ.withX₀ (t - δ)).shrink ε).set := by
    intro z hre him hr
    refine ⟨mem_shrink_iff.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, hr⟩,
      mem_shrink_iff.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, hr⟩⟩ <;>
      simp only [withX₁, withX₀] <;> linarith
  have hS : ({RectSide.right, RectSide.top, RectSide.bottom} : Finset RectSide)ᶜ =
      {RectSide.left} := by decide
  rcases hhole with hgap | hin
  · by_cases hy : σ.y₀ + 4 * ε < σ.y₁
    · refine exists_split_of_rects
        (S := {RectSide.right, RectSide.top, RectSide.bottom}) (UA := UA) (UB := UB) hP hF
        {(⟨t - δ + 3 / 2 * ε, σ.y₀ + 3 / 2 * ε⟩, ⟨t + δ - 3 / 2 * ε, σ.y₁ - 3 / 2 * ε⟩)}
        ?_ ?_ ?_ ?_
      · simp only [Finset.mem_singleton, forall_eq]
        refine ⟨by linarith, by linarith, fun z hz ↦ hV z ⟨hz.1.1, hz.1.2⟩ ⟨hz.2.1, hz.2.2⟩ ?_⟩
        exact (hgap _ ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩).trans_le (le_max_left _ _)
      · simp only [Finset.mem_singleton, forall_eq, Finset.mem_insert, forall_eq_or_imp]
        refine ⟨?_, ?_, ?_⟩ <;> refine Set.disjoint_left.2 fun z hz hz' ↦ ?_
        · have := (RectSide.set_right_subset hz').1; simp at this; linarith [(hUA z hz).1.2]
        · have := (RectSide.set_top_subset hz').2; simp at this; linarith [(hUA z hz).2.1.2]
        · have := (RectSide.set_bottom_subset hz').2; simp at this; linarith [(hUA z hz).2.1.1]
      · rw [hS]
        simp only [Finset.mem_singleton, forall_eq]
        refine Set.disjoint_left.2 fun z hz hz' ↦ ?_
        have := (RectSide.set_left_subset hz').1; simp at this; linarith [(hUB z hz).1.1]
      · intro z hz
        refine ⟨_, Finset.mem_singleton_self _, ?_, fun p' hp' hne ↦ (hne
          (Finset.mem_singleton.1 hp')).elim⟩
        obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -⟩ := hUA z hz.1
        obtain ⟨⟨h5, h6⟩, -, -⟩ := hUB z hz.2
        exact ⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by simp; linarith, by simp; linarith⟩⟩
    · refine ⟨0, 0, differentiableOn_const 0, differentiableOn_const 0, fun z hz ↦ ?_⟩
      obtain ⟨-, ⟨h3, h4⟩, -⟩ := hUA z hz.1
      exact absurd (by linarith : σ.y₀ + 4 * ε < σ.y₁) hy
  · have ht : t - δ ∈ Icc (t - δ) (t + δ) := ⟨le_rfl, by linarith⟩
    have hr0 : 0 < σ.r := by have := hin ht; simp only [mem_Ioo] at this; linarith
    set aU : ℂ := ⟨t - δ + 3 / 2 * ε, max σ.r σ.y₀ + 3 / 2 * ε⟩
    set bU : ℂ := ⟨t + δ - 3 / 2 * ε, σ.y₁ - 3 / 2 * ε⟩
    set aD : ℂ := ⟨t - δ + 3 / 2 * ε, σ.y₀ + 3 / 2 * ε⟩
    set bD : ℂ := ⟨t + δ - 3 / 2 * ε, min (-σ.r) σ.y₁ - 3 / 2 * ε⟩
    have hin' : ∀ x : ℝ, t - δ ≤ x → x ≤ t + δ → |x| < σ.r := fun x h1 h2 ↦
      abs_lt.2 (hin ⟨h1, h2⟩)
    refine exists_split_of_rects
      (S := {RectSide.right, RectSide.top, RectSide.bottom}) (UA := UA) (UB := UB) hP hF
      (({(aU, bU), (aD, bD)} : Finset (ℂ × ℂ)).filter
        fun p ↦ p.1.re < p.2.re ∧ p.1.im < p.2.im) ?_ ?_ ?_ ?_
    · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      rintro p ⟨rfl | rfl, hre, him⟩ <;> refine ⟨hre, him, fun z hz ↦ ?_⟩ <;>
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz <;> simp only [aU, bU, aD, bD] at h1 h2 h3 h4
      · refine hV z ⟨h1, h2⟩ ⟨by linarith [le_max_right σ.r σ.y₀], h4⟩ ?_
        refine lt_of_lt_of_le ?_ (le_max_right _ _)
        rw [abs_of_pos (by linarith [le_max_left σ.r σ.y₀])]
        linarith [le_max_left σ.r σ.y₀]
      · refine hV z ⟨h1, h2⟩ ⟨h3, by linarith [min_le_right (-σ.r) σ.y₁]⟩ ?_
        refine lt_of_lt_of_le ?_ (le_max_right _ _)
        rw [abs_of_neg (by linarith [min_le_left (-σ.r) σ.y₁])]
        linarith [min_le_left (-σ.r) σ.y₁]
    · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      rintro p ⟨rfl | rfl, -, -⟩ s hs <;> rcases hs with rfl | rfl | rfl <;>
        refine Set.disjoint_left.2 fun z hz hz' ↦ ?_ <;>
        obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hUA z hz
      · have := (RectSide.set_right_subset hz').1; simp [bU] at this; linarith
      · have := (RectSide.set_top_subset hz').2; simp [bU] at this; linarith
      · obtain ⟨hx, hy⟩ := RectSide.set_bottom_subset hz'
        replace hy : z.im = max σ.r σ.y₀ + 3 / 2 * ε := hy
        replace hx : t - δ + 3 / 2 * ε ≤ z.re ∧ z.re ≤ t + δ - 3 / 2 * ε := by
          rw [uIcc_of_le (show aU.re ≤ bU.re by simp [aU, bU]; linarith)] at hx
          exact hx
        have hx' := hin' z.re (by linarith [hx.1]) (by linarith [hx.2])
        rcases max_choice σ.r σ.y₀ with hm | hm <;> rw [hm] at hy
        · rcases le_max_iff.1 h5.le with h6 | h6
          · linarith
          · rw [abs_of_pos (by linarith)] at h6
            linarith [hy ▸ h6]
        · linarith
      · have := (RectSide.set_right_subset hz').1; simp [bD] at this; linarith
      · obtain ⟨hx, hy⟩ := RectSide.set_top_subset hz'
        replace hy : z.im = min (-σ.r) σ.y₁ - 3 / 2 * ε := hy
        replace hx : t - δ + 3 / 2 * ε ≤ z.re ∧ z.re ≤ t + δ - 3 / 2 * ε := by
          rw [uIcc_of_le (show aD.re ≤ bD.re by simp [aD, bD]; linarith)] at hx
          exact hx
        have hx' := hin' z.re (by linarith [hx.1]) (by linarith [hx.2])
        rcases min_choice (-σ.r) σ.y₁ with hm | hm <;> rw [hm] at hy
        · rcases le_max_iff.1 h5.le with h6 | h6
          · linarith
          · rw [abs_of_neg (by linarith)] at h6
            linarith [hy ▸ h6]
        · linarith
      · have := (RectSide.set_bottom_subset hz').2; simp [aD] at this; linarith
    · rw [hS]
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      rintro p ⟨rfl | rfl, -, -⟩ s rfl <;> refine Set.disjoint_left.2 fun z hz hz' ↦ ?_ <;>
        have := (RectSide.set_left_subset hz').1 <;> simp [aU, aD] at this <;>
        linarith [(hUB z hz).1.1]
    · intro z hz
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hUA z hz.1
      obtain ⟨⟨h6, -⟩, -, -⟩ := hUB z hz.2
      have hx := hin' z.re (by linarith) (by linarith)
      have him : σ.r + 2 * ε < |z.im| := by
        rcases lt_max_iff.1 h5 with h7 | h7
        · linarith
        · exact h7
      rcases lt_abs.1 him with h7 | h7
      · have hm : max σ.r σ.y₀ + 3 / 2 * ε < z.im := by
          have h8 : σ.r < z.im - 3 / 2 * ε := by linarith
          have h9 : σ.y₀ < z.im - 3 / 2 * ε := by linarith
          have := max_lt h8 h9
          linarith
        refine ⟨(aU, bU), ?_, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, true_or,
            true_and]
          exact ⟨show t - δ + 3 / 2 * ε < t + δ - 3 / 2 * ε by linarith,
            show max σ.r σ.y₀ + 3 / 2 * ε < σ.y₁ - 3 / 2 * ε by linarith⟩
        · exact show (t - δ + 3 / 2 * ε < z.re ∧ z.re < t + δ - 3 / 2 * ε) ∧
            (max σ.r σ.y₀ + 3 / 2 * ε < z.im ∧ z.im < σ.y₁ - 3 / 2 * ε) from
            ⟨⟨by linarith, by linarith⟩, hm, by linarith⟩
        · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          rintro p' ⟨rfl | rfl, -, -⟩ hne
          · exact (hne rfl).elim
          · rintro ⟨-, -, h8⟩
            have h8' : z.im ≤ min (-σ.r) σ.y₁ - 3 / 2 * ε := h8
            linarith [min_le_left (-σ.r) σ.y₁]
      · have hm : z.im < min (-σ.r) σ.y₁ - 3 / 2 * ε := by
          have h8 : z.im + 3 / 2 * ε < -σ.r := by linarith
          have h9 : z.im + 3 / 2 * ε < σ.y₁ := by linarith
          have := lt_min h8 h9
          linarith
        refine ⟨(aD, bD), ?_, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, or_true,
            true_and]
          exact ⟨show t - δ + 3 / 2 * ε < t + δ - 3 / 2 * ε by linarith,
            show σ.y₀ + 3 / 2 * ε < min (-σ.r) σ.y₁ - 3 / 2 * ε by linarith⟩
        · exact show (t - δ + 3 / 2 * ε < z.re ∧ z.re < t + δ - 3 / 2 * ε) ∧
            (σ.y₀ + 3 / 2 * ε < z.im ∧ z.im < min (-σ.r) σ.y₁ - 3 / 2 * ε) from
            ⟨⟨by linarith, by linarith⟩, by linarith, hm⟩
        · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          rintro p' ⟨rfl | rfl, -, -⟩ hne
          · rintro ⟨-, h8, -⟩
            have h8' : max σ.r σ.y₀ + 3 / 2 * ε ≤ z.im := h8
            linarith [le_max_left σ.r σ.y₀]
          · exact (hne rfl).elim

/-- The planar splitting for a cut in the imaginary direction. -/
theorem exists_split_cutIm {σ : HoledRect} {t δ ε : ℝ} (hε : 0 < ε) (hδ : 4 * ε < δ)
    (h0 : σ.y₀ ≤ t - δ) (h1 : t + δ ≤ σ.y₁)
    (hhole : (∀ y ∈ Icc (t - δ) (t + δ), σ.r + ε < |y|) ∨ Icc (t - δ) (t + δ) ⊆ Ioo (-σ.r) σ.r)
    {P : Set E} (hP : IsOpen P) {F : ℂ × E → ℂ}
    (hF : DifferentiableOn ℂ F
      ((((σ.withY₁ (t + δ)).shrink ε).set ∩ ((σ.withY₀ (t - δ)).shrink ε).set) ×ˢ P)) :
    ∃ fA fB : ℂ × E → ℂ,
      DifferentiableOn ℂ fA (((σ.withY₁ (t + δ)).shrink (2 * ε)).set ×ˢ P) ∧
      DifferentiableOn ℂ fB (((σ.withY₀ (t - δ)).shrink (2 * ε)).set ×ˢ P) ∧
      ∀ z ∈ ((σ.withY₁ (t + δ)).shrink (2 * ε)).set ∩ ((σ.withY₀ (t - δ)).shrink (2 * ε)).set,
        ∀ w ∈ P, F (z, w) = fA (z, w) + fB (z, w) := by
  set UA := ((σ.withY₁ (t + δ)).shrink (2 * ε)).set
  set UB := ((σ.withY₀ (t - δ)).shrink (2 * ε)).set
  have hUA : ∀ z ∈ UA, (σ.x₀ + 2 * ε < z.re ∧ z.re < σ.x₁ - 2 * ε) ∧
      (σ.y₀ + 2 * ε < z.im ∧ z.im < t + δ - 2 * ε) ∧ σ.r + 2 * ε < max |z.re| |z.im| :=
    fun z hz ↦ mem_shrink_iff.1 hz
  have hUB : ∀ z ∈ UB, (σ.x₀ + 2 * ε < z.re ∧ z.re < σ.x₁ - 2 * ε) ∧
      (t - δ + 2 * ε < z.im ∧ z.im < σ.y₁ - 2 * ε) ∧ σ.r + 2 * ε < max |z.re| |z.im| :=
    fun z hz ↦ mem_shrink_iff.1 hz
  have hV : ∀ z : ℂ, (σ.x₀ + 3 / 2 * ε ≤ z.re ∧ z.re ≤ σ.x₁ - 3 / 2 * ε) →
      (t - δ + 3 / 2 * ε ≤ z.im ∧ z.im ≤ t + δ - 3 / 2 * ε) → σ.r + ε < max |z.re| |z.im| →
      z ∈ ((σ.withY₁ (t + δ)).shrink ε).set ∩ ((σ.withY₀ (t - δ)).shrink ε).set := by
    intro z hre him hr
    refine ⟨mem_shrink_iff.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, hr⟩,
      mem_shrink_iff.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, hr⟩⟩ <;>
      simp only [withY₁, withY₀] <;> linarith
  have hS : ({RectSide.top, RectSide.left, RectSide.right} : Finset RectSide)ᶜ =
      {RectSide.bottom} := by decide
  rcases hhole with hgap | hin
  · by_cases hx : σ.x₀ + 4 * ε < σ.x₁
    · refine exists_split_of_rects
        (S := {RectSide.top, RectSide.left, RectSide.right}) (UA := UA) (UB := UB) hP hF
        {(⟨σ.x₀ + 3 / 2 * ε, t - δ + 3 / 2 * ε⟩, ⟨σ.x₁ - 3 / 2 * ε, t + δ - 3 / 2 * ε⟩)}
        ?_ ?_ ?_ ?_
      · simp only [Finset.mem_singleton, forall_eq]
        refine ⟨by linarith, by linarith, fun z hz ↦ hV z ⟨hz.1.1, hz.1.2⟩ ⟨hz.2.1, hz.2.2⟩ ?_⟩
        exact (hgap _ ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩).trans_le (le_max_right _ _)
      · simp only [Finset.mem_singleton, forall_eq, Finset.mem_insert, forall_eq_or_imp]
        refine ⟨?_, ?_, ?_⟩ <;> refine Set.disjoint_left.2 fun z hz hz' ↦ ?_
        · have := (RectSide.set_top_subset hz').2; simp at this; linarith [(hUA z hz).2.1.2]
        · have := (RectSide.set_left_subset hz').1; simp at this; linarith [(hUA z hz).1.1]
        · have := (RectSide.set_right_subset hz').1; simp at this; linarith [(hUA z hz).1.2]
      · rw [hS]
        simp only [Finset.mem_singleton, forall_eq]
        refine Set.disjoint_left.2 fun z hz hz' ↦ ?_
        have := (RectSide.set_bottom_subset hz').2; simp at this; linarith [(hUB z hz).2.1.1]
      · intro z hz
        refine ⟨_, Finset.mem_singleton_self _, ?_, fun p' hp' hne ↦ (hne
          (Finset.mem_singleton.1 hp')).elim⟩
        obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -⟩ := hUA z hz.1
        obtain ⟨-, ⟨h5, h6⟩, -⟩ := hUB z hz.2
        exact ⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by simp; linarith, by simp; linarith⟩⟩
    · refine ⟨0, 0, differentiableOn_const 0, differentiableOn_const 0, fun z hz ↦ ?_⟩
      obtain ⟨⟨h3, h4⟩, -, -⟩ := hUA z hz.1
      exact absurd (by linarith : σ.x₀ + 4 * ε < σ.x₁) hx
  · have ht : t - δ ∈ Icc (t - δ) (t + δ) := ⟨le_rfl, by linarith⟩
    have hr0 : 0 < σ.r := by have := hin ht; simp only [mem_Ioo] at this; linarith
    set aR : ℂ := ⟨max σ.r σ.x₀ + 3 / 2 * ε, t - δ + 3 / 2 * ε⟩
    set bR : ℂ := ⟨σ.x₁ - 3 / 2 * ε, t + δ - 3 / 2 * ε⟩
    set aL : ℂ := ⟨σ.x₀ + 3 / 2 * ε, t - δ + 3 / 2 * ε⟩
    set bL : ℂ := ⟨min (-σ.r) σ.x₁ - 3 / 2 * ε, t + δ - 3 / 2 * ε⟩
    have hin' : ∀ y : ℝ, t - δ ≤ y → y ≤ t + δ → |y| < σ.r := fun y h1 h2 ↦
      abs_lt.2 (hin ⟨h1, h2⟩)
    refine exists_split_of_rects
      (S := {RectSide.top, RectSide.left, RectSide.right}) (UA := UA) (UB := UB) hP hF
      (({(aR, bR), (aL, bL)} : Finset (ℂ × ℂ)).filter
        fun p ↦ p.1.re < p.2.re ∧ p.1.im < p.2.im) ?_ ?_ ?_ ?_
    · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      rintro p ⟨rfl | rfl, hre, him⟩ <;> refine ⟨hre, him, fun z hz ↦ ?_⟩ <;>
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz <;> simp only [aR, bR, aL, bL] at h1 h2 h3 h4
      · refine hV z ⟨by linarith [le_max_right σ.r σ.x₀], h2⟩ ⟨h3, h4⟩ ?_
        refine lt_of_lt_of_le ?_ (le_max_left _ _)
        rw [abs_of_pos (by linarith [le_max_left σ.r σ.x₀])]
        linarith [le_max_left σ.r σ.x₀]
      · refine hV z ⟨h1, by linarith [min_le_right (-σ.r) σ.x₁]⟩ ⟨h3, h4⟩ ?_
        refine lt_of_lt_of_le ?_ (le_max_left _ _)
        rw [abs_of_neg (by linarith [min_le_left (-σ.r) σ.x₁])]
        linarith [min_le_left (-σ.r) σ.x₁]
    · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      rintro p ⟨rfl | rfl, -, -⟩ s hs <;> rcases hs with rfl | rfl | rfl <;>
        refine Set.disjoint_left.2 fun z hz hz' ↦ ?_ <;>
        obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hUA z hz
      · have := (RectSide.set_top_subset hz').2; simp [bR] at this; linarith
      · obtain ⟨hx, hy⟩ := RectSide.set_left_subset hz'
        replace hx : z.re = max σ.r σ.x₀ + 3 / 2 * ε := hx
        replace hy : t - δ + 3 / 2 * ε ≤ z.im ∧ z.im ≤ t + δ - 3 / 2 * ε := by
          rw [uIcc_of_le (show aR.im ≤ bR.im by simp [aR, bR]; linarith)] at hy
          exact hy
        have hy' := hin' z.im (by linarith [hy.1]) (by linarith [hy.2])
        rcases max_choice σ.r σ.x₀ with hm | hm <;> rw [hm] at hx
        · rcases le_max_iff.1 h5.le with h6 | h6
          · rw [abs_of_pos (by linarith)] at h6
            linarith [hx ▸ h6]
          · linarith
        · linarith
      · have := (RectSide.set_right_subset hz').1; simp [bR] at this; linarith
      · have := (RectSide.set_top_subset hz').2; simp [bL] at this; linarith
      · have := (RectSide.set_left_subset hz').1; simp [aL] at this; linarith
      · obtain ⟨hx, hy⟩ := RectSide.set_right_subset hz'
        replace hx : z.re = min (-σ.r) σ.x₁ - 3 / 2 * ε := hx
        replace hy : t - δ + 3 / 2 * ε ≤ z.im ∧ z.im ≤ t + δ - 3 / 2 * ε := by
          rw [uIcc_of_le (show aL.im ≤ bL.im by simp [aL, bL]; linarith)] at hy
          exact hy
        have hy' := hin' z.im (by linarith [hy.1]) (by linarith [hy.2])
        rcases min_choice (-σ.r) σ.x₁ with hm | hm <;> rw [hm] at hx
        · rcases le_max_iff.1 h5.le with h6 | h6
          · rw [abs_of_neg (by linarith)] at h6
            linarith [hx ▸ h6]
          · linarith
        · linarith
    · rw [hS]
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      rintro p ⟨rfl | rfl, -, -⟩ s rfl <;> refine Set.disjoint_left.2 fun z hz hz' ↦ ?_ <;>
        have := (RectSide.set_bottom_subset hz').2 <;> simp [aR, aL] at this <;>
        linarith [(hUB z hz).2.1.1]
    · intro z hz
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hUA z hz.1
      obtain ⟨-, ⟨h6, -⟩, -⟩ := hUB z hz.2
      have hy := hin' z.im (by linarith) (by linarith)
      have hre : σ.r + 2 * ε < |z.re| := by
        rcases lt_max_iff.1 h5 with h7 | h7
        · exact h7
        · linarith
      rcases lt_abs.1 hre with h7 | h7
      · have hm : max σ.r σ.x₀ + 3 / 2 * ε < z.re := by
          have h8 : σ.r < z.re - 3 / 2 * ε := by linarith
          have h9 : σ.x₀ < z.re - 3 / 2 * ε := by linarith
          have := max_lt h8 h9
          linarith
        refine ⟨(aR, bR), ?_, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, true_or,
            true_and]
          exact ⟨show max σ.r σ.x₀ + 3 / 2 * ε < σ.x₁ - 3 / 2 * ε by linarith,
            show t - δ + 3 / 2 * ε < t + δ - 3 / 2 * ε by linarith⟩
        · exact show (max σ.r σ.x₀ + 3 / 2 * ε < z.re ∧ z.re < σ.x₁ - 3 / 2 * ε) ∧
            (t - δ + 3 / 2 * ε < z.im ∧ z.im < t + δ - 3 / 2 * ε) from
            ⟨⟨hm, by linarith⟩, by linarith, by linarith⟩
        · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          rintro p' ⟨rfl | rfl, -, -⟩ hne
          · exact (hne rfl).elim
          · rintro ⟨⟨-, h8⟩, -⟩
            have h8' : z.re ≤ min (-σ.r) σ.x₁ - 3 / 2 * ε := h8
            linarith [min_le_left (-σ.r) σ.x₁]
      · have hm : z.re < min (-σ.r) σ.x₁ - 3 / 2 * ε := by
          have h8 : z.re + 3 / 2 * ε < -σ.r := by linarith
          have h9 : z.re + 3 / 2 * ε < σ.x₁ := by linarith
          have := lt_min h8 h9
          linarith
        refine ⟨(aL, bL), ?_, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, or_true,
            true_and]
          exact ⟨show σ.x₀ + 3 / 2 * ε < min (-σ.r) σ.x₁ - 3 / 2 * ε by linarith,
            show t - δ + 3 / 2 * ε < t + δ - 3 / 2 * ε by linarith⟩
        · exact show (σ.x₀ + 3 / 2 * ε < z.re ∧ z.re < min (-σ.r) σ.x₁ - 3 / 2 * ε) ∧
            (t - δ + 3 / 2 * ε < z.im ∧ z.im < t + δ - 3 / 2 * ε) from
            ⟨⟨by linarith, hm⟩, by linarith, by linarith⟩
        · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          rintro p' ⟨rfl | rfl, -, -⟩ hne
          · rintro ⟨⟨h8, -⟩, -⟩
            have h8' : max σ.r σ.x₀ + 3 / 2 * ε ≤ z.re := h8
            linarith [le_max_left σ.r σ.x₀]
          · exact (hne rfl).elim

section Transport

variable {ι : Type*} [DecidableEq ι]

lemma splitAt_symm_apply_self [Fintype ι] (i : ι) (p : ℂ × ({j // j ≠ i} → ℂ)) :
    (splitAt i).symm p i = p.1 :=
  calc (splitAt i).symm p i = (splitAt i ((splitAt i).symm p)).1 := rfl
    _ = p.1 := by rw [ContinuousLinearEquiv.apply_symm_apply]

lemma splitAt_symm_apply_of_ne [Fintype ι] (i : ι) (p : ℂ × ({j // j ≠ i} → ℂ)) {j : ι}
    (hj : j ≠ i) :
    (splitAt i).symm p j = p.2 ⟨j, hj⟩ :=
  calc (splitAt i).symm p j = (splitAt i ((splitAt i).symm p)).2 ⟨j, hj⟩ := rfl
    _ = p.2 ⟨j, hj⟩ := by rw [ContinuousLinearEquiv.apply_symm_apply]

lemma lt_margin_iff {σ : HoledRect} {e : ℝ} {z : ℂ} :
    e < σ.margin z ↔ (σ.x₀ + e < z.re ∧ z.re < σ.x₁ - e) ∧
      (σ.y₀ + e < z.im ∧ z.im < σ.y₁ - e) ∧ σ.r + e < max |z.re| |z.im| :=
  mem_shrink_set_iff.symm.trans mem_shrink_iff

/-- A closed interval disjoint from `[-r, r]` keeps a positive distance from it. -/
lemma exists_gap {a b r : ℝ} (hab : a ≤ b) (h : Disjoint (Icc a b) (Icc (-r) r)) :
    ∃ g > 0, ∀ x ∈ Icc a b, r + g < |x| := by
  rcases lt_or_ge r 0 with hr | hr
  · exact ⟨-r / 2, by linarith, fun x _ ↦ by linarith [abs_nonneg x]⟩
  rcases lt_or_ge b (-r) with hb | hb
  · refine ⟨(-r - b) / 2, by linarith, fun x hx ↦ ?_⟩
    rw [abs_of_neg (by linarith [hx.2])]; linarith [hx.2]
  rcases lt_or_ge r a with ha | ha
  · refine ⟨(a - r) / 2, by linarith, fun x hx ↦ ?_⟩
    rw [abs_of_pos (by linarith [hx.1])]; linarith [hx.1]
  exfalso
  exact Set.disjoint_left.1 h (show max a (-r) ∈ Icc a b from ⟨le_max_left _ _, max_le hab hb⟩)
    ⟨le_max_right _ _, max_le ha (by linarith)⟩

/-- **The cut in the real direction of the `i`-th coordinate is Cousin-shrinkable**, provided the
closed strip `[t - δ, t + δ]` does not contain `±r`. -/
theorem cousinShrinkable_cutRe [Finite ι] (s : ι → HoledRect) (i : ι) {t δ : ℝ} (hδ : 0 < δ)
    (h0 : (s i).x₀ ≤ t - δ) (h1 : t + δ ≤ (s i).x₁)
    (hhole : Disjoint (Icc (t - δ) (t + δ)) (Icc (-(s i).r) (s i).r) ∨
      Icc (t - δ) (t + δ) ⊆ Ioo (-(s i).r) (s i).r) :
    CousinShrinkable (prod (Function.update s i ((s i).withX₁ (t + δ))))
      (prod (Function.update s i ((s i).withX₀ (t - δ)))) := by
  have := Fintype.ofFinite ι
  intro K hK hKAB
  set σ := s i with hσ
  set uA := Function.update s i (σ.withX₁ (t + δ))
  set uB := Function.update s i (σ.withX₀ (t - δ))
  obtain ⟨g, hg, hgap⟩ : ∃ g > 0, Disjoint (Icc (t - δ) (t + δ)) (Icc (-σ.r) σ.r) →
      ∀ x ∈ Icc (t - δ) (t + δ), σ.r + g < |x| := by
    by_cases hd : Disjoint (Icc (t - δ) (t + δ)) (Icc (-σ.r) σ.r)
    · obtain ⟨g, hg, h⟩ := exists_gap (by linarith) hd
      exact ⟨g, hg, fun _ ↦ h⟩
    · exact ⟨1, one_pos, fun h ↦ (hd h).elim⟩
  have hAB : prod uA ∪ prod uB ⊆ prod s := by
    rintro x (hx | hx) <;> refine mem_prod_iff.2 fun j ↦ ?_ <;> have := mem_prod_iff.1 hx j <;>
      rcases eq_or_ne j i with rfl | hj
    · simp only [uA, Function.update_self] at this
      obtain ⟨⟨h2, h3⟩, h4, h5⟩ := mem_set_iff'.1 this
      exact mem_set_iff'.2 ⟨⟨h2, by simp only [withX₁] at h3; linarith⟩, h4, h5⟩
    · simpa [uA, Function.update_of_ne hj] using this
    · simp only [uB, Function.update_self] at this
      obtain ⟨⟨h2, h3⟩, h4, h5⟩ := mem_set_iff'.1 this
      exact mem_set_iff'.2 ⟨⟨by simp only [withX₀] at h2; linarith, h3⟩, h4, h5⟩
    · simpa [uB, Function.update_of_ne hj] using this
  obtain ⟨ε₀, hε₀, hKs⟩ := exists_subset_prod_shrink hK (hKAB.trans hAB)
  set ε := min (ε₀ / 2) (min (δ / 5) (g / 2)) with hεdef
  have hε : 0 < ε := by positivity
  have hεε₀ : 2 * ε ≤ ε₀ := by
    have := min_le_left (ε₀ / 2) (min (δ / 5) (g / 2)); linarith
  have hεδ : 4 * ε < δ := by
    have := (min_le_right (ε₀ / 2) (min (δ / 5) (g / 2))).trans (min_le_left _ _); linarith
  have hεg : ε < g := by
    have := (min_le_right (ε₀ / 2) (min (δ / 5) (g / 2))).trans (min_le_right _ _); linarith
  have hhole' : (∀ x ∈ Icc (t - δ) (t + δ), σ.r + ε < |x|) ∨
      Icc (t - δ) (t + δ) ⊆ Ioo (-σ.r) σ.r := by
    rcases hhole with hd | hin
    · exact Or.inl fun x hx ↦ lt_trans (by linarith) (hgap hd x hx)
    · exact Or.inr hin
  set A' := prod fun j ↦ (uA j).shrink ε
  set B' := prod fun j ↦ (uB j).shrink ε
  set A'' := prod fun j ↦ (uA j).shrink (2 * ε)
  set B'' := prod fun j ↦ (uB j).shrink (2 * ε)
  have hsh : ∀ u : ι → HoledRect, (prod fun j ↦ (u j).shrink (2 * ε)) =
      prod fun j ↦ ((u j).shrink ε).shrink ε := by
    intro u; simp_rw [shrink_shrink, two_mul]
  set τ : HoledRect := ⟨t - δ + ε, t + δ - ε, σ.y₀ + ε, σ.y₁ - ε, σ.r + ε⟩
  have hplanar : ((σ.withX₁ (t + δ)).shrink ε).set ∩ ((σ.withX₀ (t - δ)).shrink ε).set =
      τ.set := by
    ext z
    simp only [mem_inter_iff, mem_set_iff', shrink, withX₁, withX₀, τ]
    constructor
    · rintro ⟨⟨⟨-, a2⟩, a3, a4⟩, ⟨⟨b1, -⟩, -, -⟩⟩
      exact ⟨⟨b1, a2⟩, a3, a4⟩
    · rintro ⟨⟨a1, a2⟩, a3, a4⟩
      exact ⟨⟨⟨by linarith, a2⟩, a3, a4⟩, ⟨⟨a1, by linarith⟩, a3, a4⟩⟩
  have hA'B' : A' ∩ B' = prod (Function.update (fun j ↦ (s j).shrink ε) i τ) := by
    ext x
    simp only [A', B', mem_inter_iff, mem_prod_iff]
    constructor
    · rintro ⟨hA, hB⟩ j
      rcases eq_or_ne j i with rfl | hj
      · have hAj := hA j
        have hBj := hB j
        simp only [uA, uB, Function.update_self] at hAj hBj ⊢
        rw [← hplanar]; exact ⟨hAj, hBj⟩
      · have := hA j
        simpa [uA, Function.update_of_ne hj] using this
    · intro h
      refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩ <;> rcases eq_or_ne j i with rfl | hj
      · have := h j
        simp only [uA, Function.update_self] at this ⊢
        rw [← hplanar] at this; exact this.1
      · simpa [uA, Function.update_of_ne hj] using h j
      · have := h j
        simp only [uB, Function.update_self] at this ⊢
        rw [← hplanar] at this; exact this.2
      · simpa [uB, Function.update_of_ne hj] using h j
  refine ⟨A', B', A'', B'', isOpen_prod _, isOpen_prod _, isOpen_prod _, isOpen_prod _,
    isCompact_closure_prod _, closure_prod_shrink_subset hε uA, isCompact_closure_prod _,
    closure_prod_shrink_subset hε uB, ?_, ?_, ?_, ⟨_, hA'B'⟩, ?_⟩
  · change closure (prod fun j ↦ (uA j).shrink (2 * ε)) ⊆ _
    rw [hsh]; exact closure_prod_shrink_subset hε _
  · change closure (prod fun j ↦ (uB j).shrink (2 * ε)) ⊆ _
    rw [hsh]; exact closure_prod_shrink_subset hε _
  · intro x hx
    have hxs := mem_prod_iff.1 (hKs hx)
    have hxi := lt_margin_iff.1 (mem_shrink_set_iff.1 (hxs i))
    obtain ⟨⟨c1, c2⟩, ⟨c3, c4⟩, c5⟩ := hxi
    have hother : ∀ u : ι → HoledRect, (∀ j, j ≠ i → u j = s j) → ∀ j, j ≠ i →
        x j ∈ ((u j).shrink (2 * ε)).set := fun u hu j hj ↦ by
      rw [hu j hj]; exact set_mono_of_le hεε₀ (hxs j)
    rcases le_or_gt (x i).re t with hre | hre
    · refine Or.inl (mem_prod_iff.2 fun j ↦ ?_)
      rcases eq_or_ne j i with rfl | hj
      · simp only [uA, Function.update_self]
        refine mem_shrink_iff.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> simp only [withX₁] <;> linarith
      · exact hother uA (fun j hj ↦ Function.update_of_ne hj _ _) j hj
    · refine Or.inr (mem_prod_iff.2 fun j ↦ ?_)
      rcases eq_or_ne j i with rfl | hj
      · simp only [uB, Function.update_self]
        refine mem_shrink_iff.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> simp only [withX₀] <;> linarith
      · exact hother uB (fun j hj ↦ Function.update_of_ne hj _ _) j hj
  · intro d hd
    set P : Set ({j // j ≠ i} → ℂ) := Set.univ.pi fun j ↦ ((s j).shrink ε).set
    have hP : IsOpen P := isOpen_set_pi finite_univ fun j _ ↦ ((s j).shrink ε).isOpen_set
    have hF : DifferentiableOn ℂ (fun p ↦ d ((splitAt i).symm p))
        ((((σ.withX₁ (t + δ)).shrink ε).set ∩ ((σ.withX₀ (t - δ)).shrink ε).set) ×ˢ P) := by
      refine hd.comp (splitAt i).symm.differentiableOn fun p hp ↦ ?_
      rw [hA'B', mem_prod_iff]
      intro j
      rcases eq_or_ne j i with rfl | hj
      · rw [Function.update_self, splitAt_symm_apply_self, ← hplanar]; exact hp.1
      · rw [Function.update_of_ne hj, splitAt_symm_apply_of_ne _ _ hj]
        exact hp.2 ⟨j, hj⟩ (mem_univ _)
    obtain ⟨fA, fB, hfA, hfB, hsplit⟩ := exists_split_cutRe hε hεδ h0 h1 hhole' hP hF
    have hmaps : ∀ u : ι → HoledRect, (∀ j, j ≠ i → u j = s j) → ∀ x ∈ prod fun j ↦
        (u j).shrink (2 * ε), (fun j : {j // j ≠ i} ↦ x j) ∈ P := by
      intro u hu x hx j _
      have := mem_prod_iff.1 hx j
      rw [hu j j.2] at this
      exact set_mono_of_le (by linarith) this
    refine ⟨fun x ↦ fA (splitAt i x), fun x ↦ fB (splitAt i x), ?_, ?_, ?_⟩
    · refine hfA.comp (splitAt i).differentiableOn fun x hx ↦ ⟨?_, ?_⟩
      · have := mem_prod_iff.1 hx i
        simpa [uA] using this
      · exact hmaps uA (fun j hj ↦ Function.update_of_ne hj _ _) x hx
    · refine hfB.comp (splitAt i).differentiableOn fun x hx ↦ ⟨?_, ?_⟩
      · have := mem_prod_iff.1 hx i
        simpa [uB] using this
      · exact hmaps uB (fun j hj ↦ Function.update_of_ne hj _ _) x hx
    · intro x hx
      have hxA := mem_prod_iff.1 hx.1 i
      have hxB := mem_prod_iff.1 hx.2 i
      simp only [uA, uB, Function.update_self] at hxA hxB
      have := hsplit (x i) ⟨hxA, hxB⟩ _
        (hmaps uA (fun j hj ↦ Function.update_of_ne hj _ _) x hx.1)
      rw [show ((x i, fun j : {j // j ≠ i} ↦ x j)) = splitAt i x from rfl,
        ContinuousLinearEquiv.symm_apply_apply] at this
      exact this

/-- **The cut in the imaginary direction of the `i`-th coordinate is Cousin-shrinkable**,
provided the closed strip `[t - δ, t + δ]` does not contain `±r`. -/
theorem cousinShrinkable_cutIm [Finite ι] (s : ι → HoledRect) (i : ι) {t δ : ℝ} (hδ : 0 < δ)
    (h0 : (s i).y₀ ≤ t - δ) (h1 : t + δ ≤ (s i).y₁)
    (hhole : Disjoint (Icc (t - δ) (t + δ)) (Icc (-(s i).r) (s i).r) ∨
      Icc (t - δ) (t + δ) ⊆ Ioo (-(s i).r) (s i).r) :
    CousinShrinkable (prod (Function.update s i ((s i).withY₁ (t + δ))))
      (prod (Function.update s i ((s i).withY₀ (t - δ)))) := by
  have := Fintype.ofFinite ι
  intro K hK hKAB
  set σ := s i with hσ
  set uA := Function.update s i (σ.withY₁ (t + δ))
  set uB := Function.update s i (σ.withY₀ (t - δ))
  obtain ⟨g, hg, hgap⟩ : ∃ g > 0, Disjoint (Icc (t - δ) (t + δ)) (Icc (-σ.r) σ.r) →
      ∀ x ∈ Icc (t - δ) (t + δ), σ.r + g < |x| := by
    by_cases hd : Disjoint (Icc (t - δ) (t + δ)) (Icc (-σ.r) σ.r)
    · obtain ⟨g, hg, h⟩ := exists_gap (by linarith) hd
      exact ⟨g, hg, fun _ ↦ h⟩
    · exact ⟨1, one_pos, fun h ↦ (hd h).elim⟩
  have hAB : prod uA ∪ prod uB ⊆ prod s := by
    rintro x (hx | hx) <;> refine mem_prod_iff.2 fun j ↦ ?_ <;> have := mem_prod_iff.1 hx j <;>
      rcases eq_or_ne j i with rfl | hj
    · simp only [uA, Function.update_self] at this
      obtain ⟨h2, ⟨h3, h4⟩, h5⟩ := mem_set_iff'.1 this
      exact mem_set_iff'.2 ⟨h2, ⟨h3, by simp only [withY₁] at h4; linarith⟩, h5⟩
    · simpa [uA, Function.update_of_ne hj] using this
    · simp only [uB, Function.update_self] at this
      obtain ⟨h2, ⟨h3, h4⟩, h5⟩ := mem_set_iff'.1 this
      exact mem_set_iff'.2 ⟨h2, ⟨by simp only [withY₀] at h3; linarith, h4⟩, h5⟩
    · simpa [uB, Function.update_of_ne hj] using this
  obtain ⟨ε₀, hε₀, hKs⟩ := exists_subset_prod_shrink hK (hKAB.trans hAB)
  set ε := min (ε₀ / 2) (min (δ / 5) (g / 2)) with hεdef
  have hε : 0 < ε := by positivity
  have hεε₀ : 2 * ε ≤ ε₀ := by
    have := min_le_left (ε₀ / 2) (min (δ / 5) (g / 2)); linarith
  have hεδ : 4 * ε < δ := by
    have := (min_le_right (ε₀ / 2) (min (δ / 5) (g / 2))).trans (min_le_left _ _); linarith
  have hεg : ε < g := by
    have := (min_le_right (ε₀ / 2) (min (δ / 5) (g / 2))).trans (min_le_right _ _); linarith
  have hhole' : (∀ x ∈ Icc (t - δ) (t + δ), σ.r + ε < |x|) ∨
      Icc (t - δ) (t + δ) ⊆ Ioo (-σ.r) σ.r := by
    rcases hhole with hd | hin
    · exact Or.inl fun x hx ↦ lt_trans (by linarith) (hgap hd x hx)
    · exact Or.inr hin
  set A' := prod fun j ↦ (uA j).shrink ε
  set B' := prod fun j ↦ (uB j).shrink ε
  set A'' := prod fun j ↦ (uA j).shrink (2 * ε)
  set B'' := prod fun j ↦ (uB j).shrink (2 * ε)
  have hsh : ∀ u : ι → HoledRect, (prod fun j ↦ (u j).shrink (2 * ε)) =
      prod fun j ↦ ((u j).shrink ε).shrink ε := by
    intro u; simp_rw [shrink_shrink, two_mul]
  set τ : HoledRect := ⟨σ.x₀ + ε, σ.x₁ - ε, t - δ + ε, t + δ - ε, σ.r + ε⟩
  have hplanar : ((σ.withY₁ (t + δ)).shrink ε).set ∩ ((σ.withY₀ (t - δ)).shrink ε).set =
      τ.set := by
    ext z
    simp only [mem_inter_iff, mem_set_iff', shrink, withY₁, withY₀, τ]
    constructor
    · rintro ⟨⟨a1, ⟨-, a2⟩, a4⟩, ⟨-, ⟨b1, -⟩, -⟩⟩
      exact ⟨a1, ⟨b1, a2⟩, a4⟩
    · rintro ⟨a1, ⟨a2, a3⟩, a4⟩
      exact ⟨⟨a1, ⟨by linarith, a3⟩, a4⟩, ⟨a1, ⟨a2, by linarith⟩, a4⟩⟩
  have hA'B' : A' ∩ B' = prod (Function.update (fun j ↦ (s j).shrink ε) i τ) := by
    ext x
    simp only [A', B', mem_inter_iff, mem_prod_iff]
    constructor
    · rintro ⟨hA, hB⟩ j
      rcases eq_or_ne j i with rfl | hj
      · have hAj := hA j
        have hBj := hB j
        simp only [uA, uB, Function.update_self] at hAj hBj ⊢
        rw [← hplanar]; exact ⟨hAj, hBj⟩
      · have := hA j
        simpa [uA, Function.update_of_ne hj] using this
    · intro h
      refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩ <;> rcases eq_or_ne j i with rfl | hj
      · have := h j
        simp only [uA, Function.update_self] at this ⊢
        rw [← hplanar] at this; exact this.1
      · simpa [uA, Function.update_of_ne hj] using h j
      · have := h j
        simp only [uB, Function.update_self] at this ⊢
        rw [← hplanar] at this; exact this.2
      · simpa [uB, Function.update_of_ne hj] using h j
  refine ⟨A', B', A'', B'', isOpen_prod _, isOpen_prod _, isOpen_prod _, isOpen_prod _,
    isCompact_closure_prod _, closure_prod_shrink_subset hε uA, isCompact_closure_prod _,
    closure_prod_shrink_subset hε uB, ?_, ?_, ?_, ⟨_, hA'B'⟩, ?_⟩
  · change closure (prod fun j ↦ (uA j).shrink (2 * ε)) ⊆ _
    rw [hsh]; exact closure_prod_shrink_subset hε _
  · change closure (prod fun j ↦ (uB j).shrink (2 * ε)) ⊆ _
    rw [hsh]; exact closure_prod_shrink_subset hε _
  · intro x hx
    have hxs := mem_prod_iff.1 (hKs hx)
    have hxi := lt_margin_iff.1 (mem_shrink_set_iff.1 (hxs i))
    obtain ⟨⟨c1, c2⟩, ⟨c3, c4⟩, c5⟩ := hxi
    have hother : ∀ u : ι → HoledRect, (∀ j, j ≠ i → u j = s j) → ∀ j, j ≠ i →
        x j ∈ ((u j).shrink (2 * ε)).set := fun u hu j hj ↦ by
      rw [hu j hj]; exact set_mono_of_le hεε₀ (hxs j)
    rcases le_or_gt (x i).im t with hre | hre
    · refine Or.inl (mem_prod_iff.2 fun j ↦ ?_)
      rcases eq_or_ne j i with rfl | hj
      · simp only [uA, Function.update_self]
        refine mem_shrink_iff.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> simp only [withY₁] <;> linarith
      · exact hother uA (fun j hj ↦ Function.update_of_ne hj _ _) j hj
    · refine Or.inr (mem_prod_iff.2 fun j ↦ ?_)
      rcases eq_or_ne j i with rfl | hj
      · simp only [uB, Function.update_self]
        refine mem_shrink_iff.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> simp only [withY₀] <;> linarith
      · exact hother uB (fun j hj ↦ Function.update_of_ne hj _ _) j hj
  · intro d hd
    set P : Set ({j // j ≠ i} → ℂ) := Set.univ.pi fun j ↦ ((s j).shrink ε).set
    have hP : IsOpen P := isOpen_set_pi finite_univ fun j _ ↦ ((s j).shrink ε).isOpen_set
    have hF : DifferentiableOn ℂ (fun p ↦ d ((splitAt i).symm p))
        ((((σ.withY₁ (t + δ)).shrink ε).set ∩ ((σ.withY₀ (t - δ)).shrink ε).set) ×ˢ P) := by
      refine hd.comp (splitAt i).symm.differentiableOn fun p hp ↦ ?_
      rw [hA'B', mem_prod_iff]
      intro j
      rcases eq_or_ne j i with rfl | hj
      · rw [Function.update_self, splitAt_symm_apply_self, ← hplanar]; exact hp.1
      · rw [Function.update_of_ne hj, splitAt_symm_apply_of_ne _ _ hj]
        exact hp.2 ⟨j, hj⟩ (mem_univ _)
    obtain ⟨fA, fB, hfA, hfB, hsplit⟩ := exists_split_cutIm hε hεδ h0 h1 hhole' hP hF
    have hmaps : ∀ u : ι → HoledRect, (∀ j, j ≠ i → u j = s j) → ∀ x ∈ prod fun j ↦
        (u j).shrink (2 * ε), (fun j : {j // j ≠ i} ↦ x j) ∈ P := by
      intro u hu x hx j _
      have := mem_prod_iff.1 hx j
      rw [hu j j.2] at this
      exact set_mono_of_le (by linarith) this
    refine ⟨fun x ↦ fA (splitAt i x), fun x ↦ fB (splitAt i x), ?_, ?_, ?_⟩
    · refine hfA.comp (splitAt i).differentiableOn fun x hx ↦ ⟨?_, ?_⟩
      · have := mem_prod_iff.1 hx i
        simpa [uA] using this
      · exact hmaps uA (fun j hj ↦ Function.update_of_ne hj _ _) x hx
    · refine hfB.comp (splitAt i).differentiableOn fun x hx ↦ ⟨?_, ?_⟩
      · have := mem_prod_iff.1 hx i
        simpa [uB] using this
      · exact hmaps uB (fun j hj ↦ Function.update_of_ne hj _ _) x hx
    · intro x hx
      have hxA := mem_prod_iff.1 hx.1 i
      have hxB := mem_prod_iff.1 hx.2 i
      simp only [uA, uB, Function.update_self] at hxA hxB
      have := hsplit (x i) ⟨hxA, hxB⟩ _
        (hmaps uA (fun j hj ↦ Function.update_of_ne hj _ _) x hx.1)
      rw [show ((x i, fun j : {j // j ≠ i} ↦ x j)) = splitAt i x from rfl,
        ContinuousLinearEquiv.symm_apply_apply] at this
      exact this

end Transport

end Complex

end
