/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.CousinShrink

/-!
# Merging along grids of holed rectangles

Let `𝒵` be a family of subsets of `ℂ^ι`, closed under taking subsets, which is closed under
merging along cuts: if a product of holed rectangles `prod s` is cut in the real or imaginary
direction of one coordinate, along a closed strip not containing the edges of the hole, into two
overlapping products which lie in `𝒵`, then `prod s ∈ 𝒵`. If every point of the closure of
`prod s₀` has a neighbourhood in `𝒵`, then `prod s₀ ∈ 𝒵`.

In the proof of Theorem B for the structure sheaf (see `Oka.Analytification.GAGA.Cousin`), `𝒵` is
the family of sets on which a given cohomology class is compactly zero; the merging hypothesis is
the Mayer–Vietoris step, whose analytic input is `Complex.cousinShrinkable_cutRe` and
`Complex.cousinShrinkable_cutIm`, and the local hypothesis holds since cohomology classes are
locally zero.

The proof processes the `2 |ι|` real directions one at a time: after the directions in `T` have
been processed, every product of holed rectangles inside `prod s₀` (with the same holes) which is
full in the directions of `T` and has width `< h` in the other directions lies in `𝒵`. A new
direction is processed by merging pieces of width `< h` one after the other, choosing each cut
so that its strip avoids the edges of the hole.

## Main results

- `Complex.HoledRect.prod_cutRe_union`, `Complex.HoledRect.prod_cutIm_union`: the two pieces of a
  cut cover the product.
- `Complex.HoledRect.MergeRe`, `Complex.HoledRect.MergeIm`: the merging hypotheses.
- `Complex.HoledRect.interval_merge`: the one-dimensional merging step.
- `Complex.HoledRect.mem_of_merge`: the merging theorem.
-/

@[expose] public section

open Set Metric

namespace Complex

namespace HoledRect

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma prod_update_union_prod_update (s : ι → HoledRect) (i : ι) (σA σB : HoledRect)
    (h : σA.set ∪ σB.set = (s i).set) :
    prod (Function.update s i σA) ∪ prod (Function.update s i σB) = prod s := by
  ext x
  simp only [mem_union, mem_prod_iff]
  constructor
  · rintro (hx | hx) <;> intro j <;> rcases eq_or_ne j i with rfl | hj
    · rw [← h]; exact Or.inl (by simpa using hx j)
    · simpa [Function.update_of_ne hj] using hx j
    · rw [← h]; exact Or.inr (by simpa using hx j)
    · simpa [Function.update_of_ne hj] using hx j
  · intro hx
    have hi := hx i
    rw [← h] at hi
    rcases hi with hi | hi
    · refine Or.inl fun j ↦ ?_
      rcases eq_or_ne j i with rfl | hj
      · simpa using hi
      · simpa [Function.update_of_ne hj] using hx j
    · refine Or.inr fun j ↦ ?_
      rcases eq_or_ne j i with rfl | hj
      · simpa using hi
      · simpa [Function.update_of_ne hj] using hx j

omit [Fintype ι] in
/-- The two pieces of a cut in the real direction cover the product. -/
lemma prod_cutRe_union (s : ι → HoledRect) (i : ι) {t δ : ℝ} (hδ : 0 < δ)
    (h0 : (s i).x₀ ≤ t - δ) (h1 : t + δ ≤ (s i).x₁) :
    prod (Function.update s i ((s i).withX₁ (t + δ))) ∪
      prod (Function.update s i ((s i).withX₀ (t - δ))) = prod s := by
  refine prod_update_union_prod_update s i _ _ ?_
  ext z
  simp only [mem_union, mem_set_iff', withX₁, withX₀]
  constructor
  · rintro (⟨⟨h2, h3⟩, h4, h5⟩ | ⟨⟨h2, h3⟩, h4, h5⟩)
    · exact ⟨⟨h2, by linarith⟩, h4, h5⟩
    · exact ⟨⟨by linarith, h3⟩, h4, h5⟩
  · rintro ⟨⟨h2, h3⟩, h4, h5⟩
    rcases le_or_gt z.re t with h | h
    · exact Or.inl ⟨⟨h2, by linarith⟩, h4, h5⟩
    · exact Or.inr ⟨⟨by linarith, h3⟩, h4, h5⟩

omit [Fintype ι] in
/-- The two pieces of a cut in the imaginary direction cover the product. -/
lemma prod_cutIm_union (s : ι → HoledRect) (i : ι) {t δ : ℝ} (hδ : 0 < δ)
    (h0 : (s i).y₀ ≤ t - δ) (h1 : t + δ ≤ (s i).y₁) :
    prod (Function.update s i ((s i).withY₁ (t + δ))) ∪
      prod (Function.update s i ((s i).withY₀ (t - δ))) = prod s := by
  refine prod_update_union_prod_update s i _ _ ?_
  ext z
  simp only [mem_union, mem_set_iff', withY₁, withY₀]
  constructor
  · rintro (⟨h2, ⟨h3, h4⟩, h5⟩ | ⟨h2, ⟨h3, h4⟩, h5⟩)
    · exact ⟨h2, ⟨h3, by linarith⟩, h5⟩
    · exact ⟨h2, ⟨by linarith, h4⟩, h5⟩
  · rintro ⟨h2, ⟨h3, h4⟩, h5⟩
    rcases le_or_gt z.im t with h | h
    · exact Or.inl ⟨h2, ⟨h3, by linarith⟩, h5⟩
    · exact Or.inr ⟨h2, ⟨by linarith, h4⟩, h5⟩

/-- A closed interval containing neither `-r` nor `r` is disjoint from `[-r, r]` or contained in
`(-r, r)`. -/
lemma disjoint_or_subset_of_notMem {a b r : ℝ} (h1 : -r ∉ Icc a b)
    (h2 : r ∉ Icc a b) : Disjoint (Icc a b) (Icc (-r) r) ∨ Icc a b ⊆ Ioo (-r) r := by
  simp only [mem_Icc, not_and_or, not_le] at h1 h2
  rcases lt_or_ge b (-r) with hb | hb
  · exact Or.inl (Set.disjoint_left.2 fun x hx hx' ↦ by linarith [hx.2, hx'.1])
  rcases lt_or_ge r a with ha | ha
  · exact Or.inl (Set.disjoint_left.2 fun x hx hx' ↦ by linarith [hx.1, hx'.2])
  have h1' : -r < a := by rcases h1 with h1 | h1 <;> linarith
  have h2' : b < r := by rcases h2 with h2 | h2 <;> linarith
  exact Or.inr fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Among the three strips `[u - 2δ, u]`, `[u - 5δ, u - 3δ]`, `[u - 8δ, u - 6δ]` one contains
neither `-r` nor `r`. -/
lemma exists_good_cut (u r : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t, u - 7 * δ ≤ t ∧ t ≤ u - δ ∧ -r ∉ Icc (t - δ) (t + δ) ∧ r ∉ Icc (t - δ) (t + δ) := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon (u - δ) (by linarith) le_rfl
  have h1 := hcon (u - 4 * δ) (by linarith) (by linarith)
  have h2 := hcon (u - 7 * δ) le_rfl (by linarith)
  by_cases hA : -r ∈ Icc (u - δ - δ) (u - δ + δ) <;>
  by_cases hB : -r ∈ Icc (u - 4 * δ - δ) (u - 4 * δ + δ) <;>
  by_cases hC : -r ∈ Icc (u - 7 * δ - δ) (u - 7 * δ + δ)
  all_goals
    first
    | (simp only [mem_Icc] at hA hB; linarith [hA.1, hA.2, hB.1, hB.2])
    | (simp only [mem_Icc] at hA hC; linarith [hA.1, hA.2, hC.1, hC.2])
    | (simp only [mem_Icc] at hB hC; linarith [hB.1, hB.2, hC.1, hC.2])
    | skip
  all_goals
    first
    | (have e1 := h1 hB; have e2 := h2 hC; simp only [mem_Icc] at e1 e2
       linarith [e1.1, e1.2, e2.1, e2.2])
    | (have e0 := h0 hA; have e2 := h2 hC; simp only [mem_Icc] at e0 e2
       linarith [e0.1, e0.2, e2.1, e2.2])
    | (have e0 := h0 hA; have e1 := h1 hB; simp only [mem_Icc] at e0 e1
       linarith [e0.1, e0.2, e1.1, e1.2])

/-- **Merging along an interval.** Let `Q a c` be a property of intervals which is inherited by
subintervals, holds for all intervals of length `< h` inside `[X₀, X₁]`, and is closed under
merging `[a, t + δ]` and `[t - δ, c]` when the strip `[t - δ, t + δ]` contains neither `-r` nor
`r`. Then `Q X₀ X₁`. -/
lemma interval_merge {Q : ℝ → ℝ → Prop} {X₀ X₁ h r : ℝ} (hh : 0 < h)
    (hmono : ∀ a c a' c', Q a c → a ≤ a' → c' ≤ c → Q a' c')
    (hpiece : ∀ a c, X₀ ≤ a → c ≤ X₁ → c - a < h → Q a c)
    (hmerge : ∀ a c t δ, 0 < δ → a ≤ t - δ → t + δ ≤ c → -r ∉ Icc (t - δ) (t + δ) →
      r ∉ Icc (t - δ) (t + δ) → Q a (t + δ) → Q (t - δ) c → Q a c) :
    Q X₀ X₁ := by
  rcases lt_or_ge X₁ X₀ with hX | hX
  · exact hpiece X₀ X₁ le_rfl le_rfl (by linarith)
  have key : ∀ n : ℕ, Q X₀ (min X₁ (X₀ + n * (h / 4))) := by
    intro n
    induction n with
    | zero => exact hpiece _ _ le_rfl (min_le_left _ _) (by simp [min_eq_right hX]; linarith)
    | succ n ih =>
      set u := min X₁ (X₀ + n * (h / 4))
      set u' := min X₁ (X₀ + (n + 1 : ℕ) * (h / 4))
      have hu' : u' ≤ X₁ := min_le_left _ _
      by_cases hsmall : u' - X₀ < h
      · exact hpiece _ _ le_rfl hu' hsmall
      push Not at hsmall
      have huu' : u' ≤ u + h / 4 := by
        simp only [u, u']
        rw [min_le_iff]
        rcases le_total X₁ (X₀ + n * (h / 4)) with h1 | h1
        · left; rw [min_eq_left h1] at *; linarith
        · right; rw [min_eq_right h1]; push_cast; linarith
      have hu : X₀ + h / 2 ≤ u := by
        have h1 : X₀ + h ≤ X₁ := by linarith [min_le_left X₁ (X₀ + (n + 1 : ℕ) * (h / 4))]
        linarith
      have hu_le : u ≤ u' := min_le_min le_rfl (by push_cast; linarith)
      obtain ⟨t, ht1, ht2, hr1, hr2⟩ := exists_good_cut u r (δ := h / 32) (by positivity)
      refine hmerge X₀ u' t (h / 32) (by positivity) (by linarith) (by linarith) hr1 hr2 ?_ ?_
      · exact hmono _ _ _ _ ih le_rfl (by linarith)
      · exact hpiece _ _ (by linarith) hu' (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_ge ((X₁ - X₀) / (h / 4))
  have hn' : X₁ ≤ X₀ + n * (h / 4) := by
    rw [div_le_iff₀ (by positivity)] at hn; linarith
  simpa [min_eq_left hn'] using key n

/-- The lower end of `σ` in the real (`false`) or imaginary (`true`) direction. -/
def lo (σ : HoledRect) : Bool → ℝ
  | false => σ.x₀
  | true => σ.y₀

/-- The upper end of `σ` in the real (`false`) or imaginary (`true`) direction. -/
def hi (σ : HoledRect) : Bool → ℝ
  | false => σ.x₁
  | true => σ.y₁

/-- `σ` with its range in the real (`false`) or imaginary (`true`) direction replaced by
`(a, c)`. -/
def setRange (σ : HoledRect) : Bool → ℝ → ℝ → HoledRect
  | false, a, c => ⟨a, c, σ.y₀, σ.y₁, σ.r⟩
  | true, a, c => ⟨σ.x₀, σ.x₁, a, c, σ.r⟩

@[simp] lemma lo_setRange_self (σ : HoledRect) (b : Bool) (a c : ℝ) :
    lo (setRange σ b a c) b = a := by cases b <;> rfl

@[simp] lemma hi_setRange_self (σ : HoledRect) (b : Bool) (a c : ℝ) :
    hi (setRange σ b a c) b = c := by cases b <;> rfl

lemma lo_setRange_of_ne (σ : HoledRect) {b b' : Bool} (h : b' ≠ b) (a c : ℝ) :
    lo (setRange σ b a c) b' = lo σ b' := by cases b <;> cases b' <;> simp_all [lo, setRange]

lemma hi_setRange_of_ne (σ : HoledRect) {b b' : Bool} (h : b' ≠ b) (a c : ℝ) :
    hi (setRange σ b a c) b' = hi σ b' := by cases b <;> cases b' <;> simp_all [hi, setRange]

@[simp] lemma r_setRange (σ : HoledRect) (b : Bool) (a c : ℝ) : (setRange σ b a c).r = σ.r := by
  cases b <;> rfl

lemma setRange_lo_hi (σ : HoledRect) (b : Bool) : setRange σ b (lo σ b) (hi σ b) = σ := by
  cases b <;> rfl

/-- A holed rectangle with the same hole and smaller ranges is a subset. -/
lemma set_subset_of_ranges {σ τ : HoledRect} (hr : σ.r = τ.r)
    (h : ∀ b, lo τ b ≤ lo σ b ∧ hi σ b ≤ hi τ b) : σ.set ⊆ τ.set := by
  intro z hz
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := mem_set_iff'.1 hz
  obtain ⟨h6, h7⟩ := h false
  obtain ⟨h8, h9⟩ := h true
  simp only [lo, hi] at h6 h7 h8 h9
  exact mem_set_iff'.2 ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hr ▸ h5⟩

omit [Fintype ι] in
lemma prod_update_mono (s : ι → HoledRect) (i : ι) {σ σ' : HoledRect} (h : σ'.set ⊆ σ.set) :
    prod (Function.update s i σ') ⊆ prod (Function.update s i σ) := by
  intro x hx
  refine mem_prod_iff.2 fun j ↦ ?_
  rcases eq_or_ne j i with rfl | hj
  · simpa using h (by simpa using mem_prod_iff.1 hx j)
  · simpa [Function.update_of_ne hj] using mem_prod_iff.1 hx j

/-- `s` is a cell of `s₀`: the same holes and smaller ranges. -/
def IsCell (s₀ s : ι → HoledRect) : Prop :=
  ∀ i, (s i).r = (s₀ i).r ∧ ∀ b, lo (s₀ i) b ≤ lo (s i) b ∧ hi (s i) b ≤ hi (s₀ i) b

omit [Fintype ι] [DecidableEq ι] in
lemma IsCell.prod_subset {s₀ s : ι → HoledRect} (hs : IsCell s₀ s) : prod s ⊆ prod s₀ :=
  fun _ hx ↦ mem_prod_iff.2 fun i ↦
    set_subset_of_ranges (hs i).1 (hs i).2 (mem_prod_iff.1 hx i)

/-- The merge hypothesis in the real direction. -/
def MergeRe (𝒵 : Set (Set (ι → ℂ))) : Prop :=
  ∀ (s : ι → HoledRect) (i : ι) (t δ : ℝ), 0 < δ → (s i).x₀ ≤ t - δ → t + δ ≤ (s i).x₁ →
    (Disjoint (Icc (t - δ) (t + δ)) (Icc (-(s i).r) (s i).r) ∨
      Icc (t - δ) (t + δ) ⊆ Ioo (-(s i).r) (s i).r) →
    prod (Function.update s i ((s i).withX₁ (t + δ))) ∈ 𝒵 →
    prod (Function.update s i ((s i).withX₀ (t - δ))) ∈ 𝒵 → prod s ∈ 𝒵

/-- The merge hypothesis in the imaginary direction. -/
def MergeIm (𝒵 : Set (Set (ι → ℂ))) : Prop :=
  ∀ (s : ι → HoledRect) (i : ι) (t δ : ℝ), 0 < δ → (s i).y₀ ≤ t - δ → t + δ ≤ (s i).y₁ →
    (Disjoint (Icc (t - δ) (t + δ)) (Icc (-(s i).r) (s i).r) ∨
      Icc (t - δ) (t + δ) ⊆ Ioo (-(s i).r) (s i).r) →
    prod (Function.update s i ((s i).withY₁ (t + δ))) ∈ 𝒵 →
    prod (Function.update s i ((s i).withY₀ (t - δ))) ∈ 𝒵 → prod s ∈ 𝒵

omit [Fintype ι] in
lemma merge_setRange {𝒵 : Set (Set (ι → ℂ))} (hRe : MergeRe 𝒵) (hIm : MergeIm 𝒵)
    (s : ι → HoledRect) (i : ι) (b : Bool) {a c t δ : ℝ} (hδ : 0 < δ) (ha : a ≤ t - δ)
    (hc : t + δ ≤ c) (h1 : -(s i).r ∉ Icc (t - δ) (t + δ)) (h2 : (s i).r ∉ Icc (t - δ) (t + δ))
    (hA : prod (Function.update s i (setRange (s i) b a (t + δ))) ∈ 𝒵)
    (hB : prod (Function.update s i (setRange (s i) b (t - δ) c)) ∈ 𝒵) :
    prod (Function.update s i (setRange (s i) b a c)) ∈ 𝒵 := by
  have hhole := disjoint_or_subset_of_notMem h1 h2
  cases b
  · refine hRe _ i t δ hδ (by simpa [setRange] using ha) (by simpa [setRange] using hc)
      (by simpa [setRange] using hhole) ?_ ?_
    · simpa [Function.update_idem, setRange, withX₁] using hA
    · simpa [Function.update_idem, setRange, withX₀] using hB
  · refine hIm _ i t δ hδ (by simpa [setRange] using ha) (by simpa [setRange] using hc)
      (by simpa [setRange] using hhole) ?_ ?_
    · simpa [Function.update_idem, setRange, withY₁] using hA
    · simpa [Function.update_idem, setRange, withY₀] using hB

omit [Fintype ι] in
/-- **Merging along grids.** Let `𝒵` be a family of subsets of `ℂ^ι` containing `∅`, closed
under taking subsets and under merging along cuts (`MergeRe`, `MergeIm`). If every point of the
closure of `prod s₀` has a neighbourhood in `𝒵`, then `prod s₀ ∈ 𝒵`. -/
theorem mem_of_merge [Finite ι] (𝒵 : Set (Set (ι → ℂ))) (hempty : ∅ ∈ 𝒵)
    (hsub : ∀ W ∈ 𝒵, ∀ W', W' ⊆ W → W' ∈ 𝒵) (hRe : MergeRe 𝒵) (hIm : MergeIm 𝒵)
    (s₀ : ι → HoledRect) (hloc : ∀ x ∈ closure (prod s₀), ∃ W ∈ 𝒵, W ∈ nhds x) :
    prod s₀ ∈ 𝒵 := by
  cases nonempty_fintype ι
  choose! W hW hWn using hloc
  obtain ⟨l, hl, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_closure_prod s₀)
    (c := fun x : closure (prod s₀) ↦ interior (W x)) (fun _ ↦ isOpen_interior)
    (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hWn x hx)⟩)
  set h := l / 2 with hhdef
  have hh : 0 < h := by positivity
  have hsmall : ∀ s : ι → HoledRect, IsCell s₀ s → (∀ i b, hi (s i) b - lo (s i) b < h) →
      prod s ∈ 𝒵 := by
    intro s hs hsm
    rcases (prod s).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · rw [he]; exact hempty
    have hxK : x ∈ closure (prod s₀) := subset_closure (hs.prod_subset hx)
    obtain ⟨y, hy⟩ := hleb x hxK
    refine hsub _ (hW y y.2) _ fun z hz ↦ interior_subset (hy ?_)
    rw [mem_ball, dist_pi_lt_iff hl]
    intro i
    have hzi := mem_set_iff'.1 (mem_prod_iff.1 hz i)
    have hxi := mem_set_iff'.1 (mem_prod_iff.1 hx i)
    have e1 := hsm i false
    have e2 := hsm i true
    simp only [lo, hi] at e1 e2
    rw [Complex.dist_eq]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    simp only [sub_re, sub_im]
    have a1 : |(z i).re - (x i).re| < h := by
      rw [abs_sub_lt_iff]; constructor <;> linarith [hzi.1.1, hzi.1.2, hxi.1.1, hxi.1.2]
    have a2 : |(z i).im - (x i).im| < h := by
      rw [abs_sub_lt_iff]; constructor <;> linarith [hzi.2.1.1, hzi.2.1.2, hxi.2.1.1, hxi.2.1.2]
    linarith
  have hΦ : ∀ T : Finset (ι × Bool), ∀ s, IsCell s₀ s →
      (∀ d ∈ T, lo (s d.1) d.2 = lo (s₀ d.1) d.2 ∧ hi (s d.1) d.2 = hi (s₀ d.1) d.2) →
      (∀ d ∉ T, hi (s d.1) d.2 - lo (s d.1) d.2 < h) → prod s ∈ 𝒵 := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun s hs _ hsm ↦ hsmall s hs fun i b ↦ hsm (i, b) (Finset.notMem_empty _)
    | insert d T hdT ih =>
      intro s hs hfull hsm
      obtain ⟨i, b⟩ := d
      have hQ := interval_merge (Q := fun a c ↦
        prod (Function.update s i (setRange (s i) b a c)) ∈ 𝒵)
        (X₀ := lo (s₀ i) b) (X₁ := hi (s₀ i) b) (r := (s i).r) hh ?_ ?_ ?_
      · obtain ⟨e1, e2⟩ := hfull (i, b) (Finset.mem_insert_self _ _)
        simp only at e1 e2
        rwa [← e1, ← e2, setRange_lo_hi, Function.update_eq_self] at hQ
      · intro a c a' c' hQ ha hc
        refine hsub _ hQ _ (prod_update_mono s i ?_)
        refine set_subset_of_ranges (by simp) fun b' ↦ ?_
        rcases eq_or_ne b' b with rfl | hb
        · simpa using ⟨ha, hc⟩
        · simp [lo_setRange_of_ne _ hb, hi_setRange_of_ne _ hb]
      · intro a c ha hc hac
        refine ih _ ?_ ?_ ?_
        · intro j
          rcases eq_or_ne j i with rfl | hj
          · refine ⟨by simpa using (hs j).1, fun b' ↦ ?_⟩
            rcases eq_or_ne b' b with rfl | hb
            · simpa using ⟨ha, hc⟩
            · simpa [lo_setRange_of_ne _ hb, hi_setRange_of_ne _ hb] using (hs j).2 b'
          · simpa [Function.update_of_ne hj] using hs j
        · rintro ⟨j, b'⟩ hd
          have hne : (j, b') ≠ (i, b) := fun h ↦ hdT (h ▸ hd)
          have := hfull (j, b') (Finset.mem_insert_of_mem hd)
          rcases eq_or_ne j i with rfl | hj
          · have hb : b' ≠ b := fun h ↦ hne (by rw [h])
            simpa [lo_setRange_of_ne _ hb, hi_setRange_of_ne _ hb] using this
          · simpa [Function.update_of_ne hj] using this
        · rintro ⟨j, b'⟩ hd
          by_cases hji : (j, b') = (i, b)
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hji
            simpa using hac
          · have := hsm (j, b') (by simp [Finset.mem_insert, hji, hd])
            rcases eq_or_ne j i with rfl | hj
            · have hb : b' ≠ b := fun h ↦ hji (by rw [h])
              simpa [lo_setRange_of_ne _ hb, hi_setRange_of_ne _ hb] using this
            · simpa [Function.update_of_ne hj] using this
      · intro a c t δ hδ ha hc h1 h2 hA hB
        exact merge_setRange hRe hIm s i b hδ ha hc h1 h2 hA hB
  exact hΦ Finset.univ s₀ (fun i ↦ ⟨rfl, fun b ↦ ⟨le_rfl, le_rfl⟩⟩)
    (fun d _ ↦ ⟨rfl, rfl⟩) (fun d hd ↦ (hd (Finset.mem_univ d)).elim)

end HoledRect

end Complex

end
