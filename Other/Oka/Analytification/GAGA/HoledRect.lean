/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Rectangles with a centred square hole, and their products

The domains on which Theorem B for the structure sheaf is proved by Cousin integrals are
products of planar sets `(x₀, x₁) × (y₀, y₁) \ [-r, r]²` (no hole if `r < 0`). This file sets up
these sets and their shrinkings.

## Main definitions

- `Complex.HoledRect`: the data `x₀ x₁ y₀ y₁ r : ℝ`, with `HoledRect.set` the planar set
  `(x₀, x₁) × (y₀, y₁) \ [-r, r]²`.
- `Complex.HoledRect.margin σ z`: a continuous function which is positive exactly on `σ.set`,
  the distance of `z` to the boundary of `σ.set` in a suitable sense.
- `Complex.HoledRect.shrink ε σ`: the set of points with margin `> ε`.
- `Complex.HoledRect.prod s`: the product `∏ i, (s i).set ⊆ ℂ^ι`.
- `Complex.HoledRect.puncturedSet P`: the product `(ℂ^×)^P × ℂ^{ι \ P}`.

## Main results

- `Complex.HoledRect.exists_subset_prod_shrink`: a compact subset of `prod s` lies in
  `prod (shrink ε ∘ s)` for some `ε > 0`.
- `Complex.HoledRect.closure_prod_shrink_subset`, `Complex.HoledRect.isCompact_closure_prod`:
  shrinking gives relatively compact subsets.
- `Complex.HoledRect.exists_prod_of_isCompact`: a compact subset of `(ℂ^×)^P × ℂ^{ι \ P}` lies
  in a product of holed squares with compact closure in `(ℂ^×)^P × ℂ^{ι \ P}`.
-/

@[expose] public section

open Set

namespace Complex

/-- A planar rectangle with a centred square hole: the set `(x₀, x₁) × (y₀, y₁) \ [-r, r]²`
(there is no hole if `r < 0`). -/
structure HoledRect where
  /-- The left end of the rectangle. -/
  x₀ : ℝ
  /-- The right end of the rectangle. -/
  x₁ : ℝ
  /-- The lower end of the rectangle. -/
  y₀ : ℝ
  /-- The upper end of the rectangle. -/
  y₁ : ℝ
  /-- The half side length of the hole. -/
  r : ℝ

namespace HoledRect

/-- The closed square `[-r, r]²` (empty if `r < 0`). -/
def hole (r : ℝ) : Set ℂ := Icc (-r) r ×ℂ Icc (-r) r

/-- The planar set `(x₀, x₁) × (y₀, y₁) \ [-r, r]²`. -/
def set (σ : HoledRect) : Set ℂ := (Ioo σ.x₀ σ.x₁ ×ℂ Ioo σ.y₀ σ.y₁) \ hole σ.r

/-- The margin of `z` in `σ`: positive exactly on `σ.set`. -/
noncomputable def margin (σ : HoledRect) (z : ℂ) : ℝ :=
  min (min (z.re - σ.x₀) (σ.x₁ - z.re)) (min (min (z.im - σ.y₀) (σ.y₁ - z.im))
    (max |z.re| |z.im| - σ.r))

/-- Shrinking by `ε`: the rectangle shrinks by `ε` on each side and the hole grows by `ε`. -/
def shrink (ε : ℝ) (σ : HoledRect) : HoledRect :=
  ⟨σ.x₀ + ε, σ.x₁ - ε, σ.y₀ + ε, σ.y₁ - ε, σ.r + ε⟩

lemma mem_hole_iff {r : ℝ} {z : ℂ} : z ∈ hole r ↔ max |z.re| |z.im| ≤ r := by
  simp [hole, mem_reProdIm, abs_le]

lemma isClosed_hole (r : ℝ) : IsClosed (hole r) := isClosed_Icc.reProdIm isClosed_Icc

lemma isOpen_set (σ : HoledRect) : IsOpen σ.set :=
  (isOpen_Ioo.reProdIm isOpen_Ioo).sdiff (isClosed_hole _)

@[fun_prop]
lemma continuous_margin (σ : HoledRect) : Continuous σ.margin := by
  unfold margin; fun_prop

lemma mem_set_iff {σ : HoledRect} {z : ℂ} : z ∈ σ.set ↔ 0 < σ.margin z := by
  simp only [set, mem_sdiff, mem_reProdIm, mem_Ioo, mem_hole_iff, not_le, margin, lt_min_iff,
    sub_pos]
  tauto

lemma margin_shrink (ε : ℝ) (σ : HoledRect) (z : ℂ) :
    (σ.shrink ε).margin z = σ.margin z - ε := by
  simp only [margin, shrink]
  have h1 : z.re - (σ.x₀ + ε) = z.re - σ.x₀ - ε := by ring
  have h2 : σ.x₁ - ε - z.re = σ.x₁ - z.re - ε := by ring
  have h3 : z.im - (σ.y₀ + ε) = z.im - σ.y₀ - ε := by ring
  have h4 : σ.y₁ - ε - z.im = σ.y₁ - z.im - ε := by ring
  have h5 : max |z.re| |z.im| - (σ.r + ε) = max |z.re| |z.im| - σ.r - ε := by ring
  rw [h1, h2, h3, h4, h5]
  simp only [min_sub_sub_right]

lemma mem_shrink_set_iff {ε : ℝ} {σ : HoledRect} {z : ℂ} :
    z ∈ (σ.shrink ε).set ↔ ε < σ.margin z := by
  rw [mem_set_iff, margin_shrink, sub_pos]

lemma shrink_shrink (ε ε' : ℝ) (σ : HoledRect) :
    (σ.shrink ε).shrink ε' = σ.shrink (ε + ε') := by
  simp only [shrink, HoledRect.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ring

lemma set_subset_rect (σ : HoledRect) : σ.set ⊆ Icc σ.x₀ σ.x₁ ×ℂ Icc σ.y₀ σ.y₁ :=
  fun _ hz ↦ ⟨Ioo_subset_Icc_self hz.1.1, Ioo_subset_Icc_self hz.1.2⟩

/-- The closure of a shrinking consists of points of margin `≥ ε`. -/
lemma closure_shrink_set_subset (ε : ℝ) (σ : HoledRect) :
    closure (σ.shrink ε).set ⊆ {z | ε ≤ σ.margin z} := by
  refine closure_minimal (fun z hz ↦ (mem_shrink_set_iff.1 hz).le) ?_
  exact isClosed_le continuous_const σ.continuous_margin

lemma closure_shrink_set_subset_set {ε : ℝ} (hε : 0 < ε) (σ : HoledRect) :
    closure (σ.shrink ε).set ⊆ σ.set := fun _ hz ↦
  mem_set_iff.2 (hε.trans_le (closure_shrink_set_subset ε σ hz))

lemma isCompact_closure_set (σ : HoledRect) : IsCompact (closure σ.set) :=
  (isCompact_Icc.reProdIm isCompact_Icc).of_isClosed_subset isClosed_closure
    (closure_minimal σ.set_subset_rect (isClosed_Icc.reProdIm isClosed_Icc))

variable {ι : Type*} [Finite ι]

/-- The product `∏ i, (s i).set ⊆ ℂ^ι`. -/
def prod (s : ι → HoledRect) : Set (ι → ℂ) := Set.univ.pi fun i ↦ (s i).set

lemma isOpen_prod (s : ι → HoledRect) : IsOpen (prod s) :=
  isOpen_set_pi finite_univ fun i _ ↦ (s i).isOpen_set

omit [Finite ι] in
lemma mem_prod_iff {s : ι → HoledRect} {x : ι → ℂ} : x ∈ prod s ↔ ∀ i, x i ∈ (s i).set := by
  simp [prod]

omit [Finite ι] in
lemma closure_prod (s : ι → HoledRect) :
    closure (prod s) = Set.univ.pi fun i ↦ closure (s i).set :=
  closure_pi_set _ _

omit [Finite ι] in
lemma isCompact_closure_prod (s : ι → HoledRect) : IsCompact (closure (prod s)) := by
  rw [closure_prod]
  exact isCompact_univ_pi fun i ↦ (s i).isCompact_closure_set

omit [Finite ι] in
lemma closure_prod_shrink_subset {ε : ℝ} (hε : 0 < ε) (s : ι → HoledRect) :
    closure (prod fun i ↦ (s i).shrink ε) ⊆ prod s := by
  rw [closure_prod]
  exact pi_mono fun i _ ↦ closure_shrink_set_subset_set hε (s i)

/-- A compact subset of `prod s` lies in a uniform shrinking of `prod s`. -/
lemma exists_subset_prod_shrink {s : ι → HoledRect} {K : Set (ι → ℂ)} (hK : IsCompact K)
    (hKs : K ⊆ prod s) : ∃ ε > 0, K ⊆ prod fun i ↦ (s i).shrink ε := by
  cases nonempty_fintype ι
  have h : ∀ i, ∃ e > 0, ∀ x ∈ K, e ≤ (s i).margin (x i) := by
    intro i
    rcases K.eq_empty_or_nonempty with hK0 | hK0
    · exact ⟨1, one_pos, by simp [hK0]⟩
    obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hK0
      (f := fun x : ι → ℂ ↦ (s i).margin (x i)) (by fun_prop)
    exact ⟨_, mem_set_iff.1 (mem_prod_iff.1 (hKs hx) i), fun y hy ↦ hmin hy⟩
  choose e he hle using h
  set ε : ℝ := 1 / (1 + ∑ i, 1 / e i) with hε
  have hsum : 0 ≤ ∑ i, 1 / e i := Finset.sum_nonneg fun i _ ↦ (one_div_pos.2 (he i)).le
  have hε0 : 0 < ε := by positivity
  refine ⟨ε, hε0, fun x hx ↦ mem_prod_iff.2 fun i ↦ mem_shrink_set_iff.2 ?_⟩
  refine lt_of_lt_of_le ?_ (hle i x hx)
  rw [hε, div_lt_iff₀ (by positivity)]
  have : 1 / e i ≤ ∑ j, 1 / e j :=
    Finset.single_le_sum (f := fun j ↦ 1 / e j) (fun j _ ↦ (one_div_pos.2 (he j)).le)
      (Finset.mem_univ i)
  have h1 : e i * (1 / e i) = 1 := mul_one_div_cancel (he i).ne'
  nlinarith [he i]

omit [Finite ι] in
/-- The closure of `σ.set` avoids the hole. -/
lemma closure_set_subset (σ : HoledRect) : closure σ.set ⊆ {z | σ.r ≤ max |z.re| |z.im|} := by
  refine closure_minimal (fun z hz ↦ ?_) (isClosed_le continuous_const (by fun_prop))
  have := mem_set_iff.1 hz
  simp only [margin, lt_min_iff, sub_pos] at this
  exact this.2.2.le

/-- The product of copies of `ℂ` and of `ℂ^×`: the points whose coordinates in `P` do not
vanish. -/
def puncturedSet (P : Set ι) : Set (ι → ℂ) := {x | ∀ i ∈ P, x i ≠ 0}

/-- A compact subset of `(ℂ^×)^P × ℂ^{ι \ P}` lies in a product of holed squares whose closure is
compact and still contained in `(ℂ^×)^P × ℂ^{ι \ P}`. -/
lemma exists_prod_of_isCompact (P : Set ι) {K : Set (ι → ℂ)} (hK : IsCompact K)
    (hKP : K ⊆ puncturedSet P) :
    ∃ s : ι → HoledRect, K ⊆ prod s ∧ closure (prod s) ⊆ puncturedSet P := by
  classical
  cases nonempty_fintype ι
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have he : ∀ i, ∃ e > 0, i ∈ P → ∀ x ∈ K, e ≤ max |(x i).re| |(x i).im| := by
    intro i
    by_cases hi : i ∈ P
    · rcases K.eq_empty_or_nonempty with hK0 | hK0
      · exact ⟨1, one_pos, fun _ ↦ by simp [hK0]⟩
      obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hK0
        (f := fun x : ι → ℂ ↦ max |(x i).re| |(x i).im|) (by fun_prop)
      refine ⟨_, ?_, fun _ y hy ↦ hmin hy⟩
      have hxi : x i ≠ 0 := hKP hx i hi
      by_contra hle
      push Not at hle
      have h1 : |(x i).re| = 0 := le_antisymm ((le_max_left _ _).trans hle) (abs_nonneg _)
      have h2 : |(x i).im| = 0 := le_antisymm ((le_max_right _ _).trans hle) (abs_nonneg _)
      exact hxi (Complex.ext (abs_eq_zero.1 h1) (abs_eq_zero.1 h2))
    · exact ⟨1, one_pos, fun h ↦ (hi h).elim⟩
  choose e he0 hle using he
  refine ⟨fun i ↦ ⟨-(R + 1), R + 1, -(R + 1), R + 1, if i ∈ P then e i / 2 else -1⟩, ?_, ?_⟩
  · intro x hx
    refine mem_prod_iff.2 fun i ↦ mem_set_iff.2 ?_
    have hxi : ‖x i‖ ≤ R := (norm_le_pi_norm x i).trans (hR x hx)
    have h1 := (Complex.abs_re_le_norm (x i)).trans hxi
    have h2 := (Complex.abs_im_le_norm (x i)).trans hxi
    rw [abs_le] at h1 h2
    simp only [margin, lt_min_iff, sub_pos]
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
    split_ifs with hi
    · linarith [hle i hi x hx, he0 i]
    · linarith [le_max_left |(x i).re| |(x i).im|, abs_nonneg (x i).re]
  · intro x hx i hi hxi
    rw [closure_prod] at hx
    have := closure_set_subset _ (hx i (mem_univ i))
    simp only [hi, if_true, mem_setOf_eq, hxi, zero_re, zero_im, abs_zero, max_self] at this
    linarith [he0 i]

end HoledRect

end Complex

end
