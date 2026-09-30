/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.CousinShrink
public import Other.Oka.Analytification.GAGA.MittagLeffler
public import Other.Oka.Analytification.GAGA.RungeFrame

/-!
# Runge approximation in several variables and `lim¹ = 0` on `(ℂ^×)^P × ℂ^{ι \ P}`

Approximation of holomorphic functions on products is done one coordinate at a time, the other
coordinates being holomorphic parameters (`Complex.exists_approx_pi`). For the exhaustion of
`D = (ℂ^×)^P × ℂ^{ι \ P}` by the products of holed squares
`U n = ∏ i, (-(n + 1), n + 1)² \ [-(1/4)^(n+1), (1/4)^(n+1)]²` (no hole for `i ∉ P`), every
function holomorphic on `U (n + 1)` is a uniform limit on `U n` of functions holomorphic on `D`
(one-variable Runge on frames, resp. rectangles), and the Mittag-Leffler argument gives
`lim¹_n 𝒪(U n) = 0`, the input for the exhaustion step of Theorem B on `D`.

## Main results

- `Complex.exists_approx_pi`: approximation on products, given one-variable approximation with
  holomorphic parameters in each coordinate.
- `Complex.exhaustion`: the exhaustion `U n` of `D`, with `Complex.iUnion_exhaustion`,
  `Complex.monotone_exhaustion`, `Complex.closure_exhaustion_subset` (`U n ⋐ U (n + 1)`).
- `Complex.exists_approx_exhaustion`: functions on `U (n + 1)` are uniform limits on `U n` of
  functions on `D`.
- `Complex.exists_mittagLeffler_exhaustion`: `lim¹_n 𝒪(U n) = 0`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Complex

variable {ι : Type*} [Finite ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Approximation on products.** Let `Ω i ⊆ T i` be open subsets of `ℂ`, and `K i ⊆ Ω i`
compact, such that in each coordinate every function holomorphic on `Ω i × P` (holomorphic
parameters in an open `P ⊆ ℂ^{ι \ {i}}`) is a uniform limit on `K i × L` (`L ⊆ P` compact) of
functions holomorphic on `T i × P`. Then every function holomorphic on `∏ Ω i` is a uniform limit
on `∏ K i` of functions holomorphic on `∏ T i`. -/
theorem exists_approx_pi (Ω T K : ι → Set ℂ) (hΩ : ∀ i, IsOpen (Ω i)) (hT : ∀ i, IsOpen (T i))
    (hΩT : ∀ i, Ω i ⊆ T i) (hK : ∀ i, IsCompact (K i)) (hKΩ : ∀ i, K i ⊆ Ω i)
    (hrunge : ∀ i (P : Set ({j // j ≠ i} → ℂ)), IsOpen P → ∀ f : ℂ × ({j // j ≠ i} → ℂ) → ℂ,
      DifferentiableOn ℂ f (Ω i ×ˢ P) → ∀ L, IsCompact L → L ⊆ P → ∀ ε > 0,
      ∃ g : ℂ × ({j // j ≠ i} → ℂ) → ℂ, DifferentiableOn ℂ g (T i ×ˢ P) ∧
        ∀ z ∈ K i, ∀ w ∈ L, ‖f (z, w) - g (z, w)‖ ≤ ε)
    {g : (ι → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (Set.univ.pi Ω)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : (ι → ℂ) → ℂ, DifferentiableOn ℂ G (Set.univ.pi T) ∧
      ∀ x ∈ Set.univ.pi K, ‖g x - G x‖ ≤ ε := by
  classical
  cases nonempty_fintype ι
  set n := Fintype.card ι
  set η := ε / (n + 1) with hη
  have hη0 : 0 < η := by positivity
  have key : ∀ S : Finset ι, ∃ G : (ι → ℂ) → ℂ,
      DifferentiableOn ℂ G (Set.univ.pi fun j ↦ if j ∈ S then T j else Ω j) ∧
      ∀ x ∈ Set.univ.pi K, ‖g x - G x‖ ≤ S.card * η := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨g, by simpa using hg, fun x _ ↦ by simp⟩
    | insert i S hiS ih =>
      obtain ⟨G, hG, hGe⟩ := ih
      set M : ι → Set ℂ := fun j ↦ if j ∈ S then T j else Ω j with hM
      have hMi : M i = Ω i := by simp [M, hiS]
      have hMo : ∀ j, IsOpen (M j) := fun j ↦ by
        simp only [M]; split_ifs; exacts [hT j, hΩ j]
      have hKM : ∀ j, K j ⊆ M j := fun j ↦ by
        simp only [M]; split_ifs; exacts [(hKΩ j).trans (hΩT j), hKΩ j]
      set P : Set ({j // j ≠ i} → ℂ) := Set.univ.pi fun j ↦ M j
      have hP : IsOpen P := isOpen_set_pi finite_univ fun j _ ↦ hMo j
      have hF : DifferentiableOn ℂ (fun p ↦ G ((splitAt i).symm p)) (Ω i ×ˢ P) := by
        refine hG.comp (splitAt i).symm.differentiableOn fun p hp j _ ↦ ?_
        rcases eq_or_ne j i with rfl | hj
        · rw [splitAt_symm_apply_self, hMi]; exact hp.1
        · rw [splitAt_symm_apply_of_ne _ _ hj]; exact hp.2 ⟨j, hj⟩ (mem_univ _)
      set L : Set ({j // j ≠ i} → ℂ) := Set.univ.pi fun j ↦ K j
      have hL : IsCompact L := isCompact_univ_pi fun j ↦ hK j
      have hLP : L ⊆ P := pi_mono fun j _ ↦ hKM j
      obtain ⟨G', hG', hG'e⟩ := hrunge i P hP _ hF L hL hLP η hη0
      refine ⟨fun x ↦ G' (splitAt i x), ?_, fun x hx ↦ ?_⟩
      · refine hG'.comp (splitAt i).differentiableOn fun x hx ↦ ⟨?_, fun j _ ↦ ?_⟩
        · have := hx i (mem_univ _); simpa using this
        · have hj : (j : ι) ∈ insert i S ↔ (j : ι) ∈ S := by simp [j.2]
          simpa [M, hj] using hx j (mem_univ _)
      · have h1 := hGe x hx
        have h2 := hG'e (x i) (hx i (mem_univ _)) (fun j : {j // j ≠ i} ↦ x j)
          (fun j _ ↦ hx j (mem_univ _))
        rw [show ((x i, fun j : {j // j ≠ i} ↦ x j)) = splitAt i x from rfl,
          ContinuousLinearEquiv.symm_apply_apply] at h2
        rw [Finset.card_insert_of_notMem hiS]
        calc ‖g x - G' (splitAt i x)‖ ≤ ‖g x - G x‖ + ‖G x - G' (splitAt i x)‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ S.card * η + η := add_le_add h1 h2
          _ = ((S.card + 1 : ℕ) : ℝ) * η := by push_cast; ring
  obtain ⟨G, hG, hGe⟩ := key Finset.univ
  refine ⟨G, by simpa using hG, fun x hx ↦ (hGe x hx).trans ?_⟩
  rw [Finset.card_univ, hη, mul_div_assoc']
  rw [div_le_iff₀ (by positivity)]
  nlinarith

open HoledRect

/-- Membership in the closure of a holed rectangle. -/
lemma HoledRect.mem_closure_set {σ : HoledRect} {z : ℂ} (hz : z ∈ closure σ.set) :
    (σ.x₀ ≤ z.re ∧ z.re ≤ σ.x₁) ∧ (σ.y₀ ≤ z.im ∧ z.im ≤ σ.y₁) ∧ σ.r ≤ max |z.re| |z.im| := by
  have h1 := closure_minimal σ.set_subset_rect (isClosed_Icc.reProdIm isClosed_Icc) hz
  have h2 := σ.closure_set_subset hz
  exact ⟨h1.1, h1.2, h2⟩

/-- The exhaustion of `(ℂ^×)^P × ℂ^{ι \ P}` by products of holed squares: the square
`(-(n + 1), n + 1)²` with the hole `[-(1/4)^(n+1), (1/4)^(n+1)]²` in the coordinates in `P`. -/
noncomputable def exhaustion (P : Finset ι) (n : ℕ) : ι → HoledRect := fun i ↦
  ⟨-(n + 1), n + 1, -(n + 1), n + 1, if i ∈ P then (1 / 4) ^ (n + 1) else -1⟩

omit [Finite ι] in
lemma exhaustion_subset (P : Finset ι) (n : ℕ) :
    prod (exhaustion P n) ⊆ prod (exhaustion P (n + 1)) := by
  intro x hx
  refine mem_prod_iff.2 fun i ↦ ?_
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := mem_set_iff'.1 (mem_prod_iff.1 hx i)
  simp only [exhaustion] at h1 h2 h3 h4 h5 ⊢
  refine mem_set_iff'.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> push_cast <;> try linarith
  split_ifs at h5 ⊢
  · have : ((1 : ℝ) / 4) ^ (n + 1 + 1) ≤ (1 / 4) ^ (n + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  · exact h5

omit [Finite ι] in
lemma monotone_exhaustion (P : Finset ι) : Monotone fun n ↦ prod (exhaustion P n) :=
  monotone_nat_of_le_succ (exhaustion_subset P)

omit [Finite ι] in
/-- The members of the exhaustion avoid `0` in the coordinates in `P`. -/
lemma ne_zero_of_mem_exhaustion_set {P : Finset ι} {n : ℕ} {i : ι} (hi : i ∈ P) {z : ℂ}
    (hz : z ∈ (exhaustion P n i).set) : z ≠ 0 := by
  rintro rfl
  have := (mem_set_iff'.1 hz).2.2
  simp only [exhaustion, hi, if_true, zero_re, zero_im, abs_zero, max_self] at this
  have : (0 : ℝ) < (1 / 4) ^ (n + 1) := by positivity
  linarith

omit [Finite ι] in
/-- A point, nonzero if `i ∈ P`, eventually lies in the `i`-th factor of the exhaustion. -/
lemma eventually_mem_exhaustion_set {P : Finset ι} {i : ι} {z : ℂ} (hz : i ∈ P → z ≠ 0) :
    ∀ᶠ n : ℕ in atTop, z ∈ (exhaustion P n i).set := by
  have hev1 : ∀ᶠ n : ℕ in atTop, ‖z‖ < n + 1 := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hev2 : ∀ᶠ n : ℕ in atTop, i ∈ P → (1 / 4 : ℝ) ^ (n + 1) < max |z.re| |z.im| := by
    by_cases hi : i ∈ P
    · have hpos : 0 < max |z.re| |z.im| := by
        by_contra h
        push Not at h
        have h1 : |z.re| = 0 := le_antisymm ((le_max_left _ _).trans h) (abs_nonneg _)
        have h2 : |z.im| = 0 := le_antisymm ((le_max_right _ _).trans h) (abs_nonneg _)
        exact hz hi (Complex.ext (abs_eq_zero.1 h1) (abs_eq_zero.1 h2))
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos (show (1 / 4 : ℝ) < 1 by norm_num)
      filter_upwards [eventually_ge_atTop N] with n hn _
      exact lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hN
    · exact .of_forall fun _ h ↦ absurd h hi
  filter_upwards [hev1, hev2] with n hn1 hn2
  have h1 := abs_lt.1 (lt_of_le_of_lt (Complex.abs_re_le_norm z) hn1)
  have h2 := abs_lt.1 (lt_of_le_of_lt (Complex.abs_im_le_norm z) hn1)
  refine mem_set_iff'.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  all_goals simp only [exhaustion]
  · linarith [h1.1]
  · linarith [h1.2]
  · linarith [h2.1]
  · linarith [h2.2]
  split_ifs with hi
  · exact hn2 hi
  · exact lt_of_lt_of_le (by norm_num) (le_max_of_le_left (abs_nonneg _))

lemma iUnion_exhaustion (P : Finset ι) :
    ⋃ n, prod (exhaustion P n) = puncturedSet (P : Set ι) := by
  ext x
  simp only [mem_iUnion, puncturedSet, Finset.mem_coe, mem_setOf_eq]
  refine ⟨fun ⟨n, hn⟩ i hi ↦ ne_zero_of_mem_exhaustion_set hi (mem_prod_iff.1 hn i), fun hx ↦ ?_⟩
  obtain ⟨n, hn⟩ := (Filter.eventually_all.2 fun i ↦ eventually_mem_exhaustion_set (hx i)).exists
  exact ⟨n, mem_prod_iff.2 hn⟩

omit [Finite ι] in
lemma closure_exhaustion_set_subset (P : Finset ι) (n : ℕ) (j : ι) :
    closure (exhaustion P n j).set ⊆ (exhaustion P (n + 1) j).set := by
  intro z hz
  have hr : ∀ m : ℕ, (0 : ℝ) < (1 / 4) ^ (m + 1) := fun m ↦ by positivity
  have hr' : ((1 : ℝ) / 4) ^ (n + 1) = 4 * (1 / 4) ^ (n + 1 + 1) := by ring
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := mem_closure_set hz
  simp only [exhaustion] at h1 h2 h3 h4 h5
  refine mem_set_iff'.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  all_goals simp only [exhaustion]
  · push_cast; linarith
  · push_cast; linarith
  · push_cast; linarith
  · push_cast; linarith
  · split_ifs at h5 ⊢
    · rw [hr'] at h5; linarith [hr (n + 1)]
    · linarith [(abs_nonneg z.re).trans (le_max_left |z.re| |z.im|)]

omit [Finite ι] in
/-- The members of the exhaustion are relatively compact in the next one. -/
lemma closure_exhaustion_subset (P : Finset ι) (n : ℕ) :
    closure (prod (exhaustion P n)) ⊆ prod (exhaustion P (n + 1)) ∧
      IsCompact (closure (prod (exhaustion P n))) := by
  refine ⟨?_, isCompact_closure_prod _⟩
  rw [closure_prod]
  exact pi_mono fun j _ ↦ closure_exhaustion_set_subset P n j

omit [Finite ι] in
/-- Runge approximation in one coordinate of the exhaustion of `(ℂ^×)^P × ℂ^{ι \ P}`: functions
holomorphic on the `j`-th factor of the `(n + 1)`-st member (with holomorphic parameters) are
uniform limits on the closure of the `j`-th factor of the `n`-th member of functions holomorphic
on `ℂ^×` (if `j ∈ P`), resp. on `ℂ` (with the same parameters). -/
theorem exists_approx_exhaustion_coord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (P : Finset ι) (n : ℕ) (j : ι) {Q : Set E}
    (hQ : IsOpen Q) {f : ℂ × E → ℂ}
    (hf : DifferentiableOn ℂ f ((exhaustion P (n + 1) j).set ×ˢ Q)) {L : Set E}
    (hL : IsCompact L) (hLQ : L ⊆ Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ × E → ℂ, DifferentiableOn ℂ g ((if j ∈ P then {0}ᶜ else univ) ×ˢ Q) ∧
      ∀ z ∈ closure (exhaustion P n j).set, ∀ w ∈ L, ‖f (z, w) - g (z, w)‖ ≤ ε := by
  have hr : ∀ m : ℕ, (0 : ℝ) < (1 / 4) ^ (m + 1) := fun m ↦ by positivity
  have hr' : ((1 : ℝ) / 4) ^ (n + 1) = 4 * (1 / 4) ^ (n + 1 + 1) := by ring
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = n + 3 / 2 := ⟨_, rfl⟩
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  by_cases hj : j ∈ P
  · rw [if_pos hj]
    set ρ : ℝ := 2 * (1 / 4) ^ (n + 1 + 1)
    have hρ : 0 < ρ := by positivity
    have hρ1 : ρ < 1 := by
      have : ((1 : ℝ) / 4) ^ (n + 1 + 1) ≤ 1 / 4 := pow_le_of_le_one (by norm_num)
        (by norm_num) (by omega) |>.trans (by norm_num)
      linarith
    have hR : 1 < R := by linarith
    refine exists_approx_punctured_of_frame (X₀ := -R) (X₁ := R) (Y₀ := -R) (Y₁ := R)
      hρ (by linarith) (by linarith) (by linarith) (by linarith) ?_ hQ hf
      ((exhaustion P n j).isCompact_closure_set) ?_ ?_ hL hLQ hε
    · rintro z ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩
      refine mem_set_iff'.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      all_goals simp only [exhaustion, hj, if_true]
      · push_cast; linarith
      · push_cast; linarith
      · push_cast; linarith
      · push_cast; linarith
      by_contra hle
      push Not at hle
      refine h5 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        linarith [abs_le.1 ((le_max_left _ _).trans hle), abs_le.1 ((le_max_right _ _).trans hle)]
    · intro z hz
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := mem_closure_set hz
      simp only [exhaustion, hj, if_true] at h1 h2 h3 h4 h5
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, fun h ↦ ?_⟩
      have : max |z.re| |z.im| ≤ ρ := max_le (abs_le.2 ⟨h.1.1, h.1.2⟩) (abs_le.2 ⟨h.2.1, h.2.2⟩)
      rw [hr'] at h5
      linarith [hr (n + 1)]
    · intro z hz
      obtain ⟨-, -, h5⟩ := mem_closure_set hz
      simp only [exhaustion, hj, if_true] at h5
      rw [hr'] at h5
      refine le_trans ?_ (max_le (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z))
      linarith [hr (n + 1)]
  · rw [if_neg hj]
    refine exists_approx_entire_of_rect (a := ⟨-R, -R⟩) (b := ⟨R, R⟩) (by simp; linarith)
      (by simp; linarith) ?_ hQ hf ((exhaustion P n j).isCompact_closure_set) ?_ hL hLQ hε
    · rintro z ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      refine mem_set_iff'.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      all_goals simp only [exhaustion, hj, if_false]
      · push_cast; linarith
      · push_cast; linarith
      · push_cast; linarith
      · push_cast; linarith
      · linarith [(abs_nonneg z.re).trans (le_max_left |z.re| |z.im|)]
    · intro z hz
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -⟩ := mem_closure_set hz
      simp only [exhaustion] at h1 h2 h3 h4
      exact ⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by simp; linarith, by simp; linarith⟩⟩

/-- Functions holomorphic on the `(n + 1)`-st member of the exhaustion are uniform limits on the
`n`-th member of functions holomorphic on `(ℂ^×)^P × ℂ^{ι \ P}`. -/
theorem exists_approx_exhaustion (P : Finset ι) (n : ℕ) {g : (ι → ℂ) → ℂ}
    (hg : DifferentiableOn ℂ g (prod (exhaustion P (n + 1)))) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : (ι → ℂ) → ℂ, DifferentiableOn ℂ G (puncturedSet (P : Set ι)) ∧
      ∀ x ∈ prod (exhaustion P n), ‖g x - G x‖ ≤ ε := by
  cases nonempty_fintype ι
  set Ω : ι → Set ℂ := fun j ↦ (exhaustion P (n + 1) j).set
  set T : ι → Set ℂ := fun j ↦ if j ∈ P then {0}ᶜ else univ
  set K : ι → Set ℂ := fun j ↦ closure (exhaustion P n j).set
  have hKΩ : ∀ j, K j ⊆ Ω j := fun j ↦ closure_exhaustion_set_subset P n j
  have hrunge : ∀ j (Q : Set ({k // k ≠ j} → ℂ)), IsOpen Q → ∀ f : ℂ × ({k // k ≠ j} → ℂ) → ℂ,
      DifferentiableOn ℂ f (Ω j ×ˢ Q) → ∀ L, IsCompact L → L ⊆ Q → ∀ ε' > 0,
      ∃ g : ℂ × ({k // k ≠ j} → ℂ) → ℂ, DifferentiableOn ℂ g (T j ×ˢ Q) ∧
        ∀ z ∈ K j, ∀ w ∈ L, ‖f (z, w) - g (z, w)‖ ≤ ε' :=
    fun j _ hQ _ hf _ hL hLQ _ hε' ↦ exists_approx_exhaustion_coord P n j hQ hf hL hLQ hε'
  obtain ⟨G, hG, hGe⟩ := exists_approx_pi Ω T K (fun j ↦ (exhaustion P (n + 1) j).isOpen_set)
    (fun j ↦ by simp only [T]; split_ifs; exacts [isOpen_compl_singleton, isOpen_univ])
    (fun j z hz ↦ by
      simp only [T]
      split_ifs with hj
      · exact ne_zero_of_mem_exhaustion_set hj hz
      · exact mem_univ _)
    (fun j ↦ (exhaustion P n j).isCompact_closure_set) hKΩ hrunge hg hε
  refine ⟨G, hG.mono fun x hx j _ ↦ ?_, fun x hx ↦ hGe x fun j _ ↦
    subset_closure (mem_prod_iff.1 hx j)⟩
  simp only [T]
  split_ifs with hj
  · exact hx j hj
  · exact mem_univ _

/-- **`lim¹ = 0` for the exhaustion of `(ℂ^×)^P × ℂ^{ι \ P}`**: for all `g n` holomorphic on the
`n`-th member `U n` of the exhaustion there are `f n` holomorphic on `U n` with
`g n = f n - f (n + 1)` on `U n`. -/
theorem exists_mittagLeffler_exhaustion (P : Finset ι) (g : ℕ → (ι → ℂ) → ℂ)
    (hg : ∀ n, DifferentiableOn ℂ (g n) (prod (exhaustion P n))) :
    ∃ f : ℕ → (ι → ℂ) → ℂ, (∀ n, DifferentiableOn ℂ (f n) (prod (exhaustion P n))) ∧
      ∀ n, ∀ x ∈ prod (exhaustion P n), g n x = f n x - f (n + 1) x := by
  cases nonempty_fintype ι
  refine exists_mittagLeffler (fun n ↦ isOpen_prod _) (monotone_exhaustion P)
    (fun n g hg ε hε ↦ ?_) g hg
  obtain ⟨G, hG, hGe⟩ := exists_approx_exhaustion P n hg hε
  exact ⟨G, by rwa [iUnion_exhaustion], hGe⟩

end Complex

end
