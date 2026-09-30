/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.TheoremB

/-!
# Theorem B for the structure sheaf on open boxes

Let `B = ∏ i, (a_i.re, b_i.re) × (a_i.im, b_i.im) ⊆ ℂ^ι` be a (bounded) open box. We show
`Hᵠ(B, 𝒪) = 0` for `q ≥ 1`.

The argument is that of `Complex.TheoremB.eq_zero_of_eq_puncturedSet`, for an arbitrary exhaustion
`U₀ ⋐ U₁ ⋐ ⋯` by products of holed rectangles: classes of positive degree are compactly zero on
products of holed rectangles (`Complex.TheoremB.compactlyZeroOnProd`), which gives the vanishing
on each `U n` and, in degrees `≥ 2`, `lim¹ = 0` of the cohomology groups; in degree one we need
`lim¹_n F(U n) = 0`. For `B` we take the exhaustion by the boxes shrunk by `1 / (n + 1)`; for `𝒪`,
`lim¹ = 0` follows from Mittag-Leffler, since functions holomorphic on a box are uniform limits of
entire functions on smaller boxes (rectangle Runge, one coordinate at a time).

## Main definitions

- `Complex.openBox a b`: the open box `∏ i, (a_i.re, b_i.re) × (a_i.im, b_i.im)`.
- `Complex.HoledRect.ofRect`: an open rectangle, as a holed rectangle without hole.
- `Complex.boxExhaustion a b n`: the box shrunk by `1 / (n + 1)` on each side.

## Main results

- `Complex.TheoremB.eq_zero_of_exhaustion`: **Theorem B for an exhaustion by products of holed
  rectangles**, for an abstract abelian sheaf with Cousin splittings and `lim¹ = 0`.
- `Complex.TheoremB.limOneVanishesOn_structureSheafAb`: `lim¹ 𝒪(U n) = 0` for an exhaustion with
  the Runge approximation property.
- `Complex.exists_approx_boxExhaustion`: functions holomorphic on the `(n + 1)`-st shrunk box are
  uniform limits of entire functions on the `n`-th one.
- `Complex.TheoremB.H'_structureSheafAb_eq_zero_of_openBox`,
  `Complex.TheoremB.subsingleton_H_restrictOpen_structureSheafAb_openBox`: **Theorem B** on
  open boxes.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Opposite Set Filter
open TopCat.Sheaf.MayerVietoris
open scoped Topology

namespace Complex

namespace HoledRect

/-- The open rectangle `(x₀, x₁) × (y₀, y₁)`, as a holed rectangle without hole. -/
def ofRect (x₀ x₁ y₀ y₁ : ℝ) : HoledRect := ⟨x₀, x₁, y₀, y₁, -1⟩

lemma set_ofRect (x₀ x₁ y₀ y₁ : ℝ) : (ofRect x₀ x₁ y₀ y₁).set = Ioo x₀ x₁ ×ℂ Ioo y₀ y₁ := by
  have h : hole (-1) = ∅ := by
    ext z
    simp only [mem_hole_iff, mem_empty_iff_false, iff_false, not_le]
    linarith [(abs_nonneg z.re).trans (le_max_left |z.re| |z.im|)]
  simp [set, ofRect, h]

end HoledRect

open HoledRect

variable {ι : Type*}

/-- The open box `∏ i, (a_i.re, b_i.re) × (a_i.im, b_i.im) ⊆ ℂ^ι`. -/
def openBox (a b : ι → ℂ) : Set (ι → ℂ) :=
  Set.univ.pi fun i ↦ Ioo (a i).re (b i).re ×ℂ Ioo (a i).im (b i).im

/-- The open box `openBox a b` shrunk by `1 / (n + 1)` on each side, as a product of holed
rectangles. -/
noncomputable def boxExhaustion (a b : ι → ℂ) (n : ℕ) : ι → HoledRect := fun i ↦
  ofRect ((a i).re + 1 / ((n : ℝ) + 1)) ((b i).re - 1 / ((n : ℝ) + 1))
    ((a i).im + 1 / ((n : ℝ) + 1)) ((b i).im - 1 / ((n : ℝ) + 1))

lemma mem_boxExhaustion_set_iff {a b : ι → ℂ} {n : ℕ} {i : ι} {z : ℂ} :
    z ∈ (boxExhaustion a b n i).set ↔
      ((a i).re + 1 / ((n : ℝ) + 1) < z.re ∧ z.re < (b i).re - 1 / ((n : ℝ) + 1)) ∧
      ((a i).im + 1 / ((n : ℝ) + 1) < z.im ∧ z.im < (b i).im - 1 / ((n : ℝ) + 1)) := by
  simp [boxExhaustion, set_ofRect, mem_reProdIm]

lemma mem_closure_boxExhaustion_set {a b : ι → ℂ} {n : ℕ} {i : ι} {z : ℂ}
    (hz : z ∈ closure (boxExhaustion a b n i).set) :
    ((a i).re + 1 / ((n : ℝ) + 1) ≤ z.re ∧ z.re ≤ (b i).re - 1 / ((n : ℝ) + 1)) ∧
      ((a i).im + 1 / ((n : ℝ) + 1) ≤ z.im ∧ z.im ≤ (b i).im - 1 / ((n : ℝ) + 1)) := by
  obtain ⟨h1, h2, -⟩ := mem_closure_set hz
  exact ⟨h1, h2⟩

lemma one_div_succ_lt_one_div (n : ℕ) :
    1 / (((n + 1 : ℕ) : ℝ) + 1) < 1 / ((n : ℝ) + 1) := by
  push_cast
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- The shrunk boxes are relatively compact in each other. -/
lemma closure_boxExhaustion_set_subset (a b : ι → ℂ) (n : ℕ) (i : ι) :
    closure (boxExhaustion a b n i).set ⊆ (boxExhaustion a b (n + 1) i).set := by
  intro z hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_closure_boxExhaustion_set hz
  have := one_div_succ_lt_one_div n
  exact mem_boxExhaustion_set_iff.2
    ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma closure_prod_boxExhaustion_subset (a b : ι → ℂ) (n : ℕ) :
    closure (prod (boxExhaustion a b n)) ⊆ prod (boxExhaustion a b (n + 1)) := by
  rw [closure_prod]
  exact pi_mono fun i _ ↦ closure_boxExhaustion_set_subset a b n i

/-- The shrunk rectangles lie in the rectangle. -/
lemma mem_rect_of_mem_boxExhaustion_set {a b : ι → ℂ} {n : ℕ} {i : ι} {z : ℂ}
    (hz : z ∈ (boxExhaustion a b n i).set) :
    z ∈ Ioo (a i).re (b i).re ×ℂ Ioo (a i).im (b i).im := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_boxExhaustion_set_iff.1 hz
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- A point of the rectangle eventually lies in the shrunk rectangles. -/
lemma eventually_mem_boxExhaustion_set {a b : ι → ℂ} {i : ι} {z : ℂ}
    (hz : z ∈ Ioo (a i).re (b i).re ×ℂ Ioo (a i).im (b i).im) :
    ∀ᶠ n : ℕ in atTop, z ∈ (boxExhaustion a b n i).set := by
  have hev : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < c := fun c hc ↦
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hc)
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  filter_upwards [hev _ (sub_pos.2 h1), hev _ (sub_pos.2 h2), hev _ (sub_pos.2 h3),
    hev _ (sub_pos.2 h4)] with n e1 e2 e3 e4
  exact mem_boxExhaustion_set_iff.2 ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma prod_boxExhaustion_subset_openBox (a b : ι → ℂ) (n : ℕ) :
    prod (boxExhaustion a b n) ⊆ openBox a b :=
  fun _ hx i _ ↦ mem_rect_of_mem_boxExhaustion_set (mem_prod_iff.1 hx i)

lemma iUnion_prod_boxExhaustion [Finite ι] (a b : ι → ℂ) :
    ⋃ n, prod (boxExhaustion a b n) = openBox a b := by
  refine subset_antisymm (iUnion_subset (prod_boxExhaustion_subset_openBox a b)) fun x hx ↦ ?_
  obtain ⟨n, hn⟩ := (Filter.eventually_all.2 fun i ↦
    eventually_mem_boxExhaustion_set (hx i (mem_univ i))).exists
  exact mem_iUnion.2 ⟨n, mem_prod_iff.2 hn⟩

/-- Runge approximation in one coordinate of the box exhaustion: functions holomorphic on the
`(n + 1)`-st shrunk rectangle (with holomorphic parameters) are uniform limits on the closure of
the `n`-th one of functions holomorphic on `ℂ` (with the same parameters). -/
theorem exists_approx_boxExhaustion_coord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (a b : ι → ℂ) (n : ℕ) (j : ι) {Q : Set E}
    (hQ : IsOpen Q) {f : ℂ × E → ℂ}
    (hf : DifferentiableOn ℂ f ((boxExhaustion a b (n + 1) j).set ×ˢ Q)) {L : Set E}
    (hL : IsCompact L) (hLQ : L ⊆ Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ × E → ℂ, DifferentiableOn ℂ g (univ ×ˢ Q) ∧
      ∀ z ∈ closure (boxExhaustion a b n j).set, ∀ w ∈ L, ‖f (z, w) - g (z, w)‖ ≤ ε := by
  rcases (closure (boxExhaustion a b n j).set).eq_empty_or_nonempty with hK0 | ⟨z₀, hz₀⟩
  · exact ⟨0, differentiableOn_const 0, fun z hz ↦ by simp [hK0] at hz⟩
  obtain ⟨m, hm1, hm2⟩ := exists_between (one_div_succ_lt_one_div n)
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_closure_boxExhaustion_set hz₀
  have hre : (a j).re + m < (b j).re - m := by linarith
  have him : (a j).im + m < (b j).im - m := by linarith
  refine exists_approx_entire_of_rect (a := ⟨(a j).re + m, (a j).im + m⟩)
    (b := ⟨(b j).re - m, (b j).im - m⟩) hre him ?_ hQ hf (isCompact_closure_set _) ?_ hL hLQ hε
  · rintro z ⟨⟨e1, e2⟩, e3, e4⟩
    exact mem_boxExhaustion_set_iff.2 ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · intro z hz
    obtain ⟨⟨e1, e2⟩, e3, e4⟩ := mem_closure_boxExhaustion_set hz
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Functions holomorphic on the `(n + 1)`-st shrunk box are uniform limits on the `n`-th shrunk
box of entire functions. -/
theorem exists_approx_boxExhaustion [Finite ι] (a b : ι → ℂ) (n : ℕ) {g : (ι → ℂ) → ℂ}
    (hg : DifferentiableOn ℂ g (prod (boxExhaustion a b (n + 1)))) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : (ι → ℂ) → ℂ, DifferentiableOn ℂ G univ ∧
      ∀ x ∈ prod (boxExhaustion a b n), ‖g x - G x‖ ≤ ε := by
  classical
  cases nonempty_fintype ι
  set Ω : ι → Set ℂ := fun j ↦ (boxExhaustion a b (n + 1) j).set
  set T : ι → Set ℂ := fun _ ↦ univ
  set K : ι → Set ℂ := fun j ↦ closure (boxExhaustion a b n j).set
  have hrunge : ∀ j (Q : Set ({k // k ≠ j} → ℂ)), IsOpen Q → ∀ f : ℂ × ({k // k ≠ j} → ℂ) → ℂ,
      DifferentiableOn ℂ f (Ω j ×ˢ Q) → ∀ L, IsCompact L → L ⊆ Q → ∀ ε' > 0,
      ∃ g : ℂ × ({k // k ≠ j} → ℂ) → ℂ, DifferentiableOn ℂ g (T j ×ˢ Q) ∧
        ∀ z ∈ K j, ∀ w ∈ L, ‖f (z, w) - g (z, w)‖ ≤ ε' :=
    fun j _ hQ _ hf _ hL hLQ _ hε' ↦ exists_approx_boxExhaustion_coord a b n j hQ hf hL hLQ hε'
  obtain ⟨G, hG, hGe⟩ := exists_approx_pi Ω T K (fun j ↦ (boxExhaustion a b (n + 1) j).isOpen_set)
    (fun _ ↦ isOpen_univ) (fun _ ↦ subset_univ _)
    (fun j ↦ (boxExhaustion a b n j).isCompact_closure_set)
    (fun j ↦ closure_boxExhaustion_set_subset a b n j) hrunge hg hε
  refine ⟨G, by simpa [T] using hG, fun x hx ↦ hGe x fun j _ ↦
    subset_closure (mem_prod_iff.1 hx j)⟩

namespace TheoremB

variable {ι : Type u}

set_option hygiene false in
/-- The space `ℂ^ι` as an object of `TopCat`. -/
local notation "𝕏" => TopCat.of (ι → ℂ)

variable {F : TopCat.AbSheaf 𝕏}

/-- **Theorem B for an exhaustion by products of holed rectangles.** Let `D = ⋃ n, U n` with
`U n = prod (s n)` and `closure (U n) ⊆ U (n + 1)`. If sections of `F` split along Cousin
splittings and `lim¹_n F(U n) = 0`, then `H'ᵠ(D, F) = 0` for `q ≥ 1`. -/
theorem eq_zero_of_exhaustion [Finite ι] (hC : CousinSplitting F) (s : ℕ → ι → HoledRect)
    {U : ℕ → Opens 𝕏} (hU : Monotone U) (hUs : ∀ n, (U n : Set (ι → ℂ)) = prod (s n))
    (hcl : ∀ n, closure (prod (s n)) ⊆ prod (s (n + 1)))
    (hML : TopCat.Sheaf.LimOneVanishesOn F.obj hU) {D : Opens 𝕏} (hD : ⨆ n, U n = D) {q : ℕ}
    (c : CategoryTheory.Sheaf.H'.{u} F (q + 1) D) : c = 0 := by
  subst hD
  have hcl' : ∀ n, IsCompact (closure (U n : Set (ι → ℂ))) ∧
      closure (U n : Set (ι → ℂ)) ⊆ (U (n + 1) : Set (ι → ℂ)) := fun n ↦ by
    rw [hUs, hUs]
    exact ⟨isCompact_closure_prod _, hcl n⟩
  have hc : ∀ n, TopCat.Sheaf.H'res F (q + 1) (le_iSup U n) c = 0 := fun n ↦ by
    have h := (compactlyZeroOnProd hC q (s (n + 1)) (U (n + 1)) (hUs _)
      (res F (q + 1) (le_iSup U (n + 1)) c)).2 (U n) (hU n.le_succ) (hcl' n).1 (hcl' n).2
    rwa [res_comp] at h
  rcases q with _ | q
  · exact TopCat.Sheaf.H'_one_eq_zero_of_monotone hU F hML c hc
  · refine TopCat.Sheaf.H'_eq_zero_of_monotone hU F (q + 1)
      (TopCat.Sheaf.LimOneVanishes.of_eq_zero fun n ↦ ?_) c hc
    ext x
    exact (compactlyZeroOnProd hC q (s (n + 1)) (U (n + 1)) (hUs _) x).2 (U n)
      (hU n.le_succ) (hcl' n).1 (hcl' n).2

variable [Fintype ι]

/-- **`lim¹ 𝒪 = 0`** along an increasing sequence of opens `U n` of `ℂ^ι` such that functions
holomorphic on `U (n + 1)` are uniform limits on `U n` of functions holomorphic on `⋃ U n`. -/
theorem limOneVanishesOn_structureSheafAb {U : ℕ → Opens 𝕏} (hU : Monotone U)
    (happrox : ∀ k (g : (ι → ℂ) → ℂ), DifferentiableOn ℂ g (U (k + 1) : Set (ι → ℂ)) →
      ∀ ε > 0, ∃ h : (ι → ℂ) → ℂ, DifferentiableOn ℂ h (⋃ j, (U j : Set (ι → ℂ))) ∧
        ∀ z ∈ (U k : Set (ι → ℂ)), ‖g z - h z‖ ≤ ε) :
    TopCat.Sheaf.LimOneVanishesOn (complexSpaceStructureSheafAb ι).obj hU := by
  intro s
  obtain ⟨f, hf, hfs⟩ := exists_mittagLeffler (fun n ↦ (U n).isOpen) (fun _ _ h ↦ hU h) happrox
    (fun n ↦ (s n : OkaRing (U n)).toGlobalFun _)
    (fun n ↦ OkaRing.differentiableOn_toGlobalFun _)
  refine ⟨fun n ↦ (OkaRing.ofDifferentiableOn (f n) (hf n) : OkaRing (U n)), fun n ↦ ?_⟩
  change (s n : OkaRing (U n)) = OkaRing.ofDifferentiableOn (f n) (hf n) -
    OkaRing.restrict (hU n.le_succ) (OkaRing.ofDifferentiableOn (f (n + 1)) (hf (n + 1)))
  refine OkaRing.ext (funext fun x ↦ ?_)
  have hx := hfs n x.1 x.2
  rw [OkaRing.toGlobalFun_apply _ x.2] at hx
  exact hx

/-- The shrunk boxes `boxExhaustion a b n`, as opens. -/
noncomputable def boxExhaustionOpens (a b : ι → ℂ) (n : ℕ) : Opens 𝕏 :=
  ⟨prod (boxExhaustion a b n), isOpen_prod _⟩

lemma monotone_boxExhaustionOpens (a b : ι → ℂ) : Monotone (boxExhaustionOpens a b) :=
  monotone_nat_of_le_succ fun n ↦
    subset_closure.trans (closure_prod_boxExhaustion_subset a b n)

/-- **Theorem B on open boxes**, for Mathlib's cohomology of opens: every class of positive degree
of the structure sheaf on an open box `B = ∏ i, (a_i.re, b_i.re) × (a_i.im, b_i.im)` vanishes. -/
theorem H'_structureSheafAb_eq_zero_of_openBox (a b : ι → ℂ) {D : Opens 𝕏}
    (hD : (D : Set (ι → ℂ)) = openBox a b) {q : ℕ}
    (c : CategoryTheory.Sheaf.H'.{u} (complexSpaceStructureSheafAb ι) (q + 1) D) : c = 0 := by
  have hU := monotone_boxExhaustionOpens (ι := ι) a b
  have hUnion : ⋃ j, (boxExhaustionOpens a b j : Set (ι → ℂ)) = openBox a b :=
    iUnion_prod_boxExhaustion a b
  refine eq_zero_of_exhaustion cousinSplitting_structureSheafAb (boxExhaustion a b) hU
    (fun _ ↦ rfl) (closure_prod_boxExhaustion_subset a b)
    (limOneVanishesOn_structureSheafAb hU fun k g hg ε hε ↦ ?_)
    (Opens.ext ((Opens.coe_iSup _).trans (hUnion.trans hD.symm))) c
  obtain ⟨G, hG, hGe⟩ := exists_approx_boxExhaustion a b k hg hε
  exact ⟨G, hG.mono (subset_univ _), hGe⟩

/-- **Theorem B on open boxes**: `Hᵠ(B, 𝒪|_B) = 0` for `q ≥ 1` and every open box
`B = ∏ i, (a_i.re, b_i.re) × (a_i.im, b_i.im) ⊆ ℂ^ι`. -/
theorem subsingleton_H_restrictOpen_structureSheafAb_openBox (a b : ι → ℂ) {D : Opens 𝕏}
    (hD : (D : Set (ι → ℂ)) = openBox a b) {q : ℕ} (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H
      ((TopCat.Sheaf.restrictOpen D).obj (complexSpaceStructureSheafAb ι)) q) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hq
  rw [zero_add]
  have : Subsingleton (CategoryTheory.Sheaf.H'.{u} (complexSpaceStructureSheafAb ι) (q + 1) D) :=
    subsingleton_of_forall_eq 0 (H'_structureSheafAb_eq_zero_of_openBox a b hD)
  exact (TopCat.Sheaf.H'AddEquiv D _ (q + 1)).symm.toEquiv.subsingleton

end TheoremB

end Complex

end
