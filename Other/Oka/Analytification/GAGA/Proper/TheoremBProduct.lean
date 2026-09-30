/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.TheoremBBox

/-!
# Theorem B for the structure sheaf on products of boxes, punctured planes and planes

Let `ι` be finite, split into box coordinates `S`, punctured coordinates `P` (disjoint from
`S`) and full coordinates. The *mixed domain* `Complex.mixedSet S P a b ⊆ ℂ^ι` is the product
of the open rectangles `(a_i.re, b_i.re) × (a_i.im, b_i.im)` for `i ∈ S`, of `ℂ^×` for `i ∈ P`
and of `ℂ` for the other coordinates. We show `Hᵠ(D, 𝒪) = 0` for `q ≥ 1`, by
`Complex.TheoremB.eq_zero_of_exhaustion`: `D` is exhausted by products of holed rectangles
(shrunk boxes in `S`, the exhaustion of `Complex.exhaustion` elsewhere), and one-variable Runge
approximation in each coordinate gives `lim¹ 𝒪 = 0`.

## Main definitions

- `Complex.mixedSet S P a b`: the domain `∏_{i ∈ S} (box) × (ℂ^×)^P × ℂ^{ι \ (S ∪ P)}`.
- `Complex.mixedExhaustion S P a b n`: its exhaustion by products of holed rectangles.

## Main results

- `Complex.iUnion_prod_mixedExhaustion`, `Complex.exists_approx_mixedExhaustion`.
- `Complex.TheoremB.H'_structureSheafAb_eq_zero_of_mixedSet`,
  `Complex.TheoremB.subsingleton_H_restrictOpen_structureSheafAb_mixedSet`: **Theorem B** on
  mixed domains.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite Set Filter
open scoped Topology

namespace Complex

open HoledRect

variable {ι : Type*} [DecidableEq ι]

/-! ### Mixed domains -/

omit [DecidableEq ι] in
/-- The mixed domain: the product of the open rectangles `(a_i.re, b_i.re) × (a_i.im, b_i.im)`
for `i ∈ S`, of `ℂ^×` for `i ∈ P` and of `ℂ` for the other coordinates. -/
def mixedSet (S P : Set ι) (a b : ι → ℂ) : Set (ι → ℂ) :=
  {x | ∀ i, (i ∈ S → x i ∈ Ioo (a i).re (b i).re ×ℂ Ioo (a i).im (b i).im) ∧ (i ∈ P → x i ≠ 0)}

omit [DecidableEq ι] in
lemma mixedSet_empty_left (P : Set ι) (a b : ι → ℂ) : mixedSet ∅ P a b = puncturedSet P := by
  ext x
  simp [mixedSet, puncturedSet]

omit [DecidableEq ι] in
lemma mixedSet_univ_empty (a b : ι → ℂ) : mixedSet univ ∅ a b = openBox a b := by
  ext x
  simp [mixedSet, openBox]

/-- The exhaustion of the mixed domain: shrunk rectangles in the coordinates in `S`, and the
members of `Complex.exhaustion P` in the others. -/
noncomputable def mixedExhaustion (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) : ι → HoledRect :=
  fun i ↦ if i ∈ S then boxExhaustion a b n i else exhaustion P n i

lemma closure_mixedExhaustion_set_subset (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) (i : ι) :
    closure (mixedExhaustion S P a b n i).set ⊆ (mixedExhaustion S P a b (n + 1) i).set := by
  simp only [mixedExhaustion]
  split_ifs
  · exact closure_boxExhaustion_set_subset a b n i
  · exact closure_exhaustion_set_subset P n i

lemma closure_prod_mixedExhaustion_subset (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) :
    closure (prod (mixedExhaustion S P a b n)) ⊆ prod (mixedExhaustion S P a b (n + 1)) := by
  rw [closure_prod]
  exact pi_mono fun i _ ↦ closure_mixedExhaustion_set_subset S P a b n i

lemma prod_mixedExhaustion_subset (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) :
    prod (mixedExhaustion S P a b n) ⊆ prod (mixedExhaustion S P a b (n + 1)) :=
  subset_closure.trans (closure_prod_mixedExhaustion_subset S P a b n)

lemma prod_mixedExhaustion_subset_mixedSet {S P : Finset ι} (hSP : Disjoint S P) (a b : ι → ℂ)
    (n : ℕ) : prod (mixedExhaustion S P a b n) ⊆ mixedSet (S : Set ι) (P : Set ι) a b := by
  intro x hx i
  have hxi := mem_prod_iff.1 hx i
  refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
  · simp only [mixedExhaustion, Finset.mem_coe.1 hi, if_true] at hxi
    exact mem_rect_of_mem_boxExhaustion_set hxi
  · have hiS : i ∉ S := Finset.disjoint_right.1 hSP hi
    simp only [mixedExhaustion, hiS, if_false] at hxi
    exact ne_zero_of_mem_exhaustion_set hi hxi

lemma iUnion_prod_mixedExhaustion [Finite ι] {S P : Finset ι} (hSP : Disjoint S P)
    (a b : ι → ℂ) :
    ⋃ n, prod (mixedExhaustion S P a b n) = mixedSet (S : Set ι) (P : Set ι) a b := by
  refine subset_antisymm (iUnion_subset (prod_mixedExhaustion_subset_mixedSet hSP a b))
    fun x hx ↦ ?_
  have h : ∀ᶠ n : ℕ in atTop, ∀ i, x i ∈ (mixedExhaustion S P a b n i).set := by
    rw [Filter.eventually_all]
    intro i
    simp only [mixedExhaustion]
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      exact eventually_mem_boxExhaustion_set ((hx i).1 hi)
    · simp only [hi, if_false]
      exact eventually_mem_exhaustion_set (hx i).2
  obtain ⟨n, hn⟩ := h.exists
  exact mem_iUnion.2 ⟨n, mem_prod_iff.2 hn⟩

/-- The target of the coordinatewise approximation on the mixed domain: `ℂ^×` for `j ∈ P \ S`,
`ℂ` otherwise. -/
def mixedTarget (S P : Finset ι) (j : ι) : Set ℂ :=
  if j ∈ S then univ else if j ∈ P then {0}ᶜ else univ

lemma isOpen_mixedTarget (S P : Finset ι) (j : ι) : IsOpen (mixedTarget S P j) := by
  unfold mixedTarget
  split_ifs
  exacts [isOpen_univ, isOpen_compl_singleton, isOpen_univ]

lemma mixedExhaustion_set_subset_mixedTarget (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) (j : ι) :
    (mixedExhaustion S P a b n j).set ⊆ mixedTarget S P j := by
  intro z hz
  unfold mixedTarget
  by_cases hS : j ∈ S
  · rw [if_pos hS]; exact mem_univ _
  · rw [if_neg hS]
    by_cases hP : j ∈ P
    · rw [if_pos hP]
      have e : mixedExhaustion S P a b n j = exhaustion P n j := if_neg hS
      rw [e] at hz
      exact ne_zero_of_mem_exhaustion_set hP hz
    · rw [if_neg hP]; exact mem_univ _

lemma mixedSet_subset_pi_mixedTarget (S P : Finset ι) (a b : ι → ℂ) :
    mixedSet (S : Set ι) (P : Set ι) a b ⊆ univ.pi (mixedTarget S P) := by
  intro x hx j _
  unfold mixedTarget
  by_cases hS : j ∈ S
  · rw [if_pos hS]; exact mem_univ _
  · rw [if_neg hS]
    by_cases hP : j ∈ P
    · rw [if_pos hP]; exact (hx j).2 hP
    · rw [if_neg hP]; exact mem_univ _

/-- Runge approximation with holomorphic parameters in one coordinate of the exhaustion of the
mixed domain. -/
theorem exists_approx_mixedExhaustion_coord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) (j : ι) {Q : Set E}
    (hQ : IsOpen Q) {f : ℂ × E → ℂ}
    (hf : DifferentiableOn ℂ f ((mixedExhaustion S P a b (n + 1) j).set ×ˢ Q)) {L : Set E}
    (hL : IsCompact L) (hLQ : L ⊆ Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ × E → ℂ, DifferentiableOn ℂ g (mixedTarget S P j ×ˢ Q) ∧
      ∀ z ∈ closure (mixedExhaustion S P a b n j).set, ∀ w ∈ L,
        ‖f (z, w) - g (z, w)‖ ≤ ε := by
  by_cases hj : j ∈ S
  · have e1 : mixedExhaustion S P a b (n + 1) j = boxExhaustion a b (n + 1) j := if_pos hj
    have e2 : mixedExhaustion S P a b n j = boxExhaustion a b n j := if_pos hj
    have e3 : mixedTarget S P j = univ := if_pos hj
    rw [e1] at hf
    rw [e2, e3]
    exact exists_approx_boxExhaustion_coord a b n j hQ hf hL hLQ hε
  · have e1 : mixedExhaustion S P a b (n + 1) j = exhaustion P (n + 1) j := if_neg hj
    have e2 : mixedExhaustion S P a b n j = exhaustion P n j := if_neg hj
    have e3 : mixedTarget S P j = if j ∈ P then {0}ᶜ else univ := if_neg hj
    rw [e1] at hf
    rw [e2, e3]
    exact exists_approx_exhaustion_coord P n j hQ hf hL hLQ hε

/-- Functions holomorphic on the `(n + 1)`-st member of the exhaustion of the mixed domain are
uniform limits on the `n`-th member of functions holomorphic on the mixed domain. -/
theorem exists_approx_mixedExhaustion [Finite ι] (S P : Finset ι) (a b : ι → ℂ) (n : ℕ)
    {g : (ι → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (prod (mixedExhaustion S P a b (n + 1))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : (ι → ℂ) → ℂ, DifferentiableOn ℂ G (mixedSet (S : Set ι) (P : Set ι) a b) ∧
      ∀ x ∈ prod (mixedExhaustion S P a b n), ‖g x - G x‖ ≤ ε := by
  cases nonempty_fintype ι
  have hrunge : ∀ j (Q : Set ({k // k ≠ j} → ℂ)), IsOpen Q → ∀ f : ℂ × ({k // k ≠ j} → ℂ) → ℂ,
      DifferentiableOn ℂ f ((mixedExhaustion S P a b (n + 1) j).set ×ˢ Q) → ∀ L, IsCompact L →
      L ⊆ Q → ∀ ε' > 0, ∃ g : ℂ × ({k // k ≠ j} → ℂ) → ℂ,
        DifferentiableOn ℂ g (mixedTarget S P j ×ˢ Q) ∧
        ∀ z ∈ closure (mixedExhaustion S P a b n j).set, ∀ w ∈ L,
          ‖f (z, w) - g (z, w)‖ ≤ ε' :=
    fun j _ hQ _ hf _ hL hLQ _ hε' ↦
      exists_approx_mixedExhaustion_coord S P a b n j hQ hf hL hLQ hε'
  obtain ⟨G, hG, hGe⟩ := exists_approx_pi (fun j ↦ (mixedExhaustion S P a b (n + 1) j).set)
    (mixedTarget S P) (fun j ↦ closure (mixedExhaustion S P a b n j).set)
    (fun j ↦ (mixedExhaustion S P a b (n + 1) j).isOpen_set) (isOpen_mixedTarget S P)
    (mixedExhaustion_set_subset_mixedTarget S P a b (n + 1))
    (fun j ↦ (mixedExhaustion S P a b n j).isCompact_closure_set)
    (fun j ↦ closure_mixedExhaustion_set_subset S P a b n j) hrunge hg hε
  exact ⟨G, hG.mono (mixedSet_subset_pi_mixedTarget S P a b), fun x hx ↦ hGe x fun j _ ↦
    subset_closure (mem_prod_iff.1 hx j)⟩

namespace TheoremB

variable {ι : Type u} [Fintype ι]

set_option hygiene false in
/-- The space `ℂ^ι` as an object of `TopCat`. -/
local notation "𝕏" => TopCat.of (ι → ℂ)

/-- The members of the exhaustion of the mixed domain, as opens. -/
noncomputable def mixedExhaustionOpens [DecidableEq ι] (S P : Finset ι) (a b : ι → ℂ) (n : ℕ) :
    Opens 𝕏 :=
  ⟨prod (mixedExhaustion S P a b n), isOpen_prod _⟩

/-- **Theorem B on mixed domains**, for Mathlib's cohomology of opens: every class of positive
degree of the structure sheaf on `D = ∏_{i ∈ S} (box) × (ℂ^×)^P × ℂ^{ι \ (S ∪ P)}` vanishes. -/
theorem H'_structureSheafAb_eq_zero_of_mixedSet {S P : Set ι} (hSP : Disjoint S P)
    (a b : ι → ℂ) {D : Opens 𝕏} (hD : (D : Set (ι → ℂ)) = mixedSet S P a b) {q : ℕ}
    (c : CategoryTheory.Sheaf.H'.{u} (complexSpaceStructureSheafAb ι) (q + 1) D) : c = 0 := by
  classical
  set S' := (Set.toFinite S).toFinset
  set P' := (Set.toFinite P).toFinset
  have hS' : (S' : Set ι) = S := Set.Finite.coe_toFinset _
  have hP' : (P' : Set ι) = P := Set.Finite.coe_toFinset _
  have hSP' : Disjoint S' P' := by
    rw [← Finset.disjoint_coe, hS', hP']
    exact hSP
  have hU : Monotone (mixedExhaustionOpens S' P' a b) :=
    monotone_nat_of_le_succ fun n ↦ prod_mixedExhaustion_subset S' P' a b n
  have hUnion : ⋃ j, (mixedExhaustionOpens S' P' a b j : Set (ι → ℂ)) = mixedSet S P a b := by
    rw [← hS', ← hP']
    exact iUnion_prod_mixedExhaustion hSP' a b
  refine eq_zero_of_exhaustion cousinSplitting_structureSheafAb (mixedExhaustion S' P' a b) hU
    (fun _ ↦ rfl) (closure_prod_mixedExhaustion_subset S' P' a b)
    (limOneVanishesOn_structureSheafAb hU fun k g hg ε hε ↦ ?_)
    (Opens.ext ((Opens.coe_iSup _).trans (hUnion.trans hD.symm))) c
  obtain ⟨G, hG, hGe⟩ := exists_approx_mixedExhaustion S' P' a b k hg hε
  refine ⟨G, ?_, hGe⟩
  rw [hUnion, ← hS', ← hP']
  exact hG

/-- **Theorem B on mixed domains**: `Hᵠ(D, 𝒪|_D) = 0` for `q ≥ 1` and
`D = ∏_{i ∈ S} (box) × (ℂ^×)^P × ℂ^{ι \ (S ∪ P)}`, `S ∩ P = ∅`. -/
theorem subsingleton_H_restrictOpen_structureSheafAb_mixedSet {S P : Set ι} (hSP : Disjoint S P)
    (a b : ι → ℂ) {D : Opens 𝕏} (hD : (D : Set (ι → ℂ)) = mixedSet S P a b) {q : ℕ}
    (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H
      ((TopCat.Sheaf.restrictOpen D).obj (complexSpaceStructureSheafAb ι)) q) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hq
  rw [zero_add]
  have : Subsingleton (CategoryTheory.Sheaf.H'.{u} (complexSpaceStructureSheafAb ι) (q + 1) D) :=
    subsingleton_of_forall_eq 0 (H'_structureSheafAb_eq_zero_of_mixedSet hSP a b hD)
  exact (TopCat.Sheaf.H'AddEquiv D _ (q + 1)).symm.toEquiv.subsingleton

end TheoremB

end Complex

end
