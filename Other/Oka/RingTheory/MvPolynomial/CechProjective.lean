/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicTopology.SimplexCochain
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Algebra.Exact.Basic

/-!
# The Čech complex of `O(d)` on projective space: Laurent coefficients

Let `ι` be a finite type (`ι = Fin (n + 1)` for `ℙⁿ`) and `R` a commutative ring. On the
intersection `⋂_{j ∈ I} Uⱼ` of standard charts, the sections of `O(d)` are the homogeneous
degree-`d` elements of `R[Xⱼ][1 / ∏_{j ∈ I} Xⱼ]`, i.e. finite sums `∑ₐ cₐ Xᵃ` over exponents
`a : ι →₀ ℤ` of degree `d` whose *negative support* `negSupp a = {j | aⱼ < 0}` is contained in
`I`. We record such an element by its coefficients, an element of `(ι →₀ ℤ) →₀ R` in
`laurentPart I d`. The Čech complex for the standard cover then embeds into ordered cochains
with values in `(ι →₀ ℤ) →₀ R`, as the admissible cochains (`SimplexCochain.Grading`) for the
grading `laurentGrading` by negative supports, with values of degree `d`.

This file computes its cohomology (`exists_eq_d_of_laurentPart`, `exists_eq_aug_of_laurentPart`)
and transfers the result to any complex which embeds into the cochains with image the cochains
with values in `laurentPart` (`exact_of_laurentPart`, `aug_exact_of_laurentPart`):

- `H⁰ = S_d`, the polynomials of degree `d`, if `n ≠ 0` or `d ≥ 0`;
- `H^q = 0` for `0 < q < n`, for all `d`;
- `H^n = 0` if `d > -n - 1`, and `H^q = 0` for `q > n`.

Here `card ι = n + 1`; the hypothesis in the transfer theorems is phrased uniformly as
`q + 1 ≠ card ι ∨ -card ι < d`.

## Main definitions

- `MvPolynomial.negSupp a`: the negative support of an exponent `a : ι →₀ ℤ`.
- `MvPolynomial.laurentPart I d`: the coefficient families of degree `d` with negative supports
  in `I`.
- `MvPolynomial.laurentGrading`: the grading of `(ι →₀ ℤ) →₀ R` by negative supports.
-/

@[expose] public section

open SimplexCochain

namespace MvPolynomial

variable {ι : Type*} {R : Type*} [CommRing R]

/-- The negative support `{j | aⱼ < 0}` of an exponent `a : ι →₀ ℤ`. -/
def negSupp (a : ι →₀ ℤ) : Finset ι := a.support.filter fun j ↦ a j < 0

@[simp]
lemma mem_negSupp {a : ι →₀ ℤ} {j : ι} : j ∈ negSupp a ↔ a j < 0 := by
  simp only [negSupp, Finset.mem_filter, Finsupp.mem_support_iff, and_iff_right_iff_imp]
  omega

variable (R) in
/-- The Laurent coefficient families `∑ₐ cₐ Xᵃ` of degree `k` with negative supports in `I`: the
sections of `O(d)` over `⋂_{j ∈ I} Uⱼ`. -/
def laurentPart (I : Finset ι) (k : ℤ) : Submodule R ((ι →₀ ℤ) →₀ R) :=
  Finsupp.supported R R {a | negSupp a ⊆ I ∧ a.degree = k}

lemma mem_laurentPart {I : Finset ι} {k : ℤ} {f : (ι →₀ ℤ) →₀ R} :
    f ∈ laurentPart R I k ↔ ∀ a, f a ≠ 0 → negSupp a ⊆ I ∧ a.degree = k := by
  rw [laurentPart, Finsupp.mem_supported]
  exact ⟨fun h a ha ↦ h (Finsupp.mem_support_iff.mpr ha),
    fun h a ha ↦ h a (Finsupp.mem_support_iff.mp ha)⟩

variable (R) in
/-- The coefficient families of degree `k`. -/
noncomputable def degreePart (k : ℤ) : AddSubgroup ((ι →₀ ℤ) →₀ R) :=
  (Finsupp.supported R R {a : ι →₀ ℤ | a.degree = k}).toAddSubgroup

lemma mem_degreePart {k : ℤ} {f : (ι →₀ ℤ) →₀ R} :
    f ∈ degreePart R k ↔ ∀ a, f a ≠ 0 → a.degree = k := by
  rw [degreePart, Submodule.mem_toAddSubgroup, Finsupp.mem_supported]
  exact ⟨fun h a ha ↦ h (Finsupp.mem_support_iff.mpr ha),
    fun h a ha ↦ h a (Finsupp.mem_support_iff.mp ha)⟩

section Grading

variable [DecidableEq ι]

variable (R) in
/-- The projection of Laurent coefficient families onto the monomials `Xᵃ` with
`negSupp a = N`. -/
noncomputable def negProj (N : Finset ι) : ((ι →₀ ℤ) →₀ R) →+ ((ι →₀ ℤ) →₀ R) :=
  Finsupp.filterAddHom fun a ↦ negSupp a = N

@[simp]
lemma negProj_apply (N : Finset ι) (f : (ι →₀ ℤ) →₀ R) (a : ι →₀ ℤ) :
    negProj R N f a = if negSupp a = N then f a else 0 :=
  rfl

variable [Fintype ι]

variable (ι R) in
/-- The grading of Laurent coefficient families by negative supports: `proj N` keeps the
monomials `Xᵃ` with `negSupp a = N`. -/
noncomputable def laurentGrading : Grading ι ((ι →₀ ℤ) →₀ R) where
  proj := negProj R
  sum_proj m := by
    ext a
    simp [Finsupp.finsetSum_apply]
  proj_proj N N' m := by
    ext a
    by_cases h : N = N' <;> by_cases ha : negSupp a = N <;> simp_all

@[simp]
lemma laurentGrading_proj_apply (N : Finset ι) (f : (ι →₀ ℤ) →₀ R) (a : ι →₀ ℤ) :
    (laurentGrading ι R).proj N f a = if negSupp a = N then f a else 0 :=
  rfl

lemma laurentGrading_proj_mem_degreePart {k : ℤ} (N : Finset ι) (f : (ι →₀ ℤ) →₀ R)
    (hf : f ∈ degreePart R k) : (laurentGrading ι R).proj N f ∈ degreePart R k := by
  rw [mem_degreePart] at hf ⊢
  intro a ha
  simp only [laurentGrading_proj_apply] at ha
  split_ifs at ha
  · exact hf a ha
  · exact absurd rfl ha

lemma isAdmissible_iff {p : ℕ} {x : Cochain ι ((ι →₀ ℤ) →₀ R) p} :
    (laurentGrading ι R).IsAdmissible x ↔ ∀ i a, x i a ≠ 0 → negSupp a ⊆ im i := by
  refine ⟨fun hx i a ha ↦ by_contra fun h ↦ ha ?_, fun hx i N hN ↦ ?_⟩
  · simpa using DFunLike.congr_fun (hx i (negSupp a) h) a
  · ext a
    simp only [laurentGrading_proj_apply, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs with h
    · subst h
      by_contra ha
      exact hN (hx i a ha)
    · rfl

lemma forall_mem_laurentPart_iff {p : ℕ} {k : ℤ} {x : Cochain ι ((ι →₀ ℤ) →₀ R) p} :
    (∀ i, x i ∈ laurentPart R (im i) k) ↔
      (laurentGrading ι R).IsAdmissible x ∧ ∀ i, x i ∈ degreePart R k := by
  simp only [isAdmissible_iff, mem_laurentPart, mem_degreePart]
  exact ⟨fun h ↦ ⟨fun i a ha ↦ (h i a ha).1, fun i a ha ↦ (h i a ha).2⟩,
    fun h i a ha ↦ ⟨h.1 i a ha, h.2 i a ha⟩⟩

omit [DecidableEq ι] in
lemma degree_le_of_negSupp_eq_univ {a : ι →₀ ℤ} (ha : negSupp a = Finset.univ) :
    a.degree ≤ -Fintype.card ι := by
  rw [Finsupp.degree_eq_sum]
  have h (j : ι) (_ : j ∈ Finset.univ) : a j ≤ -1 := by
    have : j ∈ negSupp a := ha ▸ Finset.mem_univ j
    rw [mem_negSupp] at this
    omega
  calc ∑ j, a j ≤ ∑ _j : ι, (-1 : ℤ) := Finset.sum_le_sum h
    _ = -Fintype.card ι := by simp

lemma proj_univ_eq_zero_of_mem_degreePart {k : ℤ} (hd : -Fintype.card ι < k)
    {f : (ι →₀ ℤ) →₀ R} (hf : f ∈ degreePart R k) :
    (laurentGrading ι R).proj Finset.univ f = 0 := by
  ext a
  simp only [laurentGrading_proj_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with ha
  · by_contra h
    have := (mem_degreePart.mp hf) a h
    have := degree_le_of_negSupp_eq_univ ha
    omega
  · rfl

/-! ### The cohomology of the Laurent model -/

/-- **Vanishing of the Čech cohomology of `O(d)` in positive degrees** (Laurent model): a
cocycle of degree `p + 1` with values in `laurentPart (im i) k` is a coboundary of such a cochain,
if `p + 2 ≠ card ι` (degree `≠ n`) or `k > -card ι`. -/
theorem exists_eq_d_of_laurentPart {k : ℤ} {p : ℕ} (x : Cochain ι ((ι →₀ ℤ) →₀ R) (p + 1))
    (hx : ∀ i, x i ∈ laurentPart R (im i) k) (hdx : d (p + 1) x = 0)
    (hp : p + 2 ≠ Fintype.card ι ∨ -Fintype.card ι < k) :
    ∃ y : Cochain ι ((ι →₀ ℤ) →₀ R) p, (∀ i, y i ∈ laurentPart R (im i) k) ∧ d p y = x := by
  obtain ⟨hadm, hdeg⟩ := forall_mem_laurentPart_iff.mp hx
  obtain ⟨y, hy, hyS, hdy⟩ := (laurentGrading ι R).exists_eq_d (degreePart R k)
    (fun N m hm ↦ laurentGrading_proj_mem_degreePart N m hm) x hadm hdeg hdx (by
      rcases hp with hp | hp
      · rcases lt_or_gt_of_ne hp with hp | hp
        · exact Or.inr ((laurentGrading ι R).proj_univ_eq_zero hadm (by omega))
        · exact Or.inl (by omega)
      · exact Or.inr fun i ↦ proj_univ_eq_zero_of_mem_degreePart hp (hdeg i))
  exact ⟨y, forall_mem_laurentPart_iff.mpr ⟨hy, hyS⟩, hdy⟩

/-- **The Čech `H⁰` of `O(d)`** (Laurent model): a `0`-cocycle with values in
`laurentPart (im i) k` is constant, with value a polynomial of degree `k` (an element of
`laurentPart ∅ k`), if `card ι ≠ 1` or `k > -card ι`. -/
theorem exists_eq_aug_of_laurentPart [Nonempty ι] {k : ℤ} (x : Cochain ι ((ι →₀ ℤ) →₀ R) 0)
    (hx : ∀ i, x i ∈ laurentPart R (im i) k) (hdx : d 0 x = 0)
    (hp : 1 ≠ Fintype.card ι ∨ -Fintype.card ι < k) :
    ∃ v ∈ laurentPart R ∅ k, x = aug v := by
  obtain ⟨hadm, hdeg⟩ := forall_mem_laurentPart_iff.mp hx
  obtain ⟨v, hv, rfl⟩ := (laurentGrading ι R).exists_eq_aug x hadm hdx (by
    rcases hp with hp | hp
    · have : 0 < Fintype.card ι := Fintype.card_pos
      exact (laurentGrading ι R).proj_univ_eq_zero hadm (by omega)
    · exact fun i ↦ proj_univ_eq_zero_of_mem_degreePart hp (hdeg i))
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  refine ⟨v, mem_laurentPart.mpr fun a ha ↦ ⟨?_, mem_degreePart.mp (hdeg fun _ ↦ j₀) a ha⟩, rfl⟩
  rw [← hv, laurentGrading_proj_apply] at ha
  split_ifs at ha with h
  · exact h.le
  · exact absurd rfl ha

/-! ### Transfer to complexes embedded in the Laurent model -/

section Transfer

variable {k : ℤ} {V : ℕ → Type*} [∀ p, AddCommGroup (V p)] (D : ∀ p, V p →+ V (p + 1))
  (Φ : ∀ p, V p →+ Cochain ι ((ι →₀ ℤ) →₀ R) p) (hΦ : ∀ p, Function.Injective (Φ p))
  (hΦD : ∀ p v, Φ (p + 1) (D p v) = d p (Φ p v))
  (hΦmem : ∀ p v i, Φ p v i ∈ laurentPart R (im i) k)
  (hΦsurj : ∀ p x, (∀ i, x i ∈ laurentPart R (im i) k) → ∃ v, Φ p v = x)
include hΦ hΦD hΦmem

include hΦsurj in
/-- **Čech cohomology of `O(k)` in positive degrees**: a complex `V` which embeds into the ordered
cochains with values in Laurent coefficient families, with image the cochains with values in
`laurentPart (im i) k`, is exact in degree `p + 1` if `p + 2 ≠ card ι` or `k > -card ι`. That is,
with `card ι = n + 1`: `H^q = 0` for `0 < q ≠ n`, and `H^n = 0` if `k > -n - 1`. -/
theorem exact_of_laurentPart (p : ℕ) (hp : p + 2 ≠ Fintype.card ι ∨ -Fintype.card ι < k) :
    Function.Exact (D p) (D (p + 1)) := by
  intro v
  constructor
  · intro hv
    obtain ⟨y, hy, hdy⟩ := exists_eq_d_of_laurentPart (Φ (p + 1) v) (hΦmem _ v)
      (by rw [← hΦD, hv, map_zero]) hp
    obtain ⟨w, rfl⟩ := hΦsurj p y hy
    exact ⟨w, hΦ _ (by rw [hΦD, hdy])⟩
  · rintro ⟨w, rfl⟩
    apply hΦ
    rw [hΦD, hΦD, d_d, map_zero]

omit [DecidableEq ι] [Fintype ι] hΦ hΦD hΦmem in
/-- An augmentation which embeds into `aug` is injective. -/
theorem aug_injective_of_laurentPart [Nonempty ι] {V₀ : Type*} [AddCommGroup V₀]
    (ε : V₀ →+ V 0) (Φ₀ : V₀ →+ ((ι →₀ ℤ) →₀ R)) (hΦ₀ : Function.Injective Φ₀)
    (hΦε : ∀ v, Φ 0 (ε v) = aug (Φ₀ v)) : Function.Injective ε := by
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  intro v w h
  apply hΦ₀
  simpa [hΦε] using congrFun (congrArg (Φ 0) h) fun _ ↦ j₀

/-- **Čech `H⁰` of `O(k)`**: for a complex `V` as in `exact_of_laurentPart` with an augmentation
`ε : V₀ → V 0` embedding into `aug` with image `laurentPart ∅ k` (the polynomials of degree `k`),
the augmented complex is exact at `V 0` if `card ι ≠ 1` or `k > -card ι`. -/
theorem aug_exact_of_laurentPart [Nonempty ι] {V₀ : Type*} [AddCommGroup V₀]
    (ε : V₀ →+ V 0) (Φ₀ : V₀ →+ ((ι →₀ ℤ) →₀ R))
    (hΦε : ∀ v, Φ 0 (ε v) = aug (Φ₀ v))
    (hΦ₀surj : ∀ f ∈ laurentPart R ∅ k, ∃ v, Φ₀ v = f)
    (hp : 1 ≠ Fintype.card ι ∨ -Fintype.card ι < k) :
    Function.Exact ε (D 0) := by
  intro v
  constructor
  · intro hv
    obtain ⟨f, hf, hfv⟩ := exists_eq_aug_of_laurentPart (Φ 0 v) (hΦmem _ v)
      (by rw [← hΦD, hv, map_zero]) hp
    obtain ⟨w, rfl⟩ := hΦ₀surj f hf
    exact ⟨w, hΦ _ (by rw [hΦε, hfv])⟩
  · rintro ⟨w, rfl⟩
    apply hΦ
    rw [hΦD, hΦε, d_aug, map_zero]

end Transfer

end Grading

end MvPolynomial

end
