/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.RingTheory.MvPolynomial.LaurentAway

/-!
# The Čech cohomology of `O(k)` on projective space

Let `S = R[Xⱼ : j ∈ ι]` with `ι` finite (`ι = Fin (n + 1)` for `ℙⁿ_R`), and write
`X_I = ∏_{j ∈ I} Xⱼ`. For the standard cover of `ℙⁿ` by the `D₊(Xⱼ)`, the sections of `O(k)` over
`D₊(X_I) = ⋂_{j ∈ I} D₊(Xⱼ)` are the homogeneous elements of degree `k` of `S[1 / X_I]`, and for
`k = 0` they form the ring `S_(X_I) = HomogeneousLocalization.Away 𝒜 X_I`. The ordered Čech
complex has degree-`p` term `∏_{i : Fin (p + 1) → ι} Γ(D₊(X_{im i}), O(k))`, with the
alternating sum of restrictions as differential.

We prove:

- `homCech_exact`: for `k = 0` (with `S_(X_I)`), the Čech complex is exact in all positive
  degrees, i.e. `H^q(ℙⁿ, O) = 0` for `q ≥ 1`; and `homCech_aug_exact`, `homCechAug_injective`:
  `H⁰(ℙⁿ, O) = R`.
- `degCech_exact`: for arbitrary `k` (with `awayDegree R I k ⊆ S[1 / X_I]`), the Čech complex is
  exact in degree `q ≥ 1` if `q ≠ n` or `k > -n - 1`; and `degCech_aug_exact`,
  `degCechAug_injective`: for `k = m ≥ 0`, `H⁰(ℙⁿ, O(m)) = S_m`.

Both are obtained from the Laurent model (`exact_of_laurentPart`) via the embeddings
`homAwayCoeff` and `awayCoeff`.
-/

@[expose] public section

open SimplexCochain HomogeneousLocalization

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι : Type*) [DecidableEq ι] (R : Type*) [CommRing R]

/-! ### The Čech complex of `O` -/

/-- The degree-`p` term `∏_{i : Fin (p + 1) → ι} S_(X_{im i})` of the Čech complex of `O` for the
standard cover of projective space. -/
abbrev HomCechObj (p : ℕ) : Type _ :=
  ∀ i : Fin (p + 1) → ι, Away (homogeneousSubmodule ι R) (∏ j ∈ im i, X j)

/-- The `k`-th coface map `x ↦ (i ↦ x (i ∘ δₖ)|_{D₊(X_{im i})})` of the Čech complex of `O`. -/
noncomputable def homCechRestr (p : ℕ) (k : Fin (p + 2)) :
    HomCechObj ι R p →+ HomCechObj ι R (p + 1) :=
  AddMonoidHom.mk' (fun x i ↦ homAwayRestr (im_comp_subset i k.succAbove)
    (x fun a ↦ i (k.succAbove a))) fun x y ↦ by
    ext i : 1
    simp

/-- The Čech differential `(d x) i = ∑ₖ (-1) ^ k • x (i ∘ δₖ)|_{D₊(X_{im i})}` for `O`. -/
noncomputable def homCechD (p : ℕ) : HomCechObj ι R p →+ HomCechObj ι R (p + 1) :=
  ∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) • homCechRestr ι R p k

/-- The augmentation `R → ∏ᵢ S_(Xᵢ)`, `r ↦ (i ↦ r)`. -/
noncomputable def homCechAug : R →+ HomCechObj ι R 0 :=
  AddMonoidHom.mk' (fun r _ ↦ fromZeroRingHom _ _ ⟨C r, isHomogeneous_C _ r⟩) fun r s ↦ by
    ext i : 1
    simp only [Pi.add_apply, ← map_add]
    congr 1
    ext
    simp

variable {ι R}

/-- The Laurent coefficients of a Čech cochain of `O`. -/
noncomputable def homCechCoeff (p : ℕ) : HomCechObj ι R p →+ Cochain ι ((ι →₀ ℤ) →₀ R) p :=
  AddMonoidHom.mk' (fun x i ↦ homAwayCoeff R (im i) (x i)) fun x y ↦ by
    ext i : 1
    simp

lemma homCechCoeff_injective (p : ℕ) : Function.Injective (homCechCoeff (ι := ι) (R := R) p) :=
  fun _ _ h ↦ funext fun i ↦ homAwayCoeff_injective _ (congrFun h i)

lemma homCechCoeff_homCechD (p : ℕ) (x : HomCechObj ι R p) :
    homCechCoeff (p + 1) (homCechD ι R p x) = d p (homCechCoeff p x) := by
  ext i : 1
  simp only [homCechD, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, homCechCoeff,
    AddMonoidHom.mk'_apply, Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul, d_apply,
    homCechRestr, homAwayCoeff_homAwayRestr]

lemma homCechCoeff_homCechAug (r : R) :
    homCechCoeff 0 (homCechAug ι R r) = aug (Finsupp.single 0 r) := by
  ext i : 1
  simp only [homCechCoeff, homCechAug, AddMonoidHom.mk'_apply, aug_apply, homAwayCoeff_apply,
    awayCoeff_apply]
  have : (fromZeroRingHom (homogeneousSubmodule ι R) _
      (⟨C r, isHomogeneous_C _ r⟩ : homogeneousSubmodule ι R 0)).val =
      algebraMap (MvPolynomial ι R) (Localization.Away (∏ j ∈ im i, X j)) (C r) := by
    simp only [fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, val_mk]
    exact Localization.mk_one_eq_algebraMap _
  rw [this, awayToLaurent_algebraMap, ← monomial_zero', toLaurent_monomial, map_zero]
  rfl

omit [DecidableEq ι] in
lemma mem_laurentPart_empty_zero {F : (ι →₀ ℤ) →₀ R} (hF : F ∈ laurentPart R ∅ 0) :
    F = Finsupp.single 0 (F 0) := by
  classical
  ext a
  by_cases ha : a = 0
  · simp [ha]
  · rw [Finsupp.single_apply, if_neg (Ne.symm ha)]
    by_contra h
    obtain ⟨hN, hd⟩ := mem_laurentPart.mp hF a h
    refine ha (Finsupp.ext fun j ↦ ?_)
    have hle : ∀ t ∈ a.support, 0 ≤ a t := fun t _ ↦
      not_lt.mp fun ht ↦ by simpa using hN (mem_negSupp.mpr ht)
    rw [Finsupp.degree_apply] at hd
    by_cases hj : j ∈ a.support
    · simpa using (Finset.sum_eq_zero_iff_of_nonneg hle).mp hd j hj
    · simpa using hj

/-- **`H^q(ℙⁿ, O) = 0` for `q ≥ 1`**: the Čech complex of `O` for the standard cover is exact in
all positive degrees. -/
theorem homCech_exact [Finite ι] [Nonempty ι] (p : ℕ) :
    Function.Exact (homCechD ι R p) (homCechD ι R (p + 1)) :=
  have := Fintype.ofFinite ι
  exact_of_laurentPart (k := 0) (homCechD ι R) (fun _ ↦ homCechCoeff _) homCechCoeff_injective
    homCechCoeff_homCechD (fun _ x i ↦ homAwayCoeff_mem_laurentPart _ (x i))
    (fun _ x hx ↦ ⟨fun i ↦ (exists_homAwayCoeff_eq _ _ (hx i)).choose,
      funext fun i ↦ (exists_homAwayCoeff_eq _ _ (hx i)).choose_spec⟩) p
    (Or.inr (by simpa using Fintype.card_pos))

/-- The augmentation `R → ∏ᵢ S_(Xᵢ)` is injective. -/
theorem homCechAug_injective [Nonempty ι] : Function.Injective (homCechAug ι R) :=
  aug_injective_of_laurentPart (fun _ ↦ homCechCoeff _) (homCechAug ι R)
    (Finsupp.singleAddHom 0) (Finsupp.single_injective 0) homCechCoeff_homCechAug

/-- **`H⁰(ℙⁿ, O) = R`**: the augmented Čech complex of `O` is exact at `∏ᵢ S_(Xᵢ)`. -/
theorem homCech_aug_exact [Finite ι] [Nonempty ι] :
    Function.Exact (homCechAug ι R) (homCechD ι R 0) :=
  have := Fintype.ofFinite ι
  aug_exact_of_laurentPart (k := 0) (homCechD ι R) (fun _ ↦ homCechCoeff _)
    homCechCoeff_injective homCechCoeff_homCechD
    (fun _ x i ↦ homAwayCoeff_mem_laurentPart _ (x i)) (homCechAug ι R)
    (Finsupp.singleAddHom 0) homCechCoeff_homCechAug
    (fun F hF ↦ ⟨F 0, (mem_laurentPart_empty_zero hF).symm⟩)
    (Or.inr (by simpa using Fintype.card_pos))

lemma homCechD_homCechD (p : ℕ) (x : HomCechObj ι R p) :
    homCechD ι R (p + 1) (homCechD ι R p x) = 0 :=
  homCechCoeff_injective _ (by rw [homCechCoeff_homCechD, homCechCoeff_homCechD, d_d, map_zero])

/-! ### The Čech complex of `O(k)` -/

variable (ι R) in
/-- The degree-`p` term `∏_{i : Fin (p + 1) → ι} (S[1 / X_{im i}])_k` of the Čech complex of `O(k)`
for the standard cover of projective space. -/
abbrev DegCechObj (k : ℤ) (p : ℕ) : Type _ :=
  ∀ i : Fin (p + 1) → ι, awayDegree R (im i) k

variable (ι R) in
/-- The `l`-th coface map of the Čech complex of `O(k)`. -/
noncomputable def degCechRestr (k : ℤ) (p : ℕ) (l : Fin (p + 2)) :
    DegCechObj ι R k p →+ DegCechObj ι R k (p + 1) :=
  AddMonoidHom.mk' (fun x i ↦ ⟨awayRestr R (im_comp_subset i l.succAbove)
    (x fun a ↦ i (l.succAbove a)), awayRestr_mem_awayDegree _ (x _).2⟩) fun x y ↦ by
    ext i : 2
    simp

variable (ι R) in
/-- The Čech differential of `O(k)`. -/
noncomputable def degCechD (k : ℤ) (p : ℕ) : DegCechObj ι R k p →+ DegCechObj ι R k (p + 1) :=
  ∑ l : Fin (p + 2), ((-1 : ℤ) ^ (l : ℕ)) • degCechRestr ι R k p l

variable (ι R) in
/-- The augmentation `S_n → ∏ᵢ (S[1 / Xᵢ])_n` from homogeneous polynomials of degree `n`. -/
noncomputable def degCechAug (n : ℕ) : homogeneousSubmodule ι R n →+ DegCechObj ι R n 0 :=
  AddMonoidHom.mk' (fun p i ↦ ⟨algebraMap _ _ p.1, algebraMap_mem_awayDegree _ p.2⟩)
    fun p q ↦ by
      ext i : 2
      simp

/-- The Laurent coefficients of a Čech cochain of `O(k)`. -/
noncomputable def degCechCoeff (k : ℤ) (p : ℕ) :
    DegCechObj ι R k p →+ Cochain ι ((ι →₀ ℤ) →₀ R) p :=
  AddMonoidHom.mk' (fun x i ↦ awayCoeff R (im i) (x i)) fun x y ↦ by
    ext i : 1
    simp

lemma degCechCoeff_injective (k : ℤ) (p : ℕ) :
    Function.Injective (degCechCoeff (ι := ι) (R := R) k p) :=
  fun _ _ h ↦ funext fun i ↦ Subtype.ext (awayCoeff_injective _ (congrFun h i))

lemma degCechCoeff_degCechD (k : ℤ) (p : ℕ) (x : DegCechObj ι R k p) :
    degCechCoeff k (p + 1) (degCechD ι R k p x) = d p (degCechCoeff k p x) := by
  ext i : 1
  simp only [degCechD, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, degCechCoeff,
    AddMonoidHom.mk'_apply, Finset.sum_apply, Pi.smul_apply,
    map_sum, map_zsmul, d_apply, degCechRestr, awayCoeff_awayRestr]

lemma degCechCoeff_mem (k : ℤ) (p : ℕ) (x : DegCechObj ι R k p) (i : Fin (p + 1) → ι) :
    degCechCoeff k p x i ∈ laurentPart R (im i) k :=
  (awayCoeff_mem_laurentPart_iff _).mpr (x i).2

lemma exists_degCechCoeff_eq (k : ℤ) (p : ℕ) (x : Cochain ι ((ι →₀ ℤ) →₀ R) p)
    (hx : ∀ i, x i ∈ laurentPart R (im i) k) : ∃ y, degCechCoeff k p y = x := by
  choose y hy using fun i ↦ exists_awayCoeff_eq (x i) (hx i)
  exact ⟨fun i ↦ ⟨y i, (awayCoeff_mem_laurentPart_iff _).mp (hy i ▸ hx i)⟩, funext hy⟩

lemma degCechCoeff_degCechAug (n : ℕ) (q : homogeneousSubmodule ι R n) :
    degCechCoeff n 0 (degCechAug ι R n q) = aug (toLaurent ι R q.1).coeff := by
  ext i : 1
  simp [degCechCoeff, degCechAug, awayCoeff_apply]

/-- **`H^q(ℙⁿ, O(k))` for `q ≥ 1`**: with `card ι = n + 1`, the Čech complex of `O(k)` is exact in
degree `p + 1` if `p + 1 ≠ n` or `k > -n - 1`. -/
theorem degCech_exact [Fintype ι] (k : ℤ) (p : ℕ)
    (hp : p + 2 ≠ Fintype.card ι ∨ -Fintype.card ι < k) :
    Function.Exact (degCechD ι R k p) (degCechD ι R k (p + 1)) :=
  exact_of_laurentPart (degCechD ι R k) (degCechCoeff k) (degCechCoeff_injective k)
    (degCechCoeff_degCechD k) (degCechCoeff_mem k) (exists_degCechCoeff_eq k) p hp

/-- The augmentation `S_n → ∏ᵢ (S[1 / Xᵢ])_n` is injective. -/
theorem degCechAug_injective [Nonempty ι] (n : ℕ) : Function.Injective (degCechAug ι R n) :=
  aug_injective_of_laurentPart (degCechCoeff n) (degCechAug ι R n)
    ((AddMonoidAlgebra.coeffAddEquiv (R := R) (M := ι →₀ ℤ)).toAddMonoidHom.comp
      ((toLaurent ι R).toAddMonoidHom.comp (homogeneousSubmodule ι R n).subtype.toAddMonoidHom))
    (fun _ _ h ↦ Subtype.ext (toLaurent_injective (AddMonoidAlgebra.coeff_injective h)))
    (degCechCoeff_degCechAug n)

/-- **`H⁰(ℙⁿ, O(n)) = S_n`** for `n ≥ 0`: the augmented Čech complex of `O(n)` is exact at
`∏ᵢ (S[1 / Xᵢ])_n`. -/
theorem degCech_aug_exact [Finite ι] [Nonempty ι] (n : ℕ) :
    Function.Exact (degCechAug ι R n) (degCechD ι R n 0) :=
  have := Fintype.ofFinite ι
  aug_exact_of_laurentPart (degCechD ι R n) (degCechCoeff n) (degCechCoeff_injective n)
    (degCechCoeff_degCechD n) (degCechCoeff_mem n) (degCechAug ι R n)
    ((AddMonoidAlgebra.coeffAddEquiv (R := R) (M := ι →₀ ℤ)).toAddMonoidHom.comp
      ((toLaurent ι R).toAddMonoidHom.comp (homogeneousSubmodule ι R n).subtype.toAddMonoidHom))
    (degCechCoeff_degCechAug n)
    (fun F hF ↦ by
      obtain ⟨q, hq, rfl⟩ := exists_toLaurent_coeff_eq F hF
      exact ⟨⟨q, hq⟩, rfl⟩)
    (Or.inr (by have := Fintype.card_pos (α := ι); omega))

lemma degCechD_degCechD (k : ℤ) (p : ℕ) (x : DegCechObj ι R k p) :
    degCechD ι R k (p + 1) (degCechD ι R k p x) = 0 :=
  degCechCoeff_injective k _ (by
    rw [degCechCoeff_degCechD, degCechCoeff_degCechD, d_d, map_zero])

end MvPolynomial

end
