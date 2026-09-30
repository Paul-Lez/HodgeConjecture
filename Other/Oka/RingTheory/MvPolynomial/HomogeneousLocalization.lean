/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Degree-zero localisations of a polynomial ring at the variables

Let `A = R[X₀, …, Xₙ]` with the grading by total degree (`MvPolynomial.gradedAlgebra`). The
degree-zero part `A_(Xᵢ)` of `A[1/Xᵢ]` is a polynomial ring in the `n` fractions `Xₖ / Xᵢ`,
`k ≠ i`:

  `R[Y₀, …, Yₙ₋₁] ≃ A_(Xᵢ)`,  `Yⱼ ↦ X_{i.succAbove j} / Xᵢ`,

with inverse the *dehomogenisation* `p ↦ p(Y₀, …, 1, …, Yₙ₋₁)` (`1` in slot `i`). More generally,
for a finite set `I ∋ i` of variables, `A_(∏_{j ∈ I} Xⱼ)` is the localisation of `R[Y]` away from
the dehomogenisation of `∏_{j ∈ I} Xⱼ`, i.e. of `∏_{j ∈ I \ {i}} Y_{j}`.

These are the coordinate rings of the standard affine charts of projective space and of their
finite intersections.

## Main definitions

- `MvPolynomial.dehomogenize i`: the `R`-algebra map `R[X₀, …, Xₙ] → R[Y₀, …, Yₙ₋₁]` setting
  `Xᵢ = 1`.
- `MvPolynomial.awayXDiv i k`: the fraction `Xₖ / Xᵢ` in `A_(Xᵢ)`.
- `MvPolynomial.awayXEquiv i : R[Y₀, …, Yₙ₋₁] ≃+* A_(Xᵢ)`.
- `MvPolynomial.awayProdXEquiv i I : R[Y]_{dehomogenize i (∏_{j ∈ I} Xⱼ)} ≃+* A_(∏_{j ∈ I} Xⱼ)`
  for `i ∈ I`.

## Main results

- `MvPolynomial.isLocalization_awayProdX`: `A_(∏_{j ∈ I} Xⱼ)` is the localisation of
  `R[Y]` (via `awayXEquiv i` and `HomogeneousLocalization.awayMap`) away from
  `dehomogenize i (∏_{j ∈ I} Xⱼ)`.
-/

@[expose] public section

open HomogeneousLocalization

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type*} [CommRing R] {n : ℕ}

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R

lemma X_mem_homogeneousSubmodule_one {σ : Type*} (i : σ) :
    (X i : MvPolynomial σ R) ∈ homogeneousSubmodule σ R 1 :=
  isHomogeneous_X R i

lemma prod_X_mem_homogeneousSubmodule {σ : Type*} (s : Finset σ) :
    (∏ j ∈ s, X j : MvPolynomial σ R) ∈ homogeneousSubmodule σ R s.card := by
  simpa using SetLike.prod_mem_graded (homogeneousSubmodule σ R) (fun _ ↦ 1) (fun j ↦ X j)
    (fun j _ ↦ X_mem_homogeneousSubmodule_one j)

variable (R) in
/-- The variables generate `R[X]` over its degree-zero part. -/
lemma adjoin_range_X_gradeZero_eq_top (σ : Type*) :
    Algebra.adjoin (homogeneousSubmodule σ R 0)
      (Set.range (X : σ → MvPolynomial σ R)) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact Subalgebra.algebraMap_mem _ (⟨C r, isHomogeneous_C _ r⟩ : homogeneousSubmodule σ R 0)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p k hp => exact mul_mem hp (Algebra.subset_adjoin ⟨k, rfl⟩)

variable (R) in
/-- **Dehomogenisation** at the `i`-th variable: the `R`-algebra map
`R[X₀, …, Xₙ] → R[Y₀, …, Yₙ₋₁]` sending `Xᵢ ↦ 1` and `X_{i.succAbove j} ↦ Yⱼ`. -/
noncomputable def dehomogenize (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval (Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin n) R) i 1 X)

@[simp]
lemma dehomogenize_X_self (i : Fin (n + 1)) : dehomogenize R i (X i) = 1 := by
  simp [dehomogenize]

@[simp]
lemma dehomogenize_X_succAbove (i : Fin (n + 1)) (j : Fin n) :
    dehomogenize R i (X (i.succAbove j)) = X j := by
  simp [dehomogenize]

lemma dehomogenize_C (i : Fin (n + 1)) (r : R) : dehomogenize R i (C r) = C r := by
  simp [dehomogenize]

lemma dehomogenize_prod_X_erase (i : Fin (n + 1)) (I : Finset (Fin (n + 1))) :
    dehomogenize R i (∏ j ∈ I.erase i, X j) = dehomogenize R i (∏ j ∈ I, X j) := by
  by_cases hi : i ∈ I
  · rw [← Finset.mul_prod_erase I _ hi, map_mul, dehomogenize_X_self, one_mul]
  · rw [Finset.erase_eq_of_notMem hi]

variable (R) in
/-- The fraction `Xₖ / Xᵢ` as an element of the degree-zero localisation `A_(Xᵢ)`. -/
noncomputable def awayXDiv (i k : Fin (n + 1)) : Away 𝒜 (X i) :=
  Away.mk 𝒜 (X_mem_homogeneousSubmodule_one i) 1 (X k)
    (by rw [smul_eq_mul, mul_one]; exact X_mem_homogeneousSubmodule_one k)

lemma val_awayXDiv (i k : Fin (n + 1)) :
    (awayXDiv R i k).val =
      Localization.mk (X k) (⟨X i ^ 1, 1, rfl⟩ : Submonoid.powers (X i)) :=
  rfl

@[simp]
lemma awayXDiv_self (i : Fin (n + 1)) : awayXDiv R i i = 1 := by
  ext
  rw [val_awayXDiv, val_one, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp⟩

variable (R) in
/-- The ring map `R → 𝒜 0 → A_(Xᵢ)`. -/
noncomputable def awayXBase (i : Fin (n + 1)) : R →+* Away 𝒜 (X i) :=
  (fromZeroRingHom 𝒜 _).comp (algebraMap R (𝒜 0))

variable (R) in
/-- The ring map `R[Y₀, …, Yₙ₋₁] → A_(Xᵢ)`, `Yⱼ ↦ X_{i.succAbove j} / Xᵢ`. -/
noncomputable def toAwayX (i : Fin (n + 1)) : MvPolynomial (Fin n) R →+* Away 𝒜 (X i) :=
  eval₂Hom (awayXBase R i) fun j ↦ awayXDiv R i (i.succAbove j)

@[simp]
lemma toAwayX_X (i : Fin (n + 1)) (j : Fin n) :
    toAwayX R i (X j) = awayXDiv R i (i.succAbove j) := by
  simp [toAwayX]

@[simp]
lemma toAwayX_C (i : Fin (n + 1)) (r : R) :
    toAwayX R i (C r) = awayXBase R i r := by
  simp [toAwayX]

variable (R) in
/-- The ring map `A_(Xᵢ) → R[Y₀, …, Yₙ₋₁]` induced by dehomogenisation: `a / Xᵢᵐ ↦
dehomogenize i a`. -/
noncomputable def fromAwayX (i : Fin (n + 1)) : Away 𝒜 (X i) →+* MvPolynomial (Fin n) R :=
  (Localization.awayLift (dehomogenize R i).toRingHom (X i)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)).comp
      (algebraMap (Away 𝒜 (X i)) (Localization.Away (X i)))

lemma fromAwayX_mk (i : Fin (n + 1)) (m : ℕ) (a : MvPolynomial (Fin (n + 1)) R)
    (ha : a ∈ 𝒜 (m • 1)) :
    fromAwayX R i (Away.mk 𝒜 (X_mem_homogeneousSubmodule_one i) m a ha) =
      dehomogenize R i a := by
  simp only [fromAwayX, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
  simp

@[simp]
lemma fromAwayX_toAwayX (i : Fin (n + 1)) (p : MvPolynomial (Fin n) R) :
    fromAwayX R i (toAwayX R i p) = p := by
  suffices (fromAwayX R i).comp (toAwayX R i) = RingHom.id _ from congr($this p)
  refine ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, toAwayX_C, RingHom.id_apply, fromAwayX,
      awayXBase, HomogeneousLocalization.algebraMap_apply]
    change Localization.awayLift _ _ _ (Localization.mk _ ⟨X i ^ 0, 0, rfl⟩) = _
    rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
    simp [MvPolynomial.algebraMap_eq]
  · simp only [RingHom.coe_comp, Function.comp_apply, toAwayX_X, RingHom.id_apply, awayXDiv]
    rw [fromAwayX_mk]
    simp

lemma awayXDiv_mem_range (i k : Fin (n + 1)) : awayXDiv R i k ∈ (toAwayX R i).range := by
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i k
  · rw [awayXDiv_self]; exact one_mem _
  · exact ⟨X j, toAwayX_X i j⟩

lemma toAwayX_surjective (i : Fin (n + 1)) : Function.Surjective (toAwayX R i) := by
  intro z
  have hgen := Away.adjoin_mk_prod_pow_eq_top (X_mem_homogeneousSubmodule_one i)
    (Fin (n + 1)) X (adjoin_range_X_gradeZero_eq_top R _) (fun _ ↦ 1)
    X_mem_homogeneousSubmodule_one
  have hz : z ∈ Algebra.adjoin (𝒜 0) _ := hgen ▸ Algebra.mem_top
  suffices z ∈ (toAwayX R i).range from this
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, ai, hai, -, rfl⟩ := hx
    have : Away.mk 𝒜 (X_mem_homogeneousSubmodule_one i) a (∏ k, X k ^ ai k)
        (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun k _ ↦
          X_mem_homogeneousSubmodule_one k) = ∏ k, awayXDiv R i k ^ ai k := by
      apply val_injective
      simp only [smul_eq_mul, mul_one] at hai
      change _ = algebraMap (Away 𝒜 (X i)) (Localization.Away (X i))
        (∏ k, awayXDiv R i k ^ ai k)
      simp only [map_prod, map_pow, HomogeneousLocalization.algebraMap_apply, val_awayXDiv,
        Away.val_mk, Localization.mk_pow, Localization.mk_prod]
      congr 1
      apply Subtype.ext
      simp [Finset.prod_pow_eq_pow_sum, hai]
    rw [this]
    exact prod_mem fun k _ ↦ pow_mem (awayXDiv_mem_range i k) _
  | algebraMap r =>
    obtain ⟨p, hr⟩ := r
    rw [homogeneousSubmodule_zero, Submodule.mem_one] at hr
    obtain ⟨s, rfl⟩ := hr
    refine ⟨C s, ?_⟩
    rw [toAwayX_C]
    rfl
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

variable (R) in
/-- **The standard chart ring**: `R[Y₀, …, Yₙ₋₁] ≃ A_(Xᵢ)`, `Yⱼ ↦ X_{i.succAbove j} / Xᵢ`. The
inverse is dehomogenisation (`MvPolynomial.awayXEquiv_symm_apply`). -/
noncomputable def awayXEquiv (i : Fin (n + 1)) : MvPolynomial (Fin n) R ≃+* Away 𝒜 (X i) :=
  RingEquiv.ofBijective (toAwayX R i)
    ⟨Function.LeftInverse.injective (fromAwayX_toAwayX i), toAwayX_surjective i⟩

@[simp]
lemma awayXEquiv_apply (i : Fin (n + 1)) (p : MvPolynomial (Fin n) R) :
    awayXEquiv R i p = toAwayX R i p :=
  rfl

@[simp]
lemma awayXEquiv_symm_apply (i : Fin (n + 1)) (z : Away 𝒜 (X i)) :
    (awayXEquiv R i).symm z = fromAwayX R i z := by
  rw [RingEquiv.symm_apply_eq]
  obtain ⟨p, rfl⟩ := toAwayX_surjective (R := R) i z
  simp

@[simp]
lemma toAwayX_fromAwayX (i : Fin (n + 1)) (z : Away 𝒜 (X i)) :
    toAwayX R i (fromAwayX R i z) = z := by
  rw [← awayXEquiv_symm_apply, ← awayXEquiv_apply, RingEquiv.apply_symm_apply]

lemma toAwayX_dehomogenize_prod_X (i : Fin (n + 1)) (s : Finset (Fin (n + 1))) :
    toAwayX R i (dehomogenize R i (∏ j ∈ s, X j)) =
      Away.mk 𝒜 (X_mem_homogeneousSubmodule_one i) s.card (∏ j ∈ s, X j)
        (by rw [smul_eq_mul, mul_one]; exact prod_X_mem_homogeneousSubmodule s) := by
  rw [← fromAwayX_mk, toAwayX_fromAwayX]

section intersections

variable (i : Fin (n + 1)) (I : Finset (Fin (n + 1))) (hi : i ∈ I)

variable (R) in
/-- The degree-zero localisation at `∏_{j ∈ I} Xⱼ` as an algebra over `R[Y₀, …, Yₙ₋₁]`, via the
chart `i ∈ I`: `R[Y] ≃ A_(Xᵢ) → A_(∏_{j ∈ I} Xⱼ)`. -/
noncomputable def toAwayProdX : MvPolynomial (Fin n) R →+* Away 𝒜 (∏ j ∈ I, X j) :=
  (awayMap 𝒜 (prod_X_mem_homogeneousSubmodule (I.erase i))
    (Finset.mul_prod_erase I (fun j ↦ X j) hi).symm).comp (toAwayX R i)

include hi in
/-- **The chart description of `A_(∏_{j ∈ I} Xⱼ)`**: for `i ∈ I` it is the localisation of the
chart ring `R[Y₀, …, Yₙ₋₁]` of `Xᵢ` away from the dehomogenisation of `∏_{j ∈ I} Xⱼ`, i.e. away
from `∏_{j ∈ I, j ≠ i} Y_j`. -/
theorem isLocalization_awayProdX :
    letI := (toAwayProdX R i I hi).toAlgebra
    IsLocalization.Away (dehomogenize R i (∏ j ∈ I, X j)) (Away 𝒜 (∏ j ∈ I, X j)) := by
  have hg := prod_X_mem_homogeneousSubmodule (R := R) (I.erase i)
  have hx := (Finset.mul_prod_erase I (fun j ↦ (X j : MvPolynomial (Fin (n + 1)) R)) hi).symm
  letI := (awayMap 𝒜 hg hx).toAlgebra
  have H := Away.isLocalization_mul (X_mem_homogeneousSubmodule_one i) hg hx one_ne_zero
  have H' := IsLocalization.isLocalization_of_base_ringEquiv
    (Submonoid.powers (Away.isLocalizationElem (X_mem_homogeneousSubmodule_one i) hg))
    (Away 𝒜 (∏ j ∈ I, X j)) (awayXEquiv R i).symm
  convert H' using 1
  · simp only [Submonoid.map_powers]
    congr 1
    rw [awayXEquiv_symm_apply, fromAwayX_mk, pow_one, dehomogenize_prod_X_erase]
  · rfl

variable (R) in
/-- **The chart description of `A_(∏_{j ∈ I} Xⱼ)`** as a ring isomorphism: for `i ∈ I`,
`R[Y₀, …, Yₙ₋₁][1 / dehomogenize i (∏_{j ∈ I} Xⱼ)] ≃ A_(∏_{j ∈ I} Xⱼ)`. -/
noncomputable def awayProdXEquiv :
    Localization.Away (dehomogenize R i (∏ j ∈ I, X j)) ≃+* Away 𝒜 (∏ j ∈ I, X j) :=
  letI := (toAwayProdX R i I hi).toAlgebra
  haveI := isLocalization_awayProdX (R := R) i I hi
  (IsLocalization.algEquiv (Submonoid.powers (dehomogenize R i (∏ j ∈ I, X j))) _ _).toRingEquiv

lemma awayProdXEquiv_algebraMap (p : MvPolynomial (Fin n) R) :
    awayProdXEquiv R i I hi (algebraMap _ _ p) = toAwayProdX R i I hi p := by
  letI := (toAwayProdX R i I hi).toAlgebra
  haveI := isLocalization_awayProdX (R := R) i I hi
  exact (IsLocalization.algEquiv
    (Submonoid.powers (dehomogenize R i (∏ j ∈ I, X j))) _ _).commutes p

end intersections

end MvPolynomial

end
