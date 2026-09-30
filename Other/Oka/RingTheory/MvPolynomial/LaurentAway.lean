/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.RingTheory.MvPolynomial.CechProjective
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Localisations of a polynomial ring at monomials as Laurent polynomials

Let `S = R[Xⱼ : j ∈ ι]` and `X_I = ∏_{j ∈ I} Xⱼ` for a finset `I`. The localisation `S[1 / X_I]`
embeds into the ring of Laurent polynomials `R[ι →₀ ℤ] = AddMonoidAlgebra R (ι →₀ ℤ)`
(`MvPolynomial.awayToLaurent`), with image the Laurent polynomials whose monomials `Xᵃ` have
negative support `negSupp a ⊆ I`. Homogeneous elements of degree `k` correspond to Laurent
polynomials of degree `k` (`MvPolynomial.awayDegree`, `MvPolynomial.mem_awayDegree_iff`); in
particular the degree-zero part `S_(X_I) = HomogeneousLocalization.Away 𝒜 X_I` is identified with
`laurentPart R I 0` (`MvPolynomial.homAwayCoeff`).

## Main definitions

- `MvPolynomial.toLaurent : MvPolynomial ι R →ₐ[R] AddMonoidAlgebra R (ι →₀ ℤ)`.
- `MvPolynomial.awayToLaurent I : Localization.Away X_I →+* AddMonoidAlgebra R (ι →₀ ℤ)`.
- `MvPolynomial.awayCoeff I : Localization.Away X_I →+ ((ι →₀ ℤ) →₀ R)`: the Laurent
  coefficients.
- `MvPolynomial.awayDegree I k`: the homogeneous elements of degree `k` of `S[1 / X_I]`.
- `MvPolynomial.awayRestr`, `MvPolynomial.homAwayRestr`: the restrictions `S[1 / X_I] → S[1 / X_J]`
  and `S_(X_I) → S_(X_J)` for `I ⊆ J`.
- `MvPolynomial.homAwayCoeff I`: the Laurent coefficients of an element of
  `HomogeneousLocalization.Away 𝒜 X_I`.

## Main results

- `MvPolynomial.awayCoeff_injective`, `MvPolynomial.awayCoeff_mem_laurentPart_iff`,
  `MvPolynomial.exists_awayCoeff_eq`: `awayDegree I k ≅ laurentPart R I k`.
- `MvPolynomial.awayCoeff_comp`: compatibility with any map `S[1 / X_I] → S[1 / X_J]` under `S`.
- `MvPolynomial.homAwayCoeff_mem_laurentPart`, `MvPolynomial.exists_homAwayCoeff_eq`:
  `HomogeneousLocalization.Away 𝒜 X_I ≅ laurentPart R I 0`.
-/

@[expose] public section

open AddMonoidAlgebra

set_option backward.isDefEq.respectTransparency.types false

namespace MvPolynomial

variable {ι : Type*} {R : Type*} [CommRing R]

/-! ### Exponents -/

/-- The inclusion of exponents `(ι →₀ ℕ) → (ι →₀ ℤ)`. -/
noncomputable def expInt : (ι →₀ ℕ) →+ (ι →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

@[simp]
lemma expInt_apply (e : ι →₀ ℕ) (j : ι) : expInt e j = e j :=
  rfl

lemma expInt_injective : Function.Injective (expInt (ι := ι)) := by
  intro e e' h
  ext j
  simpa using DFunLike.congr_fun h j

lemma mem_range_expInt {a : ι →₀ ℤ} : a ∈ Set.range expInt ↔ ∀ j, 0 ≤ a j := by
  refine ⟨?_, fun h ↦ ⟨Finsupp.mapRange Int.toNat (by simp) a, ?_⟩⟩
  · rintro ⟨e, rfl⟩ j
    simp
  · ext j
    simp [h j]

lemma degree_expInt (e : ι →₀ ℕ) : (expInt e).degree = e.degree := by
  classical
  simp only [Finsupp.degree_apply, Nat.cast_sum]
  refine Finset.sum_subset (fun j ↦ by simp) fun j _ hj ↦ ?_
  simpa using hj

/-! ### Polynomials as Laurent polynomials -/

variable (ι R) in
/-- The inclusion of polynomials into Laurent polynomials. -/
noncomputable def toLaurent : MvPolynomial ι R →ₐ[R] AddMonoidAlgebra R (ι →₀ ℤ) :=
  mapDomainAlgHom R R expInt

lemma toLaurent_apply (p : MvPolynomial ι R) : toLaurent ι R p = mapDomain expInt p := by
  simp [toLaurent]

lemma coeff_toLaurent_expInt (p : MvPolynomial ι R) (e : ι →₀ ℕ) :
    (toLaurent ι R p).coeff (expInt e) = p.coeff e := by
  rw [toLaurent_apply, coeff_mapDomain, Finsupp.mapDomain_apply expInt_injective]
  rfl

lemma coeff_toLaurent_eq_zero (p : MvPolynomial ι R) {a : ι →₀ ℤ} (ha : ¬ ∀ j, 0 ≤ a j) :
    (toLaurent ι R p).coeff a = 0 := by
  rw [toLaurent_apply, coeff_mapDomain]
  exact Finsupp.mapDomain_notin_range _ _ (mem_range_expInt.not.mpr ha)

lemma toLaurent_injective : Function.Injective (toLaurent ι R) := by
  intro p q h
  rw [toLaurent_apply, toLaurent_apply] at h
  exact mapDomain_injective expInt_injective h

lemma toLaurent_monomial (e : ι →₀ ℕ) (r : R) :
    toLaurent ι R (monomial e r) = single (expInt e) r := by
  rw [toLaurent_apply, ← single_eq_monomial, mapDomain_single]

lemma exists_toLaurent_eq (F : AddMonoidAlgebra R (ι →₀ ℤ))
    (hF : ∀ a, F.coeff a ≠ 0 → ∀ j, 0 ≤ a j) : ∃ p, toLaurent ι R p = F := by
  refine ⟨comapDomain expInt expInt_injective F, ?_⟩
  rw [toLaurent_apply, mapDomain_comapDomain]
  intro a ha
  exact mem_range_expInt.mpr (hF a (Finsupp.mem_support_iff.mp ha))

/-! ### The monomial `X_I` -/

/-- The exponent `∑_{j ∈ I} eⱼ` of `X_I = ∏_{j ∈ I} Xⱼ`. -/
noncomputable def oneI (I : Finset ι) : ι →₀ ℤ := ∑ j ∈ I, Finsupp.single j 1

lemma oneI_apply [DecidableEq ι] (I : Finset ι) (j : ι) : oneI I j = if j ∈ I then 1 else 0 := by
  simp [oneI, Finsupp.finsetSum_apply, Finsupp.single_apply]

lemma degree_oneI (I : Finset ι) : (oneI I).degree = I.card := by
  simp [oneI, map_sum]

lemma toLaurent_prod_X (I : Finset ι) :
    toLaurent ι R (∏ j ∈ I, X j) = single (oneI I) 1 := by
  classical
  induction I using Finset.induction_on with
  | empty => rw [Finset.prod_empty, map_one, oneI, Finset.sum_empty]; rfl
  | insert j I hj ih =>
    rw [Finset.prod_insert hj, map_mul, ih, X, toLaurent_monomial, single_mul_single, mul_one]
    simp only [oneI]
    rw [Finset.sum_insert hj]
    congr 1
    ext t
    simp only [Finsupp.coe_add, Pi.add_apply, expInt_apply, Finsupp.single_apply]
    split_ifs <;> simp

lemma toLaurent_prod_X_mul_inv (I : Finset ι) :
    toLaurent ι R (∏ j ∈ I, X j) * single (-oneI I) 1 = 1 := by
  rw [toLaurent_prod_X, single_mul_single, add_neg_cancel, mul_one]
  rfl

/-! ### Localisations at `X_I` -/

variable (R) in
/-- The embedding `S[1 / X_I] → R[ι →₀ ℤ]` of the localisation at `X_I = ∏_{j ∈ I} Xⱼ` into
Laurent polynomials. -/
noncomputable def awayToLaurent (I : Finset ι) :
    Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R) →+* AddMonoidAlgebra R (ι →₀ ℤ) :=
  Localization.awayLift (toLaurent ι R).toRingHom _
    (isUnit_iff_exists_inv.mpr ⟨_, toLaurent_prod_X_mul_inv I⟩)

lemma awayToLaurent_mk (I : Finset ι) (p : MvPolynomial ι R) (m : ℕ) :
    awayToLaurent R I (Localization.mk p ⟨(∏ j ∈ I, X j) ^ m, m, rfl⟩) =
      toLaurent ι R p * single (-(m • oneI I)) 1 := by
  rw [awayToLaurent, Localization.awayLift_mk _ _ _ _ (toLaurent_prod_X_mul_inv I)]
  simp [single_pow]

@[simp]
lemma awayToLaurent_algebraMap (I : Finset ι) (p : MvPolynomial ι R) :
    awayToLaurent R I (algebraMap _ _ p) = toLaurent ι R p := by
  simp [awayToLaurent]

lemma coeff_awayToLaurent_mk (I : Finset ι) (p : MvPolynomial ι R) (m : ℕ) (a : ι →₀ ℤ) :
    (awayToLaurent R I (Localization.mk p ⟨(∏ j ∈ I, X j) ^ m, m, rfl⟩)).coeff a =
      (toLaurent ι R p).coeff (a + m • oneI I) := by
  rw [awayToLaurent_mk, coeff_mul_single_apply, mul_one, neg_neg]

lemma awayToLaurent_injective (I : Finset ι) : Function.Injective (awayToLaurent R I) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  induction y using Localization.induction_on with | H y => ?_
  obtain ⟨p, ⟨_, m, rfl⟩⟩ := y
  rw [awayToLaurent_mk] at hy
  have hp : toLaurent ι R p = 0 := by
    have := congrArg (· * single (m • oneI I) 1) hy
    simp only [mul_assoc, single_mul_single, neg_add_cancel, mul_one, zero_mul] at this
    rwa [← AddMonoidAlgebra.one_def, mul_one] at this
  rw [← map_zero (toLaurent ι R)] at hp
  rw [toLaurent_injective hp, Localization.mk_zero]

/-- `awayToLaurent` is compatible with every map `S[1 / X_I] → S[1 / X_J]` under `S`, e.g. the
restriction maps for `I ⊆ J`. -/
lemma awayToLaurent_comp {I J : Finset ι}
    (φ : Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R) →+*
      Localization.Away (∏ j ∈ J, X j : MvPolynomial ι R))
    (hφ : φ.comp (algebraMap (MvPolynomial ι R) _) = algebraMap (MvPolynomial ι R) _) :
    (awayToLaurent R J).comp φ = awayToLaurent R I := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (∏ j ∈ I, X j : MvPolynomial ι R)) ?_
  rw [RingHom.comp_assoc, hφ]
  exact RingHom.ext fun p ↦ by simp

variable (R) in
/-- The Laurent coefficients of an element of `S[1 / X_I]`. -/
noncomputable def awayCoeff (I : Finset ι) :
    Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R) →+ ((ι →₀ ℤ) →₀ R) :=
  (coeffAddEquiv (R := R) (M := ι →₀ ℤ)).toAddMonoidHom.comp
    (awayToLaurent R I).toAddMonoidHom

lemma awayCoeff_apply (I : Finset ι) (y : Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R)) :
    awayCoeff R I y = (awayToLaurent R I y).coeff :=
  rfl

lemma awayCoeff_injective (I : Finset ι) : Function.Injective (awayCoeff R I) :=
  coeff_injective.comp (awayToLaurent_injective I)

lemma awayCoeff_comp {I J : Finset ι}
    (φ : Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R) →+*
      Localization.Away (∏ j ∈ J, X j : MvPolynomial ι R))
    (hφ : φ.comp (algebraMap (MvPolynomial ι R) _) = algebraMap (MvPolynomial ι R) _) (y) :
    awayCoeff R J (φ y) = awayCoeff R I y := by
  rw [awayCoeff_apply, awayCoeff_apply, ← RingHom.comp_apply, awayToLaurent_comp φ hφ]

lemma negSupp_subset_of_awayCoeff (I : Finset ι)
    (y : Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R)) (a : ι →₀ ℤ)
    (ha : awayCoeff R I y a ≠ 0) : negSupp a ⊆ I := by
  classical
  induction y using Localization.induction_on with | H y => ?_
  obtain ⟨p, ⟨_, m, rfl⟩⟩ := y
  rw [awayCoeff_apply, coeff_awayToLaurent_mk] at ha
  intro j hj
  by_contra hjI
  refine ha (coeff_toLaurent_eq_zero p fun h ↦ ?_)
  have := h j
  rw [mem_negSupp] at hj
  simp [oneI_apply, hjI] at this
  omega

/-- For a Laurent polynomial `F` with negative supports in `I` there is `m` with
`F · X_I ^ m` a polynomial. -/
lemma exists_toLaurent_eq_mul (I : Finset ι) (F : AddMonoidAlgebra R (ι →₀ ℤ))
    (hF : ∀ a, F.coeff a ≠ 0 → negSupp a ⊆ I) :
    ∃ (m : ℕ) (p : MvPolynomial ι R), toLaurent ι R p = F * single (m • oneI I) 1 := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ∑ a ∈ F.coeff.support, ∑ j ∈ I, (a j).natAbs := ⟨_, rfl⟩
  refine ⟨m, exists_toLaurent_eq _ fun a ha j ↦ ?_⟩
  rw [coeff_mul_single_apply, mul_one] at ha
  have hle : ∀ j ∈ I, ((a - m • oneI I) j).natAbs ≤ m := fun j hj ↦ le_of_le_of_eq
    ((Finset.single_le_sum (f := fun j ↦ ((a - m • oneI I) j).natAbs) (fun _ _ ↦ Nat.zero_le _)
      hj).trans (Finset.single_le_sum (f := fun b ↦ ∑ j ∈ I, (b j).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finsupp.mem_support_iff.mpr ha))) hm.symm
  have := hF _ ha
  have hj' : (a - m • oneI I) j = a j - (if j ∈ I then (m : ℤ) else 0) := by
    rw [Finsupp.sub_apply, Finsupp.smul_apply, oneI_apply]
    split_ifs <;> simp
  by_cases hj : j ∈ I
  · have h := hle j hj
    rw [hj', if_pos hj] at h
    omega
  · have h : ¬ (a - m • oneI I) j < 0 := fun h ↦ hj (this (mem_negSupp.mpr h))
    rw [hj', if_neg hj] at h
    omega

/-- A Laurent coefficient family with negative supports in `I` is the family of Laurent
coefficients of some `p / X_I ^ m`. -/
lemma exists_awayCoeff_mk_eq (I : Finset ι) (F : (ι →₀ ℤ) →₀ R)
    (hF : ∀ a, F a ≠ 0 → negSupp a ⊆ I) :
    ∃ (m : ℕ) (p : MvPolynomial ι R),
      awayCoeff R I (Localization.mk p ⟨(∏ j ∈ I, X j) ^ m, m, rfl⟩) = F := by
  obtain ⟨m, p, hp⟩ := exists_toLaurent_eq_mul I (ofCoeff F) hF
  refine ⟨m, p, ?_⟩
  rw [awayCoeff_apply, awayToLaurent_mk, hp, mul_assoc, single_mul_single, add_neg_cancel,
    mul_one, ← AddMonoidAlgebra.one_def, mul_one]

/-! ### Homogeneous elements -/

variable (R) in
/-- The homogeneous elements of degree `k` of `S[1 / X_I]`, i.e. the sections of `O(k)` over
`D₊(X_I)`: the elements whose Laurent polynomial has degree `k` (see `mem_awayDegree_iff` for the
description as fractions `p / X_I ^ m` with `p` homogeneous of degree `k + m · card I`). -/
noncomputable def awayDegree (I : Finset ι) (k : ℤ) :
    AddSubgroup (Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R)) :=
  (degreePart R k).comap (awayCoeff R I)

lemma awayCoeff_mem_laurentPart_iff {I : Finset ι} {k : ℤ}
    (y : Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R)) :
    awayCoeff R I y ∈ laurentPart R I k ↔ y ∈ awayDegree R I k := by
  rw [awayDegree, AddSubgroup.mem_comap, mem_laurentPart, mem_degreePart]
  exact ⟨fun h a ha ↦ (h a ha).2, fun h a ha ↦ ⟨negSupp_subset_of_awayCoeff I y a ha, h a ha⟩⟩

lemma exists_awayCoeff_eq {I : Finset ι} {k : ℤ} (F : (ι →₀ ℤ) →₀ R)
    (hF : F ∈ laurentPart R I k) : ∃ y, awayCoeff R I y = F := by
  obtain ⟨m, p, h⟩ := exists_awayCoeff_mk_eq I F fun a ha ↦ (mem_laurentPart.mp hF a ha).1
  exact ⟨_, h⟩

/-- The monomials of `p` have degree `k + m · card I` iff the Laurent monomials of `p / X_I ^ m`
have degree `k`. -/
lemma awayCoeff_mk_mem_degreePart_iff (I : Finset ι) (k : ℤ) (p : MvPolynomial ι R) (m : ℕ) :
    awayCoeff R I (Localization.mk p ⟨(∏ j ∈ I, X j) ^ m, m, rfl⟩) ∈ degreePart R k ↔
      ∀ e, p.coeff e ≠ 0 → (e.degree : ℤ) = k + m * I.card := by
  rw [mem_degreePart]
  simp only [awayCoeff_apply, coeff_awayToLaurent_mk]
  constructor
  · intro h e he
    have := h (expInt e - m • oneI I) (by rwa [sub_add_cancel, coeff_toLaurent_expInt])
    rw [map_sub, map_nsmul, degree_oneI, degree_expInt, nsmul_eq_mul] at this
    linarith
  · intro h a ha
    by_cases hna : ∀ j, 0 ≤ (a + m • oneI I) j
    · obtain ⟨e, he⟩ := mem_range_expInt.mpr hna
      rw [← he, coeff_toLaurent_expInt] at ha
      have h₁ := h e ha
      have h₂ := congrArg Finsupp.degree he
      rw [degree_expInt, map_add, map_nsmul, degree_oneI, nsmul_eq_mul] at h₂
      linarith
    · exact absurd (coeff_toLaurent_eq_zero p hna) ha

/-- **Homogeneous elements of `S[1 / X_I]`**: `y` is homogeneous of degree `k` iff it is a
fraction `p / X_I ^ m` whose numerator has only monomials of degree `k + m · card I`. -/
lemma mem_awayDegree_iff {I : Finset ι} {k : ℤ}
    (y : Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R)) :
    y ∈ awayDegree R I k ↔ ∃ (m : ℕ) (p : MvPolynomial ι R),
      (∀ e, p.coeff e ≠ 0 → (e.degree : ℤ) = k + m * I.card) ∧
        y = Localization.mk p
          (⟨(∏ j ∈ I, X j) ^ m, m, rfl⟩ : Submonoid.powers (∏ j ∈ I, X j : MvPolynomial ι R)) := by
  rw [awayDegree, AddSubgroup.mem_comap]
  constructor
  · intro hy
    induction y using Localization.induction_on with | H y => ?_
    obtain ⟨p, ⟨_, m, rfl⟩⟩ := y
    exact ⟨m, p, (awayCoeff_mk_mem_degreePart_iff I k p m).mp hy, rfl⟩
  · rintro ⟨m, p, hp, rfl⟩
    exact (awayCoeff_mk_mem_degreePart_iff I k p m).mpr hp

lemma isHomogeneous_iff_forall_degree {p : MvPolynomial ι R} {n : ℕ} :
    p.IsHomogeneous n ↔ ∀ e, p.coeff e ≠ 0 → (e.degree : ℤ) = n := by
  have h (e : ι →₀ ℕ) : Finsupp.weight 1 e = e.degree := by
    rw [Finsupp.degree_eq_weight_one]
    rfl
  rw [IsHomogeneous, IsWeightedHomogeneous]
  refine ⟨fun hp e he ↦ ?_, fun hp e he ↦ ?_⟩
  · rw [← h, hp he]
  · rw [h]
    exact_mod_cast hp e he

lemma isUnit_algebraMap_prod_X {I J : Finset ι} (h : I ⊆ J) :
    IsUnit (algebraMap (MvPolynomial ι R) (Localization.Away (∏ j ∈ J, X j : MvPolynomial ι R))
      (∏ j ∈ I, X j)) :=
  isUnit_of_dvd_unit (map_dvd _ (Finset.prod_dvd_prod_of_subset _ _ _ h))
    (IsLocalization.Away.algebraMap_isUnit _)

variable (R) in
/-- The restriction `S[1 / X_I] → S[1 / X_J]` for `I ⊆ J`. -/
noncomputable def awayRestr {I J : Finset ι} (h : I ⊆ J) :
    Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R) →+*
      Localization.Away (∏ j ∈ J, X j : MvPolynomial ι R) :=
  Localization.awayLift (algebraMap _ _) _ (isUnit_algebraMap_prod_X h)

lemma awayCoeff_awayRestr {I J : Finset ι} (h : I ⊆ J)
    (y : Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R)) :
    awayCoeff R J (awayRestr R h y) = awayCoeff R I y :=
  awayCoeff_comp (awayRestr R h) (IsLocalization.Away.lift_comp _ (isUnit_algebraMap_prod_X h)) y

lemma awayRestr_mem_awayDegree {I J : Finset ι} (h : I ⊆ J) {k : ℤ}
    {y : Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R)} (hy : y ∈ awayDegree R I k) :
    awayRestr R h y ∈ awayDegree R J k := by
  rw [awayDegree, AddSubgroup.mem_comap, awayCoeff_awayRestr]
  exact hy

lemma algebraMap_mem_awayDegree (I : Finset ι) {n : ℕ} {p : MvPolynomial ι R}
    (hp : p.IsHomogeneous n) :
    algebraMap _ (Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R)) p ∈ awayDegree R I n := by
  rw [awayDegree, AddSubgroup.mem_comap, mem_degreePart]
  intro a ha
  rw [awayCoeff_apply, awayToLaurent_algebraMap] at ha
  by_cases hna : ∀ j, 0 ≤ a j
  · obtain ⟨e, rfl⟩ := mem_range_expInt.mpr hna
    rw [coeff_toLaurent_expInt] at ha
    rw [degree_expInt]
    exact isHomogeneous_iff_forall_degree.mp hp e ha
  · exact absurd (coeff_toLaurent_eq_zero p hna) ha

/-- A Laurent coefficient family of degree `n` without negative exponents is the coefficient
family of a homogeneous polynomial of degree `n`. -/
lemma exists_toLaurent_coeff_eq {n : ℕ} (F : (ι →₀ ℤ) →₀ R) (hF : F ∈ laurentPart R ∅ n) :
    ∃ p : MvPolynomial ι R, p.IsHomogeneous n ∧ (toLaurent ι R p).coeff = F := by
  have hF' (a : ι →₀ ℤ) (ha : F a ≠ 0) : ∀ j, 0 ≤ a j := fun j ↦
    not_lt.mp fun hj ↦ by simpa using (mem_laurentPart.mp hF a ha).1 (mem_negSupp.mpr hj)
  obtain ⟨p, hp⟩ := exists_toLaurent_eq (ofCoeff F) hF'
  refine ⟨p, isHomogeneous_iff_forall_degree.mpr fun e he ↦ ?_, by rw [hp]⟩
  rw [← coeff_toLaurent_expInt, hp] at he
  rw [← degree_expInt]
  exact (mem_laurentPart.mp hF _ he).2

/-! ### The degree-zero part `HomogeneousLocalization.Away` -/

section HomogeneousLocalization

open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R) in
/-- The Laurent coefficients of an element of `S_(X_I) = HomogeneousLocalization.Away 𝒜 X_I`,
the degree-zero part of `S[1 / X_I]`. -/
noncomputable def homAwayCoeff (I : Finset ι) :
    Away (homogeneousSubmodule ι R) (∏ j ∈ I, X j) →+ ((ι →₀ ℤ) →₀ R) :=
  (awayCoeff R I).comp (algebraMap (Away (homogeneousSubmodule ι R) (∏ j ∈ I, X j))
    (Localization.Away (∏ j ∈ I, X j : MvPolynomial ι R))).toAddMonoidHom

lemma homAwayCoeff_apply (I : Finset ι) (y : Away (homogeneousSubmodule ι R) (∏ j ∈ I, X j)) :
    homAwayCoeff R I y = awayCoeff R I y.val :=
  rfl

lemma homAwayCoeff_injective (I : Finset ι) : Function.Injective (homAwayCoeff R I) :=
  (awayCoeff_injective I).comp (val_injective _)

lemma prod_X_mem (I : Finset ι) :
    (∏ j ∈ I, X j : MvPolynomial ι R) ∈ homogeneousSubmodule ι R I.card := by
  simpa using SetLike.prod_mem_graded (homogeneousSubmodule ι R) (fun _ ↦ 1) (fun j ↦ X j)
    (fun j _ ↦ isHomogeneous_X R j)

lemma homAwayCoeff_mem_laurentPart (I : Finset ι)
    (y : Away (homogeneousSubmodule ι R) (∏ j ∈ I, X j)) :
    homAwayCoeff R I y ∈ laurentPart R I 0 := by
  obtain ⟨m, p, hp, rfl⟩ := Away.mk_surjective _ (prod_X_mem I) y
  rw [homAwayCoeff_apply, awayCoeff_mem_laurentPart_iff, mem_awayDegree_iff]
  refine ⟨m, p, fun e he ↦ ?_, by simp⟩
  rw [isHomogeneous_iff_forall_degree.mp hp e he]
  simp

lemma exists_homAwayCoeff_eq (I : Finset ι) (F : (ι →₀ ℤ) →₀ R) (hF : F ∈ laurentPart R I 0) :
    ∃ y, homAwayCoeff R I y = F := by
  obtain ⟨z, rfl⟩ := exists_awayCoeff_eq F hF
  obtain ⟨m, p, hp, rfl⟩ := (mem_awayDegree_iff z).mp ((awayCoeff_mem_laurentPart_iff z).mp hF)
  refine ⟨Away.mk _ (prod_X_mem I) m p (isHomogeneous_iff_forall_degree.mpr fun e he ↦ ?_), ?_⟩
  · rw [hp e he]
    simp
  · rw [homAwayCoeff_apply, Away.val_mk]

variable [DecidableEq ι]

/-- The restriction `S_(X_I) → S_(X_J)` for `I ⊆ J`. -/
noncomputable def homAwayRestr {I J : Finset ι} (h : I ⊆ J) :
    Away (homogeneousSubmodule ι R) (∏ j ∈ I, X j) →+*
      Away (homogeneousSubmodule ι R) (∏ j ∈ J, X j) :=
  awayMap (homogeneousSubmodule ι R) (prod_X_mem (J \ I))
    (by rw [mul_comm, Finset.prod_sdiff h])

lemma homAwayCoeff_homAwayRestr {I J : Finset ι} (h : I ⊆ J)
    (y : Away (homogeneousSubmodule ι R) (∏ j ∈ I, X j)) :
    homAwayCoeff R J (homAwayRestr h y) = homAwayCoeff R I y := by
  rw [homAwayCoeff_apply, homAwayCoeff_apply, homAwayRestr, val_awayMap,
    awayCoeff_comp _ (IsLocalization.Away.lift_comp _ _)]

end HomogeneousLocalization

end MvPolynomial

end
