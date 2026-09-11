/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Other.AlgebraicGeometry.MvPolynomialStandardSmooth

/-!
# The standard affine charts of `Proj` of a polynomial ring

The degree-zero part of the localization of `R[X₀, …, X_N]` away from the variable `Xᵢ` is a
polynomial ring in `N` variables, namely the ratios `X_{i.succAbove j} / Xᵢ`.  This is the ring
level statement that the standard affine chart `D₊(Xᵢ) ⊆ ℙᴺ_R` is an affine space `𝔸ᴺ_R`, and it
is the missing local model for smoothness of projective space.
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization

namespace Other.ProjectiveChart

/-! ### Homogeneous polynomials under rescaling of the variables -/

/-- Evaluating a homogeneous polynomial of degree `n` at `t • g` scales the value by `tⁿ`. -/
theorem eval₂_mul_of_isHomogeneous {R B σ : Type*} [CommSemiring R] [CommSemiring B]
    [Fintype σ] [DecidableEq σ] {a : MvPolynomial σ R} {n : ℕ} (ha : a.IsHomogeneous n)
    (f : R →+* B) (g : σ → B) (t : B) :
    eval₂ f (fun l ↦ t * g l) a = t ^ n * eval₂ f g a := by
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdeg : ∑ l : σ, d l = n := by
    have h := ha.degree_eq_sum_deg_support hd
    rw [h]
    exact (Finset.sum_subset (Finset.subset_univ _)
      fun l _ hl ↦ Finsupp.notMem_support_iff.mp hl).symm
  have hprod : ∏ l : σ, (t * g l) ^ (d l) = t ^ n * ∏ l : σ, g l ^ (d l) := by
    simp only [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  rw [hprod]
  ring

/-! ### Setup -/

section Chart

variable (R : Type*) [CommRing R] (N : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Constants are homogeneous of degree zero. -/
theorem C_mem_zero (r : R) :
    (C r : MvPolynomial (Fin (N + 1)) R) ∈ homogeneousSubmodule (Fin (N + 1)) R 0 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_C _ r)

/-- The constants, as a ring map into the degree-zero homogeneous part. -/
def cZero : R →+* (homogeneousSubmodule (Fin (N + 1)) R 0) where
  toFun r := ⟨C r, C_mem_zero R N r⟩
  map_one' := Subtype.ext (map_one C)
  map_mul' _ _ := Subtype.ext (map_mul C _ _)
  map_zero' := Subtype.ext (map_zero C)
  map_add' _ _ := Subtype.ext (map_add C _ _)

variable {N}

/-- `Xᵢ` is homogeneous of degree one. -/
theorem X_mem_one (i : Fin (N + 1)) :
    (X i : MvPolynomial (Fin (N + 1)) R) ∈ homogeneousSubmodule (Fin (N + 1)) R 1 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X R i)

theorem X_mem_smul (j : Fin (N + 1)) :
    (X j : MvPolynomial (Fin (N + 1)) R) ∈
      homogeneousSubmodule (Fin (N + 1)) R (1 • 1) := by
  simpa using X_mem_one R j

/-- The `j`-th affine coordinate of the `i`-th standard chart, as an element of the degree-zero
homogeneous localization away from `Xᵢ`. -/
def gen (i : Fin (N + 1)) (j : Fin N) :
    Away (homogeneousSubmodule (Fin (N + 1)) R) (X i) :=
  Away.mk _ (X_mem_one R i) 1 (X (i.succAbove j)) (X_mem_smul R (i.succAbove j))

/-- The structure map of `A⁰_{Xᵢ}` as an `R`-algebra. -/
def cR (i : Fin (N + 1)) : R →+* Away (homogeneousSubmodule (Fin (N + 1)) R) (X i) :=
  (fromZeroRingHom _ _).comp (cZero R N)

/-- The comparison map from the polynomial ring in `N` affine coordinates. -/
def chartHom (i : Fin (N + 1)) :
    MvPolynomial (Fin N) R →+* Away (homogeneousSubmodule (Fin (N + 1)) R) (X i) :=
  eval₂Hom (cR R i) (gen R i)

/-- Dehomogenisation: substitute `Xᵢ ↦ 1` and `X_{i.succAbove j} ↦ Yⱼ`. -/
def deh (i : Fin (N + 1)) :
    MvPolynomial (Fin (N + 1)) R →+* MvPolynomial (Fin N) R :=
  eval₂Hom C (Fin.insertNth i (1 : MvPolynomial (Fin N) R) X)

@[simp]
theorem deh_C (i : Fin (N + 1)) (r : R) : deh R i (C r) = C r := by
  simp [deh]

@[simp]
theorem deh_X_self (i : Fin (N + 1)) : deh R i (X i) = 1 := by
  simp [deh]

@[simp]
theorem deh_X_succAbove (i : Fin (N + 1)) (j : Fin N) :
    deh R i (X (i.succAbove j)) = X j := by
  simp [deh]

end Chart

/-! ### The chart isomorphism -/

section Main

variable (R : Type*) [CommRing R] {N : ℕ} (i : Fin (N + 1))

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The localization of the homogeneous coordinate ring away from `Xᵢ`. -/
abbrev Loc : Type _ := Localization.Away (X i : MvPolynomial (Fin (N + 1)) R)

/-- The inverse of `Xᵢ` in the localization away from `Xᵢ`. -/
def invX : Loc R i :=
  IsLocalization.Away.invSelf (S := Loc R i) (X i : MvPolynomial (Fin (N + 1)) R)

theorem algebraMap_X_mul_invX :
    algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R i) (X i) * invX R i = 1 :=
  IsLocalization.Away.mul_invSelf _

/-- The substitution `X l ↦ X l / Xᵢ`, as a ring map to the localization. -/
def theta : MvPolynomial (Fin (N + 1)) R →+* Loc R i :=
  eval₂Hom ((algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R i)).comp
      (C : R →+* MvPolynomial (Fin (N + 1)) R))
    fun l ↦ invX R i * algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R i) (X l)

theorem eval₂Hom_algebraMap :
    (eval₂Hom ((algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R i)).comp
        (C : R →+* MvPolynomial (Fin (N + 1)) R))
      fun l ↦ algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R i) (X l)) =
      algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R i) := by
  apply MvPolynomial.ringHom_ext <;> simp

/-- On a homogeneous polynomial of degree `n`, the substitution `X ↦ X / Xᵢ` divides by
`Xᵢ ^ n`. -/
theorem theta_of_isHomogeneous {a : MvPolynomial (Fin (N + 1)) R} {n : ℕ}
    (ha : a.IsHomogeneous n) :
    theta R i a = invX R i ^ n * algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R i) a := by
  have h := eval₂_mul_of_isHomogeneous ha
    ((algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R i)).comp
      (C : R →+* MvPolynomial (Fin (N + 1)) R))
    (fun l ↦ algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R i) (X l)) (invX R i)
  have h2 := congrArg (fun f : MvPolynomial (Fin (N + 1)) R →+* Loc R i ↦ f a)
    (eval₂Hom_algebraMap R i)
  simp only [coe_eval₂Hom] at h2
  rw [theta, coe_eval₂Hom, h, h2]

@[simp]
theorem theta_X (l : Fin (N + 1)) :
    theta R i (X l) = invX R i * algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R i) (X l) := by
  simp [theta]

@[simp]
theorem theta_C (r : R) :
    theta R i (C r) = algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R i) (C r) := by
  simp [theta]

theorem theta_X_self : theta R i (X i) = 1 := by
  rw [theta_X, mul_comm]
  exact algebraMap_X_mul_invX R i

theorem val_cR (r : R) :
    (cR R i r).val = algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R i) (C r) := by
  rw [← Localization.mk_one_eq_algebraMap]
  rfl

theorem val_gen (j : Fin N) :
    (gen R i j).val =
      Localization.mk (X (i.succAbove j) : MvPolynomial (Fin (N + 1)) R)
        (⟨(X i : MvPolynomial (Fin (N + 1)) R) ^ 1, ⟨1, rfl⟩⟩ :
          Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) R)) := rfl

theorem theta_X_succAbove (j : Fin N) :
    theta R i (X (i.succAbove j)) = (gen R i j).val := by
  rw [theta_X, val_gen, invX, IsLocalization.Away.invSelf, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_eq_mk', ← IsLocalization.mk'_mul]
  congr 1
  · rw [one_mul]
  · exact Subtype.ext (by simp)

/-! ### Surjectivity -/

theorem algebraMap_chartHom_deh (a : MvPolynomial (Fin (N + 1)) R) :
    algebraMap (Away (homogeneousSubmodule (Fin (N + 1)) R) (X i)) (Loc R i)
        (chartHom R i (deh R i a)) = theta R i a := by
  have key : ((algebraMap (Away (homogeneousSubmodule (Fin (N + 1)) R) (X i)) (Loc R i)).comp
      (chartHom R i)).comp (deh R i) = theta R i := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [chartHom, val_cR]
    · intro l
      refine Fin.succAboveCases i ?_ ?_ l
      · simp only [RingHom.coe_comp, Function.comp_apply, deh_X_self, map_one]
        exact (theta_X_self R i).symm
      · intro j
        simp only [RingHom.coe_comp, Function.comp_apply, deh_X_succAbove, chartHom,
          eval₂Hom_X', HomogeneousLocalization.algebraMap_apply]
        exact (theta_X_succAbove R i j).symm
  exact congrArg (fun f : MvPolynomial (Fin (N + 1)) R →+* Loc R i ↦ f a) key

theorem chartHom_deh_eq {a : MvPolynomial (Fin (N + 1)) R} {n : ℕ}
    (ha : a ∈ homogeneousSubmodule (Fin (N + 1)) R (n • 1)) :
    chartHom R i (deh R i a) = Away.mk _ (X_mem_one R i) n a ha := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk]
  have hhom : a.IsHomogeneous n := by
    have h := (mem_homogeneousSubmodule _ _).1 ha
    simpa using h
  have h1 := algebraMap_chartHom_deh R i a
  rw [HomogeneousLocalization.algebraMap_apply] at h1
  rw [h1, theta_of_isHomogeneous R i hhom]
  have hinv : invX R i ^ n = Localization.mk (1 : MvPolynomial (Fin (N + 1)) R)
      ((⟨(X i : MvPolynomial (Fin (N + 1)) R), Submonoid.mem_powers _⟩ :
        Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) R)) ^ n) := by
    rw [invX, IsLocalization.Away.invSelf, ← Localization.mk_eq_mk', Localization.mk_pow, one_pow]
  rw [hinv, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, mul_one]
  congr 1

theorem chartHom_surjective : Function.Surjective (chartHom R i) := by
  intro z
  obtain ⟨n, a, ha, hz⟩ := Away.mk_surjective _ (X_mem_one R i) z
  exact ⟨deh R i a, by rw [chartHom_deh_eq R i ha]; exact hz⟩

/-! ### Injectivity -/

/-- Dehomogenisation extends to the localization because `Xᵢ` is sent to `1`. -/
def dehLift : Loc R i →+* MvPolynomial (Fin N) R :=
  Localization.awayLift (deh R i) (X i) (by rw [deh_X_self]; exact isUnit_one)

/-- The candidate inverse of the chart map. -/
def chartInv : Away (homogeneousSubmodule (Fin (N + 1)) R) (X i) →+*
    MvPolynomial (Fin N) R :=
  (dehLift R i).comp (algebraMap _ (Loc R i))

theorem chartInv_chartHom : (chartInv R i).comp (chartHom R i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    show dehLift R i (algebraMap _ (Loc R i) (chartHom R i (C r))) = C r
    rw [show chartHom R i (C r) = cR R i r from by simp [chartHom],
      HomogeneousLocalization.algebraMap_apply, val_cR, dehLift]
    simp [Localization.awayLift, IsLocalization.Away.lift]
  · intro j
    show dehLift R i (algebraMap _ (Loc R i) (chartHom R i (X j))) = X j
    rw [show chartHom R i (X j) = gen R i j from by simp [chartHom],
      HomogeneousLocalization.algebraMap_apply, val_gen, dehLift]
    rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
    simp

theorem chartHom_injective : Function.Injective (chartHom R i) := by
  have h : Function.LeftInverse (chartInv R i) (chartHom R i) := fun a ↦ by
    have hc := congrArg (fun f : MvPolynomial (Fin N) R →+* MvPolynomial (Fin N) R ↦ f a)
      (chartInv_chartHom R i)
    simpa using hc
  exact h.injective

/-! ### The chart isomorphism -/

/-- **The standard affine chart of `Proj` of a polynomial ring.**  The degree-zero part of the
localization of `R[X₀, …, X_N]` away from the variable `Xᵢ` is a polynomial ring in `N`
variables, the affine coordinates being the ratios `X_{i.succAbove j} / Xᵢ`.

This is the ring-theoretic form of the statement that the standard chart `D₊(Xᵢ) ⊆ ℙᴺ_R` is an
affine space `𝔸ᴺ_R`. -/
def chartRingEquiv : MvPolynomial (Fin N) R ≃+*
    Away (homogeneousSubmodule (Fin (N + 1)) R) (X i) :=
  RingEquiv.ofBijective (chartHom R i) ⟨chartHom_injective R i, chartHom_surjective R i⟩

@[simp]
theorem chartRingEquiv_apply (P : MvPolynomial (Fin N) R) :
    chartRingEquiv R i P = chartHom R i P := rfl

@[simp]
theorem chartHom_C (r : R) : chartHom R i (C r) = cR R i r := by
  simp [chartHom]

@[simp]
theorem chartHom_X (j : Fin N) : chartHom R i (X j) = gen R i j := by
  simp [chartHom]

/-- The chart isomorphism is compatible with the structure map from `R`. -/
theorem chartRingEquiv_comp_C :
    (chartRingEquiv R i : MvPolynomial (Fin N) R →+*
        Away (homogeneousSubmodule (Fin (N + 1)) R) (X i)).comp
      (C : R →+* MvPolynomial (Fin N) R) = cR R i := by
  ext r
  simp

/-! ### Standard smoothness of the chart -/

/-- The degree-zero homogeneous part of `R[X₀, …, X_N]` is `R`. -/
def cZeroEquiv : R ≃+* (homogeneousSubmodule (Fin (N + 1)) R 0) where
  toFun := cZero R N
  invFun a := coeff 0 (a : MvPolynomial (Fin (N + 1)) R)
  left_inv r := by simp [cZero]
  right_inv a := by
    apply Subtype.ext
    have hhom : (a : MvPolynomial (Fin (N + 1)) R).IsHomogeneous 0 :=
      (mem_homogeneousSubmodule _ _).1 a.2
    have hdeg : (a : MvPolynomial (Fin (N + 1)) R).totalDegree = 0 :=
      Nat.le_zero.mp hhom.totalDegree_le
    exact (totalDegree_eq_zero_iff_eq_C.mp hdeg).symm
  map_mul' _ _ := map_mul (cZero R N) _ _
  map_add' _ _ := map_add (cZero R N) _ _

theorem fromZeroRingHom_eq :
    (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule (Fin (N + 1)) R)
        (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) R))) =
      ((chartRingEquiv R i : MvPolynomial (Fin N) R →+*
          Away (homogeneousSubmodule (Fin (N + 1)) R) (X i)).comp
        ((C : R →+* MvPolynomial (Fin N) R).comp
          ((cZeroEquiv (N := N) R).symm : (homogeneousSubmodule (Fin (N + 1)) R 0) →+* R))) := by
  refine RingHom.ext fun a ↦ ?_
  have key : chartHom R i (C ((cZeroEquiv (N := N) R).symm a)) =
      HomogeneousLocalization.fromZeroRingHom
        (homogeneousSubmodule (Fin (N + 1)) R)
        (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) R)) a := by
    rw [chartHom_C, cR, RingHom.comp_apply]
    congr 1
    exact (cZeroEquiv (N := N) R).apply_symm_apply a
  simpa using key.symm

/-- **The standard chart of `Proj` is standard smooth of relative dimension `N`.**  The structure
map from the degree-zero part to the degree-zero homogeneous localization away from `Xᵢ` is
standard smooth of relative dimension `N`. -/
theorem isStandardSmoothOfRelativeDimension_fromZeroRingHom :
    RingHom.IsStandardSmoothOfRelativeDimension N
      (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule (Fin (N + 1)) R)
        (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) R))) := by
  rw [fromZeroRingHom_eq]
  have hC : RingHom.IsStandardSmoothOfRelativeDimension N
      (C : R →+* MvPolynomial (Fin N) R) := by
    rw [show (C : R →+* MvPolynomial (Fin N) R) = algebraMap R (MvPolynomial (Fin N) R) from rfl,
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    infer_instance
  have hinner : RingHom.IsStandardSmoothOfRelativeDimension (N + 0)
      ((C : R →+* MvPolynomial (Fin N) R).comp
        ((cZeroEquiv (N := N) R).symm : (homogeneousSubmodule (Fin (N + 1)) R 0) →+* R)) :=
    hC.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv (cZeroEquiv (N := N) R).symm)
  have := (RingHom.IsStandardSmoothOfRelativeDimension.equiv
    (chartRingEquiv R i)).comp hinner
  simpa using this

end Main

end Other.ProjectiveChart
