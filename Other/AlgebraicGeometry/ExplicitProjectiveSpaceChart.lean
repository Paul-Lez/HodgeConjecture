/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Coordinate rings of standard projective-space charts

For any finite set of homogeneous coordinates and a chosen nonzero coordinate, the
degree-zero localization is explicitly a polynomial ring in all the other coordinate ratios.
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.ProjectiveSpaceChart

universe u

variable (R : Type u) [CommRing R] {σ : Type u} (i : σ)

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The homogeneous grading on the coordinate ring of the projective space. -/
abbrev grading := homogeneousSubmodule σ R

/-- The coordinate ring of the standard chart where `X_i` is nonzero. -/
abbrev Ring := HomogeneousLocalization.Away (grading R (σ := σ)) (X i)

/-- The coordinate ratio `X_j / X_i`. -/
def ratio (j : σ) : Ring R i :=
  Away.mk (grading R (σ := σ)) (isHomogeneous_X R i) 1 (X j)
    (by simpa using isHomogeneous_X R j)

@[simp]
theorem ratio_self : ratio R i i = 1 := by
  rw [HomogeneousLocalization.ext_iff_val]
  simp [ratio, Away.val_mk]

/-- Constants in the affine chart ring. -/
def coefficient : R →+* Ring R i :=
  (fromZeroRingHom (grading R (σ := σ)) (.powers (X i))).comp
    (ProjectiveSpace.degreeZeroEquiv σ R).symm.toRingHom

variable [DecidableEq σ]

/-- Homogeneous coordinates normalized to make the chosen coordinate one. -/
def coordinateValues (j : σ) : MvPolynomial {j : σ // j ≠ i} R :=
  if h : j = i then 1 else X ⟨j, h⟩

@[simp]
theorem coordinateValues_self : coordinateValues R i i = 1 := by
  simp [coordinateValues]

@[simp]
theorem coordinateValues_other (j : {j : σ // j ≠ i}) :
    coordinateValues R i j.1 = X j := by
  simp [coordinateValues, j.2]

/-- Substitute one for the chart coordinate and retain the remaining coordinates. -/
def dehomogenize : MvPolynomial σ R →+* MvPolynomial {j : σ // j ≠ i} R :=
  eval₂Hom C (coordinateValues R i)

@[simp]
theorem dehomogenize_X (j : σ) :
    dehomogenize R i (X j) = coordinateValues R i j := by
  simp [dehomogenize, coordinateValues]

/-- A homogeneous fraction on the chart gives a polynomial in the coordinate ratios. -/
def toPolynomial : Ring R i →+* MvPolynomial {j : σ // j ≠ i} R :=
  (Localization.awayLift (dehomogenize R i) (X i) (by simp)).comp
    (algebraMap (Ring R i) (Localization.Away (X i)))

/-- Evaluation of a homogeneous degree-`d` fraction is dehomogenization of its numerator. -/
theorem toPolynomial_mk (d : ℕ) (f : MvPolynomial σ R)
    (hf : f ∈ grading R (σ := σ) d) :
    toPolynomial R i (Away.mk (grading R (σ := σ)) (isHomogeneous_X R i) d f
      (by simpa using hf)) = dehomogenize R i f := by
  change Localization.awayLift (dehomogenize R i) (X i) (by simp)
    (Localization.mk f ⟨X i ^ d, ⟨d, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
  simp

@[simp]
theorem toPolynomial_ratio (j : σ) :
    toPolynomial R i (ratio R i j) = coordinateValues R i j := by
  rw [ratio, toPolynomial_mk R i 1 _ (isHomogeneous_X R j), dehomogenize_X]

@[simp]
theorem toPolynomial_coefficient (r : R) :
    toPolynomial R i (coefficient R i r) = C r := by
  change Localization.awayLift (dehomogenize R i) (X i) (by simp)
    (Localization.mk (C r) ⟨X i ^ 0, ⟨0, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
  simp [dehomogenize]

/-- A polynomial in the remaining variables gives a regular function on the standard chart. -/
def fromPolynomial : MvPolynomial {j : σ // j ≠ i} R →+* Ring R i :=
  eval₂Hom (coefficient R i) (fun j ↦ ratio R i j.1)

omit [DecidableEq σ] in
@[simp]
theorem fromPolynomial_C (r : R) : fromPolynomial R i (C r) = coefficient R i r := by
  simp [fromPolynomial]

omit [DecidableEq σ] in
@[simp]
theorem fromPolynomial_X (j : {j : σ // j ≠ i}) :
    fromPolynomial R i (X j) = ratio R i j.1 := by
  simp [fromPolynomial]

variable [Fintype σ]

omit [DecidableEq σ] [Fintype σ] in
private theorem adjoin_coordinates_eq_top :
    Algebra.adjoin (grading R (σ := σ) 0) (Set.range (fun j : σ ↦ (X j :
      MvPolynomial σ R))) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
      exact (Algebra.adjoin (grading R (σ := σ) 0)
        (Set.range (fun j : σ ↦ (X j : MvPolynomial σ R)))).algebraMap_mem
          ⟨C a, isHomogeneous_C _ _⟩
  | add p q hp hq => exact add_mem hp hq
  | mul_X p j hp =>
      exact mul_mem hp (Algebra.subset_adjoin ⟨j, by simp⟩)

private theorem mk_prod_eq (a : ℕ) (ai : σ → ℕ) (hai : ∑ j, ai j = a) :
    Away.mk (grading R (σ := σ)) (isHomogeneous_X R i) a
      (∏ j, X j ^ ai j)
      (by
        convert SetLike.prod_pow_mem_graded (grading R (σ := σ)) (fun _ ↦ (1 : ℕ))
          (fun j ↦ X j) ai (F := Finset.univ) (fun j _ ↦ isHomogeneous_X R j) using 1
        simp [hai]) = ∏ j, ratio R i j ^ ai j := by
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk]
  rw [show (∏ j, ratio R i j ^ ai j).val = ∏ j, (ratio R i j).val ^ ai j by
    induction (Finset.univ : Finset σ) using Finset.induction with
    | empty => exact HomogeneousLocalization.val_one
    | @insert j s hjs ih =>
        rw [Finset.prod_insert hjs, Finset.prod_insert hjs,
          HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, ih]]
  simp only [ratio, Away.val_mk]
  simp_rw [Localization.mk_pow]
  rw [Localization.mk_prod (Finset.univ : Finset σ)]
  apply Localization.mk_eq_mk_iff.mpr
  rw [Localization.r_iff_exists]
  use 1
  simp only [Submonoid.coe_one, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, one_mul]
  congr 1
  simp [Finset.prod_pow_eq_pow_sum, hai]

/-- The coordinate ratios generate the standard chart over the degree-zero coefficient ring. -/
theorem adjoin_ratios_eq_top : Algebra.adjoin (grading R (σ := σ) 0) (Set.range (ratio R i)) = ⊤ := by
  apply top_unique
  rw [← Away.adjoin_mk_prod_pow_eq_top (isHomogeneous_X R i) σ
    (fun j ↦ X j) (adjoin_coordinates_eq_top R (σ := σ)) (fun _ ↦ 1)
    (fun j ↦ isHomogeneous_X R j)]
  apply Algebra.adjoin_le
  rintro _ ⟨a, ai, hai, _, rfl⟩
  rw [mk_prod_eq R i a ai (by simpa using hai)]
  apply prod_mem
  intro j _
  apply pow_mem
  exact Algebra.subset_adjoin ⟨j, rfl⟩

/-- A ring homomorphism out of the chart is determined by constants and coordinate ratios. -/
theorem ringHom_ext {S : Type*} [CommRing S] (f g : Ring R i →+* S)
    (hc : ∀ r, f (coefficient R i r) = g (coefficient R i r))
    (hv : ∀ j, f (ratio R i j) = g (ratio R i j)) : f = g := by
  apply RingHom.ext
  intro x
  have hx : x ∈ Algebra.adjoin (grading R (σ := σ) 0) (Set.range (ratio R i)) := by
    rw [adjoin_ratios_eq_top]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hv j
  | algebraMap r =>
      obtain ⟨r, rfl⟩ := (ProjectiveSpace.degreeZeroEquiv σ R).symm.surjective r
      exact hc r
  | add x y _ _ hx hy => simp [hx, hy]
  | mul x y _ _ hx hy => simp [hx, hy]

private theorem fromPolynomial_comp_toPolynomial :
    (fromPolynomial R i).comp (toPolynomial R i) = RingHom.id _ := by
  apply ringHom_ext
  · intro r
    simp
  · intro j
    by_cases h : j = i
    · subst j; simp
    · simp [coordinateValues, h] 

omit [Fintype σ] in
private theorem toPolynomial_comp_fromPolynomial :
    (toPolynomial R i).comp (fromPolynomial R i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro j
    simp [coordinateValues, j.2]

/-- The coordinate ring of the standard projective-space chart is a polynomial ring in the
remaining coordinate ratios. -/
def equiv : Ring R i ≃+* MvPolynomial {j : σ // j ≠ i} R where
  toFun := toPolynomial R i
  invFun := fromPolynomial R i
  left_inv x := by exact DFunLike.congr_fun (fromPolynomial_comp_toPolynomial R i) x
  right_inv x := by exact DFunLike.congr_fun (toPolynomial_comp_fromPolynomial R i) x
  map_add' := (toPolynomial R i).map_add
  map_mul' := (toPolynomial R i).map_mul

instance : Algebra R (Ring R i) := (coefficient R i).toAlgebra

/-- The chart-coordinate equivalence respects the coefficient ring. -/
def algEquiv : Ring R i ≃ₐ[R] MvPolynomial {j : σ // j ≠ i} R where
  __ := equiv R i
  commutes' := toPolynomial_coefficient R i

open CategoryTheory in
/-- The corresponding actual standard open subscheme of projective space is the spectrum
of the polynomial ring in the remaining coordinate ratios. -/
def basicOpenIso : (Proj.basicOpen (grading R (σ := σ)) (X i)).toScheme ≅
    Spec (CommRingCat.of (MvPolynomial {j : σ // j ≠ i} R)) :=
  Proj.basicOpenIsoSpec (grading R (σ := σ)) (X i) (isHomogeneous_X R i) zero_lt_one ≪≫
    Scheme.Spec.mapIso (equiv R i).symm.toCommRingCatIso.op

open CategoryTheory in
/-- The polynomial chart map into the actual projective spectrum. -/
def chartMap : Spec (CommRingCat.of (MvPolynomial {j : σ // j ≠ i} R)) ⟶ Proj (grading R (σ := σ)) :=
  (basicOpenIso R i).inv ≫ (Proj.basicOpen (grading R (σ := σ)) (X i)).ι

open CategoryTheory in
theorem chartMap_eq : chartMap R i =
    Spec.map (CommRingCat.ofHom (toPolynomial R i)) ≫
      Proj.awayι (grading R (σ := σ)) (X i) (isHomogeneous_X R i) zero_lt_one := by
  rfl

/-- A homogeneous equation on projective space becomes its dehomogenization on this chart. -/
theorem chartMap_preimage_basicOpen (d : ℕ) (f : MvPolynomial σ R)
    (hf : f.IsHomogeneous d) (hd : 0 < d) :
    chartMap R i ⁻¹ᵁ Proj.basicOpen (grading R (σ := σ)) f =
      PrimeSpectrum.basicOpen (dehomogenize R i f) := by
  rw [chartMap_eq, Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen (grading R (σ := σ)) (isHomogeneous_X R i)
    zero_lt_one hf hd]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  simp only [CommRingCat.hom_ofHom, HomogeneousLocalization.Away.isLocalizationElem, pow_one]
  exact toPolynomial_mk R i d f hf

open CategoryTheory in
/-- The structure morphism of the projective spectrum over its coefficient ring. -/
def toBase : Proj (grading R (σ := σ)) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (grading R (σ := σ)) ≫
    Spec.map (CommRingCat.ofHom (ProjectiveSpace.degreeZeroEquiv σ R).symm.toRingHom)

open CategoryTheory in
/-- The polynomial chart map respects the coefficient ring. -/
@[reassoc] theorem chartMap_toBase :
    chartMap R i ≫ toBase R (σ := σ) = Spec.map (CommRingCat.ofHom C) := by
  simp only [chartMap_eq, toBase, Category.assoc, Proj.awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact toPolynomial_coefficient R i r

open CategoryTheory in
/-- The standard affine chart isomorphism respects the structure map. -/
@[reassoc] theorem basicOpenIso_hom_toBase :
    (basicOpenIso R i).hom ≫ Spec.map (CommRingCat.ofHom C) =
      (Proj.basicOpen (grading R (σ := σ)) (X i)).ι ≫ toBase R (σ := σ) := by
  rw [← chartMap_toBase R i]
  simp only [chartMap, Category.assoc, Iso.hom_inv_id_assoc]

end AlgebraicGeometry.ProjectiveSpaceChart
