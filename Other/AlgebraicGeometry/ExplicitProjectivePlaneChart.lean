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
# Coordinate rings of standard projective-plane charts

The degree-zero localization of `R[X₀,X₁,X₂]` at one coordinate is explicitly a polynomial
ring in the other two coordinate ratios. A permutation of the coordinates makes this construction
usable on every standard chart.
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.ProjectivePlaneChart

variable (R : Type*) [CommRing R] (e : Equiv.Perm (Fin 3))

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The homogeneous grading on the coordinate ring of the projective plane. -/
abbrev grading := homogeneousSubmodule (Fin 3) R

/-- The coordinate ring of the standard chart where `X_(e 2)` is nonzero. -/
abbrev Ring := HomogeneousLocalization.Away (grading R) (X (e 2))

/-- The coordinate ratio `X_(e j) / X_(e 2)`. -/
def ratio (j : Fin 3) : Ring R e :=
  Away.mk (grading R) (isHomogeneous_X R (e 2)) 1 (X (e j))
    (by simpa using isHomogeneous_X R (e j))

@[simp]
theorem ratio_two : ratio R e 2 = 1 := by
  rw [HomogeneousLocalization.ext_iff_val]
  simp [ratio, Away.val_mk]

/-- Constants in the affine chart ring. -/
def coefficient : R →+* Ring R e :=
  (fromZeroRingHom (grading R) (.powers (X (e 2)))).comp
    (ProjectiveSpace.degreeZeroEquiv (Fin 3) R).symm.toRingHom

/-- The values of the three homogeneous coordinates on the chart. -/
def coordinateValues : Fin 3 → MvPolynomial (Fin 2) R := ![X 0, X 1, 1] ∘ e.symm

/-- Substitute one for the chart coordinate and retain the other two coordinates. -/
def dehomogenize : MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 2) R :=
  eval₂Hom C (coordinateValues R e)

@[simp]
theorem dehomogenize_X (j : Fin 3) :
    dehomogenize R e (X (e j)) = ![X 0, X 1, 1] j := by
  simp [dehomogenize, coordinateValues]

/-- A homogeneous fraction on the chart gives a polynomial in the coordinate ratios. -/
def toPolynomial : Ring R e →+* MvPolynomial (Fin 2) R :=
  (Localization.awayLift (dehomogenize R e) (X (e 2)) (by simp)).comp
    (algebraMap (Ring R e) (Localization.Away (X (e 2))))

/-- Evaluation of a homogeneous degree-`d` fraction is dehomogenization of its numerator. -/
theorem toPolynomial_mk (d : ℕ) (f : MvPolynomial (Fin 3) R)
    (hf : f ∈ grading R d) :
    toPolynomial R e (Away.mk (grading R) (isHomogeneous_X R (e 2)) d f
      (by simpa using hf)) = dehomogenize R e f := by
  change Localization.awayLift (dehomogenize R e) (X (e 2)) (by simp)
    (Localization.mk f ⟨X (e 2) ^ d, ⟨d, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
  simp

@[simp]
theorem toPolynomial_ratio (j : Fin 3) :
    toPolynomial R e (ratio R e j) = ![X 0, X 1, 1] j := by
  rw [ratio, toPolynomial_mk R e 1 _ (isHomogeneous_X R (e j)), dehomogenize_X]

@[simp]
theorem toPolynomial_coefficient (r : R) :
    toPolynomial R e (coefficient R e r) = C r := by
  change Localization.awayLift (dehomogenize R e) (X (e 2)) (by simp)
    (Localization.mk (C r) ⟨X (e 2) ^ 0, ⟨0, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
  simp [dehomogenize]

/-- A polynomial in two variables gives a regular function on the standard chart. -/
def fromPolynomial : MvPolynomial (Fin 2) R →+* Ring R e :=
  eval₂Hom (coefficient R e) (fun j ↦ ratio R e j.castSucc)

@[simp]
theorem fromPolynomial_C (r : R) : fromPolynomial R e (C r) = coefficient R e r := by
  simp [fromPolynomial]

@[simp]
theorem fromPolynomial_X (j : Fin 2) :
    fromPolynomial R e (X j) = ratio R e j.castSucc := by
  simp [fromPolynomial]

private theorem adjoin_coordinates_eq_top :
    Algebra.adjoin (grading R 0) (Set.range (fun j : Fin 3 ↦ (X (e j) :
      MvPolynomial (Fin 3) R))) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
      exact (Algebra.adjoin (grading R 0)
        (Set.range (fun j : Fin 3 ↦ (X (e j) : MvPolynomial (Fin 3) R)))).algebraMap_mem
          ⟨C a, isHomogeneous_C _ _⟩
  | add p q hp hq => exact add_mem hp hq
  | mul_X p j hp =>
      exact mul_mem hp (Algebra.subset_adjoin ⟨e.symm j, by simp⟩)

private theorem mk_prod_eq (a : ℕ) (ai : Fin 3 → ℕ) (hai : ∑ j, ai j = a) :
    Away.mk (grading R) (isHomogeneous_X R (e 2)) a
      (∏ j, X (e j) ^ ai j)
      (by
        convert SetLike.prod_pow_mem_graded (grading R) (fun _ ↦ (1 : ℕ))
          (fun j ↦ X (e j)) ai (F := Finset.univ) (fun j _ ↦ isHomogeneous_X R (e j)) using 1
        simp [hai]) = ∏ j, ratio R e j ^ ai j := by
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk]
  rw [show (∏ j, ratio R e j ^ ai j).val = ∏ j, (ratio R e j).val ^ ai j by
    induction (Finset.univ : Finset (Fin 3)) using Finset.induction with
    | empty => exact HomogeneousLocalization.val_one
    | @insert j s hjs ih =>
        rw [Finset.prod_insert hjs, Finset.prod_insert hjs,
          HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, ih]]
  simp only [ratio, Away.val_mk]
  simp_rw [Localization.mk_pow]
  rw [Localization.mk_prod (Finset.univ : Finset (Fin 3))]
  apply Localization.mk_eq_mk_iff.mpr
  rw [Localization.r_iff_exists]
  use 1
  simp only [Submonoid.coe_one, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, one_mul]
  congr 1
  simp [Finset.prod_pow_eq_pow_sum, hai]

/-- The coordinate ratios generate the standard chart over the degree-zero coefficient ring. -/
theorem adjoin_ratios_eq_top : Algebra.adjoin (grading R 0) (Set.range (ratio R e)) = ⊤ := by
  apply top_unique
  rw [← Away.adjoin_mk_prod_pow_eq_top (isHomogeneous_X R (e 2)) (Fin 3)
    (fun j ↦ X (e j)) (adjoin_coordinates_eq_top R e) (fun _ ↦ 1)
    (fun j ↦ isHomogeneous_X R (e j))]
  apply Algebra.adjoin_le
  rintro _ ⟨a, ai, hai, _, rfl⟩
  rw [mk_prod_eq R e a ai (by simpa using hai)]
  apply prod_mem
  intro j _
  apply pow_mem
  exact Algebra.subset_adjoin ⟨j, rfl⟩

/-- A ring homomorphism out of the chart is determined by constants and coordinate ratios. -/
theorem ringHom_ext {S : Type*} [CommRing S] (f g : Ring R e →+* S)
    (hc : ∀ r, f (coefficient R e r) = g (coefficient R e r))
    (hv : ∀ j, f (ratio R e j) = g (ratio R e j)) : f = g := by
  apply RingHom.ext
  intro x
  have hx : x ∈ Algebra.adjoin (grading R 0) (Set.range (ratio R e)) := by
    rw [adjoin_ratios_eq_top]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hv j
  | algebraMap r =>
      obtain ⟨r, rfl⟩ := (ProjectiveSpace.degreeZeroEquiv (Fin 3) R).symm.surjective r
      exact hc r
  | add x y _ _ hx hy => simp [hx, hy]
  | mul x y _ _ hx hy => simp [hx, hy]

private theorem fromPolynomial_comp_toPolynomial :
    (fromPolynomial R e).comp (toPolynomial R e) = RingHom.id _ := by
  apply ringHom_ext
  · intro r
    simp
  · intro j
    fin_cases j <;> simp

private theorem toPolynomial_comp_fromPolynomial :
    (toPolynomial R e).comp (fromPolynomial R e) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro j
    fin_cases j <;> simp

/-- The coordinate ring of the standard projective-plane chart is a polynomial ring in the
two remaining coordinate ratios. -/
def equiv : Ring R e ≃+* MvPolynomial (Fin 2) R where
  toFun := toPolynomial R e
  invFun := fromPolynomial R e
  left_inv x := by exact DFunLike.congr_fun (fromPolynomial_comp_toPolynomial R e) x
  right_inv x := by exact DFunLike.congr_fun (toPolynomial_comp_fromPolynomial R e) x
  map_add' := (toPolynomial R e).map_add
  map_mul' := (toPolynomial R e).map_mul

instance : Algebra R (Ring R e) := (coefficient R e).toAlgebra

/-- The chart-coordinate equivalence respects the coefficient ring. -/
def algEquiv : Ring R e ≃ₐ[R] MvPolynomial (Fin 2) R where
  __ := equiv R e
  commutes' := toPolynomial_coefficient R e

open CategoryTheory in
/-- The corresponding actual standard open subscheme of projective space is the spectrum
of the polynomial ring in the two coordinate ratios. -/
def basicOpenIso : (Proj.basicOpen (grading R) (X (e 2))).toScheme ≅
    Spec (CommRingCat.of (MvPolynomial (Fin 2) R)) :=
  Proj.basicOpenIsoSpec (grading R) (X (e 2)) (isHomogeneous_X R (e 2)) zero_lt_one ≪≫
    Scheme.Spec.mapIso (equiv R e).symm.toCommRingCatIso.op

open CategoryTheory in
/-- The polynomial chart map into the actual projective spectrum. -/
def chartMap : Spec (CommRingCat.of (MvPolynomial (Fin 2) R)) ⟶ Proj (grading R) :=
  (basicOpenIso R e).inv ≫ (Proj.basicOpen (grading R) (X (e 2))).ι

open CategoryTheory in
theorem chartMap_eq : chartMap R e =
    Spec.map (CommRingCat.ofHom (toPolynomial R e)) ≫
      Proj.awayι (grading R) (X (e 2)) (isHomogeneous_X R (e 2)) zero_lt_one := by
  rfl

/-- A homogeneous equation on projective space becomes its dehomogenization on this chart. -/
theorem chartMap_preimage_basicOpen (d : ℕ) (f : MvPolynomial (Fin 3) R)
    (hf : f.IsHomogeneous d) (hd : 0 < d) :
    chartMap R e ⁻¹ᵁ Proj.basicOpen (grading R) f =
      PrimeSpectrum.basicOpen (dehomogenize R e f) := by
  rw [chartMap_eq, Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen (grading R) (isHomogeneous_X R (e 2))
    zero_lt_one hf hd]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  simp only [CommRingCat.hom_ofHom, HomogeneousLocalization.Away.isLocalizationElem, pow_one]
  exact toPolynomial_mk R e d f hf

end AlgebraicGeometry.ProjectivePlaneChart
