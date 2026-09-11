/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Analysis.PolynomialFactorGrowth
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Factors selected on the simple-root cover

This file studies a monic polynomial whose coefficients are polynomials in one complex
parameter.  Over the locus where every root is simple, a subset of the root cover canonically
selects a monic factor in each fiber.
-/

@[expose] public section

open scoped Polynomial Topology
open Filter
open Set

namespace Polynomial

noncomputable section

/-- Specialization of a one-parameter polynomial family. -/
def familySpecialization (p : Polynomial (Polynomial ℂ)) (z : ℂ) : Polynomial ℂ :=
  p.map (Polynomial.evalRingHom z)

/-- The equation of the polynomial family in parameter-root coordinates. -/
def familyEquation (p : Polynomial (Polynomial ℂ)) (zw : ℂ × ℂ) : ℂ :=
  (familySpecialization p zw.1).eval zw.2

theorem analyticAt_familyEquation (p : Polynomial (Polynomial ℂ)) (zw : ℂ × ℂ) :
    AnalyticAt ℂ (familyEquation p) zw := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show familyEquation (p + q) = fun u ↦ familyEquation p u + familyEquation q u by
        funext u
        simp [familyEquation, familySpecialization]]
      exact hp.add hq
  | monomial k a =>
      rw [show familyEquation (Polynomial.monomial k a) =
          fun u : ℂ × ℂ ↦ a.eval u.1 * u.2 ^ k by
        funext u
        simp [familyEquation, familySpecialization]]
      exact ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) a) zw.1 (Set.mem_univ _)).comp (ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.fst ℂ ℂ ℂ) zw) |>.mul
          ((ContinuousLinearMap.analyticAt
            (ContinuousLinearMap.snd ℂ ℂ ℂ) zw).pow k)

theorem fderiv_familyEquation_comp_inr (p : Polynomial (Polynomial ℂ)) (zw : ℂ × ℂ) :
    fderiv ℂ (familyEquation p) zw ∘L ContinuousLinearMap.inr ℂ ℂ ℂ =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((familySpecialization p zw.1).derivative.eval zw.2) := by
  have hins : HasFDerivAt (fun t : ℂ ↦ (zw.1, t))
      (ContinuousLinearMap.inr ℂ ℂ ℂ) zw.2 :=
    (hasFDerivAt_const zw.1 zw.2).prodMk (hasFDerivAt_id zw.2)
  have hchain := ((analyticAt_familyEquation p zw).differentiableAt).hasFDerivAt.comp zw.2 hins
  have hchain' : HasFDerivAt (fun t : ℂ ↦ (familySpecialization p zw.1).eval t)
      (fderiv ℂ (familyEquation p) zw ∘L ContinuousLinearMap.inr ℂ ℂ ℂ) zw.2 := by
    simpa [Function.comp_def, familyEquation] using hchain
  have hpoly := (familySpecialization p zw.1).hasFDerivAt zw.2
  simpa using hchain'.unique hpoly

theorem hasStrictFDerivAt_familyEquation (p : Polynomial (Polynomial ℂ)) (zw : ℂ × ℂ) :
    HasStrictFDerivAt (familyEquation p) (fderiv ℂ (familyEquation p) zw) zw :=
  (analyticAt_familyEquation p zw).hasStrictFDerivAt

/-- The parameter locus on which all roots of a polynomial family are simple. -/
def SimpleRootBase (p : Polynomial (Polynomial ℂ)) :=
  {z : ℂ // ∀ w : ℂ, (familySpecialization p z).eval w = 0 →
    (familySpecialization p z).derivative.eval w ≠ 0}

/-- The simple-root cover of a one-parameter polynomial family. -/
def SimpleRootCover (p : Polynomial (Polynomial ℂ)) :=
  {zw : SimpleRootBase p × ℂ // (familySpecialization p zw.1.1).eval zw.2 = 0}

/-- Projection of the simple-root cover to its parameter. -/
def SimpleRootCover.proj {p : Polynomial (Polynomial ℂ)} : SimpleRootCover p → SimpleRootBase p :=
  fun zw ↦ zw.1.1

lemma simpleRootCover_rootDirection_isInvertible {p : Polynomial (Polynomial ℂ)}
    (zw : SimpleRootCover p) :
    (fderiv ℂ (familyEquation p) (zw.1.1.1, zw.1.2) ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  rw [fderiv_familyEquation_comp_inr]
  let d := (familySpecialization p zw.1.1.1).derivative.eval zw.1.2
  have hd : d ≠ 0 := zw.1.1.2 zw.1.2 zw.2
  change (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).IsInvertible
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d⁻¹)
  · ext
    simp [hd]
  · ext
    simp [hd]

/-- The implicit local root branch through a point of the simple-root cover. -/
noncomputable def localRootBranch {p : Polynomial (Polynomial ℂ)}
    (zw : SimpleRootCover p) : ℂ → ℂ :=
  let hs := hasStrictFDerivAt_familyEquation p (zw.1.1.1, zw.1.2)
  hs.implicitFunctionOfProdDomain (simpleRootCover_rootDirection_isInvertible zw)

theorem hasStrictFDerivAt_localRootBranch {p : Polynomial (Polynomial ℂ)}
    (zw : SimpleRootCover p) :
    HasStrictFDerivAt (localRootBranch zw)
      (-(fderiv ℂ (familyEquation p) (zw.1.1.1, zw.1.2) ∘L
          ContinuousLinearMap.inr ℂ ℂ ℂ).inverse ∘L
        (fderiv ℂ (familyEquation p) (zw.1.1.1, zw.1.2) ∘L
          ContinuousLinearMap.inl ℂ ℂ ℂ)) zw.1.1.1 := by
  simpa [localRootBranch] using
    (hasStrictFDerivAt_familyEquation p (zw.1.1.1, zw.1.2)).hasStrictFDerivAt_implicitFunctionOfProdDomain
      (simpleRootCover_rootDirection_isInvertible zw)

/-- Near its center, the implicit branch consists of roots of the specialized family. -/
theorem eventually_familyEquation_localRootBranch {p : Polynomial (Polynomial ℂ)}
    (zw : SimpleRootCover p) :
    ∀ᶠ z in 𝓝 zw.1.1.1, familyEquation p (z, localRootBranch zw z) = 0 := by
  let hs := hasStrictFDerivAt_familyEquation p (zw.1.1.1, zw.1.2)
  have h := hs.eventually_apply_implicitFunctionOfProdDomain
    (simpleRootCover_rootDirection_isInvertible zw)
  have hzero : familyEquation p (zw.1.1.1, zw.1.2) = 0 := zw.2
  simpa [localRootBranch, hzero] using h

/-- The multiset of roots in a fiber which belong to a specified subset of the root cover. -/
def selectedRoots {p : Polynomial (Polynomial ℂ)}
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) : Multiset ℂ := by
  classical
  exact (familySpecialization p z.1).roots.filter fun w ↦
    ∃ h : (familySpecialization p z.1).eval w = 0,
      (⟨(z, w), h⟩ : SimpleRootCover p) ∈ S

/-- The monic fiber factor selected by a subset of the simple-root cover. -/
def selectedFactor {p : Polynomial (Polynomial ℂ)} (_hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) : Polynomial ℂ :=
  ((selectedRoots S z).map fun w ↦ X - C w).prod

theorem selectedFactor_monic {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) :
    (selectedFactor hp S z).Monic := by
  exact monic_multisetProd_X_sub_C (selectedRoots S z)

theorem selectedFactor_dvd {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) :
    selectedFactor hp S z ∣ familySpecialization p z.1 := by
  classical
  rw [selectedFactor, selectedRoots]
  exact (Multiset.prod_dvd_prod_of_le
    (Multiset.map_le_map (Multiset.filter_le _ _))).trans
      (familySpecialization p z.1).prod_multiset_X_sub_C_dvd

theorem natDegree_selectedFactor {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) :
    (selectedFactor hp S z).natDegree =
      (selectedRoots S z).card := by
  simp [selectedFactor]

end

end Polynomial
