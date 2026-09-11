/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Analysis.PolynomialFactorHolomorphic

/-!
# Factors in multivariable polynomial families

The local analytic theory for a polynomial whose coefficients depend polynomially on a
finite-dimensional complex parameter space.
-/

@[expose] public section

open scoped Polynomial Topology
open Filter Set

namespace Polynomial

noncomputable section

/-- Specialization of a multivariable polynomial family. -/
def mvFamilySpecialization {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ))
    (z : Fin n → ℂ) : Polynomial ℂ :=
  p.map (MvPolynomial.eval z)

/-- The equation of a multivariable polynomial family in parameter-root coordinates. -/
def mvFamilyEquation {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ))
    (zw : (Fin n → ℂ) × ℂ) : ℂ :=
  (mvFamilySpecialization p zw.1).eval zw.2

theorem analyticAt_mvFamilyEquation {n : ℕ}
    (p : Polynomial (MvPolynomial (Fin n) ℂ)) (zw : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℂ (mvFamilyEquation p) zw := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show mvFamilyEquation (p + q) =
          fun u ↦ mvFamilyEquation p u + mvFamilyEquation q u by
        funext u
        simp [mvFamilyEquation, mvFamilySpecialization]]
      exact hp.add hq
  | monomial k a =>
      rw [show mvFamilyEquation (Polynomial.monomial k a) =
          fun u : (Fin n → ℂ) × ℂ ↦ MvPolynomial.eval u.1 a * u.2 ^ k by
        funext u
        simp [mvFamilyEquation, mvFamilySpecialization]]
      have ha : AnalyticAt ℂ (fun z : Fin n → ℂ ↦ MvPolynomial.eval z a) zw.1 :=
        AnalyticOnNhd.eval_mvPolynomial a zw.1 (Set.mem_univ _)
      exact (ha.comp (ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ) zw)).mul
          ((ContinuousLinearMap.analyticAt
            (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ) zw).pow k)

theorem fderiv_mvFamilyEquation_comp_inr {n : ℕ}
    (p : Polynomial (MvPolynomial (Fin n) ℂ)) (zw : (Fin n → ℂ) × ℂ) :
    fderiv ℂ (mvFamilyEquation p) zw ∘L ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((mvFamilySpecialization p zw.1).derivative.eval zw.2) := by
  have hins : HasFDerivAt (fun t : ℂ ↦ (zw.1, t))
      (ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ) zw.2 :=
    (hasFDerivAt_const zw.1 zw.2).prodMk (hasFDerivAt_id zw.2)
  have hchain := ((analyticAt_mvFamilyEquation p zw).differentiableAt).hasFDerivAt.comp zw.2 hins
  have hchain' : HasFDerivAt (fun t : ℂ ↦ (mvFamilySpecialization p zw.1).eval t)
      (fderiv ℂ (mvFamilyEquation p) zw ∘L
        ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ) zw.2 := by
    simpa [Function.comp_def, mvFamilyEquation] using hchain
  exact hchain'.unique ((mvFamilySpecialization p zw.1).hasFDerivAt zw.2)

theorem hasStrictFDerivAt_mvFamilyEquation {n : ℕ}
    (p : Polynomial (MvPolynomial (Fin n) ℂ)) (zw : (Fin n → ℂ) × ℂ) :
    HasStrictFDerivAt (mvFamilyEquation p) (fderiv ℂ (mvFamilyEquation p) zw) zw :=
  (analyticAt_mvFamilyEquation p zw).hasStrictFDerivAt

/-- The parameter locus on which all roots are simple. -/
abbrev MvSimpleRootBase {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ)) :=
  {z : Fin n → ℂ // ∀ w : ℂ, (mvFamilySpecialization p z).eval w = 0 →
    (mvFamilySpecialization p z).derivative.eval w ≠ 0}

/-- The root cover above the simple-root locus. -/
abbrev MvSimpleRootCover {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ)) :=
  {zw : MvSimpleRootBase p × ℂ // (mvFamilySpecialization p zw.1.1).eval zw.2 = 0}

def MvSimpleRootCover.proj {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)} :
    MvSimpleRootCover p → MvSimpleRootBase p := fun zw ↦ zw.1.1

lemma mvSimpleRootCover_rootDirection_isInvertible {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (zw : MvSimpleRootCover p) :
    (fderiv ℂ (mvFamilyEquation p) (zw.1.1.1, zw.1.2) ∘L
      ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ).IsInvertible := by
  rw [fderiv_mvFamilyEquation_comp_inr]
  let d := (mvFamilySpecialization p zw.1.1.1).derivative.eval zw.1.2
  have hd : d ≠ 0 := zw.1.1.2 zw.1.2 zw.2
  change (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).IsInvertible
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d⁻¹)
  · ext
    simp [hd]
  · ext
    simp [hd]

/-- The implicit local root branch through a point of the multivariable root cover. -/
noncomputable def mvLocalRootBranch {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (zw : MvSimpleRootCover p) :
    (Fin n → ℂ) → ℂ :=
  (hasStrictFDerivAt_mvFamilyEquation p (zw.1.1.1, zw.1.2)).implicitFunctionOfProdDomain
    (mvSimpleRootCover_rootDirection_isInvertible zw)

theorem hasStrictFDerivAt_mvLocalRootBranch {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (zw : MvSimpleRootCover p) :
    HasStrictFDerivAt (mvLocalRootBranch zw)
      (-(fderiv ℂ (mvFamilyEquation p) (zw.1.1.1, zw.1.2) ∘L
          ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ).inverse ∘L
        (fderiv ℂ (mvFamilyEquation p) (zw.1.1.1, zw.1.2) ∘L
          ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ)) zw.1.1.1 := by
  simpa [mvLocalRootBranch] using
    (hasStrictFDerivAt_mvFamilyEquation p (zw.1.1.1, zw.1.2)).hasStrictFDerivAt_implicitFunctionOfProdDomain
      (mvSimpleRootCover_rootDirection_isInvertible zw)

theorem mvLocalRootBranch_apply_base {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (zw : MvSimpleRootCover p) :
    mvLocalRootBranch zw zw.1.1.1 = zw.1.2 := by
  let hs := hasStrictFDerivAt_mvFamilyEquation p (zw.1.1.1, zw.1.2)
  have h := (hs.eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (mvSimpleRootCover_rootDirection_isInvertible zw)).self_of_nhds
  apply h.mp
  rfl

theorem differentiableAt_mvLocalRootBranch {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (zw : MvSimpleRootCover p) :
    DifferentiableAt ℂ (mvLocalRootBranch zw) zw.1.1.1 :=
  (hasStrictFDerivAt_mvLocalRootBranch zw).differentiableAt

theorem eventually_mvFamilyEquation_mvLocalRootBranch {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (zw : MvSimpleRootCover p) :
    ∀ᶠ z in 𝓝 zw.1.1.1, mvFamilyEquation p (z, mvLocalRootBranch zw z) = 0 := by
  let hs := hasStrictFDerivAt_mvFamilyEquation p (zw.1.1.1, zw.1.2)
  have h := hs.eventually_apply_implicitFunctionOfProdDomain
    (mvSimpleRootCover_rootDirection_isInvertible zw)
  have hzero : mvFamilyEquation p (zw.1.1.1, zw.1.2) = 0 := zw.2
  simpa [mvLocalRootBranch, hzero] using h

end

end Polynomial
