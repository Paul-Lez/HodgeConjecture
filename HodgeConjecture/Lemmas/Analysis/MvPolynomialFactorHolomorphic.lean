/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Analysis.PolynomialFactorGrowth
public import Other.Analysis.Complex.FiniteSingularityPolynomial
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.RationalRoot

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


/-- A fiber over the simple-root locus has the expected number of distinct roots. -/
theorem mvRoots_card_nodup_of_mem_simpleRootBase {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) :
    (mvFamilySpecialization p z.1).roots.card = p.natDegree ∧
      (mvFamilySpecialization p z.1).roots.Nodup := by
  let q := mvFamilySpecialization p z.1
  have hq : q.Monic := by
    exact hp.map (MvPolynomial.eval z.1)
  have hsplit : q.Splits := IsAlgClosed.splits q
  have hcard : q.roots.card = q.natDegree :=
    hsplit.natDegree_eq_card_roots.symm
  have hdegree : q.natDegree = p.natDegree := by
    exact hp.natDegree_map (MvPolynomial.eval z.1)
  refine ⟨hcard.trans hdegree, ?_⟩
  rw [nodup_roots_iff_of_splits hq.ne_zero hsplit]
  rw [Separable, ← gcd_isUnit_iff, isUnit_iff_degree_eq_zero]
  by_contra hnot
  obtain ⟨w, hw⟩ := Splits.exists_eval_eq_zero
    (Splits.of_dvd hsplit hq.ne_zero (gcd_dvd_left q q.derivative)) hnot
  exact z.2 w
    (eval_eq_zero_of_dvd_of_eval_eq_zero (gcd_dvd_left q q.derivative) hw)
    (eval_eq_zero_of_dvd_of_eval_eq_zero (gcd_dvd_right q q.derivative) hw)

/-- An explicit enumeration of the roots of a simple fiber. -/
noncomputable def mvSimpleRootEnumeration {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) : Fin p.natDegree → ℂ :=
  let r := (mvFamilySpecialization p z.1).roots
  let hcard : r.toFinset.card = p.natDegree :=
    (Multiset.toFinset_card_of_nodup
      (mvRoots_card_nodup_of_mem_simpleRootBase hp z).2).trans
      (mvRoots_card_nodup_of_mem_simpleRootBase hp z).1
  fun i ↦ ((r.toFinset.equivFinOfCardEq hcard).symm i : ℂ)

theorem mvSimpleRootEnumeration_isRoot {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) (i : Fin p.natDegree) :
    (mvFamilySpecialization p z.1).eval (mvSimpleRootEnumeration hp z i) = 0 := by
  apply (mem_roots (hp.map (MvPolynomial.eval z.1)).ne_zero).mp
  change mvSimpleRootEnumeration hp z i ∈
    (mvFamilySpecialization p z.1).roots
  let e := ((mvFamilySpecialization p z.1).roots.toFinset.equivFinOfCardEq
      ((Multiset.toFinset_card_of_nodup
        (mvRoots_card_nodup_of_mem_simpleRootBase hp z).2).trans
        (mvRoots_card_nodup_of_mem_simpleRootBase hp z).1)).symm
  refine Multiset.mem_toFinset.mp ?_
  change (((mvFamilySpecialization p z.1).roots.toFinset.equivFinOfCardEq
    ((Multiset.toFinset_card_of_nodup
      (mvRoots_card_nodup_of_mem_simpleRootBase hp z).2).trans
      (mvRoots_card_nodup_of_mem_simpleRootBase hp z).1)).symm i : ℂ) ∈
    (mvFamilySpecialization p z.1).roots.toFinset
  exact (e i).property

theorem mvSimpleRootEnumeration_injective {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) :
    Function.Injective (mvSimpleRootEnumeration hp z) := by
  intro i j hij
  have hsub : ((mvFamilySpecialization p z.1).roots.toFinset.equivFinOfCardEq
      ((Multiset.toFinset_card_of_nodup
        (mvRoots_card_nodup_of_mem_simpleRootBase hp z).2).trans
        (mvRoots_card_nodup_of_mem_simpleRootBase hp z).1)).symm i =
      ((mvFamilySpecialization p z.1).roots.toFinset.equivFinOfCardEq
      ((Multiset.toFinset_card_of_nodup
        (mvRoots_card_nodup_of_mem_simpleRootBase hp z).2).trans
        (mvRoots_card_nodup_of_mem_simpleRootBase hp z).1)).symm j := by
    exact Subtype.ext (by simpa [mvSimpleRootEnumeration] using hij)
  exact (Equiv.injective _ hsub)

theorem exists_mvSimpleRootEnumeration {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) (w : ℂ)
    (hw : (mvFamilySpecialization p z.1).eval w = 0) :
    ∃ i : Fin p.natDegree, mvSimpleRootEnumeration hp z i = w := by
  have hmem : w ∈ (mvFamilySpecialization p z.1).roots :=
    (mem_roots (hp.map (MvPolynomial.eval z.1)).ne_zero).mpr hw
  let e := ((mvFamilySpecialization p z.1).roots.toFinset.equivFinOfCardEq
    ((Multiset.toFinset_card_of_nodup
      (mvRoots_card_nodup_of_mem_simpleRootBase hp z).2).trans
      (mvRoots_card_nodup_of_mem_simpleRootBase hp z).1)).symm
  have hwfin : w ∈ (mvFamilySpecialization p z.1).roots.toFinset := by
    simpa using hmem
  refine ⟨e.symm ⟨w, hwfin⟩, ?_⟩
  simp [mvSimpleRootEnumeration, e]

/-- The point of the root cover attached to an enumerated root of a simple fiber. -/
noncomputable def mvSimpleRootCoverPoint {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) (i : Fin p.natDegree) : MvSimpleRootCover p :=
  ⟨(z, mvSimpleRootEnumeration hp z i), mvSimpleRootEnumeration_isRoot hp z i⟩

/-- One neighborhood of the base point supports all the finitely many local root branches. -/
theorem eventually_all_mvFamilyEquation_mvLocalRootBranch {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ i : Fin p.natDegree,
      mvFamilyEquation p (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0 := by
  exact eventually_all.2 fun i ↦
    eventually_mvFamilyEquation_mvLocalRootBranch (mvSimpleRootCoverPoint hp z i)

/-- Near the center, the finitely many root branches remain pairwise distinct. -/
theorem eventually_injective_mvLocalRootBranches {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, Function.Injective
      (fun i : Fin p.natDegree ↦ mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') := by
  have hpair : ∀ i j : Fin p.natDegree, i ≠ j →
      ∀ᶠ z' in 𝓝 z.1,
        mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z' ≠
          mvLocalRootBranch (mvSimpleRootCoverPoint hp z j) z' := by
    intro i j hij
    have hne : mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z.1 -
        mvLocalRootBranch (mvSimpleRootCoverPoint hp z j) z.1 ≠ 0 := by
      have hi : mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z.1 =
          mvSimpleRootEnumeration hp z i := by
        change mvLocalRootBranch (mvSimpleRootCoverPoint hp z i)
          (mvSimpleRootCoverPoint hp z i).1.1.1 = _
        exact mvLocalRootBranch_apply_base _
      have hj : mvLocalRootBranch (mvSimpleRootCoverPoint hp z j) z.1 =
          mvSimpleRootEnumeration hp z j := by
        change mvLocalRootBranch (mvSimpleRootCoverPoint hp z j)
          (mvSimpleRootCoverPoint hp z j).1.1.1 = _
        exact mvLocalRootBranch_apply_base _
      rw [hi, hj]
      exact sub_ne_zero.mpr (fun h ↦ hij (mvSimpleRootEnumeration_injective hp z h))
    have hcont :=
      (differentiableAt_mvLocalRootBranch (mvSimpleRootCoverPoint hp z i)).continuousAt.sub
        (differentiableAt_mvLocalRootBranch (mvSimpleRootCoverPoint hp z j)).continuousAt
    filter_upwards [hcont.eventually (isOpen_compl_singleton.mem_nhds hne)] with z' hz
    exact sub_ne_zero.mp hz
  filter_upwards [eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
    eventually_all.2 fun hij : i ≠ j ↦ hpair i j hij] with z' hz
  intro i j heq
  by_contra hij
  exact hz i j hij heq

/-- On a common neighborhood, the local branches exhaust every root of every fiber. -/
theorem eventually_exists_mvLocalRootBranch_eq_of_mvFamilyEquation_eq_zero
    {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic) (z : MvSimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ w : ℂ, mvFamilyEquation p (z', w) = 0 →
      ∃ i : Fin p.natDegree, mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z' = w := by
  filter_upwards [eventually_all_mvFamilyEquation_mvLocalRootBranch hp z,
    eventually_injective_mvLocalRootBranches hp z] with z' hroot hinj
  intro w hw
  let q := mvFamilySpecialization p z'
  let f : Fin p.natDegree → ℂ :=
    fun i ↦ mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z'
  let B : Finset ℂ := Finset.univ.image f
  have hq : q.Monic := hp.map (MvPolynomial.eval z')
  have hdegree : q.natDegree = p.natDegree := hp.natDegree_map (MvPolynomial.eval z')
  have hBcard : B.card = p.natDegree := by
    rw [Finset.card_image_iff.mpr hinj.injOn]
    simp
  have hBroot : ∀ a ∈ B, q.eval a = 0 := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact hroot i
  have hroots : q.roots = B.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero hBroot
    simpa [hdegree] using hBcard.ge
    exact hq.ne_zero
  have hmem : w ∈ B := by
    have hwroot : w ∈ q.roots := (mem_roots hq.ne_zero).mpr hw
    have : w ∈ B.val := by rwa [hroots] at hwroot
    simpa using this
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi⟩

/-- The simple-root base contains a neighborhood of each of its points. -/
theorem eventually_mem_mvSimpleRootBase {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
      (mvFamilySpecialization p z').derivative.eval w ≠ 0 := by
  filter_upwards [eventually_all_mvFamilyEquation_mvLocalRootBranch hp z,
    eventually_injective_mvLocalRootBranches hp z] with z' hroot hinj
  let q := mvFamilySpecialization p z'
  let f : Fin p.natDegree → ℂ :=
    fun i ↦ mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z'
  let B : Finset ℂ := Finset.univ.image f
  have hq : q.Monic := hp.map (MvPolynomial.eval z')
  have hdegree : q.natDegree = p.natDegree := hp.natDegree_map (MvPolynomial.eval z')
  have hBcard : B.card = p.natDegree := by
    rw [Finset.card_image_iff.mpr hinj.injOn]
    simp
  have hBroot : ∀ a ∈ B, q.eval a = 0 := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact hroot i
  have hroots : q.roots = B.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero hBroot
    simpa [hdegree] using hBcard.ge
    exact hq.ne_zero
  intro w hw
  have hnodup : q.roots.Nodup := by rw [hroots]; exact B.nodup
  have hseparable : q.Separable :=
    (nodup_roots_iff_of_splits hq.ne_zero (IsAlgClosed.splits q)).mp hnodup
  intro hderiv
  have hdiv : X - C w ∣ gcd q q.derivative :=
    dvd_gcd (dvd_iff_isRoot.mpr hw) (dvd_iff_isRoot.mpr hderiv)
  exact not_isUnit_X_sub_C w
    (isUnit_of_dvd_unit hdiv ((gcd_isUnit_iff q q.derivative).mpr hseparable))



theorem isOpen_mvSimpleRootBase {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) :
    IsOpen {z : Fin n → ℂ | ∀ w : ℂ, (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact eventually_mem_mvSimpleRootBase hp ⟨z, hz⟩


/-- The locus of individual simple roots over a principal open, in the form used by standard
étale coordinates. Other roots in the same fiber need not be simple. -/
abbrev MvSimpleRootLocusOn {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ))
    (r : MvPolynomial (Fin n) ℂ) :=
  {zw : (Fin n → ℂ) × ℂ // mvFamilyEquation p zw = 0 ∧
    MvPolynomial.eval zw.1 r * (mvFamilySpecialization p zw.1).derivative.eval zw.2 ≠ 0}

noncomputable def mvSimpleRootLocusOnPoint {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (z : MvSimpleRootBase p)
    (hzr : MvPolynomial.eval z.1 r ≠ 0) (i : Fin p.natDegree) : MvSimpleRootLocusOn p r := by
  refine ⟨(z.1, mvSimpleRootEnumeration hp z i), mvSimpleRootEnumeration_isRoot hp z i, ?_⟩
  exact mul_ne_zero hzr (z.2 _ (mvSimpleRootEnumeration_isRoot hp z i))

/-- Membership in a clopen part of the restricted cover is constant along each local branch. -/
theorem eventually_mem_clopen_mvSimpleRootLocusOn_iff {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r))
    (hS : IsClopen S) (z : MvSimpleRootBase p) (hzr : MvPolynomial.eval z.1 r ≠ 0)
    (i : Fin p.natDegree) :
    ∀ᶠ z' in 𝓝 z.1, ∀ (hbase : ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
        (mvFamilySpecialization p z').derivative.eval w ≠ 0)
      (hroot : mvFamilyEquation p
        (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0)
      (hr : MvPolynomial.eval z' r ≠ 0),
      (⟨(z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z'), hroot,
          mul_ne_zero hr (hbase _ hroot)⟩ : MvSimpleRootLocusOn p r) ∈ S ↔
        mvSimpleRootLocusOnPoint hp r z hzr i ∈ S := by
  let U : Set (Fin n → ℂ) := {z' | (∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
      (mvFamilySpecialization p z').derivative.eval w ≠ 0) ∧
    mvFamilyEquation p (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0 ∧
    MvPolynomial.eval z' r ≠ 0}
  have hnonzero : ∀ᶠ z' in 𝓝 z.1, MvPolynomial.eval z' r ≠ 0 :=
    (AnalyticOnNhd.eval_mvPolynomial r z.1 (Set.mem_univ _)).continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds hzr)
  have hU : U ∈ 𝓝 z.1 := inter_mem (eventually_mem_mvSimpleRootBase hp z)
    (inter_mem (eventually_mvFamilyEquation_mvLocalRootBranch (mvSimpleRootCoverPoint hp z i))
      hnonzero)
  have hzU : z.1 ∈ U := by
    refine ⟨z.2, ?_, hzr⟩
    change (mvFamilySpecialization p z.1).eval
      (mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z.1) = 0
    have hbranch : mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z.1 =
        mvSimpleRootEnumeration hp z i := by
      simpa [mvSimpleRootCoverPoint] using
        mvLocalRootBranch_apply_base (mvSimpleRootCoverPoint hp z i)
    rw [hbranch]
    exact mvSimpleRootEnumeration_isRoot hp z i
  let g : U → MvSimpleRootLocusOn p r := fun x ↦
    ⟨(x.1, mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) x.1), x.2.2.1,
      mul_ne_zero x.2.2.2 (x.2.1 _ x.2.2.1)⟩
  have hg : ContinuousAt g ⟨z.1, hzU⟩ := by
    apply ContinuousAt.codRestrict
    apply ContinuousAt.prodMk
    · exact continuousAt_subtype_val
    · exact (differentiableAt_mvLocalRootBranch (mvSimpleRootCoverPoint hp z i)).continuousAt.comp_of_eq
        continuousAt_subtype_val rfl
  have hg_center : g ⟨z.1, hzU⟩ = mvSimpleRootLocusOnPoint hp r z hzr i := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z.1 =
          mvSimpleRootEnumeration hp z i
      exact mvLocalRootBranch_apply_base _
  have hmap : Filter.map ((↑) : U → (Fin n → ℂ)) (𝓝 ⟨z.1, hzU⟩) = 𝓝 z.1 :=
    map_nhds_subtype_coe_eq_nhds hzU hU
  by_cases hi : mvSimpleRootLocusOnPoint hp r z hzr i ∈ S
  · have hevent : ∀ᶠ x in 𝓝 (⟨z.1, hzU⟩ : U), g x ∈ S :=
      hg (hS.isOpen.mem_nhds (hg_center.symm ▸ hi))
    have hevent' : ∀ᶠ z' in 𝓝 z.1, ∀ hz' : z' ∈ U, g ⟨z', hz'⟩ ∈ S := by
      rw [← hmap, eventually_map]
      filter_upwards [hevent] with x hx
      intro hx'
      convert hx using 1
    filter_upwards [hU, hevent'] with z' hz' hmem hbase hroot hr
    exact ⟨fun _ ↦ hi, fun _ ↦ by simpa only [g, Subtype.ext_iff] using hmem hz'⟩
  · have hevent : ∀ᶠ x in 𝓝 (⟨z.1, hzU⟩ : U), g x ∈ Sᶜ :=
      hg (hS.isClosed.isOpen_compl.mem_nhds (by simpa [hg_center] using hi))
    have hevent' : ∀ᶠ z' in 𝓝 z.1, ∀ hz' : z' ∈ U, g ⟨z', hz'⟩ ∈ Sᶜ := by
      rw [← hmap, eventually_map]
      filter_upwards [hevent] with x hx
      intro hx'
      convert hx using 1
    filter_upwards [hU, hevent'] with z' hz' hmem hbase hroot hr
    exact ⟨fun h ↦ ((hmem hz') h).elim, fun h ↦ (hi h).elim⟩


/-- Roots selected in a simple fiber by a subset of the principal-open root cover. -/
def mvSelectedRootsOn {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r))
    (z : MvSimpleRootBase p) (hzr : MvPolynomial.eval z.1 r ≠ 0) : Multiset ℂ := by
  classical
  exact (mvFamilySpecialization p z.1).roots.filter fun w ↦
    ∃ h : (mvFamilySpecialization p z.1).eval w = 0,
      (⟨(z.1, w), h, mul_ne_zero hzr (z.2 w h)⟩ : MvSimpleRootLocusOn p r) ∈ S

/-- The monic fiber factor selected on the principal-open root cover. -/
def mvSelectedFactorOn {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r))
    (z : MvSimpleRootBase p) (hzr : MvPolynomial.eval z.1 r ≠ 0) : Polynomial ℂ :=
  ((mvSelectedRootsOn r S z hzr).map fun w ↦ X - C w).prod

theorem mvSelectedFactorOn_monic {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r))
    (z : MvSimpleRootBase p) (hzr : MvPolynomial.eval z.1 r ≠ 0) :
    (mvSelectedFactorOn r S z hzr).Monic :=
  monic_multisetProd_X_sub_C (mvSelectedRootsOn r S z hzr)

theorem mvSelectedFactorOn_dvd {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r))
    (z : MvSimpleRootBase p) (hzr : MvPolynomial.eval z.1 r ≠ 0) :
    mvSelectedFactorOn r S z hzr ∣ mvFamilySpecialization p z.1 := by
  classical
  rw [mvSelectedFactorOn, mvSelectedRootsOn]
  exact (Multiset.prod_dvd_prod_of_le
    (Multiset.map_le_map (Multiset.filter_le _ _))).trans
      (mvFamilySpecialization p z.1).prod_multiset_X_sub_C_dvd

theorem natDegree_mvSelectedFactorOn {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r))
    (z : MvSimpleRootBase p) (hzr : MvPolynomial.eval z.1 r ≠ 0) :
    (mvSelectedFactorOn r S z hzr).natDegree = (mvSelectedRootsOn r S z hzr).card := by
  simp [mvSelectedFactorOn]


noncomputable def mvSelectedBranchIndicesOn {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r))
    (z : MvSimpleRootBase p) (hzr : MvPolynomial.eval z.1 r ≠ 0) :
    Finset (Fin p.natDegree) := by
  classical
  exact Finset.univ.filter fun i ↦ mvSimpleRootLocusOnPoint hp r z hzr i ∈ S

/-- Near a center fiber, the restricted selection is a fixed set of local branches. -/
theorem eventually_mvSelectedRootsOn_eq_map_mvLocalRootBranches {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r)) (hS : IsClopen S)
    (z : MvSimpleRootBase p) (hzr : MvPolynomial.eval z.1 r ≠ 0) :
    ∀ᶠ z' in 𝓝 z.1, ∀ (hbase : ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
        (mvFamilySpecialization p z').derivative.eval w ≠ 0)
      (hr : MvPolynomial.eval z' r ≠ 0),
      mvSelectedRootsOn r S ⟨z', hbase⟩ hr =
        (mvSelectedBranchIndicesOn hp r S z hzr).1.map fun i ↦
          mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z' := by
  classical
  have hselection : ∀ᶠ z' in 𝓝 z.1, ∀ i : Fin p.natDegree,
      ∀ (hbase : ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
          (mvFamilySpecialization p z').derivative.eval w ≠ 0)
        (hroot : mvFamilyEquation p
          (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0)
        (hr : MvPolynomial.eval z' r ≠ 0),
        ((⟨(z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z'), hroot,
            mul_ne_zero hr (hbase _ hroot)⟩ : MvSimpleRootLocusOn p r) ∈ S ↔
          mvSimpleRootLocusOnPoint hp r z hzr i ∈ S) :=
    eventually_all.2 fun i ↦ eventually_mem_clopen_mvSimpleRootLocusOn_iff hp r S hS z hzr i
  filter_upwards [eventually_all_mvFamilyEquation_mvLocalRootBranch hp z,
    eventually_injective_mvLocalRootBranches hp z,
    eventually_exists_mvLocalRootBranch_eq_of_mvFamilyEquation_eq_zero hp z,
    hselection] with z' hroot hinj hexhaust hselect
  intro hbase hr
  let q := mvFamilySpecialization p z'
  rw [mvSelectedRootsOn]
  apply (Multiset.Nodup.ext (s := _) (t := _)
    ((mvRoots_card_nodup_of_mem_simpleRootBase hp ⟨z', hbase⟩).2.filter _)
    ((Multiset.nodup_map_iff_of_injective hinj).2
      (mvSelectedBranchIndicesOn hp r S z hzr).nodup)).2
  intro w
  constructor
  · intro hw
    rw [Multiset.mem_filter] at hw
    obtain ⟨hwroot, hmem⟩ := hw
    have hweval : q.eval w = 0 :=
      (mem_roots (hp.map (MvPolynomial.eval z')).ne_zero).mp hwroot
    obtain ⟨i, hi⟩ := hexhaust w hweval
    rw [Multiset.mem_map]
    refine ⟨i, ?_, hi⟩
    obtain ⟨hwproof, hwS⟩ := hmem
    have hbranchS :
        (⟨(z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z'), hroot i,
          mul_ne_zero hr (hbase _ (hroot i))⟩ : MvSimpleRootLocusOn p r) ∈ S := by
      convert hwS using 1
      all_goals simp [hi]
    change i ∈ mvSelectedBranchIndicesOn hp r S z hzr
    simpa [mvSelectedBranchIndicesOn] using
      (hselect i hbase (hroot i) hr).mp hbranchS
  · intro hw
    rw [Multiset.mem_map] at hw
    obtain ⟨i, hiI, rfl⟩ := hw
    rw [Multiset.mem_filter]
    refine ⟨(mem_roots (hp.map (MvPolynomial.eval z')).ne_zero).mpr (hroot i), ?_⟩
    refine ⟨hroot i, ?_⟩
    apply (hselect i hbase (hroot i) hr).mpr
    simpa [mvSelectedBranchIndicesOn] using hiI

/-- The degree of a clopen-selected restricted fiber factor is locally constant. -/
theorem eventually_natDegree_mvSelectedFactorOn_eq_card {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r)) (hS : IsClopen S)
    (z : MvSimpleRootBase p) (hzr : MvPolynomial.eval z.1 r ≠ 0) :
    ∀ᶠ z' in 𝓝 z.1, ∀ (hbase : ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
        (mvFamilySpecialization p z').derivative.eval w ≠ 0)
      (hr : MvPolynomial.eval z' r ≠ 0),
      (mvSelectedFactorOn r S ⟨z', hbase⟩ hr).natDegree =
        (mvSelectedBranchIndicesOn hp r S z hzr).card := by
  filter_upwards [eventually_mvSelectedRootsOn_eq_map_mvLocalRootBranches hp r S hS z hzr]
    with z' hz hbase hr
  rw [natDegree_mvSelectedFactorOn, hz hbase hr, Multiset.card_map]
  rfl


noncomputable def mvLocalBranchFactor {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic) (z : MvSimpleRootBase p)
    (I : Finset (Fin p.natDegree)) : (Fin n → ℂ) → Polynomial ℂ := fun z' ↦
  (I.1.map fun i ↦ X - C (mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z')).prod

private theorem differentiableAt_coeff_X_sub_C_mvLocalRootBranch {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic) (z : MvSimpleRootBase p)
    (i : Fin p.natDegree) (k : ℕ) : DifferentiableAt ℂ
      (fun z' ↦ (X - C (mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z')).coeff k) z.1 := by
  rcases k with _ | k
  · simpa [mvSimpleRootCoverPoint] using
      (differentiableAt_mvLocalRootBranch (mvSimpleRootCoverPoint hp z i)).neg
  rcases k with _ | k <;> simp

theorem differentiableAt_coeff_mvLocalBranchFactor {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic) (z : MvSimpleRootBase p)
    (I : Finset (Fin p.natDegree)) (k : ℕ) :
    DifferentiableAt ℂ (fun z' ↦ (mvLocalBranchFactor hp z I z').coeff k) z.1 := by
  induction I using Finset.induction_on generalizing k with
  | empty => simp [mvLocalBranchFactor]
  | @insert i I hi hI =>
      have hfactor : mvLocalBranchFactor hp z (insert i I) = fun z' ↦
          (X - C (mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z')) *
            mvLocalBranchFactor hp z I z' := by
        funext z'
        simp [mvLocalBranchFactor, hi]
      rw [hfactor]
      simp_rw [coeff_mul]
      apply DifferentiableAt.fun_sum
      intro ij hij
      exact (differentiableAt_coeff_X_sub_C_mvLocalRootBranch hp z i ij.1).mul (hI ij.2)

theorem eventually_mvSelectedFactorOn_eq_mvLocalBranchFactor {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r)) (hS : IsClopen S)
    (z : MvSimpleRootBase p) (hzr : MvPolynomial.eval z.1 r ≠ 0) :
    ∀ᶠ z' in 𝓝 z.1, ∀ (hbase : ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
        (mvFamilySpecialization p z').derivative.eval w ≠ 0)
      (hr : MvPolynomial.eval z' r ≠ 0),
      mvSelectedFactorOn r S ⟨z', hbase⟩ hr =
        mvLocalBranchFactor hp z (mvSelectedBranchIndicesOn hp r S z hzr) z' := by
  filter_upwards [eventually_mvSelectedRootsOn_eq_map_mvLocalRootBranches hp r S hS z hzr]
    with z' hz hbase hr
  rw [mvSelectedFactorOn, mvLocalBranchFactor, hz hbase hr, Multiset.map_map]
  rfl

noncomputable def mvSelectedFactorCoeffOn {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (r : MvPolynomial (Fin n) ℂ)
    (S : Set (MvSimpleRootLocusOn p r))
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0)
    (k : ℕ) (z : Fin n → ℂ) : ℂ := by
  classical
  exact if hr : MvPolynomial.eval z r ≠ 0 then
    (mvSelectedFactorOn r S ⟨z, hsimple z hr⟩ hr).coeff k else 0

theorem mvSelectedFactorCoeffOn_eq {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (r : MvPolynomial (Fin n) ℂ)
    (S : Set (MvSimpleRootLocusOn p r)) (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 →
      ∀ w : ℂ, (mvFamilySpecialization p z).eval w = 0 →
        (mvFamilySpecialization p z).derivative.eval w ≠ 0)
    (k : ℕ) (z : Fin n → ℂ) (hr : MvPolynomial.eval z r ≠ 0) :
    mvSelectedFactorCoeffOn r S hsimple k z =
      (mvSelectedFactorOn r S ⟨z, hsimple z hr⟩ hr).coeff k := by
  simp [mvSelectedFactorCoeffOn, hr]

theorem differentiableOn_mvSelectedFactorCoeffOn {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r)) (hS : IsClopen S)
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0) (k : ℕ) :
    DifferentiableOn ℂ (mvSelectedFactorCoeffOn r S hsimple k)
      {z | MvPolynomial.eval z r ≠ 0} := by
  intro z hz
  let zbase : MvSimpleRootBase p := ⟨z, hsimple z hz⟩
  let I := mvSelectedBranchIndicesOn hp r S zbase hz
  have heq : ∀ᶠ z' in 𝓝 z,
      mvSelectedFactorCoeffOn r S hsimple k z' =
        (mvLocalBranchFactor hp zbase I z').coeff k := by
    filter_upwards [eventually_mem_mvSimpleRootBase hp zbase,
      (AnalyticOnNhd.eval_mvPolynomial r z (Set.mem_univ _)).continuousAt.eventually
        (isOpen_compl_singleton.mem_nhds hz),
      eventually_mvSelectedFactorOn_eq_mvLocalBranchFactor hp r S hS zbase hz]
      with z' hbase hr hfactor
    rw [mvSelectedFactorCoeffOn_eq r S hsimple k z' hr]
    simpa only [I, Subtype.ext_iff] using
      congrArg (fun q : Polynomial ℂ ↦ q.coeff k) (hfactor hbase hr)
  exact ((differentiableAt_coeff_mvLocalBranchFactor hp zbase I k).congr_of_eventuallyEq heq).differentiableWithinAt


theorem exists_mvSelectedFactorCoeffOn_growth {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r))
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ k z, MvPolynomial.eval z r ≠ 0 →
      ‖mvSelectedFactorCoeffOn r S hsimple k z‖ ≤ C * (1 + ‖z‖) ^ N := by
  obtain ⟨C, N, hC, hbound⟩ := exists_monic_factor_coeff_mvPolynomial_growth p hp
  refine ⟨C, N, hC, fun k z hr ↦ ?_⟩
  rw [mvSelectedFactorCoeffOn_eq r S hsimple k z hr]
  exact hbound z _ (mvSelectedFactorOn_monic r S ⟨z, hsimple z hr⟩ hr)
    (mvSelectedFactorOn_dvd r S ⟨z, hsimple z hr⟩ hr) k

theorem exists_mvPolynomial_mvSelectedFactorCoeffOn {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (hr0 : r ≠ 0)
    (S : Set (MvSimpleRootLocusOn p r)) (hS : IsClopen S)
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0) (k : ℕ) :
    ∃ a : MvPolynomial (Fin n) ℂ, ∀ z (hr : MvPolynomial.eval z r ≠ 0),
      MvPolynomial.eval z a = (mvSelectedFactorOn r S ⟨z, hsimple z hr⟩ hr).coeff k := by
  obtain ⟨C, N, hC, hbound⟩ := exists_mvSelectedFactorCoeffOn_growth hp r S hsimple
  obtain ⟨a, ha⟩ := Complex.exists_mvPolynomial_of_polynomial_growth_on_nonzero r hr0
    (differentiableOn_mvSelectedFactorCoeffOn hp r S hS hsimple k) hC N
    (fun z hz ↦ hbound k z hz)
  exact ⟨a, fun z hr ↦ (ha z hr).trans (mvSelectedFactorCoeffOn_eq r S hsimple k z hr)⟩

/-- The selected fiber factors on `D(r)` are specializations of one polynomial family. -/
theorem exists_mvPolynomialFamily_mvSelectedFactorOn {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (hr0 : r ≠ 0)
    (S : Set (MvSimpleRootLocusOn p r)) (hS : IsClopen S)
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0) :
    ∃ q : Polynomial (MvPolynomial (Fin n) ℂ), q.natDegree ≤ p.natDegree ∧
      ∀ z (hr : MvPolynomial.eval z r ≠ 0),
        q.map (MvPolynomial.eval z) = mvSelectedFactorOn r S ⟨z, hsimple z hr⟩ hr := by
  classical
  choose a ha using fun k ↦
    exists_mvPolynomial_mvSelectedFactorCoeffOn hp r hr0 S hS hsimple k
  let q : Polynomial (MvPolynomial (Fin n) ℂ) :=
    ∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial k (a k)
  have hqdegree : q.natDegree ≤ p.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [show q.coeff k = ∑ x ∈ Finset.range (p.natDegree + 1),
      (Polynomial.monomial x (a x)).coeff k by simp [q]]
    apply Finset.sum_eq_zero
    intro x hx
    apply coeff_monomial_of_ne
    exact ne_of_gt (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hx)) hk)
  refine ⟨q, hqdegree, fun z hr ↦ ?_⟩
  ext k
  rw [coeff_map]
  rw [show q.coeff k = ∑ x ∈ Finset.range (p.natDegree + 1),
    (Polynomial.monomial x (a x)).coeff k by simp [q], map_sum]
  by_cases hk : k ≤ p.natDegree
  · rw [Finset.sum_eq_single k]
    · rw [coeff_monomial_same]
      exact ha k z hr
    · intro x hx hxk
      rw [coeff_monomial_of_ne _ hxk.symm]
      simp
    · exact fun h ↦ (h (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))).elim
  · have hdegree : (mvSelectedFactorOn r S ⟨z, hsimple z hr⟩ hr).natDegree ≤
        p.natDegree :=
      (natDegree_le_of_dvd (mvSelectedFactorOn_dvd r S ⟨z, hsimple z hr⟩ hr)
        (hp.map (MvPolynomial.eval z)).ne_zero).trans_eq
          (hp.natDegree_map (MvPolynomial.eval z))
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree (lt_of_not_ge hk))]
    apply Finset.sum_eq_zero
    intro x hx
    have hxk : x ≠ k := fun h ↦ hk (h ▸ Nat.le_of_lt_succ (Finset.mem_range.mp hx))
    rw [coeff_monomial_of_ne _ hxk.symm]
    simp


/-- Fiberwise divisibility on a nonempty principal open implies divisibility of polynomial
families, provided the divisor family is monic. -/
theorem dvd_of_map_dvd_on_mvPolynomial_nonzero {n : ℕ}
    (p q : Polynomial (MvPolynomial (Fin n) ℂ)) (hq : q.Monic)
    (r : MvPolynomial (Fin n) ℂ) (hr0 : r ≠ 0)
    (hdiv : ∀ z, MvPolynomial.eval z r ≠ 0 →
      q.map (MvPolynomial.eval z) ∣ p.map (MvPolynomial.eval z)) : q ∣ p := by
  rw [← modByMonic_eq_zero_iff_dvd hq]
  let s := p %ₘ q
  change s = 0
  apply Polynomial.ext
  intro k
  have hclosed : IsClosed {z : Fin n → ℂ | MvPolynomial.eval z (s.coeff k) = 0} :=
    isClosed_singleton.preimage
      (AnalyticOnNhd.eval_mvPolynomial (s.coeff k)).continuous
  have hsubset : {z : Fin n → ℂ | MvPolynomial.eval z r ≠ 0} ⊆
      {z : Fin n → ℂ | MvPolynomial.eval z (s.coeff k) = 0} := by
    intro z hz
    have hsmap : s.map (MvPolynomial.eval z) = 0 := by
      change (p %ₘ q).map (MvPolynomial.eval z) = 0
      rw [map_modByMonic _ hq,
        (modByMonic_eq_zero_iff_dvd (hq.map (MvPolynomial.eval z))).2 (hdiv z hz)]
    have hc := congrArg (fun t : Polynomial ℂ ↦ t.coeff k) hsmap
    simpa [coeff_map] using hc
  have hall : ∀ z : Fin n → ℂ, MvPolynomial.eval z (s.coeff k) = 0 := by
    intro z
    apply (closure_minimal hsubset hclosed)
    rw [(MvPolynomial.dense_complex_nonzero r hr0).closure_eq]
    trivial
  exact MvPolynomial.funext (fun z ↦ by simpa using hall z)


noncomputable def mvSelectedDegreeOn {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r))
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0)
    (z : {z : Fin n → ℂ // MvPolynomial.eval z r ≠ 0}) : ℕ :=
  (mvSelectedFactorOn r S ⟨z.1, hsimple z.1 z.2⟩ z.2).natDegree

theorem isLocallyConstant_mvSelectedDegreeOn {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r)) (hS : IsClopen S)
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0) :
    IsLocallyConstant (mvSelectedDegreeOn r S hsimple) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  let zbase : MvSimpleRootBase p := ⟨z.1, hsimple z.1 z.2⟩
  have hdeg := eventually_natDegree_mvSelectedFactorOn_eq_card hp r S hS zbase z.2
  have hcenter := hdeg.self_of_nhds (hsimple z.1 z.2) z.2
  filter_upwards [continuousAt_subtype_val.eventually hdeg] with y hy
  change (mvSelectedFactorOn r S ⟨y.1, hsimple y.1 y.2⟩ y.2).natDegree =
    (mvSelectedFactorOn r S ⟨z.1, hsimple z.1 z.2⟩ z.2).natDegree
  exact (hy (hsimple y.1 y.2) y.2).trans hcenter.symm

theorem mvSelectedDegreeOn_eq {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (hr0 : r ≠ 0)
    (S : Set (MvSimpleRootLocusOn p r)) (hS : IsClopen S)
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0)
    (x y : {z : Fin n → ℂ // MvPolynomial.eval z r ≠ 0}) :
    mvSelectedDegreeOn r S hsimple x = mvSelectedDegreeOn r S hsimple y := by
  let _ : PreconnectedSpace {z : Fin n → ℂ // MvPolynomial.eval z r ≠ 0} :=
    Subtype.preconnectedSpace
      (MvPolynomial.isPathConnected_complex_nonzero r hr0).isConnected.isPreconnected
  exact (isLocallyConstant_mvSelectedDegreeOn hp r S hS hsimple).apply_eq_of_preconnectedSpace x y


theorem mvPolynomial_eq_of_eval_eq_on_nonzero {n : ℕ}
    (r : MvPolynomial (Fin n) ℂ) (hr0 : r ≠ 0) (a b : MvPolynomial (Fin n) ℂ)
    (h : ∀ z, MvPolynomial.eval z r ≠ 0 → MvPolynomial.eval z a = MvPolynomial.eval z b) :
    a = b := by
  apply MvPolynomial.funext
  intro z
  have hclosed : IsClosed {x : Fin n → ℂ | MvPolynomial.eval x (a - b) = 0} :=
    isClosed_singleton.preimage
      (AnalyticOnNhd.eval_mvPolynomial (a - b)).continuous
  have hsubset : {x : Fin n → ℂ | MvPolynomial.eval x r ≠ 0} ⊆
      {x : Fin n → ℂ | MvPolynomial.eval x (a - b) = 0} := by
    intro x hx
    simpa using sub_eq_zero.mpr (h x hx)
  have hz := closure_minimal hsubset hclosed
  have : MvPolynomial.eval z (a - b) = 0 := by
    apply hz
    rw [(MvPolynomial.dense_complex_nonzero r hr0).closure_eq]
    trivial
  rw [map_sub] at this
  exact sub_eq_zero.mp this

/-- The algebraized selected family can be chosen monic because its degree is constant on `D(r)`. -/
theorem exists_monic_mvPolynomialFamily_mvSelectedFactorOn {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (hr0 : r ≠ 0)
    (S : Set (MvSimpleRootLocusOn p r)) (hS : IsClopen S)
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0) :
    ∃ q : Polynomial (MvPolynomial (Fin n) ℂ), q.Monic ∧
      ∀ z (hr : MvPolynomial.eval z r ≠ 0),
        q.map (MvPolynomial.eval z) = mvSelectedFactorOn r S ⟨z, hsimple z hr⟩ hr := by
  obtain ⟨q, hqbound, hq⟩ :=
    exists_mvPolynomialFamily_mvSelectedFactorOn hp r hr0 S hS hsimple
  obtain ⟨x, hx⟩ := (MvPolynomial.isPathConnected_complex_nonzero r hr0).nonempty
  let xb : {z : Fin n → ℂ // MvPolynomial.eval z r ≠ 0} := ⟨x, hx⟩
  let d := mvSelectedDegreeOn r S hsimple xb
  have hdegree : ∀ z (hz : MvPolynomial.eval z r ≠ 0),
      (mvSelectedFactorOn r S ⟨z, hsimple z hz⟩ hz).natDegree = d := by
    intro z hz
    exact mvSelectedDegreeOn_eq hp r hr0 S hS hsimple ⟨z, hz⟩ xb
  have hdle : d ≤ p.natDegree := by
    rw [← hdegree x hx]
    exact (natDegree_le_of_dvd (mvSelectedFactorOn_dvd r S ⟨x, hsimple x hx⟩ hx)
      (hp.map (MvPolynomial.eval x)).ne_zero).trans_eq
        (hp.natDegree_map (MvPolynomial.eval x))
  have habove : ∀ k, d < k → q.coeff k = 0 := by
    intro k hk
    apply mvPolynomial_eq_of_eval_eq_on_nonzero r hr0
    intro z hz
    have hc := congrArg (fun t : Polynomial ℂ ↦ t.coeff k) (hq z hz)
    rw [coeff_map] at hc
    have hzero : (mvSelectedFactorOn r S ⟨z, hsimple z hz⟩ hz).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simpa [hdegree z hz] using hk)
    simpa [hzero] using hc
  have hqle : q.natDegree ≤ d := natDegree_le_iff_coeff_eq_zero.mpr habove
  have hcoeffd : q.coeff d = 1 := by
    apply mvPolynomial_eq_of_eval_eq_on_nonzero r hr0
    intro z hz
    have hc := congrArg (fun t : Polynomial ℂ ↦ t.coeff d) (hq z hz)
    rw [coeff_map] at hc
    have hm := (mvSelectedFactorOn_monic r S ⟨z, hsimple z hz⟩ hz).coeff_natDegree
    rw [hdegree z hz] at hm
    simpa [hm] using hc
  have hqnat : q.natDegree = d :=
    natDegree_eq_of_le_of_coeff_ne_zero hqle (hcoeffd.symm ▸ one_ne_zero)
  have hqmonic : q.Monic := by
    rw [Monic, leadingCoeff, hqnat, hcoeffd]
  exact ⟨q, hqmonic, hq⟩

/-- The monic algebraized selected family divides the original polynomial family. -/
theorem exists_monic_dvd_mvPolynomialFamily_mvSelectedFactorOn {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (hr0 : r ≠ 0)
    (S : Set (MvSimpleRootLocusOn p r)) (hS : IsClopen S)
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0) :
    ∃ q : Polynomial (MvPolynomial (Fin n) ℂ), q.Monic ∧ q ∣ p ∧
      ∀ z (hr : MvPolynomial.eval z r ≠ 0),
        q.map (MvPolynomial.eval z) = mvSelectedFactorOn r S ⟨z, hsimple z hr⟩ hr := by
  obtain ⟨q, hqmonic, hq⟩ :=
    exists_monic_mvPolynomialFamily_mvSelectedFactorOn hp r hr0 S hS hsimple
  refine ⟨q, hqmonic, dvd_of_map_dvd_on_mvPolynomial_nonzero p q hqmonic r hr0 ?_, hq⟩
  intro z hz
  rw [hq z hz]
  exact mvSelectedFactorOn_dvd r S ⟨z, hsimple z hz⟩ hz


private theorem mvSimpleRootLocusOn_set_eq_empty_of_factor_eq_one {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r))
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0)
    (hfactor : ∀ z (hr : MvPolynomial.eval z r ≠ 0),
      mvSelectedFactorOn r S ⟨z, hsimple z hr⟩ hr = 1) : S = ∅ := by
  classical
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hr : MvPolynomial.eval x.1.1 r ≠ 0 :=
    left_ne_zero_of_mul x.2.2
  have hroot : (mvFamilySpecialization p x.1.1).eval x.1.2 = 0 := x.2.1
  have hmem : x.1.2 ∈ mvSelectedRootsOn r S ⟨x.1.1, hsimple x.1.1 hr⟩ hr := by
    rw [mvSelectedRootsOn, Multiset.mem_filter]
    refine ⟨(mem_roots ?_).mpr hroot, ⟨hroot, ?_⟩⟩
    · exact (hp.map (MvPolynomial.eval x.1.1)).ne_zero
    · convert hx using 1
  have hcard : 0 < (mvSelectedRootsOn r S ⟨x.1.1, hsimple x.1.1 hr⟩ hr).card :=
    Multiset.card_pos.mpr (by intro hzero; have := hmem; rw [hzero] at this; simp at this)
  have hdegree := natDegree_mvSelectedFactorOn r S ⟨x.1.1, hsimple x.1.1 hr⟩ hr
  rw [hfactor x.1.1 hr, natDegree_one] at hdegree
  omega

private theorem mvSimpleRootLocusOn_set_eq_univ_of_factor_eq_family {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootLocusOn p r))
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0)
    (hfactor : ∀ z (hr : MvPolynomial.eval z r ≠ 0),
      mvSelectedFactorOn r S ⟨z, hsimple z hr⟩ hr = mvFamilySpecialization p z) :
    S = Set.univ := by
  classical
  ext x
  simp only [Set.mem_univ, iff_true]
  have hr : MvPolynomial.eval x.1.1 r ≠ 0 := left_ne_zero_of_mul x.2.2
  have hroot : (mvFamilySpecialization p x.1.1).eval x.1.2 = 0 := x.2.1
  have hfactorRoot :
      (mvSelectedFactorOn r S ⟨x.1.1, hsimple x.1.1 hr⟩ hr).eval x.1.2 = 0 := by
    rw [hfactor x.1.1 hr]
    exact hroot
  have hrootmem : x.1.2 ∈
      (mvSelectedFactorOn r S ⟨x.1.1, hsimple x.1.1 hr⟩ hr).roots :=
    (mem_roots (mvSelectedFactorOn_monic r S ⟨x.1.1, hsimple x.1.1 hr⟩ hr).ne_zero).mpr
      hfactorRoot
  have hselected : x.1.2 ∈ mvSelectedRootsOn r S ⟨x.1.1, hsimple x.1.1 hr⟩ hr := by
    simpa [mvSelectedFactorOn] using hrootmem
  rw [mvSelectedRootsOn, Multiset.mem_filter] at hselected
  obtain ⟨_, hxS⟩ := hselected.2
  convert hxS using 1

/-- The root cover over a simple principal open is connected for an irreducible monic family. -/
theorem connectedSpace_mvSimpleRootLocusOn {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic) (hirr : Irreducible p)
    (hpdeg : 0 < p.natDegree) (r : MvPolynomial (Fin n) ℂ) (hr0 : r ≠ 0)
    (hsimple : ∀ z, MvPolynomial.eval z r ≠ 0 → ∀ w : ℂ,
      (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0) :
    ConnectedSpace (MvSimpleRootLocusOn p r) := by
  rw [connectedSpace_iff_clopen]
  constructor
  · obtain ⟨z, hz⟩ := (MvPolynomial.isPathConnected_complex_nonzero r hr0).nonempty
    let f := mvFamilySpecialization p z
    have hfmonic : f.Monic := hp.map (MvPolynomial.eval z)
    have hfdegree : f.natDegree = p.natDegree := hp.natDegree_map (MvPolynomial.eval z)
    have hfroots : f.roots.card = f.natDegree :=
      (IsAlgClosed.splits f).natDegree_eq_card_roots.symm
    have hnonempty : f.roots ≠ 0 := by
      intro hzero
      have : f.roots.card = 0 := by simp [hzero]
      omega
    obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hnonempty
    have hwroot : f.eval w = 0 := (mem_roots hfmonic.ne_zero).mp hw
    refine ⟨⟨(z, w), hwroot, ?_⟩⟩
    exact mul_ne_zero hz (hsimple z hz w hwroot)
  · intro S hS
    obtain ⟨q, hqmonic, hqdvd, hq⟩ :=
      exists_monic_dvd_mvPolynomialFamily_mvSelectedFactorOn hp r hr0 S hS hsimple
    rcases hirr.dvd_iff.mp hqdvd with hqunit | hpq
    · left
      apply mvSimpleRootLocusOn_set_eq_empty_of_factor_eq_one hp r S hsimple
      intro z hz
      rw [← hq z hz, hqmonic.eq_one_of_isUnit hqunit]
      simp
    · right
      have hpqeq : p = q := eq_of_monic_of_associated hp hqmonic hpq
      apply mvSimpleRootLocusOn_set_eq_univ_of_factor_eq_family r S hsimple
      intro z hz
      rw [← hq z hz, ← hpqeq]
      rfl


/-- The resultant cutting out fibers with a multiple root. -/
noncomputable def mvRamificationPolynomial {n : ℕ}
    (p : Polynomial (MvPolynomial (Fin n) ℂ)) : MvPolynomial (Fin n) ℂ :=
  resultant p p.derivative p.natDegree (p.natDegree - 1)

theorem eval_mvRamificationPolynomial {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (z : Fin n → ℂ) :
    MvPolynomial.eval z (mvRamificationPolynomial p) =
      resultant (mvFamilySpecialization p z) (mvFamilySpecialization p z).derivative
        p.natDegree (p.natDegree - 1) := by
  change (MvPolynomial.eval z) (resultant p p.derivative p.natDegree
    (p.natDegree - 1)) = _
  calc
    _ = resultant (p.map (MvPolynomial.eval z))
        (p.derivative.map (MvPolynomial.eval z)) p.natDegree (p.natDegree - 1) :=
      (resultant_map_map p p.derivative p.natDegree (p.natDegree - 1)
        (MvPolynomial.eval z)).symm
    _ = _ := by
      simp only [mvFamilySpecialization]
      rw [derivative_map]

theorem simple_fiber_of_eval_mvRamificationPolynomial_ne_zero {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic) (z : Fin n → ℂ)
    (hz : MvPolynomial.eval z (mvRamificationPolynomial p) ≠ 0) :
    ∀ w : ℂ, (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0 := by
  intro w hw hwd
  let q := mvFamilySpecialization p z
  have hq : q.Monic := hp.map (MvPolynomial.eval z)
  have hncp : ¬IsCoprime q q.derivative := by
    intro hc
    obtain ⟨a, b, hab⟩ := hc
    have heval := congrArg (Polynomial.eval w) hab
    rw [eval_add, eval_mul, eval_mul, hw, hwd] at heval
    simp at heval
  have hres : resultant q q.derivative = 0 :=
    resultant_eq_zero_iff.mpr ⟨Or.inl hq.ne_zero, hncp⟩
  have hdegree : q.natDegree = p.natDegree := hp.natDegree_map (MvPolynomial.eval z)
  rw [hdegree, natDegree_derivative, hdegree] at hres
  apply hz
  rw [eval_mvRamificationPolynomial]
  exact hres

theorem mvRamificationPolynomial_ne_zero_of_isCoprime_fractionRing {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (hcoprime : IsCoprime
      (p.map (algebraMap (MvPolynomial (Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n) ℂ))))
      (p.map (algebraMap (MvPolynomial (Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n) ℂ)))).derivative) :
    mvRamificationPolynomial p ≠ 0 := by
  let K := FractionRing (MvPolynomial (Fin n) ℂ)
  let φ : MvPolynomial (Fin n) ℂ →+* K := algebraMap _ K
  let pK : Polynomial K := p.map φ
  have hdegree : pK.natDegree = p.natDegree := hp.natDegree_map φ
  have hres : resultant pK pK.derivative p.natDegree (p.natDegree - 1) ≠ 0 := by
    simpa only [hdegree, natDegree_derivative] using
      resultant_ne_zero pK pK.derivative hcoprime
  intro hzero
  apply hres
  have hmap : φ (mvRamificationPolynomial p) =
      resultant pK pK.derivative p.natDegree (p.natDegree - 1) := by
    rw [mvRamificationPolynomial]
    calc
      _ = resultant (p.map φ) (p.derivative.map φ) p.natDegree (p.natDegree - 1) :=
        (resultant_map_map p p.derivative p.natDegree (p.natDegree - 1) φ).symm
      _ = _ := by
        change resultant pK (p.derivative.map φ) p.natDegree (p.natDegree - 1) = _
        rw [derivative_map]
  rw [hzero, map_zero] at hmap
  exact hmap.symm

theorem mvRamificationPolynomial_ne_zero_of_irreducible {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic) (hirr : Irreducible p) :
    mvRamificationPolynomial p ≠ 0 := by
  let _ : IsIntegrallyClosed (MvPolynomial (Fin n) ℂ) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  apply mvRamificationPolynomial_ne_zero_of_isCoprime_fractionRing hp
  rw [← separable_def]
  exact ((hp.irreducible_iff_irreducible_map_fraction_map).mp hirr).separable

/-- Multiplying any nonzero normalization denominator by the ramification resultant gives a
principal open whose complex root cover is connected. -/
theorem connectedSpace_mvSimpleRootLocusOn_mul_mvRamificationPolynomial {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic) (hirr : Irreducible p)
    (r₀ : MvPolynomial (Fin n) ℂ) (hr₀ : r₀ ≠ 0) :
    ConnectedSpace (MvSimpleRootLocusOn p (r₀ * mvRamificationPolynomial p)) := by
  have hram := mvRamificationPolynomial_ne_zero_of_irreducible hp hirr
  apply connectedSpace_mvSimpleRootLocusOn hp hirr
    (hp.natDegree_pos_of_not_isUnit hirr.not_isUnit) _ (mul_ne_zero hr₀ hram)
  intro z hz
  have hzram : MvPolynomial.eval z (mvRamificationPolynomial p) ≠ 0 := by
    rw [map_mul] at hz
    exact right_ne_zero_of_mul hz
  exact simple_fiber_of_eval_mvRamificationPolynomial_ne_zero hp z hzram

end

end Polynomial
